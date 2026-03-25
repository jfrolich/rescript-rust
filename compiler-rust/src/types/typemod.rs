//! Module type checking for ReScript.
//!
//! This module handles type checking of:
//! - Module expressions (`ModuleExpr`)
//! - Structures (module bodies)
//! - Signatures (module types)
//! - Functor application and coercion

#![allow(unused_variables)]
#![allow(dead_code)]

use crate::ident::Ident;
use crate::intern::StrIdx;
use crate::location::Location;
use crate::parse_arena::{LidentIdx, LocIdx, Located, ParseArena};
use crate::parser::ast::Attributes;
use crate::parser::ast::RecFlag;
use crate::parser::ast::Variance as ParserVariance;
use crate::parser::ast::{
    Attribute as ParsedAttribute, Payload as ParsedPayload,
    ModuleExpr as ParsedModuleExpr, ModuleExprDesc as ParsedModuleExprDesc,
    StructureItem as ParsedStructureItem, StructureItemDesc as ParsedStructureItemDesc,
};
use crate::parser::longident::Longident;
use crate::types::Path;
use crate::types::Variance as TypesVariance;
use crate::types::env::Env;
use crate::types::type_expr::TypeExprRef;
use crate::types::typecore::{
    TypeCheckContext, TypeCoreError, transl_type, type_binding, type_expression,
};
use crate::types::typedtree::{
    EnvRef, Expression, IncludeDeclaration, ModuleBinding, ModuleCoercion, ModuleExpr,
    ModuleExprDesc, ModuleType, ModuleTypeDeclaration, OpenDeclaration, Structure, StructureItem,
    StructureItemDesc, TypeExtension, TypedConstructorArguments, TypedConstructorDeclaration,
    TypedCoreType, TypedCoreTypeDesc, TypedLabelDeclaration, TypedTypeDeclaration, TypedTypeKind,
    ValueBinding,
};
use std::collections::{HashMap, HashSet};
use std::cell::Cell;

// ============================================================================
// Helper Functions for Path Conversion
// ============================================================================

/// Convert a Longident to a Path.
pub fn path_from_longident<'a>(
    lid: &Longident,
    get_str: impl Fn(StrIdx) -> &'a str + Copy,
) -> Path {
    match lid {
        Longident::Lident(name) => Path::pident(Ident::create_local(get_str(*name))),
        Longident::Ldot(prefix, name) => {
            let prefix_path = path_from_longident(prefix, get_str);
            Path::pdot(prefix_path, get_str(*name))
        }
        Longident::Lapply(functor, arg) => {
            let functor_path = path_from_longident(functor, get_str);
            let arg_path = path_from_longident(arg, get_str);
            Path::papply(functor_path, arg_path)
        }
    }
}

/// Wrap a translated label type in Ttyp_poly if not already poly.
/// Mirrors OCaml `Ast_helper.Typ.force_poly` + `transl_simple_type` flow in `transl_labels`:
/// if the parsed label type was already `Ptyp_poly`, `transl_type` already produced a
/// `Ttyp_poly` core type, so we don't double-wrap. If it wasn't poly, we wrap in
/// `Ttyp_poly([], inner)` to match OCaml's `force_poly` behavior.
fn force_poly_typed_core_type(
    ctx: &crate::types::context::TypeContext<'_>,
    typed_core_type: TypedCoreType,
    ty_ref: TypeExprRef,
) -> (TypedCoreType, TypeExprRef) {
    match &typed_core_type.ctyp_desc {
        TypedCoreTypeDesc::Ttyp_poly(_, _) => {
            // Already a Ttyp_poly — return as-is, like OCaml force_poly on Ptyp_poly
            (typed_core_type, ty_ref)
        }
        _ => {
            // Wrap in Ttyp_poly([], inner), like OCaml force_poly on non-Ptyp_poly
            let poly_ty = ctx.new_poly(ty_ref, vec![]);
            let poly_ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_poly(vec![], Box::new(typed_core_type.clone())),
                ctyp_type: poly_ty,
                ctyp_env: typed_core_type.ctyp_env,
                ctyp_loc: typed_core_type.ctyp_loc,
                ctyp_attributes: Attributes::new(),
            };
            (poly_ctyp, poly_ty)
        }
    }
}

fn parser_attr_to_decl_attr(
    arena: &ParseArena,
    attr: &ParsedAttribute,
) -> crate::types::decl::Attribute {
    let (name, payload) = attr;
    let attr_payload = match payload {
        ParsedPayload::PStr(_) => crate::types::decl::AttributePayload::Structure(vec![]),
        ParsedPayload::PSig(_) => crate::types::decl::AttributePayload::Structure(vec![]),
        ParsedPayload::PTyp(_) => crate::types::decl::AttributePayload::Ident("<core_type>".into()),
        ParsedPayload::PPat(_) => crate::types::decl::AttributePayload::Ident("<pattern>".into()),
    };
    crate::types::decl::Attribute {
        attr_name: crate::types::asttypes::Located {
            txt: arena.get_string(name.txt).to_string(),
            loc: arena.to_location(name.loc),
        },
        attr_payload,
        attr_loc: arena.to_location(name.loc),
    }
}

fn parser_attrs_to_decl_attrs(
    arena: &ParseArena,
    attrs: &Attributes,
) -> Vec<crate::types::decl::Attribute> {
    attrs.iter()
        .map(|attr| parser_attr_to_decl_attr(arena, attr))
        .collect()
}

fn decl_attr_to_parser_attr(
    arena: &ParseArena,
    attr: &crate::types::decl::Attribute,
) -> ParsedAttribute {
    let name_idx = arena
        .find_string_idx(&attr.attr_name.txt)
        .unwrap_or_else(|| {
            panic!(
                "decl attribute name must already be interned in ParseArena: {}",
                attr.attr_name.txt
            )
        });
    (
        Located::mknoloc(name_idx),
        ParsedPayload::PStr(Box::new(vec![])),
    )
}

fn decl_attrs_to_parser_attrs(
    arena: &ParseArena,
    attrs: &[crate::types::decl::Attribute],
) -> Attributes {
    Attributes::from_vec(
        attrs.iter()
            .map(|attr| decl_attr_to_parser_attr(arena, attr))
            .collect(),
    )
}

/// Try to convert a parsed module expression to a module path.
/// Mirrors OCaml `Typemod.path_of_module` for applicative functor paths.
fn path_of_parsed_module_expr(mod_expr: &ParsedModuleExpr, arena: &ParseArena) -> Option<Path> {
    match &*mod_expr.pmod_desc {
        ParsedModuleExprDesc::Pmod_ident(lid) => {
            let longident = arena.get_longident(lid.txt);
            Some(path_from_longident(longident, |idx| arena.get_string(idx)))
        }
        ParsedModuleExprDesc::Pmod_apply(functor, arg) => {
            let funct_path = path_of_parsed_module_expr(arena.get_mod_expr(*functor), arena)?;
            let arg_path = path_of_parsed_module_expr(arena.get_mod_expr(*arg), arena)?;
            Some(Path::papply(funct_path, arg_path))
        }
        ParsedModuleExprDesc::Pmod_constraint(inner, _) => path_of_parsed_module_expr(arena.get_mod_expr(*inner), arena),
        _ => None,
    }
}

fn collect_functor_arg_module_aliases(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    arg_expr: &ParsedModuleExpr,
    arena: &ParseArena,
) -> HashMap<String, Path> {
    fn resolved_path_of_parsed_module_expr(
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        mod_expr: &ParsedModuleExpr,
        arena: &ParseArena,
    ) -> Option<Path> {
        match &*mod_expr.pmod_desc {
            ParsedModuleExprDesc::Pmod_ident(lid) => {
                let longident = arena.get_longident(lid.txt);
                lookup_module_path_by_lid(
                    longident,
                    arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .or_else(|| Some(path_from_longident(longident, |idx| arena.get_string(idx))))
            }
            ParsedModuleExprDesc::Pmod_apply(functor, arg) => {
                let funct_path = resolved_path_of_parsed_module_expr(
                    tctx,
                    env,
                    arena.get_mod_expr(*functor),
                    arena,
                )?;
                let arg_path =
                    resolved_path_of_parsed_module_expr(tctx, env, arena.get_mod_expr(*arg), arena)?;
                Some(Path::papply(funct_path, arg_path))
            }
            ParsedModuleExprDesc::Pmod_constraint(inner, _) => {
                resolved_path_of_parsed_module_expr(tctx, env, arena.get_mod_expr(*inner), arena)
            }
            _ => None,
        }
    }

    let mut aliases = HashMap::new();
    if let ParsedModuleExprDesc::Pmod_structure(items) = &*arg_expr.pmod_desc {
        for item in items.iter() {
            if let ParsedStructureItemDesc::Pstr_module(mb) = &*item.pstr_desc {
                let name = arena.get_string(mb.pmb_name.txt).to_string();
                let mod_expr = arena.get_mod_expr(mb.pmb_expr);
                if let Some(path) = resolved_path_of_parsed_module_expr(tctx, env, mod_expr, arena)
                {
                    aliases.insert(name, path);
                }
            }
        }
    }
    aliases
}

fn inline_record_type_params(
    ctx: &crate::types::context::TypeContext<'_>,
    parent_type_params: &[TypeExprRef],
    labels: &[crate::types::LabelDeclaration],
) -> Vec<TypeExprRef> {
    parent_type_params
        .iter()
        .copied()
        .filter(|param| {
            labels
                .iter()
                .any(|label| crate::types::ctype::deep_occur(ctx, *param, label.ld_type))
        })
        .collect()
}

fn find_existing_loc_idx(arena: &ParseArena, target: &Location) -> Option<LocIdx> {
    for idx in (0..arena.locations().len()).rev() {
        let loc_idx = LocIdx(idx as u32);
        if arena.to_location(loc_idx) == *target {
            return Some(loc_idx);
        }
    }
    None
}

fn include_module_flat_name(mod_expr: &ModuleExpr) -> Option<String> {
    include_module_root_path(mod_expr).map(|path| path.name().replace('.', "_"))
}

fn include_module_root_path(mod_expr: &ModuleExpr) -> Option<Path> {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(path, _) => Some(path.clone()),
        ModuleExprDesc::Tmod_constraint(inner, _, _, _) => include_module_root_path(inner),
        _ => None,
    }
}

fn rewrite_included_path_to_local(
    path: &Path,
    include_root_path: Option<&Path>,
    include_flat_name: Option<&str>,
    local_type_ids: &HashMap<String, Ident>,
    local_module_ids: &HashMap<String, Ident>,
    local_modtype_ids: &HashMap<String, Ident>,
) -> Option<Path> {
    let rewrite_direct_child = |name: &str| {
        local_type_ids
            .get(name)
            .or_else(|| local_module_ids.get(name))
            .or_else(|| local_modtype_ids.get(name))
            .map(|id| Path::Pident(id.clone()))
    };

    match path {
        Path::Pident(id) => {
            if include_flat_name.is_some_and(|flat| id.name() == flat) {
                None
            } else {
                None
            }
        }
        Path::Pdot(prefix, name, pos) => {
            if include_root_path.is_some_and(|root| prefix.as_ref().same(root)) {
                if let Some(rewritten) = rewrite_direct_child(name) {
                    return Some(rewritten);
                }
            }

            if let Path::Pident(prefix_id) = prefix.as_ref() {
                if include_flat_name.is_some_and(|flat| prefix_id.name() == flat) {
                    if let Some(rewritten) = rewrite_direct_child(name) {
                        return Some(rewritten);
                    }
                }
            }

            rewrite_included_path_to_local(
                prefix,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
            )
            .map(|rewritten_prefix| Path::Pdot(Box::new(rewritten_prefix), name.clone(), *pos))
        }
        Path::Papply(functor, arg) => {
            let rewritten_functor = rewrite_included_path_to_local(
                functor,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
            );
            let rewritten_arg = rewrite_included_path_to_local(
                arg,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
            );
            if rewritten_functor.is_none() && rewritten_arg.is_none() {
                None
            } else {
                Some(Path::Papply(
                    Box::new(rewritten_functor.unwrap_or_else(|| functor.as_ref().clone())),
                    Box::new(rewritten_arg.unwrap_or_else(|| arg.as_ref().clone())),
                ))
            }
        }
    }
}

fn rewrite_included_type_paths_to_local(
    ctx: &crate::types::context::TypeContext<'_>,
    ty_ref: TypeExprRef,
    include_root_path: Option<&Path>,
    include_flat_name: Option<&str>,
    local_type_ids: &HashMap<String, Ident>,
    local_module_ids: &HashMap<String, Ident>,
    local_modtype_ids: &HashMap<String, Ident>,
    visited: &mut HashSet<TypeExprRef>,
) {
    use crate::types::type_expr::{RowField, TypeDesc};

    let ty_ref = ctx.repr(ty_ref);
    if !visited.insert(ty_ref) {
        return;
    }

    let desc = ctx.get_desc(ty_ref).clone();
    match &desc {
        TypeDesc::Tconstr { path, args, abbrev } => {
            if let Some(rewritten_path) = rewrite_included_path_to_local(
                path,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
            ) {
                ctx.set_desc(
                    ty_ref,
                    TypeDesc::Tconstr {
                        path: rewritten_path,
                        args: args.clone(),
                        abbrev: *abbrev,
                    },
                );
            }
            for arg in args {
                rewrite_included_type_paths_to_local(
                    ctx,
                    *arg,
                    include_root_path,
                    include_flat_name,
                    local_type_ids,
                    local_module_ids,
                    local_modtype_ids,
                    visited,
                );
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            rewrite_included_type_paths_to_local(
                ctx,
                arg.typ,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
                visited,
            );
            rewrite_included_type_paths_to_local(
                ctx,
                *ret,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
                visited,
            );
        }
        TypeDesc::Ttuple(types) => {
            for ty in types {
                rewrite_included_type_paths_to_local(
                    ctx,
                    *ty,
                    include_root_path,
                    include_flat_name,
                    local_type_ids,
                    local_module_ids,
                    local_modtype_ids,
                    visited,
                );
            }
        }
        TypeDesc::Tlink(ty) | TypeDesc::Tsubst(ty) => {
            rewrite_included_type_paths_to_local(
                ctx,
                *ty,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
                visited,
            );
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_included_type_paths_to_local(
                ctx,
                *body,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
                visited,
            );
            for var in vars {
                rewrite_included_type_paths_to_local(
                    ctx,
                    *var,
                    include_root_path,
                    include_flat_name,
                    local_type_ids,
                    local_module_ids,
                    local_modtype_ids,
                    visited,
                );
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_included_type_paths_to_local(
                ctx,
                *fields,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
                visited,
            );
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_included_type_paths_to_local(
                ctx,
                *typ,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
                visited,
            );
            rewrite_included_type_paths_to_local(
                ctx,
                *rest,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
                visited,
            );
        }
        TypeDesc::Tvariant(row) => {
            rewrite_included_type_paths_to_local(
                ctx,
                row.row_more,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
                visited,
            );
            for (_, field) in &row.row_fields {
                match field {
                    RowField::Rpresent(Some(ty)) => rewrite_included_type_paths_to_local(
                        ctx,
                        *ty,
                        include_root_path,
                        include_flat_name,
                        local_type_ids,
                        local_module_ids,
                        local_modtype_ids,
                        visited,
                    ),
                    RowField::Reither { types, .. } => {
                        for ty in types {
                            rewrite_included_type_paths_to_local(
                                ctx,
                                *ty,
                                include_root_path,
                                include_flat_name,
                                local_type_ids,
                                local_module_ids,
                                local_modtype_ids,
                                visited,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { args, .. } => {
            for arg in args {
                rewrite_included_type_paths_to_local(
                    ctx,
                    *arg,
                    include_root_path,
                    include_flat_name,
                    local_type_ids,
                    local_module_ids,
                    local_modtype_ids,
                    visited,
                );
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

fn rewrite_included_type_decl_paths_to_local(
    ctx: &crate::types::context::TypeContext<'_>,
    id: &Ident,
    decl: &mut crate::types::decl::TypeDeclaration,
    include_root_path: Option<&Path>,
    include_flat_name: Option<&str>,
    local_type_ids: &HashMap<String, Ident>,
    local_module_ids: &HashMap<String, Ident>,
    local_modtype_ids: &HashMap<String, Ident>,
    visited: &mut HashSet<TypeExprRef>,
) {
    decl.type_path = Some(Path::Pident(id.clone()));
    for param in &decl.type_params {
        rewrite_included_type_paths_to_local(
            ctx,
            *param,
            include_root_path,
            include_flat_name,
            local_type_ids,
            local_module_ids,
            local_modtype_ids,
            visited,
        );
    }
    if let Some(manifest) = decl.type_manifest {
        rewrite_included_type_paths_to_local(
            ctx,
            manifest,
            include_root_path,
            include_flat_name,
            local_type_ids,
            local_module_ids,
            local_modtype_ids,
            visited,
        );
    }
    match &mut decl.type_kind {
        crate::types::TypeKind::TypeVariant(constructors) => {
            for cd in constructors {
                match &cd.cd_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for arg in args {
                            rewrite_included_type_paths_to_local(
                                ctx,
                                *arg,
                                include_root_path,
                                include_flat_name,
                                local_type_ids,
                                local_module_ids,
                                local_modtype_ids,
                                visited,
                            );
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for label in labels {
                            rewrite_included_type_paths_to_local(
                                ctx,
                                label.ld_type,
                                include_root_path,
                                include_flat_name,
                                local_type_ids,
                                local_module_ids,
                                local_modtype_ids,
                                visited,
                            );
                        }
                    }
                }
                if let Some(res_ty) = cd.cd_res {
                    rewrite_included_type_paths_to_local(
                        ctx,
                        res_ty,
                        include_root_path,
                        include_flat_name,
                        local_type_ids,
                        local_module_ids,
                        local_modtype_ids,
                        visited,
                    );
                }
            }
        }
        crate::types::TypeKind::TypeRecord(labels, _) => {
            for label in labels {
                rewrite_included_type_paths_to_local(
                    ctx,
                    label.ld_type,
                    include_root_path,
                    include_flat_name,
                    local_type_ids,
                    local_module_ids,
                    local_modtype_ids,
                    visited,
                );
            }
        }
        crate::types::TypeKind::TypeAbstract | crate::types::TypeKind::TypeOpen => {}
    }
}

fn rewrite_included_module_type_paths_to_local(
    ctx: &crate::types::context::TypeContext<'_>,
    mty: &mut crate::types::decl::ModuleType,
    include_root_path: Option<&Path>,
    include_flat_name: Option<&str>,
    local_type_ids: &HashMap<String, Ident>,
    local_module_ids: &HashMap<String, Ident>,
    local_modtype_ids: &HashMap<String, Ident>,
    visited: &mut HashSet<TypeExprRef>,
) {
    match mty {
        crate::types::decl::ModuleType::MtyIdent(path)
        | crate::types::decl::ModuleType::MtyAlias(_, path) => {
            if let Some(rewritten) = rewrite_included_path_to_local(
                path,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
            ) {
                *path = rewritten;
            }
        }
        crate::types::decl::ModuleType::MtySignature(sig) => {
            rewrite_included_signature_paths_to_local(
                ctx,
                sig,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
                visited,
            );
        }
        crate::types::decl::ModuleType::MtyFunctor {
            param_type,
            result,
            ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                rewrite_included_module_type_paths_to_local(
                    ctx,
                    param_type,
                    include_root_path,
                    include_flat_name,
                    local_type_ids,
                    local_module_ids,
                    local_modtype_ids,
                    visited,
                );
            }
            rewrite_included_module_type_paths_to_local(
                ctx,
                result,
                include_root_path,
                include_flat_name,
                local_type_ids,
                local_module_ids,
                local_modtype_ids,
                visited,
            );
        }
    }
}

fn rewrite_included_signature_paths_to_local(
    ctx: &crate::types::context::TypeContext<'_>,
    sig: &mut [crate::types::decl::SignatureItem],
    include_root_path: Option<&Path>,
    include_flat_name: Option<&str>,
    local_type_ids: &HashMap<String, Ident>,
    local_module_ids: &HashMap<String, Ident>,
    local_modtype_ids: &HashMap<String, Ident>,
    visited: &mut HashSet<TypeExprRef>,
) {
    for item in sig {
        match item {
            crate::types::decl::SignatureItem::SigValue(_, desc) => {
                desc.val_path = None;
                rewrite_included_type_paths_to_local(
                    ctx,
                    desc.val_type,
                    include_root_path,
                    include_flat_name,
                    local_type_ids,
                    local_module_ids,
                    local_modtype_ids,
                    visited,
                );
            }
            crate::types::decl::SignatureItem::SigType(id, decl, _) => {
                rewrite_included_type_decl_paths_to_local(
                    ctx,
                    id,
                    decl,
                    include_root_path,
                    include_flat_name,
                    local_type_ids,
                    local_module_ids,
                    local_modtype_ids,
                    visited,
                );
            }
            crate::types::decl::SignatureItem::SigTypext(_, ext, _) => {
                if let Some(rewritten) = rewrite_included_path_to_local(
                    &ext.ext_type_path,
                    include_root_path,
                    include_flat_name,
                    local_type_ids,
                    local_module_ids,
                    local_modtype_ids,
                ) {
                    ext.ext_type_path = rewritten;
                }
                for param in &ext.ext_type_params {
                    rewrite_included_type_paths_to_local(
                        ctx,
                        *param,
                        include_root_path,
                        include_flat_name,
                        local_type_ids,
                        local_module_ids,
                        local_modtype_ids,
                        visited,
                    );
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for arg in args {
                            rewrite_included_type_paths_to_local(
                                ctx,
                                *arg,
                                include_root_path,
                                include_flat_name,
                                local_type_ids,
                                local_module_ids,
                                local_modtype_ids,
                                visited,
                            );
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for label in labels {
                            rewrite_included_type_paths_to_local(
                                ctx,
                                label.ld_type,
                                include_root_path,
                                include_flat_name,
                                local_type_ids,
                                local_module_ids,
                                local_modtype_ids,
                                visited,
                            );
                        }
                    }
                }
                if let Some(ret_ty) = ext.ext_ret_type {
                    rewrite_included_type_paths_to_local(
                        ctx,
                        ret_ty,
                        include_root_path,
                        include_flat_name,
                        local_type_ids,
                        local_module_ids,
                        local_modtype_ids,
                        visited,
                    );
                }
            }
            crate::types::decl::SignatureItem::SigModule(id, md, _) => {
                md.md_path = Some(Path::Pident(id.clone()));
                rewrite_included_module_type_paths_to_local(
                    ctx,
                    &mut md.md_type,
                    include_root_path,
                    include_flat_name,
                    local_type_ids,
                    local_module_ids,
                    local_modtype_ids,
                    visited,
                );
            }
            crate::types::decl::SignatureItem::SigModtype(id, mtd) => {
                if let Some(mty) = mtd.mtd_type.as_mut() {
                    rewrite_included_module_type_paths_to_local(
                        ctx,
                        mty,
                        include_root_path,
                        include_flat_name,
                        local_type_ids,
                        local_module_ids,
                        local_modtype_ids,
                        visited,
                    );
                }
                let _ = id;
            }
            crate::types::decl::SignatureItem::SigClass
            | crate::types::decl::SignatureItem::SigClassType => {}
        }
    }
}

fn rewrite_module_path_prefix(path: &Path, old_param: &Ident, new_prefix: &Path) -> Path {
    match path {
        Path::Pident(id) if id.same(old_param) => new_prefix.clone(),
        Path::Pdot(prefix, name, pos) => Path::Pdot(
            Box::new(rewrite_module_path_prefix(prefix, old_param, new_prefix)),
            name.clone(),
            *pos,
        ),
        Path::Papply(functor, arg) => Path::Papply(
            Box::new(rewrite_module_path_prefix(functor, old_param, new_prefix)),
            Box::new(rewrite_module_path_prefix(arg, old_param, new_prefix)),
        ),
        _ => path.clone(),
    }
}

fn rewrite_module_prefix_in_type(
    ty_ref: TypeExprRef,
    old_param: &Ident,
    new_prefix: &Path,
    ctx: &crate::types::context::TypeContext<'_>,
    visited: &mut HashSet<TypeExprRef>,
) {
    use crate::types::type_expr::{RowField, TypeDesc};

    let ty_ref = ctx.repr(ty_ref);
    if !visited.insert(ty_ref) {
        return;
    }

    let desc = ctx.get_desc(ty_ref);

    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            let rewritten = rewrite_module_path_prefix(path, old_param, new_prefix);
            if rewritten != *path {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                    *path = rewritten;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for &arg in args {
                rewrite_module_prefix_in_type(arg, old_param, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            rewrite_module_prefix_in_type(arg.typ, old_param, new_prefix, ctx, visited);
            rewrite_module_prefix_in_type(*ret, old_param, new_prefix, ctx, visited);
        }
        TypeDesc::Ttuple(types) => {
            for &ty in types {
                rewrite_module_prefix_in_type(ty, old_param, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tlink(ty) | TypeDesc::Tsubst(ty) => {
            rewrite_module_prefix_in_type(*ty, old_param, new_prefix, ctx, visited);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_module_prefix_in_type(*body, old_param, new_prefix, ctx, visited);
            for &var in vars {
                rewrite_module_prefix_in_type(var, old_param, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_module_prefix_in_type(*fields, old_param, new_prefix, ctx, visited);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_module_prefix_in_type(*typ, old_param, new_prefix, ctx, visited);
            rewrite_module_prefix_in_type(*rest, old_param, new_prefix, ctx, visited);
        }
        TypeDesc::Tvariant(row) => {
            rewrite_module_prefix_in_type(row.row_more, old_param, new_prefix, ctx, visited);
            for (_, row_field) in &row.row_fields {
                match row_field {
                    RowField::Rpresent(Some(ty)) => {
                        rewrite_module_prefix_in_type(*ty, old_param, new_prefix, ctx, visited);
                    }
                    RowField::Reither { types, .. } => {
                        for &ty in types {
                            rewrite_module_prefix_in_type(ty, old_param, new_prefix, ctx, visited);
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { path, args, .. } => {
            let rewritten = rewrite_module_path_prefix(path, old_param, new_prefix);
            if rewritten != *path {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = rewritten;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for &arg in args {
                rewrite_module_prefix_in_type(arg, old_param, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

fn copy_and_rewrite_module_prefix_type(
    ty_ref: TypeExprRef,
    old_param: &Ident,
    new_prefix: &Path,
    ctx: &crate::types::context::TypeContext<'_>,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> TypeExprRef {
    // Functor-result substitution is a module-type operation; copied nodes should
    // live at signature (generic) level, independent of the ambient typing level.
    let old_level = ctx.current_level();
    ctx.set_current_level(crate::types::type_expr::GENERIC_LEVEL);
    let copied = crate::types::ctype::copy_type_deep(ctx, ty_ref, copy_cache);
    ctx.set_current_level(old_level);
    let mut visited = HashSet::new();
    rewrite_module_prefix_in_type(copied, old_param, new_prefix, ctx, &mut visited);
    copied
}

fn copy_and_rewrite_constructor_args(
    args: &crate::types::decl::ConstructorArguments,
    old_param: &Ident,
    arg_path: &Path,
    ctx: &crate::types::context::TypeContext<'_>,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::ConstructorArguments {
    match args {
        crate::types::decl::ConstructorArguments::CstrTuple(args) => {
            crate::types::decl::ConstructorArguments::CstrTuple(
                args.iter()
                    .map(|ty| {
                        copy_and_rewrite_module_prefix_type(
                            *ty, old_param, arg_path, ctx, copy_cache,
                        )
                    })
                    .collect(),
            )
        }
        crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
            crate::types::decl::ConstructorArguments::CstrRecord(
                labels
                    .iter()
                    .map(|label| {
                        let mut copied = label.clone();
                        copied.ld_type = copy_and_rewrite_module_prefix_type(
                            label.ld_type,
                            old_param,
                            arg_path,
                            ctx,
                            copy_cache,
                        );
                        copied
                    })
                    .collect(),
            )
        }
    }
}

fn copy_and_rewrite_type_kind(
    type_kind: &crate::types::decl::TypeKind,
    old_param: &Ident,
    arg_path: &Path,
    ctx: &crate::types::context::TypeContext<'_>,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::TypeKind {
    match type_kind {
        crate::types::decl::TypeKind::TypeAbstract => crate::types::decl::TypeKind::TypeAbstract,
        crate::types::decl::TypeKind::TypeOpen => crate::types::decl::TypeKind::TypeOpen,
        crate::types::decl::TypeKind::TypeRecord(labels, repr) => {
            crate::types::decl::TypeKind::TypeRecord(
                labels
                    .iter()
                    .map(|label| {
                        let mut copied = label.clone();
                        copied.ld_type = copy_and_rewrite_module_prefix_type(
                            label.ld_type,
                            old_param,
                            arg_path,
                            ctx,
                            copy_cache,
                        );
                        copied
                    })
                    .collect(),
                repr.clone(),
            )
        }
        crate::types::decl::TypeKind::TypeVariant(constructors) => {
            crate::types::decl::TypeKind::TypeVariant(
                constructors
                    .iter()
                    .map(|constructor| {
                        let mut copied = constructor.clone();
                        copied.cd_args = copy_and_rewrite_constructor_args(
                            &constructor.cd_args,
                            old_param,
                            arg_path,
                            ctx,
                            copy_cache,
                        );
                        copied.cd_res = constructor.cd_res.map(|ty| {
                            copy_and_rewrite_module_prefix_type(
                                ty, old_param, arg_path, ctx, copy_cache,
                            )
                        });
                        copied
                    })
                    .collect(),
            )
        }
    }
}

fn copy_and_rewrite_type_inlined(
    inlined: &crate::types::decl::TypeInlinedType,
    old_param: &Ident,
    arg_path: &Path,
    ctx: &crate::types::context::TypeContext<'_>,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::TypeInlinedType {
    match inlined {
        crate::types::decl::TypeInlinedType::Record { type_name, labels } => {
            crate::types::decl::TypeInlinedType::Record {
                type_name: type_name.clone(),
                labels: labels
                    .iter()
                    .map(|label| {
                        let mut copied = label.clone();
                        copied.ld_type = copy_and_rewrite_module_prefix_type(
                            label.ld_type,
                            old_param,
                            arg_path,
                            ctx,
                            copy_cache,
                        );
                        copied
                    })
                    .collect(),
            }
        }
    }
}

fn substitute_functor_param_in_signature(
    sig_items: &[crate::types::decl::SignatureItem],
    old_param: &Ident,
    arg_path: &Path,
    ctx: &crate::types::context::TypeContext<'_>,
) -> Vec<crate::types::decl::SignatureItem> {
    use crate::types::decl::SignatureItem;

    let mut copy_cache = HashMap::new();
    sig_items
        .iter()
        .map(|item| match item {
            SignatureItem::SigValue(id, vd) => {
                let mut copied_vd = vd.clone();
                copied_vd.val_type = copy_and_rewrite_module_prefix_type(
                    vd.val_type,
                    old_param,
                    arg_path,
                    ctx,
                    &mut copy_cache,
                );
                SignatureItem::SigValue(id.clone(), copied_vd)
            }
            SignatureItem::SigType(id, decl, rec_status) => {
                let mut copied_decl = decl.clone();
                copied_decl.type_params = decl
                    .type_params
                    .iter()
                    .map(|ty| {
                        copy_and_rewrite_module_prefix_type(
                            *ty,
                            old_param,
                            arg_path,
                            ctx,
                            &mut copy_cache,
                        )
                    })
                    .collect();
                copied_decl.type_kind = copy_and_rewrite_type_kind(
                    &decl.type_kind,
                    old_param,
                    arg_path,
                    ctx,
                    &mut copy_cache,
                );
                copied_decl.type_manifest = decl.type_manifest.map(|ty| {
                    copy_and_rewrite_module_prefix_type(
                        ty,
                        old_param,
                        arg_path,
                        ctx,
                        &mut copy_cache,
                    )
                });
                copied_decl.type_inlined_types = decl
                    .type_inlined_types
                    .iter()
                    .map(|inlined| {
                        copy_and_rewrite_type_inlined(
                            inlined,
                            old_param,
                            arg_path,
                            ctx,
                            &mut copy_cache,
                        )
                    })
                    .collect();
                SignatureItem::SigType(id.clone(), copied_decl, *rec_status)
            }
            SignatureItem::SigTypext(id, ext, ext_status) => {
                let mut copied_ext = ext.clone();
                copied_ext.ext_type_params = ext
                    .ext_type_params
                    .iter()
                    .map(|ty| {
                        copy_and_rewrite_module_prefix_type(
                            *ty,
                            old_param,
                            arg_path,
                            ctx,
                            &mut copy_cache,
                        )
                    })
                    .collect();
                copied_ext.ext_args = copy_and_rewrite_constructor_args(
                    &ext.ext_args,
                    old_param,
                    arg_path,
                    ctx,
                    &mut copy_cache,
                );
                copied_ext.ext_ret_type = ext.ext_ret_type.map(|ty| {
                    copy_and_rewrite_module_prefix_type(
                        ty,
                        old_param,
                        arg_path,
                        ctx,
                        &mut copy_cache,
                    )
                });
                SignatureItem::SigTypext(id.clone(), copied_ext, *ext_status)
            }
            SignatureItem::SigModule(id, md, rec_status) => {
                let mut rewritten_md = md.clone();
                rewritten_md.md_type =
                    substitute_functor_param_in_module_type(
                        &md.md_type,
                        old_param,
                        arg_path,
                        ctx,
                    );
                rewritten_md.md_path = md
                    .md_path
                    .as_ref()
                    .map(|path| rewrite_module_path_prefix(path, old_param, arg_path));
                SignatureItem::SigModule(id.clone(), rewritten_md, *rec_status)
            }
            SignatureItem::SigModtype(id, mtd) => {
                let mut rewritten_mtd = mtd.clone();
                rewritten_mtd.mtd_type = mtd.mtd_type.as_ref().map(|mty| {
                    substitute_functor_param_in_module_type(mty, old_param, arg_path, ctx)
                });
                SignatureItem::SigModtype(id.clone(), rewritten_mtd)
            }
            _ => item.clone(),
        })
        .collect()
}

fn substitute_functor_param_in_module_type(
    mty: &crate::types::decl::ModuleType,
    old_param: &Ident,
    arg_path: &Path,
    ctx: &crate::types::context::TypeContext<'_>,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;

    match mty {
        DeclMty::MtySignature(sig_items) => DeclMty::MtySignature(
            substitute_functor_param_in_signature(sig_items, old_param, arg_path, ctx),
        ),
        DeclMty::MtyIdent(path) => {
            DeclMty::MtyIdent(rewrite_module_path_prefix(path, old_param, arg_path))
        }
        DeclMty::MtyAlias(alias_presence, path) => DeclMty::MtyAlias(
            *alias_presence,
            rewrite_module_path_prefix(path, old_param, arg_path),
        ),
        DeclMty::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            let rewritten_param_type = param_type.as_ref().map(|inner| {
                Box::new(substitute_functor_param_in_module_type(
                    inner, old_param, arg_path, ctx,
                ))
            });
            if param.same(old_param) {
                DeclMty::MtyFunctor {
                    param: param.clone(),
                    param_type: rewritten_param_type,
                    result: result.clone(),
                }
            } else {
                DeclMty::MtyFunctor {
                    param: param.clone(),
                    param_type: rewritten_param_type,
                    result: Box::new(substitute_functor_param_in_module_type(
                        result, old_param, arg_path, ctx,
                    )),
                }
            }
        }
    }
}

fn rewrite_module_path_prefix_with_aliases(
    path: &Path,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
) -> Path {
    match path {
        Path::Pdot(prefix, name, pos) => {
            let rewritten_prefix =
                rewrite_module_path_prefix_with_aliases(prefix, old_param, arg_aliases);
            if let Path::Pident(id) = &rewritten_prefix {
                if id.same(old_param) {
                    if let Some(alias_path) = arg_aliases.get(name) {
                        return alias_path.clone();
                    }
                }
            }
            Path::Pdot(Box::new(rewritten_prefix), name.clone(), *pos)
        }
        Path::Papply(functor, arg) => Path::Papply(
            Box::new(rewrite_module_path_prefix_with_aliases(
                functor,
                old_param,
                arg_aliases,
            )),
            Box::new(rewrite_module_path_prefix_with_aliases(
                arg,
                old_param,
                arg_aliases,
            )),
        ),
        _ => path.clone(),
    }
}

fn rewrite_module_aliases_in_type(
    ty_ref: TypeExprRef,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext<'_>,
    visited: &mut HashSet<TypeExprRef>,
) {
    use crate::types::type_expr::{RowField, TypeDesc};

    let ty_ref = ctx.repr(ty_ref);
    if !visited.insert(ty_ref) {
        return;
    }

    let desc = ctx.get_desc(ty_ref).clone();
    match &desc {
        TypeDesc::Tconstr { path, args, abbrev } => {
            let rewritten = rewrite_module_path_prefix_with_aliases(path, old_param, arg_aliases);
            if rewritten != *path {
                ctx.set_desc(
                    ty_ref,
                    TypeDesc::Tconstr {
                        path: rewritten,
                        args: args.clone(),
                        abbrev: *abbrev,
                    },
                );
            }
            for arg in args {
                rewrite_module_aliases_in_type(*arg, old_param, arg_aliases, ctx, visited);
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            rewrite_module_aliases_in_type(arg.typ, old_param, arg_aliases, ctx, visited);
            rewrite_module_aliases_in_type(*ret, old_param, arg_aliases, ctx, visited);
        }
        TypeDesc::Ttuple(tys) => {
            for ty in tys {
                rewrite_module_aliases_in_type(*ty, old_param, arg_aliases, ctx, visited);
            }
        }
        TypeDesc::Tlink(ty) | TypeDesc::Tsubst(ty) => {
            rewrite_module_aliases_in_type(*ty, old_param, arg_aliases, ctx, visited);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_module_aliases_in_type(*body, old_param, arg_aliases, ctx, visited);
            for var in vars {
                rewrite_module_aliases_in_type(*var, old_param, arg_aliases, ctx, visited);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_module_aliases_in_type(*fields, old_param, arg_aliases, ctx, visited);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_module_aliases_in_type(*typ, old_param, arg_aliases, ctx, visited);
            rewrite_module_aliases_in_type(*rest, old_param, arg_aliases, ctx, visited);
        }
        TypeDesc::Tvariant(row) => {
            rewrite_module_aliases_in_type(row.row_more, old_param, arg_aliases, ctx, visited);
            for (_, row_field) in &row.row_fields {
                match row_field {
                    RowField::Rpresent(Some(ty)) => {
                        rewrite_module_aliases_in_type(*ty, old_param, arg_aliases, ctx, visited);
                    }
                    RowField::Reither { types, .. } => {
                        for ty in types {
                            rewrite_module_aliases_in_type(
                                *ty,
                                old_param,
                                arg_aliases,
                                ctx,
                                visited,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { path, args, lids } => {
            let rewritten = rewrite_module_path_prefix_with_aliases(path, old_param, arg_aliases);
            if rewritten != *path {
                ctx.set_desc(
                    ty_ref,
                    TypeDesc::Tpackage {
                        path: rewritten,
                        lids: lids.clone(),
                        args: args.clone(),
                    },
                );
            }
            for arg in args {
                rewrite_module_aliases_in_type(*arg, old_param, arg_aliases, ctx, visited);
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

fn copy_and_rewrite_module_aliases_type(
    ty_ref: TypeExprRef,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext<'_>,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> TypeExprRef {
    let old_level = ctx.current_level();
    ctx.set_current_level(crate::types::type_expr::GENERIC_LEVEL);
    let copied = crate::types::ctype::copy_type_deep(ctx, ty_ref, copy_cache);
    ctx.set_current_level(old_level);
    let mut visited = HashSet::new();
    rewrite_module_aliases_in_type(copied, old_param, arg_aliases, ctx, &mut visited);
    copied
}

fn copy_and_rewrite_constructor_args_with_aliases(
    args: &crate::types::decl::ConstructorArguments,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext<'_>,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::ConstructorArguments {
    match args {
        crate::types::decl::ConstructorArguments::CstrTuple(args) => {
            crate::types::decl::ConstructorArguments::CstrTuple(
                args.iter()
                    .map(|ty| {
                        copy_and_rewrite_module_aliases_type(
                            *ty, old_param, arg_aliases, ctx, copy_cache,
                        )
                    })
                    .collect(),
            )
        }
        crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
            crate::types::decl::ConstructorArguments::CstrRecord(
                labels
                    .iter()
                    .map(|label| {
                        let mut copied = label.clone();
                        copied.ld_type = copy_and_rewrite_module_aliases_type(
                            label.ld_type,
                            old_param,
                            arg_aliases,
                            ctx,
                            copy_cache,
                        );
                        copied
                    })
                    .collect(),
            )
        }
    }
}

fn copy_and_rewrite_type_kind_with_aliases(
    kind: &crate::types::TypeKind,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext<'_>,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::TypeKind {
    match kind {
        crate::types::TypeKind::TypeAbstract => crate::types::TypeKind::TypeAbstract,
        crate::types::TypeKind::TypeOpen => crate::types::TypeKind::TypeOpen,
        crate::types::TypeKind::TypeVariant(ctors) => crate::types::TypeKind::TypeVariant(
            ctors
                .iter()
                .map(|ctor| {
                    let mut copied = ctor.clone();
                    copied.cd_args = copy_and_rewrite_constructor_args_with_aliases(
                        &ctor.cd_args,
                        old_param,
                        arg_aliases,
                        ctx,
                        copy_cache,
                    );
                    if let Some(ret) = ctor.cd_res {
                        copied.cd_res = Some(copy_and_rewrite_module_aliases_type(
                            ret,
                            old_param,
                            arg_aliases,
                            ctx,
                            copy_cache,
                        ));
                    }
                    copied
                })
                .collect(),
        ),
        crate::types::TypeKind::TypeRecord(labels, repr) => crate::types::TypeKind::TypeRecord(
            labels
                .iter()
                .map(|label| {
                    let mut copied = label.clone();
                    copied.ld_type = copy_and_rewrite_module_aliases_type(
                        label.ld_type,
                        old_param,
                        arg_aliases,
                        ctx,
                        copy_cache,
                    );
                    copied
                })
                .collect(),
            repr.clone(),
        ),
    }
}

fn copy_and_rewrite_type_inlined_with_aliases(
    inlined: &crate::types::decl::TypeInlinedType,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext<'_>,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::TypeInlinedType {
    match inlined {
        crate::types::decl::TypeInlinedType::Record { type_name, labels } => {
            crate::types::decl::TypeInlinedType::Record {
                type_name: type_name.clone(),
                labels: labels
                    .iter()
                    .map(|label| {
                        let mut copied = label.clone();
                        copied.ld_type = copy_and_rewrite_module_aliases_type(
                            label.ld_type,
                            old_param,
                            arg_aliases,
                            ctx,
                            copy_cache,
                        );
                        copied
                    })
                    .collect(),
            }
        }
    }
}

fn substitute_functor_param_aliases_in_signature(
    sig_items: &[crate::types::decl::SignatureItem],
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext<'_>,
) -> Vec<crate::types::decl::SignatureItem> {
    use crate::types::decl::SignatureItem;

    let mut copy_cache = HashMap::new();
    sig_items
        .iter()
        .map(|item| match item {
            SignatureItem::SigValue(id, vd) => {
                let mut copied_vd = vd.clone();
                copied_vd.val_type = copy_and_rewrite_module_aliases_type(
                    vd.val_type,
                    old_param,
                    arg_aliases,
                    ctx,
                    &mut copy_cache,
                );
                SignatureItem::SigValue(id.clone(), copied_vd)
            }
            SignatureItem::SigType(id, decl, rec_status) => {
                let mut copied_decl = decl.clone();
                copied_decl.type_params = decl
                    .type_params
                    .iter()
                    .map(|ty| {
                        copy_and_rewrite_module_aliases_type(
                            *ty,
                            old_param,
                            arg_aliases,
                            ctx,
                            &mut copy_cache,
                        )
                    })
                    .collect();
                copied_decl.type_kind = copy_and_rewrite_type_kind_with_aliases(
                    &decl.type_kind,
                    old_param,
                    arg_aliases,
                    ctx,
                    &mut copy_cache,
                );
                copied_decl.type_manifest = decl.type_manifest.map(|ty| {
                    copy_and_rewrite_module_aliases_type(
                        ty,
                        old_param,
                        arg_aliases,
                        ctx,
                        &mut copy_cache,
                    )
                });
                copied_decl.type_inlined_types = decl
                    .type_inlined_types
                    .iter()
                    .map(|inlined| {
                        copy_and_rewrite_type_inlined_with_aliases(
                            inlined,
                            old_param,
                            arg_aliases,
                            ctx,
                            &mut copy_cache,
                        )
                    })
                    .collect();
                SignatureItem::SigType(id.clone(), copied_decl, *rec_status)
            }
            SignatureItem::SigTypext(id, ext, ext_status) => {
                let mut copied_ext = ext.clone();
                copied_ext.ext_type_params = ext
                    .ext_type_params
                    .iter()
                    .map(|ty| {
                        copy_and_rewrite_module_aliases_type(
                            *ty,
                            old_param,
                            arg_aliases,
                            ctx,
                            &mut copy_cache,
                        )
                    })
                    .collect();
                copied_ext.ext_args = copy_and_rewrite_constructor_args_with_aliases(
                    &ext.ext_args,
                    old_param,
                    arg_aliases,
                    ctx,
                    &mut copy_cache,
                );
                copied_ext.ext_ret_type = ext.ext_ret_type.map(|ty| {
                    copy_and_rewrite_module_aliases_type(
                        ty,
                        old_param,
                        arg_aliases,
                        ctx,
                        &mut copy_cache,
                    )
                });
                SignatureItem::SigTypext(id.clone(), copied_ext, *ext_status)
            }
            SignatureItem::SigModule(id, md, rec_status) => {
                let mut rewritten_md = md.clone();
                rewritten_md.md_type =
                    substitute_functor_param_aliases_in_module_type(
                        &md.md_type,
                        old_param,
                        arg_aliases,
                        ctx,
                    );
                rewritten_md.md_path = md.md_path.as_ref().map(|path| {
                    rewrite_module_path_prefix_with_aliases(path, old_param, arg_aliases)
                });
                SignatureItem::SigModule(id.clone(), rewritten_md, *rec_status)
            }
            SignatureItem::SigModtype(id, mtd) => {
                let mut rewritten_mtd = mtd.clone();
                rewritten_mtd.mtd_type = mtd.mtd_type.as_ref().map(|mty| {
                    substitute_functor_param_aliases_in_module_type(
                        mty,
                        old_param,
                        arg_aliases,
                        ctx,
                    )
                });
                SignatureItem::SigModtype(id.clone(), rewritten_mtd)
            }
            _ => item.clone(),
        })
        .collect()
}

fn substitute_functor_param_aliases_in_module_type(
    mty: &crate::types::decl::ModuleType,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext<'_>,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;

    match mty {
        DeclMty::MtySignature(sig_items) => DeclMty::MtySignature(
            substitute_functor_param_aliases_in_signature(sig_items, old_param, arg_aliases, ctx),
        ),
        DeclMty::MtyIdent(path) => DeclMty::MtyIdent(rewrite_module_path_prefix_with_aliases(
            path, old_param, arg_aliases,
        )),
        DeclMty::MtyAlias(alias_presence, path) => DeclMty::MtyAlias(
            *alias_presence,
            rewrite_module_path_prefix_with_aliases(path, old_param, arg_aliases),
        ),
        DeclMty::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            let rewritten_param_type = param_type.as_ref().map(|inner| {
                Box::new(substitute_functor_param_aliases_in_module_type(
                    inner,
                    old_param,
                    arg_aliases,
                    ctx,
                ))
            });
            if param.same(old_param) {
                DeclMty::MtyFunctor {
                    param: param.clone(),
                    param_type: rewritten_param_type,
                    result: result.clone(),
                }
            } else {
                DeclMty::MtyFunctor {
                    param: param.clone(),
                    param_type: rewritten_param_type,
                    result: Box::new(substitute_functor_param_aliases_in_module_type(
                        result,
                        old_param,
                        arg_aliases,
                        ctx,
                    )),
                }
            }
        }
    }
}

fn unwrap_poly_type(ctx: &crate::types::context::TypeContext<'_>, ty: TypeExprRef) -> TypeExprRef {
    let repr = ctx.repr(ty);
    match &*ctx.get_desc(repr) {
        crate::types::TypeDesc::Tpoly { body, .. } => ctx.repr(*body),
        _ => repr,
    }
}

fn find_type_decl_for_path(
    env: &Env,
    ctx: &crate::types::context::TypeContext<'_>,
    path: &Path,
) -> Option<crate::types::TypeDeclaration> {
    // `Env.lookup_type` on qualified paths currently falls back to leaf-name
    // lookup, which can select an unrelated declaration with the same type
    // name. Keep direct env lookup for simple identifiers only.
    if let Path::Pident(_) = path {
        if let Ok(type_decl) = env.lookup_type(path) {
            return Some((*type_decl).clone());
        }
    }
    if let Path::Pident(id) = path {
        if let Some(type_decl) = ctx.find_type_decl_by_stamp(id.stamp()) {
            return Some((*type_decl).clone());
        }
    }
    let path_str = path.name();
    if let Some(type_decl) = ctx.find_type_decl_by_path(&path_str) {
        return Some((*type_decl).clone());
    }

    if let Some(type_decl) = crate::types::ctype::resolve_type_through_modules(ctx, path) {
        return Some(type_decl);
    }

    // Try resolving through module aliases visible in the local env.
    if let Path::Pdot(parent, type_name, _) = path {
        if let Path::Pident(parent_id) = parent.as_ref() {
            if let Ok(module_desc) = env
                .lookup_module(parent.as_ref())
                .or_else(|_| env.find_module(parent_id.name()))
            {
                use crate::types::decl::ModuleType;
                use crate::types::decl::SignatureItem;
                match &module_desc.md_type {
                    ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path) => {
                        let resolved_path = Path::pdot(alias_path.clone(), type_name.as_str());
                        if let Some(type_decl) = ctx.find_type_decl_by_path(&resolved_path.name()) {
                            return Some((*type_decl).clone());
                        }
                        if let Some(type_decl) =
                            crate::types::ctype::resolve_type_through_modules(ctx, &resolved_path)
                        {
                            return Some(type_decl);
                        }
                    }
                    ModuleType::MtySignature(sig_items) => {
                        for item in sig_items {
                            if let SignatureItem::SigType(id, decl, _) = item {
                                if id.name() == type_name.as_str() {
                                    return Some(decl.clone());
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let short_name = path.head_name();
    ctx.find_type_decl(short_name).map(|decl| (*decl).clone())
}

fn expand_record_spread_label(
    ctx: &crate::types::context::TypeContext<'_>,
    env: &Env,
    label: &crate::types::LabelDeclaration,
    visited: &mut HashSet<String>,
) -> Option<Vec<crate::types::LabelDeclaration>> {
    fn with_original_level(
        ctx: &crate::types::context::TypeContext<'_>,
        original: TypeExprRef,
        rebuilt: TypeExprRef,
    ) -> TypeExprRef {
        let original = ctx.repr(original);
        let level = ctx.get_level(original);
        if ctx.get_level(rebuilt) != level {
            ctx.set_level(rebuilt, level);
        }
        if rebuilt != original {
            // record_type_spread.ml substitutes with `{t with desc = ...}`,
            // preserving OCaml `type_expr.id`. Rust allocates fresh refs here;
            // record the alias so sexp dedup can use the original key.
            ctx.set_arity_alias(rebuilt, original);
        }
        rebuilt
    }

    fn substitute_type_params(
        ctx: &crate::types::context::TypeContext<'_>,
        ty: TypeExprRef,
        params: &[TypeExprRef],
        args: &[TypeExprRef],
        cache: &mut HashMap<TypeExprRef, TypeExprRef>,
    ) -> TypeExprRef {
        if let Some(substituted) = cache.get(&ty) {
            return *substituted;
        }
        let find_substitution = |name: &str| -> Option<TypeExprRef> {
            for (idx, param) in params.iter().enumerate() {
                let param_desc = ctx.get_desc(*param);
                match &*param_desc {
                    crate::types::TypeDesc::Tvar(Some(param_name))
                    | crate::types::TypeDesc::Tunivar(Some(param_name))
                        if param_name == name =>
                    {
                        return Some(args[idx]);
                    }
                    _ => {}
                }
            }
            None
        };

        let desc = ctx.get_desc(ty);
        let substituted = match &*desc {
            crate::types::TypeDesc::Tvar(Some(name))
            | crate::types::TypeDesc::Tunivar(Some(name)) => {
                find_substitution(name).unwrap_or(ty)
            }
            crate::types::TypeDesc::Tvar(None)
            | crate::types::TypeDesc::Tunivar(None)
            | crate::types::TypeDesc::Tnil => ty,
            crate::types::TypeDesc::Tlink(target) => {
                let new_target = substitute_type_params(ctx, *target, params, args, cache);
                if new_target == *target {
                    ty
                } else {
                    with_original_level(
                        ctx,
                        ty,
                        ctx.new_type(crate::types::TypeDesc::Tlink(new_target)),
                    )
                }
            }
            crate::types::TypeDesc::Tsubst(target) => {
                let new_target = substitute_type_params(ctx, *target, params, args, cache);
                if new_target == *target {
                    ty
                } else {
                    with_original_level(
                        ctx,
                        ty,
                        ctx.new_type(crate::types::TypeDesc::Tsubst(new_target)),
                    )
                }
            }
            crate::types::TypeDesc::Tconstr {
                path,
                args: inner_args,
                ..
            } => {
                let mut changed = false;
                let new_args: Vec<_> = inner_args
                    .iter()
                    .map(|arg| {
                        let new_arg = substitute_type_params(ctx, *arg, params, args, cache);
                        if new_arg != *arg {
                            changed = true;
                        }
                        new_arg
                    })
                    .collect();
                if changed {
                    with_original_level(ctx, ty, ctx.new_constr(path.clone(), new_args))
                } else {
                    ty
                }
            }
            crate::types::TypeDesc::Tarrow {
                arg, ret, arity, ..
            } => {
                let new_arg = substitute_type_params(ctx, arg.typ, params, args, cache);
                let new_ret = substitute_type_params(ctx, *ret, params, args, cache);
                if new_arg == arg.typ && new_ret == *ret {
                    ty
                } else {
                    with_original_level(
                        ctx,
                        ty,
                        ctx.new_arrow(arg.lbl.clone(), new_arg, new_ret, *arity),
                    )
                }
            }
            crate::types::TypeDesc::Ttuple(items) => {
                let mut changed = false;
                let new_items: Vec<_> = items
                    .iter()
                    .map(|item| {
                        let new_item = substitute_type_params(ctx, *item, params, args, cache);
                        if new_item != *item {
                            changed = true;
                        }
                        new_item
                    })
                    .collect();
                if changed {
                    with_original_level(ctx, ty, ctx.new_tuple(new_items))
                } else {
                    ty
                }
            }
            crate::types::TypeDesc::Tobject { fields, name } => {
                let new_fields = substitute_type_params(ctx, *fields, params, args, cache);
                let mut name_changed = false;
                let new_name = name.as_ref().map(|(path, type_args)| {
                    (
                        path.clone(),
                        type_args
                            .iter()
                            .map(|arg| {
                                let new_arg =
                                    substitute_type_params(ctx, *arg, params, args, cache);
                                if new_arg != *arg {
                                    name_changed = true;
                                }
                                new_arg
                            })
                            .collect::<Vec<_>>(),
                    )
                });
                if new_fields == *fields && !name_changed {
                    ty
                } else {
                    with_original_level(
                        ctx,
                        ty,
                        ctx.new_type(crate::types::TypeDesc::Tobject {
                            fields: new_fields,
                            name: new_name,
                        }),
                    )
                }
            }
            crate::types::TypeDesc::Tfield {
                name,
                kind,
                typ,
                rest,
            } => {
                let new_typ = substitute_type_params(ctx, *typ, params, args, cache);
                let new_rest = substitute_type_params(ctx, *rest, params, args, cache);
                if new_typ == *typ && new_rest == *rest {
                    ty
                } else {
                    with_original_level(
                        ctx,
                        ty,
                        ctx.new_type(crate::types::TypeDesc::Tfield {
                            name: name.clone(),
                            kind: kind.clone(),
                            typ: new_typ,
                            rest: new_rest,
                        }),
                    )
                }
            }
            crate::types::TypeDesc::Tvariant(row) => {
                let mut changed = false;
                let new_fields: Vec<_> = row
                    .row_fields
                    .iter()
                    .map(|(label, field)| {
                        let new_field = match field {
                            crate::types::RowField::Rpresent(Some(t)) => {
                                let new_t = substitute_type_params(ctx, *t, params, args, cache);
                                if new_t != *t {
                                    changed = true;
                                }
                                crate::types::RowField::Rpresent(Some(new_t))
                            }
                            crate::types::RowField::Reither {
                                constant,
                                types,
                                matched,
                                link,
                            } => {
                                let new_types: Vec<_> = types
                                    .iter()
                                    .map(|t| {
                                        let new_t =
                                            substitute_type_params(ctx, *t, params, args, cache);
                                        if new_t != *t {
                                            changed = true;
                                        }
                                        new_t
                                    })
                                    .collect();
                                crate::types::RowField::Reither {
                                    constant: *constant,
                                    types: new_types,
                                    matched: *matched,
                                    link: *link,
                                }
                            }
                            other => other.clone(),
                        };
                        (label.clone(), new_field)
                    })
                    .collect();
                let new_more = substitute_type_params(ctx, row.row_more, params, args, cache);
                if new_more != row.row_more {
                    changed = true;
                }
                let new_name = row.row_name.as_ref().map(|(path, row_args)| {
                    (
                        path.clone(),
                        row_args
                            .iter()
                            .map(|arg| {
                                let new_arg =
                                    substitute_type_params(ctx, *arg, params, args, cache);
                                if new_arg != *arg {
                                    changed = true;
                                }
                                new_arg
                            })
                            .collect::<Vec<_>>(),
                    )
                });
                if changed {
                    with_original_level(
                        ctx,
                        ty,
                        ctx.new_variant(crate::types::RowDesc {
                            row_fields: new_fields,
                            row_more: new_more,
                            row_closed: row.row_closed,
                            row_fixed: row.row_fixed,
                            row_name: new_name,
                        }),
                    )
                } else {
                    ty
                }
            }
            crate::types::TypeDesc::Tpoly { body, vars } => {
                if vars.is_empty() {
                    substitute_type_params(ctx, *body, params, args, cache)
                } else {
                    let new_body = substitute_type_params(ctx, *body, params, args, cache);
                    let mut changed = new_body != *body;
                    let new_vars: Vec<_> = vars
                        .iter()
                        .map(|var| {
                            let new_var = substitute_type_params(ctx, *var, params, args, cache);
                            if new_var != *var {
                                changed = true;
                            }
                            new_var
                        })
                        .collect();
                    if changed {
                        with_original_level(ctx, ty, ctx.new_poly(new_body, new_vars))
                    } else {
                        ty
                    }
                }
            }
            crate::types::TypeDesc::Tpackage {
                path,
                lids,
                args: pkg_args,
            } => {
                let mut changed = false;
                let new_args: Vec<_> = pkg_args
                    .iter()
                    .map(|arg| {
                        let new_arg = substitute_type_params(ctx, *arg, params, args, cache);
                        if new_arg != *arg {
                            changed = true;
                        }
                        new_arg
                    })
                    .collect();
                if changed {
                    with_original_level(
                        ctx,
                        ty,
                        ctx.new_type(crate::types::TypeDesc::Tpackage {
                            path: path.clone(),
                            lids: lids.clone(),
                            args: new_args,
                        }),
                    )
                } else {
                    ty
                }
            }
        };
        cache.insert(ty, substituted);
        substituted
    }

    if label.ld_id.name() != "..." {
        return Some(vec![label.clone()]);
    }

    // Match OCaml record_type_spread.extract + Ctype.extract_concrete_typedecl:
    // unwrap top-level Tpoly([], ..), then expand type aliases to the concrete
    // head before reading the spread path/type args.
    let spread_ty = unwrap_poly_type(ctx, label.ld_type);
    let spread_ty = crate::types::ctype::expand_head(ctx, env, spread_ty);
    let spread_ty = unwrap_poly_type(ctx, spread_ty);
    let (spread_path, spread_args) = match &*ctx.get_desc(spread_ty) {
        crate::types::TypeDesc::Tconstr { path, args, .. } => (path.clone(), args.clone()),
        _ => return None,
    };
    let path_name = spread_path.name();
    if !visited.insert(path_name.clone()) {
        return None;
    }
    let result = if let Some(mut source_decl) = find_type_decl_for_path(env, ctx, &spread_path) {
        // Follow manifest aliases until we reach a concrete record declaration,
        // matching OCaml Ctype.extract_concrete_typedecl behavior.
        let mut source_args = spread_args.clone();
        let mut resolution_seen = HashSet::new();
        resolution_seen.insert(path_name.clone());
        let source_record = loop {
            if let crate::types::TypeKind::TypeRecord(inner_fields, _) = &source_decl.type_kind {
                break Some((inner_fields.clone(), source_decl.type_params.clone(), source_args.clone()));
            }
            let manifest = match source_decl.type_manifest {
                Some(manifest) => manifest,
                None => break None,
            };
            let manifest = unwrap_poly_type(ctx, crate::types::ctype::expand_head(ctx, env, manifest));
            let (next_path, next_args) = match &*ctx.get_desc(manifest) {
                crate::types::TypeDesc::Tconstr { path, args, .. } => (path.clone(), args.clone()),
                _ => break None,
            };
            let next_name = next_path.name();
            if !resolution_seen.insert(next_name) {
                break None;
            }
            source_decl = match find_type_decl_for_path(env, ctx, &next_path) {
                Some(decl) => decl,
                None => break None,
            };
            source_args = next_args;
        };
        if let Some((inner_fields, source_params, source_args)) = source_record {
            let mut expanded = Vec::new();
            // Share the substitution cache across all fields so that shared type
            // nodes (e.g., the same type parameter used in multiple fields) get
            // the same substituted result, matching OCaml's node sharing.
            let mut cache = HashMap::new();
            for inner_field in &inner_fields {
                let resolved_inner = expand_record_spread_label(ctx, env, inner_field, visited)?;
                for mut field in resolved_inner {
                    if source_params.len() == source_args.len() && !source_params.is_empty() {
                        field.ld_type = substitute_type_params(
                            ctx,
                            field.ld_type,
                            &source_params,
                            &source_args,
                            &mut cache,
                        );
                    }
                    expanded.push(field);
                }
            }
            Some(expanded)
        } else {
            None
        }
    } else {
        None
    };
    visited.remove(&path_name);
    result
}

fn make_typed_spread_label(
    arena: &ParseArena,
    ctx: &crate::types::context::TypeContext<'_>,
    template: &TypedLabelDeclaration,
    field: &crate::types::LabelDeclaration,
) -> TypedLabelDeclaration {
    fn find_loc_idx_by_location(arena: &ParseArena, loc: &Location) -> Option<LocIdx> {
        arena
            .locations()
            .iter()
            .enumerate()
            .find_map(|(idx, interned)| {
                let start = arena.get_position(interned.loc_start);
                let end = arena.get_position(interned.loc_end);
                if *start == loc.loc_start
                    && *end == loc.loc_end
                    && interned.loc_ghost == loc.loc_ghost
                {
                    Some(LocIdx(idx as u32))
                } else {
                    None
                }
            })
    }

    let actual_field_type = unwrap_poly_type(ctx, field.ld_type);
    let typed_ld_type = match &template.ld_type.ctyp_desc {
        TypedCoreTypeDesc::Ttyp_poly(vars, inner_ctyp) => TypedCoreType {
            ctyp_desc: TypedCoreTypeDesc::Ttyp_poly(vars.clone(), inner_ctyp.clone()),
            ctyp_type: actual_field_type,
            ..template.ld_type.clone()
        },
        _ => TypedCoreType {
            ctyp_type: actual_field_type,
            ..template.ld_type.clone()
        },
    };
    let parser_mutable = match field.ld_mutable {
        crate::types::MutableFlag::Immutable => crate::parser::ast::MutableFlag::Immutable,
        crate::types::MutableFlag::Mutable => crate::parser::ast::MutableFlag::Mutable,
    };
    // OCaml record_type_spread.mk_lbl uses the expanded source field location
    // for both ld_name.loc and ld_loc (not the spread marker location).
    let source_loc = find_loc_idx_by_location(arena, &field.ld_loc).unwrap_or(template.ld_loc);
    TypedLabelDeclaration {
        ld_id: field.ld_id.clone(),
        ld_name: Located {
            txt: field.ld_id.name().to_string(),
            loc: source_loc,
        },
        ld_mutable: parser_mutable,
        ld_optional: field.ld_optional,
        ld_type: typed_ld_type,
        ld_loc: source_loc,
        ld_attributes: decl_attrs_to_parser_attrs(arena, &field.ld_attributes),
    }
}

// ============================================================================
// Module Type Checking Results
// ============================================================================

/// Result type for module type checking operations.
pub type TypeModResult<T> = Result<T, TypeModError>;

/// Errors that can occur during module type checking.
#[derive(Debug, Clone)]
pub enum TypeModError {
    /// Core type checking error.
    CoreError(TypeCoreError),
    /// Module not found.
    ModuleNotFound(String),
    /// Signature mismatch.
    SignatureMismatch { expected: String, found: String },
    /// Functor application error.
    FunctorApplicationError(String),
    /// Invalid module expression.
    InvalidModuleExpr(Location),
}

impl From<TypeCoreError> for TypeModError {
    fn from(err: TypeCoreError) -> Self {
        TypeModError::CoreError(err)
    }
}

fn union_variance_rows(lhs: &[TypesVariance], rhs: &[TypesVariance]) -> Vec<TypesVariance> {
    let len = lhs.len().max(rhs.len());
    (0..len)
        .map(|idx| {
            let left = lhs.get(idx).copied().unwrap_or_else(TypesVariance::null);
            let right = rhs.get(idx).copied().unwrap_or_else(TypesVariance::null);
            left.union(&right)
        })
        .collect()
}

fn compute_type_variance_fixpoint(
    ctx: &crate::types::context::TypeContext<'_>,
    env: &Env,
    type_ids: &[Ident],
) -> Vec<Vec<TypesVariance>> {
    let paths: Vec<Path> = type_ids
        .iter()
        .map(|id| Path::pident(id.clone()))
        .collect();

    let templates: Vec<_> = paths
        .iter()
        .filter_map(|path| env.lookup_type(path).ok().cloned())
        .collect();
    if templates.len() != type_ids.len() {
        return vec![];
    }

    // OCaml typedecl.ml compute_properties_fixpoint:
    // start from null variances and monotonically grow via union.
    let mut variances: Vec<Vec<TypesVariance>> = templates
        .iter()
        .map(|decl| vec![TypesVariance::null(); decl.type_params.len()])
        .collect();

    for _ in 0..32 {
        let mut iter_env = env.clone();
        for ((type_id, template), variance) in type_ids
            .iter()
            .zip(templates.iter())
            .zip(variances.iter())
        {
            let mut decl = template.clone();
            decl.type_variance = variance.clone();
            iter_env.add_type(type_id.clone(), decl);
        }

        let computed: Vec<Vec<TypesVariance>> = paths
            .iter()
            .filter_map(|path| iter_env.lookup_type(path).ok())
            .map(|decl| crate::types::ctype::compute_variance_decl(ctx, &iter_env, &decl))
            .collect();
        if computed.len() != variances.len() {
            break;
        }

        let next_variances: Vec<Vec<TypesVariance>> = variances
            .iter()
            .zip(computed.iter())
            .map(|(old, new)| union_variance_rows(old, new))
            .collect();

        if next_variances == variances {
            break;
        }
        variances = next_variances;
    }

    variances
}

// ============================================================================
// Signature Simplification
// ============================================================================

/// Iterate identifiers bound by a typed pattern.
/// Mirrors OCaml `Typedtree.bound_idents` traversal:
/// - alias patterns visit the inner pattern first, then alias id
/// - or-patterns visit only the left branch
fn iter_bound_pattern_idents<'a, F>(pat: &'a crate::types::typedtree::Pattern, f: &mut F)
where
    F: FnMut(&'a Ident),
{
    use crate::types::typedtree::PatternDesc;

    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => f(id),
        PatternDesc::Tpat_alias(inner, id, _) => {
            iter_bound_pattern_idents(inner, f);
            f(id);
        }
        PatternDesc::Tpat_tuple(pats)
        | PatternDesc::Tpat_construct(_, _, pats)
        | PatternDesc::Tpat_array(pats) => {
            for p in pats {
                iter_bound_pattern_idents(p, f);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, p, _) in fields {
                iter_bound_pattern_idents(p, f);
            }
        }
        PatternDesc::Tpat_variant(_, Some(inner), _) => iter_bound_pattern_idents(inner, f),
        PatternDesc::Tpat_or(left, _right, _) => iter_bound_pattern_idents(left, f),
        PatternDesc::Tpat_any
        | PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_variant(_, None, _) => {}
    }
}

fn push_sig_values_from_env_pattern(
    env: &Env,
    pat: &crate::types::typedtree::Pattern,
    sig_items: &mut Vec<crate::types::decl::SignatureItem>,
) {
    use crate::types::typedtree::PatternDesc;

    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => {
            let value_desc = env
                .lookup_value(&Path::Pident(id.clone()))
                .expect("let-bound value missing from structure environment")
                .clone();
            sig_items.push(crate::types::decl::SignatureItem::SigValue(
                id.clone(),
                value_desc,
            ));
        }
        PatternDesc::Tpat_alias(inner, id, _) => {
            push_sig_values_from_env_pattern(env, inner, sig_items);
            let value_desc = env
                .lookup_value(&Path::Pident(id.clone()))
                .expect("let-bound alias missing from structure environment")
                .clone();
            sig_items.push(crate::types::decl::SignatureItem::SigValue(
                id.clone(),
                value_desc,
            ));
        }
        PatternDesc::Tpat_tuple(pats) => {
            for p in pats {
                push_sig_values_from_env_pattern(env, p, sig_items);
            }
        }
        _ => {}
    }
}

fn extract_sig_values_from_pattern(
    pat: &crate::types::typedtree::Pattern,
    ty: TypeExprRef,
    sig_items: &mut Vec<crate::types::decl::SignatureItem>,
) {
    use crate::types::decl::{SignatureItem as SigItem, ValueDescription};
    iter_bound_pattern_idents(pat, &mut |id| {
        sig_items.push(SigItem::SigValue(
            id.clone(),
            ValueDescription {
                val_type: ty,
                val_kind: crate::types::decl::ValueKind::ValReg,
                val_loc: crate::location::Location::none(),
                val_attributes: vec![],
                val_path: None,
            },
        ));
    });
}

fn sig_rec_status(rec_flag: RecFlag, index: usize) -> crate::types::decl::RecStatus {
    match rec_flag {
        RecFlag::Recursive => {
            if index == 0 {
                crate::types::decl::RecStatus::TrecFirst
            } else {
                crate::types::decl::RecStatus::TrecNext
            }
        }
        RecFlag::Nonrecursive => crate::types::decl::RecStatus::TrecNot,
    }
}

fn sig_ext_status(index: usize) -> crate::types::decl::ExtStatus {
    if index == 0 {
        crate::types::decl::ExtStatus::TextFirst
    } else {
        crate::types::decl::ExtStatus::TextNext
    }
}

fn sig_type_rec_statuses(
    rec_flag: RecFlag,
    decls: &[TypedTypeDeclaration],
) -> Vec<crate::types::decl::RecStatus> {
    let mut statuses = Vec::with_capacity(decls.len());
    let mut first_non_row = true;
    for decl in decls {
        if crate::types::btype::is_row_name(decl.typ_id.name()) {
            statuses.push(crate::types::decl::RecStatus::TrecNot);
            continue;
        }
        if first_non_row {
            first_non_row = false;
            statuses.push(match rec_flag {
                RecFlag::Recursive => crate::types::decl::RecStatus::TrecFirst,
                RecFlag::Nonrecursive => crate::types::decl::RecStatus::TrecNot,
            });
        } else {
            statuses.push(crate::types::decl::RecStatus::TrecNext);
        }
    }
    statuses
}

fn decl_module_type_from_typed_module_expr_for_sig(
    mod_expr: &ModuleExpr,
) -> Option<crate::types::decl::ModuleType> {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_structure(structure) => Some(
            crate::types::decl::ModuleType::MtySignature(structure.str_type.clone()),
        ),
        _ => decl_module_type_from_typed(&mod_expr.mod_type),
    }
}

/// Check if a structure has duplicate value names (like OCaml's simplify_signature).
/// Returns true if there are duplicates, meaning the structure should be wrapped
/// in Tmod_constraint with Tmodtype_implicit.
///
/// OCaml's simplify_signature operates on the signature (Sig_value items).
/// We approximate this by collecting value names from structure items (explicit defs
/// and includes) and checking for duplicates.
///
/// `env_before` is the env before typing the structure body.
/// `env_after` is the env after typing the structure body.
/// We use the difference between them to detect which names were added by includes.
fn structure_has_duplicate_value_names(structure: &Structure, env_before: &Env, env_after: &Env) -> bool {
    // Collect explicit value names (from Tstr_value and Tstr_primitive)
    let mut explicit_names: Vec<String> = Vec::new();
    let mut has_include = false;

    for item in &structure.str_items {
        match &item.str_desc {
            StructureItemDesc::Tstr_value(_, bindings) => {
                for vb in bindings {
                    iter_bound_pattern_idents(&vb.vb_pat, &mut |id| {
                        explicit_names.push(id.name().to_string());
                    });
                }
            }
            StructureItemDesc::Tstr_primitive(vd) => {
                explicit_names.push(vd.val_name.txt.clone());
            }
            StructureItemDesc::Tstr_include(_) => {
                has_include = true;
            }
            _ => {}
        }
    }

    // Check for duplicates among explicit definitions only
    let mut seen = HashSet::new();
    for name in explicit_names.iter().rev() {
        if !seen.insert(name.clone()) {
            return true;
        }
    }

    // If there are includes, check if any explicit name shadows a value brought
    // in by an include within THIS structure. We detect this by checking if the
    // name has MORE bindings in env_after than env_before — the difference represents
    // bindings added by this structure (both includes and explicit defs).
    if has_include {
        for name in &explicit_names {
            let before_count = env_before.count_value_bindings(name);
            let after_count = env_after.count_value_bindings(name);
            // If env_after has at least 2 MORE bindings than env_before, it means
            // both an include and an explicit def added this name in this structure.
            if after_count >= before_count + 2 {
                return true;
            }
        }
    }

    false
}

/// Look up the semantic module type for a longident by searching env and persistent env.
/// Returns a `decl::ModuleType` (the semantic type), not the `typedtree::ModuleType` (the syntactic type tree).
pub fn lookup_module_path_by_lid<'b>(
    lid: &crate::parser::longident::Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<Path> {
    use crate::parser::longident::Longident;

    match lid {
        Longident::Lident(mod_idx) => {
            let mod_name = arena.get_string(*mod_idx);
            if let Ok((id, md)) = env.find_module_with_id(mod_name) {
                if let Some(path) = &md.md_path {
                    return Some(path.clone());
                }
                return Some(Path::pident(id.clone()));
            }
            if let Some(pers) = pers_env.as_mut() {
                if pers.find_pers_struct(mod_name, ctx).is_some() {
                    return Some(Path::pident(Ident::create_persistent(mod_name)));
                }
            }
            None
        }
        Longident::Ldot(prefix, submod_idx) => {
            let submod_name = arena.get_string(*submod_idx);
            let parent_path = lookup_module_path_by_lid(prefix, arena, env, pers_env, ctx)?;
            let parent_type = lookup_module_type_by_lid(prefix, arena, env, pers_env, ctx)?;
            let parent_sig = resolve_mod_type_to_sig(&parent_type, Some(env), pers_env, ctx)?;
            for sig_item in &parent_sig {
                if let crate::types::decl::SignatureItem::SigModule(id, _sub_md, _) = sig_item {
                    if id.name() == submod_name {
                        return Some(Path::pdot(parent_path, submod_name));
                    }
                }
            }
            None
        }
        Longident::Lapply(functor, arg) => {
            let functor_path = lookup_module_path_by_lid(functor, arena, env, pers_env, ctx)?;
            let arg_path = lookup_module_path_by_lid(arg, arena, env, pers_env, ctx)?;
            Some(Path::papply(functor_path, arg_path))
        }
    }
}

/// Look up a module-type path by longident in the module-type namespace.
/// This mirrors OCaml `Typetexp.find_modtype` / `transl_modtype_longident`.
pub fn lookup_modtype_path_by_lid<'b>(
    lid: &crate::parser::longident::Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<Path> {
    use crate::parser::longident::Longident;

    match lid {
        Longident::Lident(modtype_idx) => {
            let modtype_name = arena.get_string(*modtype_idx);
            env.find_modtype_with_id(modtype_name)
                .ok()
                .map(|(id, _)| Path::pident(id.clone()))
        }
        Longident::Ldot(prefix, submodtype_idx) => {
            let submodtype_name = arena.get_string(*submodtype_idx);
            let parent_path = lookup_module_path_by_lid(prefix, arena, env, pers_env, ctx)?;
            let parent_type = lookup_module_type_by_lid(prefix, arena, env, pers_env, ctx)?;
            let parent_sig = resolve_mod_type_to_sig(&parent_type, Some(env), pers_env, ctx)?;
            for sig_item in &parent_sig {
                if let crate::types::decl::SignatureItem::SigModtype(id, _) = sig_item {
                    if id.name() == submodtype_name {
                        return Some(Path::pdot(parent_path, submodtype_name));
                    }
                }
            }
            None
        }
        Longident::Lapply(_, _) => None,
    }
}

/// Look up the semantic module type for a longident by searching env and persistent env.
/// Returns a `decl::ModuleType` (the semantic type), not the `typedtree::ModuleType` (the syntactic type tree).
pub fn lookup_module_type_by_lid<'b>(
    lid: &crate::parser::longident::Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<crate::types::decl::ModuleType> {
    use crate::parser::longident::Longident;
    use crate::types::decl::ModuleType as DeclMty;
    let debug_lookup = std::env::var_os("RUST_DEBUG_LOOKUP_MOD").is_some();
    match lid {
        Longident::Lident(mod_idx) => {
            let mod_name = arena.get_string(*mod_idx);
            // Try local env first
            if let Ok(md) = env.find_module(mod_name) {
                if debug_lookup {
                    let kind = match &md.md_type {
                        DeclMty::MtySignature(_) => "mty-signature",
                        DeclMty::MtyFunctor { .. } => "mty-functor",
                        DeclMty::MtyIdent(_) => "mty-ident",
                        DeclMty::MtyAlias(_, _) => "mty-alias",
                    };
                    eprintln!("[lookup-mod] lid={} kind={}", mod_name, kind);
                }
                return Some(md.md_type.clone());
            }
            // Try persistent env
            if let Some(pers) = pers_env.as_mut() {
                if let Some(ps) = pers.find_pers_struct(mod_name, ctx) {
                    if debug_lookup {
                        eprintln!("[lookup-mod] lid={} kind=mty-signature(persistent)", mod_name);
                    }
                    return Some(DeclMty::MtySignature(ps.ps_sig.clone()));
                }
            }
            None
        }
        Longident::Ldot(prefix, submod_idx) => {
            let submod_name = arena.get_string(*submod_idx);
            // Recursively resolve prefix to get parent module type
            let parent_type = lookup_module_type_by_lid(prefix, arena, env, pers_env, ctx)?;
            // Keep alias identity for dotted module lookups through aliased parents.
            // OCaml `Env.find_module` preserves this (Belt.Id.MakeComparable is an alias
            // through Belt_Id.MakeComparable), which is required for implicit
            // Tmod_constraint wrapping on Pmod_ident.
            let parent_alias = match &parent_type {
                DeclMty::MtyAlias(alias_presence, alias_path) => {
                    Some((*alias_presence, alias_path.clone()))
                }
                _ => None,
            };
            // Resolve parent type to signature
            let parent_sig = resolve_mod_type_to_sig(&parent_type, Some(env), pers_env, ctx)?;
            // Find sub-module in parent signature
            for sig_item in &parent_sig {
                if let crate::types::decl::SignatureItem::SigModule(id, sub_md, _) = sig_item {
                    if id.name() == submod_name {
                        if let Some((alias_presence, alias_path)) = parent_alias.clone() {
                            if let DeclMty::MtyAlias(child_presence, child_path) = &sub_md.md_type
                            {
                                return Some(DeclMty::MtyAlias(
                                    *child_presence,
                                    child_path.clone(),
                                ));
                            }
                            return Some(DeclMty::MtyAlias(
                                alias_presence,
                                Path::pdot(alias_path, submod_name.to_string()),
                            ));
                        }
                        if debug_lookup {
                            let parent_name = match &parent_type {
                                DeclMty::MtyIdent(path) | DeclMty::MtyAlias(_, path) => path.name(),
                                _ => "<module>".to_string(),
                            };
                            let kind = match &sub_md.md_type {
                                DeclMty::MtySignature(_) => "mty-signature",
                                DeclMty::MtyFunctor { .. } => "mty-functor",
                                DeclMty::MtyIdent(_) => "mty-ident",
                                DeclMty::MtyAlias(_, _) => "mty-alias",
                            };
                            eprintln!(
                                "[lookup-mod] lid={}.{} kind={}",
                                parent_name,
                                submod_name,
                                kind
                            );
                        }
                        return Some(sub_md.md_type.clone());
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Resolve a decl::ModuleType to a signature, following aliases via local and
/// persistent environments. This mirrors OCaml's Env.scrape_alias behavior.
pub fn resolve_mod_type_to_sig<'b>(
    mty: &crate::types::decl::ModuleType,
    env: Option<&Env>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<crate::types::decl::Signature> {
    let mut visiting = HashSet::new();
    resolve_mod_type_to_sig_impl(mty, env, pers_env, ctx, &mut visiting)
}

fn resolve_mod_type_to_sig_impl<'b>(
    mty: &crate::types::decl::ModuleType,
    env: Option<&Env>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
    visiting: &mut HashSet<Path>,
) -> Option<crate::types::decl::Signature> {
    thread_local! {
        static RESOLVE_SIG_DEBUG_DEPTH: Cell<usize> = const { Cell::new(0) };
    }

    struct ResolveSigDebugGuard;
    impl Drop for ResolveSigDebugGuard {
        fn drop(&mut self) {
            RESOLVE_SIG_DEBUG_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
        }
    }

    let _resolve_sig_debug_guard = if std::env::var_os("RUST_DEBUG_RESOLVE_SIG_DEPTH").is_some() {
        RESOLVE_SIG_DEBUG_DEPTH.with(|depth| {
            let next = depth.get() + 1;
            depth.set(next);
            if next > 200 {
                let kind = match mty {
                    crate::types::decl::ModuleType::MtySignature(_) => "sig".to_string(),
                    crate::types::decl::ModuleType::MtyIdent(path) => path.name(),
                    crate::types::decl::ModuleType::MtyAlias(_, path) => path.name(),
                    crate::types::decl::ModuleType::MtyFunctor { .. } => "functor".to_string(),
                };
                panic!("resolve_mod_type_to_sig_impl depth={} kind={}", next, kind);
            }
        });
        Some(ResolveSigDebugGuard)
    } else {
        None
    };

    use crate::types::decl::ModuleType as DeclMty;
    match mty {
        DeclMty::MtySignature(sig) => Some(sig.clone()),
        DeclMty::MtyAlias(_, path) | DeclMty::MtyIdent(path) => {
            resolve_path_to_sig_impl(path, env, pers_env, ctx, visiting)
        }
        _ => None,
    }
}

/// Resolve a module/modtype path to a signature by following through local and
/// persistent environments.
fn resolve_path_to_sig_impl<'b>(
    path: &Path,
    env: Option<&Env>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
    visiting: &mut HashSet<Path>,
) -> Option<crate::types::decl::Signature> {
    use crate::types::decl::SignatureItem as SigItem;

    thread_local! {
        static RESOLVE_PATH_TO_SIG_DEBUG_DEPTH: Cell<usize> = const { Cell::new(0) };
    }

    struct ResolvePathToSigDebugGuard;
    impl Drop for ResolvePathToSigDebugGuard {
        fn drop(&mut self) {
            RESOLVE_PATH_TO_SIG_DEBUG_DEPTH
                .with(|depth| depth.set(depth.get().saturating_sub(1)));
        }
    }

    let _resolve_path_to_sig_debug_guard =
        if std::env::var_os("RUST_DEBUG_RESOLVE_PATH_TO_SIG_DEPTH").is_some() {
            RESOLVE_PATH_TO_SIG_DEBUG_DEPTH.with(|depth| {
                let next = depth.get() + 1;
                depth.set(next);
                if next > 200 {
                    panic!(
                        "resolve_path_to_sig_impl depth={} path={}",
                        next,
                        path.name()
                    );
                }
            });
            Some(ResolvePathToSigDebugGuard)
        } else {
            None
        };

    if !visiting.insert(path.clone()) {
        return None;
    }

    let result = match path {
        Path::Pident(id) => {
            let name = id.name();
            if let Some(local_env) = env {
                if let Ok(md) = local_env.lookup_module(&Path::pident(id.clone())) {
                    if let Some(sig) =
                        resolve_mod_type_to_sig_impl(&md.md_type, env, pers_env, ctx, visiting)
                    {
                        visiting.remove(path);
                        return Some(sig);
                    }
                }
                if let Ok(mtd) = local_env.lookup_modtype(&Path::pident(id.clone())) {
                    if let Some(mty) = &mtd.mtd_type {
                        if let Some(sig) =
                            resolve_mod_type_to_sig_impl(mty, env, pers_env, ctx, visiting)
                        {
                            visiting.remove(path);
                            return Some(sig);
                        }
                    }
                }
            }

            if let Some(pers) = pers_env.as_mut() {
                if let Some(ps) = pers.find_pers_struct(name, ctx) {
                    Some(ps.ps_sig.clone())
                } else {
                    None
                }
            } else {
                None
            }
        }
        Path::Pdot(parent, name, _) => {
            let parent_sig = resolve_path_to_sig_impl(parent, env, pers_env, ctx, visiting)?;
            for sig_item in &parent_sig {
                match sig_item {
                    SigItem::SigModule(id, md, _) if id.name() == name.as_str() => {
                        if let Some(sig) =
                            resolve_mod_type_to_sig_impl(&md.md_type, env, pers_env, ctx, visiting)
                        {
                            visiting.remove(path);
                            return Some(sig);
                        }
                    }
                    SigItem::SigModtype(id, mtd) if id.name() == name.as_str() => {
                        if let Some(mty) = &mtd.mtd_type {
                            if let Some(sig) =
                                resolve_mod_type_to_sig_impl(mty, env, pers_env, ctx, visiting)
                            {
                                visiting.remove(path);
                                return Some(sig);
                            }
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        _ => None,
    };

    visiting.remove(path);
    result
}

type PackageConstraint = (Vec<String>, TypeExprRef);

fn flatten_package_constraint_path(
    lid: &Longident,
    arena: &ParseArena,
    ctx: &crate::types::context::TypeContext<'_>,
) -> Vec<String> {
    lid.flatten_idx()
        .into_iter()
        .map(|idx| ctx.resolve_longident_component(arena, idx))
        .collect()
}

fn nested_package_constraints(
    module_name: &str,
    constraints: &[PackageConstraint],
) -> Vec<PackageConstraint> {
    constraints
        .iter()
        .filter_map(|(path, ty)| {
            let (head, tail) = path.split_first()?;
            if head == module_name && !tail.is_empty() {
                Some((tail.to_vec(), *ty))
            } else {
                None
            }
        })
        .collect()
}

fn copy_signature_for_package_constraints(
    sig_items: &[crate::types::decl::SignatureItem],
    ctx: &crate::types::context::TypeContext<'_>,
) -> crate::types::decl::Signature {
    // package_constraints mutates type nodes through later env substitutions.
    // Copy the signature graph first so each package instantiation has isolated
    // type nodes, matching OCaml's per-instantiation Subst behavior.
    let dummy_param = Ident::create_local("__pkg_copy_param__");
    let dummy_path = Path::pident(Ident::create_local("__pkg_copy_path__"));
    substitute_functor_param_in_signature(sig_items, &dummy_param, &dummy_path, ctx)
}

fn rewrite_parent_scoped_type_paths_for_package<'b>(
    ctx: &'b crate::types::context::TypeContext<'b>,
    ty: TypeExprRef,
    local_type_ids: &HashMap<String, Ident>,
    parent_path: &Path,
    seen: &mut HashSet<TypeExprRef>,
) {
    let ty = ctx.repr(ty);
    if !seen.insert(ty) {
        return;
    }

    let desc = ctx.get_desc(ty).clone();
    if let crate::types::type_expr::TypeDesc::Tconstr { path, args, abbrev } = &desc {
        for arg in args {
            rewrite_parent_scoped_type_paths_for_package(
                ctx,
                *arg,
                local_type_ids,
                parent_path,
                seen,
            );
        }
        if let Path::Pident(id) = path {
            if !id.is_persistent() && !local_type_ids.contains_key(id.name()) {
                ctx.set_desc(
                    ty,
                    crate::types::type_expr::TypeDesc::Tconstr {
                        path: Path::pdot(parent_path.clone(), id.name()),
                        args: args.clone(),
                        abbrev: *abbrev,
                    },
                );
            }
        }
        return;
    }

    crate::types::iter_type_expr(ctx, ty, |child| {
        rewrite_parent_scoped_type_paths_for_package(ctx, child, local_type_ids, parent_path, seen);
    });
}

fn rewrite_package_constrained_type_refs<'b>(
    ctx: &'b crate::types::context::TypeContext<'b>,
    ty: TypeExprRef,
    constrained_type_map: &HashMap<i32, TypeExprRef>,
    seen: &mut HashSet<TypeExprRef>,
) {
    use crate::types::type_expr::TypeDesc;

    let ty = ctx.repr(ty);
    if !seen.insert(ty) {
        return;
    }

    let desc = ctx.get_desc(ty).clone();
    match desc {
        TypeDesc::Tconstr { path, args, .. } => {
            for arg in &args {
                rewrite_package_constrained_type_refs(ctx, *arg, constrained_type_map, seen);
            }
            if args.is_empty() {
                if let Path::Pident(id) = &path {
                    if let Some(&manifest_ty) = constrained_type_map.get(&id.stamp()) {
                        crate::types::link_type(ctx, ty, manifest_ty);
                        return;
                    }
                }
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            rewrite_package_constrained_type_refs(ctx, arg.typ, constrained_type_map, seen);
            rewrite_package_constrained_type_refs(ctx, ret, constrained_type_map, seen);
        }
        TypeDesc::Ttuple(types) => {
            for child in &types {
                rewrite_package_constrained_type_refs(ctx, *child, constrained_type_map, seen);
            }
        }
        TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
            rewrite_package_constrained_type_refs(ctx, target, constrained_type_map, seen);
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_package_constrained_type_refs(ctx, fields, constrained_type_map, seen);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_package_constrained_type_refs(ctx, typ, constrained_type_map, seen);
            rewrite_package_constrained_type_refs(ctx, rest, constrained_type_map, seen);
        }
        TypeDesc::Tvariant(row) => {
            rewrite_package_constrained_type_refs(ctx, row.row_more, constrained_type_map, seen);
            for (_, field) in &row.row_fields {
                match field {
                    crate::types::type_expr::RowField::Rpresent(Some(t)) => {
                        rewrite_package_constrained_type_refs(ctx, *t, constrained_type_map, seen);
                    }
                    crate::types::type_expr::RowField::Reither { types, .. } => {
                        for t in types {
                            rewrite_package_constrained_type_refs(ctx, *t, constrained_type_map, seen);
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_package_constrained_type_refs(ctx, body, constrained_type_map, seen);
            for v in &vars {
                rewrite_package_constrained_type_refs(ctx, *v, constrained_type_map, seen);
            }
        }
        TypeDesc::Tpackage { args, .. } => {
            for arg in &args {
                rewrite_package_constrained_type_refs(ctx, *arg, constrained_type_map, seen);
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

fn apply_package_constraints_to_module_type<'b>(
    env: &Env,
    mty: &crate::types::decl::ModuleType,
    constraints: &[PackageConstraint],
    package_parent_path: Option<&Path>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::ModuleType as DeclMty;
    use crate::types::decl::SignatureItem;

    if constraints.is_empty() {
        return Some(mty.clone());
    }

    // Match OCaml Typemod.package_constraints:
    // - extract signature for the module type
    // - only rewrite constrained Sig_type manifests
    // - recurse into Sig_module with nested constraints
    let sig = resolve_mod_type_to_sig(mty, Some(env), pers_env, ctx)?;
    let sig = copy_signature_for_package_constraints(&sig, ctx);
    let mut rewritten_sig = Vec::with_capacity(sig.len());
    let local_type_ids: HashMap<String, Ident> = sig
        .iter()
        .filter_map(|item| match item {
            SignatureItem::SigType(id, _, _) => Some((id.name().to_string(), id.clone())),
            _ => None,
        })
        .collect();
    let mut constrained_type_map: HashMap<i32, TypeExprRef> = HashMap::new();
    for item in sig {
        match item {
            SignatureItem::SigValue(id, mut vd) => {
                if let Some(parent_path) = package_parent_path {
                    let mut seen = HashSet::new();
                    rewrite_parent_scoped_type_paths_for_package(
                        ctx,
                        vd.val_type,
                        &local_type_ids,
                        parent_path,
                        &mut seen,
                    );
                }
                rewritten_sig.push(SignatureItem::SigValue(id, vd));
            }
            SignatureItem::SigType(id, mut td, rec_status) => {
                if td.type_params.is_empty() {
                    if let Some((_, manifest_ty)) = constraints
                        .iter()
                        .find(|(path, _)| path.len() == 1 && path[0] == id.name())
                    {
                        td.type_manifest = Some(*manifest_ty);
                        if id.stamp() != 0 {
                            let manifest = ctx.repr(*manifest_ty);
                            let manifest_desc = ctx.get_desc(manifest);
                            if matches!(
                                &*manifest_desc,
                                crate::types::type_expr::TypeDesc::Tconstr {
                                    path: Path::Pident(manifest_id),
                                    args,
                                    ..
                                } if args.is_empty() && !manifest_id.is_persistent() && id.name() == "state"
                            ) {
                                constrained_type_map.insert(id.stamp(), *manifest_ty);
                            }
                        }
                    }
                }
                rewritten_sig.push(SignatureItem::SigType(id, td, rec_status));
            }
            SignatureItem::SigModule(id, mut md, rec_status) => {
                let nested = nested_package_constraints(id.name(), constraints);
                if !nested.is_empty() {
                    let nested_parent_path =
                        package_parent_path.map(|p| Path::pdot(p.clone(), id.name()));
                    md.md_type = apply_package_constraints_to_module_type(
                        env,
                        &md.md_type,
                        &nested,
                        nested_parent_path.as_ref(),
                        pers_env,
                        ctx,
                    )?;
                }
                rewritten_sig.push(SignatureItem::SigModule(id, md, rec_status));
            }
            other => rewritten_sig.push(other),
        }
    }

    if !constrained_type_map.is_empty() {
        let mut seen = HashSet::new();
        for item in &rewritten_sig {
            match item {
                SignatureItem::SigValue(_, vd) => {
                    rewrite_package_constrained_type_refs(
                        ctx,
                        vd.val_type,
                        &constrained_type_map,
                        &mut seen,
                    );
                }
                SignatureItem::SigType(_, td, _) => {
                    if let Some(manifest) = td.type_manifest {
                        rewrite_package_constrained_type_refs(
                            ctx,
                            manifest,
                            &constrained_type_map,
                            &mut seen,
                        );
                    }
                    match &td.type_kind {
                        crate::types::TypeKind::TypeVariant(constrs) => {
                            for cd in constrs {
                                match &cd.cd_args {
                                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                        for arg in args {
                                            rewrite_package_constrained_type_refs(
                                                ctx,
                                                *arg,
                                                &constrained_type_map,
                                                &mut seen,
                                            );
                                        }
                                    }
                                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                        for lbl in labels {
                                            rewrite_package_constrained_type_refs(
                                                ctx,
                                                lbl.ld_type,
                                                &constrained_type_map,
                                                &mut seen,
                                            );
                                        }
                                    }
                                }
                                if let Some(res) = cd.cd_res {
                                    rewrite_package_constrained_type_refs(
                                        ctx,
                                        res,
                                        &constrained_type_map,
                                        &mut seen,
                                    );
                                }
                            }
                        }
                        crate::types::TypeKind::TypeRecord(labels, _) => {
                            for lbl in labels {
                                rewrite_package_constrained_type_refs(
                                    ctx,
                                    lbl.ld_type,
                                    &constrained_type_map,
                                    &mut seen,
                                );
                            }
                        }
                        _ => {}
                    }
                }
                SignatureItem::SigTypext(_, ext, _) => {
                    for arg in &ext.ext_type_params {
                        rewrite_package_constrained_type_refs(
                            ctx,
                            *arg,
                            &constrained_type_map,
                            &mut seen,
                        );
                    }
                    match &ext.ext_args {
                        crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                            for arg in args {
                                rewrite_package_constrained_type_refs(
                                    ctx,
                                    *arg,
                                    &constrained_type_map,
                                    &mut seen,
                                );
                            }
                        }
                        crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                            for lbl in labels {
                                rewrite_package_constrained_type_refs(
                                    ctx,
                                    lbl.ld_type,
                                    &constrained_type_map,
                                    &mut seen,
                                );
                            }
                        }
                    }
                    if let Some(ret) = ext.ext_ret_type {
                        rewrite_package_constrained_type_refs(
                            ctx,
                            ret,
                            &constrained_type_map,
                            &mut seen,
                        );
                    }
                }
                _ => {}
            }
        }
    }

    Some(DeclMty::MtySignature(rewritten_sig))
}

/// Port of OCaml `Typemod.modtype_of_package` + `package_constraints`.
/// Converts `Tpackage(path, lids, args)` into a semantic module type by
/// resolving the package modtype path and applying `with type ... = ...`
/// constraints onto the resulting signature.
pub fn modtype_of_package<'b>(
    env: &Env,
    package_path: &Path,
    package_lids: &[Longident],
    package_args: &[TypeExprRef],
    arena: &ParseArena,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::ModuleType as DeclMty;

    if package_lids.len() != package_args.len() {
        return None;
    }

    if package_lids.is_empty() {
        return Some(DeclMty::MtyIdent(package_path.clone()));
    }

    let constraints: Vec<PackageConstraint> = package_lids
        .iter()
        .zip(package_args.iter())
        .map(|(lid, ty)| (flatten_package_constraint_path(lid, arena, ctx), *ty))
        .collect();

    let base_mty = DeclMty::MtyIdent(package_path.clone());
    let package_parent_path = match package_path {
        Path::Pdot(parent, _, _) => Some(parent.as_ref().clone()),
        _ => None,
    };
    apply_package_constraints_to_module_type(
        env,
        &base_mty,
        &constraints,
        package_parent_path.as_ref(),
        pers_env,
        ctx,
    )
}

fn parent_path_for_module_type(mty: &crate::types::decl::ModuleType) -> Option<Path> {
    use crate::types::decl::ModuleType as DeclMty;

    match mty {
        DeclMty::MtyIdent(Path::Pdot(parent, _, _))
        | DeclMty::MtyAlias(_, Path::Pdot(parent, _, _)) => Some(parent.as_ref().clone()),
        _ => None,
    }
}

fn collect_pmty_with_type_constraints<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    constraints: &[crate::parser::ast::WithConstraint],
) -> TypeModResult<Vec<PackageConstraint>> {
    use crate::parser::ast::WithConstraint as ParsedWithConstraint;

    let mut out = Vec::new();
    for constraint in constraints {
        match constraint {
            ParsedWithConstraint::Pwith_type(lid, decl)
            | ParsedWithConstraint::Pwith_typesubst(lid, decl) => {
                if let Some(manifest) = decl.ptype_manifest {
                    let (_, manifest_ty) = transl_type(tctx, env, arena.get_core_type(manifest))?;
                    let longident = tctx.resolve_lid(lid.txt).clone();
                    let path = flatten_package_constraint_path(&longident, arena, tctx.type_ctx);
                    out.push((path, manifest_ty));
                }
            }
            ParsedWithConstraint::Pwith_module(_, _)
            | ParsedWithConstraint::Pwith_modsubst(_, _) => {}
        }
    }

    Ok(out)
}

fn transl_with_constraints<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    constraints: &[crate::parser::ast::WithConstraint],
) -> TypeModResult<Vec<(Path, Located<LidentIdx>, crate::types::typedtree::WithConstraint)>> {
    use crate::parser::ast::WithConstraint as ParsedWithConstraint;
    use crate::types::typedtree::WithConstraint as TypedWithConstraint;

    let mut typed_constraints = Vec::with_capacity(constraints.len());
    for constraint in constraints {
        match constraint {
            ParsedWithConstraint::Pwith_type(lid, decl) => {
                let longident = tctx.resolve_lid(lid.txt).clone();
                let path = path_from_longident(&longident, |idx| arena.get_string(idx));
                let mut typed_decls =
                    transl_sig_type_declarations(tctx, env, arena, std::slice::from_ref(decl))?;
                if let Some(typed_decl) = typed_decls.pop() {
                    typed_constraints.push((
                        path,
                        lid.clone(),
                        TypedWithConstraint::Twith_type(typed_decl),
                    ));
                }
            }
            ParsedWithConstraint::Pwith_typesubst(lid, decl) => {
                let longident = tctx.resolve_lid(lid.txt).clone();
                let path = path_from_longident(&longident, |idx| arena.get_string(idx));
                let mut typed_decls =
                    transl_sig_type_declarations(tctx, env, arena, std::slice::from_ref(decl))?;
                if let Some(typed_decl) = typed_decls.pop() {
                    typed_constraints.push((
                        path,
                        lid.clone(),
                        TypedWithConstraint::Twith_typesubst(typed_decl),
                    ));
                }
            }
            ParsedWithConstraint::Pwith_module(lid, rhs_lid) => {
                let lhs_longident = tctx.resolve_lid(lid.txt).clone();
                let lhs_path = path_from_longident(&lhs_longident, |idx| arena.get_string(idx));
                let rhs_longident = tctx.resolve_lid(rhs_lid.txt).clone();
                let rhs_path = lookup_module_path_by_lid(
                    &rhs_longident,
                    arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .unwrap_or_else(|| path_from_longident(&rhs_longident, |idx| arena.get_string(idx)));
                typed_constraints.push((
                    lhs_path,
                    lid.clone(),
                    TypedWithConstraint::Twith_module(rhs_path, rhs_lid.clone()),
                ));
            }
            ParsedWithConstraint::Pwith_modsubst(lid, rhs_lid) => {
                let lhs_longident = tctx.resolve_lid(lid.txt).clone();
                let lhs_path = path_from_longident(&lhs_longident, |idx| arena.get_string(idx));
                let rhs_longident = tctx.resolve_lid(rhs_lid.txt).clone();
                let rhs_path = lookup_module_path_by_lid(
                    &rhs_longident,
                    arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .unwrap_or_else(|| path_from_longident(&rhs_longident, |idx| arena.get_string(idx)));
                typed_constraints.push((
                    lhs_path,
                    lid.clone(),
                    TypedWithConstraint::Twith_modsubst(rhs_path, rhs_lid.clone()),
                ));
            }
        }
    }

    Ok(typed_constraints)
}

fn collect_manifest_type_aliases_for_functor_arg(
    arg_mty: &crate::types::decl::ModuleType,
) -> HashMap<String, TypeExprRef> {
    use crate::types::decl::SignatureItem;

    let mut manifests = HashMap::new();

    if let crate::types::decl::ModuleType::MtySignature(sig_items) = arg_mty {
        for item in sig_items {
            if let SignatureItem::SigType(id, decl, _) = item {
                if decl.type_params.is_empty() {
                    if let Some(manifest) = decl.type_manifest {
                        manifests.insert(id.name().to_string(), manifest);
                    }
                }
            }
        }
    }

    manifests
}

fn rewrite_functor_param_type_paths_in_type(
    ty: TypeExprRef,
    param_name: &str,
    manifests: &HashMap<String, TypeExprRef>,
    ctx: &crate::types::context::TypeContext<'_>,
    visited: &mut HashSet<TypeExprRef>,
    manifest_subst_cache: &mut HashMap<String, TypeExprRef>,
) {
    use crate::types::type_expr::{RowField, TypeDesc};

    let ty = ctx.repr(ty);
    if !visited.insert(ty) {
        return;
    }

    let desc = ctx.get_desc(ty).clone();
    match desc {
        TypeDesc::Tconstr { path, args, .. } => {
            let has_args = !args.is_empty();
            for arg in args {
                rewrite_functor_param_type_paths_in_type(arg, param_name, manifests, ctx, visited, manifest_subst_cache);
            }

            if let Path::Pdot(prefix, type_name, _) = path {
                if let Path::Pident(id) = prefix.as_ref() {
                    if id.name() == param_name && !has_args {
                        if let Some(manifest_ty) = manifests.get(type_name.as_str()) {
                            // Cache manifest substitution results so all occurrences of
                            // the same functor parameter type (e.g. S.elt) map to the
                            // SAME substituted node, matching OCaml's Subst.typexp sharing.
                            let manifest_copy = if let Some(&cached) = manifest_subst_cache.get(type_name.as_str()) {
                                cached
                            } else {
                                let mut manifest_copy_cache = HashMap::new();
                                let old_level = ctx.current_level();
                                ctx.set_current_level(crate::types::type_expr::GENERIC_LEVEL);
                                let copy = crate::types::ctype::copy_type_deep(
                                    ctx,
                                    *manifest_ty,
                                    &mut manifest_copy_cache,
                                );
                                ctx.set_current_level(old_level);
                                let mut manifest_visited = HashSet::new();
                                rewrite_functor_param_type_paths_in_type(
                                    copy,
                                    param_name,
                                    manifests,
                                    ctx,
                                    &mut manifest_visited,
                                    manifest_subst_cache,
                                );
                                manifest_subst_cache.insert(type_name.clone(), copy);
                                copy
                            };
                            ctx.set_desc(ty, TypeDesc::Tlink(manifest_copy));
                        }
                    }
                }
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            rewrite_functor_param_type_paths_in_type(arg.typ, param_name, manifests, ctx, visited, manifest_subst_cache);
            rewrite_functor_param_type_paths_in_type(ret, param_name, manifests, ctx, visited, manifest_subst_cache);
        }
        TypeDesc::Ttuple(types) => {
            for inner in types {
                rewrite_functor_param_type_paths_in_type(
                    inner, param_name, manifests, ctx, visited, manifest_subst_cache,
                );
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_functor_param_type_paths_in_type(fields, param_name, manifests, ctx, visited, manifest_subst_cache);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_functor_param_type_paths_in_type(typ, param_name, manifests, ctx, visited, manifest_subst_cache);
            rewrite_functor_param_type_paths_in_type(rest, param_name, manifests, ctx, visited, manifest_subst_cache);
        }
        TypeDesc::Tvariant(row) => {
            rewrite_functor_param_type_paths_in_type(
                row.row_more,
                param_name,
                manifests,
                ctx,
                visited,
                manifest_subst_cache,
            );
            if let Some((_path, row_types)) = row.row_name {
                for row_ty in row_types {
                    rewrite_functor_param_type_paths_in_type(
                        row_ty, param_name, manifests, ctx, visited, manifest_subst_cache,
                    );
                }
            }
            for (_label, row_field) in row.row_fields {
                match row_field {
                    RowField::Rpresent(Some(row_ty)) => {
                        rewrite_functor_param_type_paths_in_type(
                            row_ty, param_name, manifests, ctx, visited, manifest_subst_cache,
                        );
                    }
                    RowField::Reither { types, .. } => {
                        for row_ty in types {
                            rewrite_functor_param_type_paths_in_type(
                                row_ty, param_name, manifests, ctx, visited, manifest_subst_cache,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_functor_param_type_paths_in_type(body, param_name, manifests, ctx, visited, manifest_subst_cache);
            for var in vars {
                rewrite_functor_param_type_paths_in_type(var, param_name, manifests, ctx, visited, manifest_subst_cache);
            }
        }
        TypeDesc::Tpackage { args, .. } => {
            for arg in args {
                rewrite_functor_param_type_paths_in_type(arg, param_name, manifests, ctx, visited, manifest_subst_cache);
            }
        }
        TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
            rewrite_functor_param_type_paths_in_type(target, param_name, manifests, ctx, visited, manifest_subst_cache);
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

fn copy_and_specialize_functor_arg_type(
    ty: TypeExprRef,
    param_name: &str,
    manifests: &HashMap<String, TypeExprRef>,
    ctx: &crate::types::context::TypeContext<'_>,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
    manifest_subst_cache: &mut HashMap<String, TypeExprRef>,
) -> TypeExprRef {
    // Same rationale as copy_and_rewrite_module_prefix_type: result-signature
    // specialization must not capture ambient non-generic levels.
    let old_level = ctx.current_level();
    ctx.set_current_level(crate::types::type_expr::GENERIC_LEVEL);
    let copied = crate::types::ctype::copy_type_deep(ctx, ty, copy_cache);
    ctx.set_current_level(old_level);
    let mut visited = HashSet::new();
    rewrite_functor_param_type_paths_in_type(copied, param_name, manifests, ctx, &mut visited, manifest_subst_cache);
    copied
}

fn specialize_functor_result_value_types(
    mty: &crate::types::decl::ModuleType,
    param_name: &str,
    manifests: &HashMap<String, TypeExprRef>,
    ctx: &crate::types::context::TypeContext<'_>,
) -> crate::types::decl::ModuleType {
    fn specialize_label_decl(
        label: &crate::types::decl::LabelDeclaration,
        param_name: &str,
        manifests: &HashMap<String, TypeExprRef>,
        ctx: &crate::types::context::TypeContext<'_>,
        copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
        manifest_subst_cache: &mut HashMap<String, TypeExprRef>,
    ) -> crate::types::decl::LabelDeclaration {
        let mut specialized = label.clone();
        specialized.ld_type = copy_and_specialize_functor_arg_type(
            label.ld_type,
            param_name,
            manifests,
            ctx,
            copy_cache,
            manifest_subst_cache,
        );
        specialized
    }

    fn specialize_constructor_args(
        args: &crate::types::decl::ConstructorArguments,
        param_name: &str,
        manifests: &HashMap<String, TypeExprRef>,
        ctx: &crate::types::context::TypeContext<'_>,
        copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
        manifest_subst_cache: &mut HashMap<String, TypeExprRef>,
    ) -> crate::types::decl::ConstructorArguments {
        match args {
            crate::types::decl::ConstructorArguments::CstrTuple(types) => {
                crate::types::decl::ConstructorArguments::CstrTuple(
                    types
                        .iter()
                        .map(|ty| {
                            copy_and_specialize_functor_arg_type(
                                *ty, param_name, manifests, ctx, copy_cache, manifest_subst_cache,
                            )
                        })
                        .collect(),
                )
            }
            crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                crate::types::decl::ConstructorArguments::CstrRecord(
                    labels
                        .iter()
                        .map(|label| {
                            specialize_label_decl(label, param_name, manifests, ctx, copy_cache, manifest_subst_cache)
                        })
                        .collect(),
                )
            }
        }
    }

    fn specialize_type_kind(
        kind: &crate::types::decl::TypeKind,
        param_name: &str,
        manifests: &HashMap<String, TypeExprRef>,
        ctx: &crate::types::context::TypeContext<'_>,
        copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
        manifest_subst_cache: &mut HashMap<String, TypeExprRef>,
    ) -> crate::types::decl::TypeKind {
        match kind {
            crate::types::decl::TypeKind::TypeAbstract => {
                crate::types::decl::TypeKind::TypeAbstract
            }
            crate::types::decl::TypeKind::TypeOpen => crate::types::decl::TypeKind::TypeOpen,
            crate::types::decl::TypeKind::TypeRecord(labels, repre) => {
                crate::types::decl::TypeKind::TypeRecord(
                    labels
                        .iter()
                        .map(|label| {
                            specialize_label_decl(label, param_name, manifests, ctx, copy_cache, manifest_subst_cache)
                        })
                        .collect(),
                    repre.clone(),
                )
            }
            crate::types::decl::TypeKind::TypeVariant(constructors) => {
                crate::types::decl::TypeKind::TypeVariant(
                    constructors
                        .iter()
                        .map(|constructor| {
                            let mut specialized = constructor.clone();
                            specialized.cd_args = specialize_constructor_args(
                                &constructor.cd_args,
                                param_name,
                                manifests,
                                ctx,
                                copy_cache,
                                manifest_subst_cache,
                            );
                            specialized.cd_res = constructor.cd_res.map(|ty| {
                                copy_and_specialize_functor_arg_type(
                                    ty, param_name, manifests, ctx, copy_cache, manifest_subst_cache,
                                )
                            });
                            specialized
                        })
                        .collect(),
                )
            }
        }
    }

    fn specialize_type_inlined(
        inlined: &crate::types::decl::TypeInlinedType,
        param_name: &str,
        manifests: &HashMap<String, TypeExprRef>,
        ctx: &crate::types::context::TypeContext<'_>,
        copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
        manifest_subst_cache: &mut HashMap<String, TypeExprRef>,
    ) -> crate::types::decl::TypeInlinedType {
        match inlined {
            crate::types::decl::TypeInlinedType::Record { type_name, labels } => {
                crate::types::decl::TypeInlinedType::Record {
                    type_name: type_name.clone(),
                    labels: labels
                        .iter()
                        .map(|label| {
                            specialize_label_decl(label, param_name, manifests, ctx, copy_cache, manifest_subst_cache)
                        })
                        .collect(),
                }
            }
        }
    }

    fn specialize_inner(
        mty: &crate::types::decl::ModuleType,
        param_name: &str,
        manifests: &HashMap<String, TypeExprRef>,
        ctx: &crate::types::context::TypeContext<'_>,
        copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
        manifest_subst_cache: &mut HashMap<String, TypeExprRef>,
    ) -> crate::types::decl::ModuleType {
        use crate::types::decl::{ModuleType as DeclMty, SignatureItem};

        match mty {
            DeclMty::MtySignature(sig_items) => {
                let specialized_sig = sig_items
                    .iter()
                    .map(|item| match item {
                        SignatureItem::SigValue(id, vd) => {
                            let mut specialized_vd = vd.clone();
                            specialized_vd.val_type = copy_and_specialize_functor_arg_type(
                                vd.val_type,
                                param_name,
                                manifests,
                                ctx,
                                copy_cache,
                                manifest_subst_cache,
                            );
                            SignatureItem::SigValue(id.clone(), specialized_vd)
                        }
                        SignatureItem::SigType(id, decl, rec_status) => {
                            let mut local_copy_cache = HashMap::new();
                            let mut specialized_decl = decl.clone();
                            specialized_decl.type_params = decl
                                .type_params
                                .iter()
                                .map(|ty| {
                                    copy_and_specialize_functor_arg_type(
                                        *ty,
                                        param_name,
                                        manifests,
                                        ctx,
                                        &mut local_copy_cache,
                                        manifest_subst_cache,
                                    )
                                })
                                .collect();
                            specialized_decl.type_kind = specialize_type_kind(
                                &decl.type_kind,
                                param_name,
                                manifests,
                                ctx,
                                &mut local_copy_cache,
                                manifest_subst_cache,
                            );
                            specialized_decl.type_manifest = decl.type_manifest.map(|ty| {
                                copy_and_specialize_functor_arg_type(
                                    ty,
                                    param_name,
                                    manifests,
                                    ctx,
                                    &mut local_copy_cache,
                                    manifest_subst_cache,
                                )
                            });
                            specialized_decl.type_inlined_types = decl
                                .type_inlined_types
                                .iter()
                                .map(|inlined| {
                                    specialize_type_inlined(
                                        inlined,
                                        param_name,
                                        manifests,
                                        ctx,
                                        &mut local_copy_cache,
                                        manifest_subst_cache,
                                    )
                                })
                                .collect();
                            SignatureItem::SigType(id.clone(), specialized_decl, *rec_status)
                        }
                        SignatureItem::SigTypext(id, ext, ext_status) => {
                            let mut local_copy_cache = HashMap::new();
                            let mut specialized_ext = ext.clone();
                            specialized_ext.ext_type_params = ext
                                .ext_type_params
                                .iter()
                                .map(|ty| {
                                    copy_and_specialize_functor_arg_type(
                                        *ty,
                                        param_name,
                                        manifests,
                                        ctx,
                                        &mut local_copy_cache,
                                        manifest_subst_cache,
                                    )
                                })
                                .collect();
                            specialized_ext.ext_args = specialize_constructor_args(
                                &ext.ext_args,
                                param_name,
                                manifests,
                                ctx,
                                &mut local_copy_cache,
                                manifest_subst_cache,
                            );
                            specialized_ext.ext_ret_type = ext.ext_ret_type.map(|ty| {
                                copy_and_specialize_functor_arg_type(
                                    ty,
                                    param_name,
                                    manifests,
                                    ctx,
                                    &mut local_copy_cache,
                                    manifest_subst_cache,
                                )
                            });
                            SignatureItem::SigTypext(id.clone(), specialized_ext, *ext_status)
                        }
                        SignatureItem::SigModule(id, md, rec_status) => {
                            let mut specialized_md = md.clone();
                            specialized_md.md_type = specialize_inner(
                                &md.md_type,
                                param_name,
                                manifests,
                                ctx,
                                copy_cache,
                                manifest_subst_cache,
                            );
                            SignatureItem::SigModule(id.clone(), specialized_md, *rec_status)
                        }
                        SignatureItem::SigModtype(id, mtd) => {
                            let mut specialized_mtd = mtd.clone();
                            specialized_mtd.mtd_type = mtd.mtd_type.as_ref().map(|inner| {
                                specialize_inner(inner, param_name, manifests, ctx, copy_cache, manifest_subst_cache)
                            });
                            SignatureItem::SigModtype(id.clone(), specialized_mtd)
                        }
                        _ => item.clone(),
                    })
                    .collect();
                DeclMty::MtySignature(specialized_sig)
            }
            DeclMty::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                let specialized_param_type = param_type.as_ref().map(|inner| {
                    Box::new(specialize_inner(
                        inner, param_name, manifests, ctx, copy_cache, manifest_subst_cache,
                    ))
                });
                if param.name() == param_name {
                    DeclMty::MtyFunctor {
                        param: param.clone(),
                        param_type: specialized_param_type,
                        result: result.clone(),
                    }
                } else {
                    DeclMty::MtyFunctor {
                        param: param.clone(),
                        param_type: specialized_param_type,
                        result: Box::new(specialize_inner(
                            result, param_name, manifests, ctx, copy_cache, manifest_subst_cache,
                        )),
                    }
                }
            }
            DeclMty::MtyIdent(_) | DeclMty::MtyAlias(_, _) => mty.clone(),
        }
    }

    if manifests.is_empty() {
        return mty.clone();
    }

    let mut copy_cache = HashMap::new();
    let mut manifest_subst_cache = HashMap::new();
    specialize_inner(mty, param_name, manifests, ctx, &mut copy_cache, &mut manifest_subst_cache)
}

/// Mirror OCaml `Env.scrape_alias` enough for functor-application typing:
/// follow `Mty_alias`/`Mty_ident` module-type paths until reaching a
/// concrete module type (for example `Mty_functor`).
fn scrape_alias_module_type<'b>(
    mty: &crate::types::decl::ModuleType,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::ModuleType as DeclMty;

    fn resolve_path<'b>(
        path: &Path,
        env: &Env,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
        visiting: &mut HashSet<Path>,
    ) -> Option<DeclMty> {
        thread_local! {
            static SCRAPE_ALIAS_PATH_DEBUG_DEPTH: Cell<usize> = const { Cell::new(0) };
        }

        struct ScrapeAliasPathDebugGuard;
        impl Drop for ScrapeAliasPathDebugGuard {
            fn drop(&mut self) {
                SCRAPE_ALIAS_PATH_DEBUG_DEPTH
                    .with(|depth| depth.set(depth.get().saturating_sub(1)));
            }
        }

        let _scrape_alias_path_debug_guard =
            if std::env::var_os("RUST_DEBUG_SCRAPE_ALIAS_PATH_DEPTH").is_some() {
                SCRAPE_ALIAS_PATH_DEBUG_DEPTH.with(|depth| {
                    let next = depth.get() + 1;
                    depth.set(next);
                    if next > 200 {
                        panic!(
                            "scrape_alias resolve_path depth={} path={}",
                            next,
                            path.name()
                        );
                    }
                });
                Some(ScrapeAliasPathDebugGuard)
            } else {
                None
            };

        fn anchored(owner_path: &Path, mty: &DeclMty) -> DeclMty {
            let mut mty = mty.clone();
            anchor_local_module_aliases_to_owner(&mut mty, owner_path);
            mty
        }

        if !visiting.insert(path.clone()) {
            return None;
        }

        let resolved = match path {
            Path::Pident(id) => {
                let name = id.name();
                if let Ok(md) = env.lookup_module(&Path::pident(id.clone())) {
                    match &md.md_type {
                        DeclMty::MtyAlias(_, alias_path) | DeclMty::MtyIdent(alias_path) => {
                            resolve_path(alias_path, env, pers_env, ctx, visiting)
                        }
                        other => Some(anchored(&Path::pident(id.clone()), other)),
                    }
                } else if let Some(pers) = pers_env.as_mut() {
                    pers.find_pers_struct(name, ctx)
                        .map(|ps| anchored(&Path::pident(id.clone()), &DeclMty::MtySignature(ps.ps_sig.clone())))
                } else {
                    None
                }
            }
            Path::Pdot(parent, submod, _) => {
                let parent_mty = resolve_path(parent, env, pers_env, ctx, visiting)?;
                let parent_sig = resolve_mod_type_to_sig(&parent_mty, Some(env), pers_env, ctx)?;
                let owner_path = Path::pdot((**parent).clone(), submod);
                parent_sig.iter().find_map(|sig_item| match sig_item {
                    crate::types::decl::SignatureItem::SigModule(id, md, _)
                        if id.name() == submod.as_str() =>
                    {
                        match &md.md_type {
                            DeclMty::MtyAlias(_, alias_path) | DeclMty::MtyIdent(alias_path) => {
                                resolve_path(alias_path, env, pers_env, ctx, visiting)
                            }
                            other => Some(anchored(&owner_path, other)),
                        }
                    }
                    _ => None,
                })
            }
            Path::Papply(_, _) => None,
        };

        visiting.remove(path);
        resolved
    }

    match mty {
        DeclMty::MtyAlias(_, path) | DeclMty::MtyIdent(path) => {
            let mut visiting = HashSet::new();
            resolve_path(path, env, pers_env, ctx, &mut visiting)
        }
        other => Some(other.clone()),
    }
}

/// Extract the result type of a functor application.
/// Given a parsed module expression desc for the functor part, looks up its type
/// and returns the result type if it's a functor type.
fn extract_functor_result_type<'b>(
    tctx: &mut TypeCheckContext<'b>,
    functor_desc: &ParsedModuleExprDesc,
    arg_expr: &ParsedModuleExpr,
    arena: &'b ParseArena,
    env: &Env,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::ModuleType as DeclMty;
    // Resolve the functor's module type
    let functor_mty = match functor_desc {
        ParsedModuleExprDesc::Pmod_ident(lid) => {
            let longident = arena.get_longident(lid.txt);
            lookup_module_type_by_lid(
                longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )?
        }
        _ => return None,
    };
    if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
        let kind = match &functor_mty {
            DeclMty::MtySignature(_) => "mty-signature",
            DeclMty::MtyFunctor { .. } => "mty-functor",
            DeclMty::MtyIdent(_) => "mty-ident",
            DeclMty::MtyAlias(_, _) => "mty-alias",
        };
        eprintln!("[functor-result] lookup_functor_mty={}", kind);
    }
    let functor_mty = match scrape_alias_module_type(
        &functor_mty,
        env,
        &mut tctx.persistent_env,
        tctx.type_ctx,
    ) {
        Some(scraped) => scraped,
        None => functor_mty,
    };
    if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
        let kind = match &functor_mty {
            DeclMty::MtySignature(_) => "mty-signature",
            DeclMty::MtyFunctor { .. } => "mty-functor",
            DeclMty::MtyIdent(_) => "mty-ident",
            DeclMty::MtyAlias(_, _) => "mty-alias",
        };
        eprintln!("[functor-result] scraped_functor_mty={}", kind);
    }
    // Extract the result type if it's a functor
    match functor_mty {
        DeclMty::MtyFunctor { param, result, .. } => {
            let mut result = *result;
            // Functor result module types may carry an unqualified local modtype
            // identifier (e.g. `S`) from the defining module signature. Qualify
            // it with the functor's owner module path when needed so downstream
            // signature scraping can resolve it (e.g. `DB__Key.S`).
            if let DeclMty::MtyIdent(path) = &result {
                if resolve_mod_type_to_sig(&result, Some(env), &mut tctx.persistent_env, tctx.type_ctx)
                    .is_none()
                {
                    if let ParsedModuleExprDesc::Pmod_ident(lid) = functor_desc {
                        if let crate::parser::longident::Longident::Ldot(owner_lid, _) =
                            arena.get_longident(lid.txt)
                        {
                            if let Some(owner_path) = lookup_module_path_by_lid(
                                owner_lid,
                                arena,
                                env,
                                &mut tctx.persistent_env,
                                tctx.type_ctx,
                            ) {
                                let qualified =
                                    DeclMty::MtyIdent(Path::pdot(owner_path, path.last().to_string()));
                                if resolve_mod_type_to_sig(
                                    &qualified,
                                    Some(env),
                                    &mut tctx.persistent_env,
                                    tctx.type_ctx,
                                )
                                .is_some()
                                {
                                    result = qualified;
                                }
                            }
                        }
                    }
                }
            }
            if let Some(arg_path) = path_of_parsed_module_expr(arg_expr, arena) {
                Some(substitute_functor_param_in_module_type(
                    &result,
                    &param,
                    &arg_path,
                    tctx.type_ctx,
                ))
            } else {
                let arg_aliases = collect_functor_arg_module_aliases(tctx, env, arg_expr, arena);
                if !arg_aliases.is_empty() {
                    result = substitute_functor_param_aliases_in_module_type(
                        &result,
                        &param,
                        &arg_aliases,
                        tctx.type_ctx,
                    );
                }

                let arg_mty = lookup_module_type_from_parsed_module_expr(
                    tctx, env, arena, arg_expr,
                )
                .or_else(|| {
                    type_module_expr(tctx, env, arena, arg_expr)
                        .ok()
                        .and_then(|typed_arg| {
                            extract_module_type_from_mod_expr_with_ctx(
                                &typed_arg,
                                Some(env),
                                tctx.type_ctx,
                            )
                        })
                });

                if let Some(arg_mty) = arg_mty {
                    let manifests = collect_manifest_type_aliases_for_functor_arg(&arg_mty);
                    if !manifests.is_empty() {
                        return Some(specialize_functor_result_value_types(
                            &result,
                            param.name(),
                            &manifests,
                            tctx.type_ctx,
                        ));
                    }
                }
                Some(result)
            }
        }
        _ => None,
    }
}

/// Find an embedded packed module expression inside an unpack payload expression.
/// This follows common wrappers produced by await/import rewrites.
fn find_packed_module_expr<'a>(expr: &'a crate::parser::ast::Expression, arena: &'a ParseArena) -> Option<&'a ParsedModuleExpr> {
    use crate::parser::ast::ExpressionDesc;

    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_pack(mod_expr_idx) => Some(arena.get_mod_expr(*mod_expr_idx)),
        ExpressionDesc::Pexp_constraint(inner) => find_packed_module_expr(arena.get_expr(inner.0), arena),
        ExpressionDesc::Pexp_coerce(inner) => find_packed_module_expr(arena.get_expr(inner.0), arena),
        ExpressionDesc::Pexp_await(inner) => find_packed_module_expr(arena.get_expr(*inner), arena),
        ExpressionDesc::Pexp_apply(apply) => {
            find_packed_module_expr(arena.get_expr(apply.funct), arena).or_else(|| {
                apply.args.iter()
                    .find_map(|(_, arg)| find_packed_module_expr(arena.get_expr(*arg), arena))
            })
        }
        _ => None,
    }
}

/// Build a typed module-type hint from a parsed module expression when the module
/// expression is (or wraps) an identifier.
fn module_type_hint_from_parsed_module_expr<'a>(
    tctx: &TypeCheckContext<'a>,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
) -> Option<ModuleType> {
    match &*mod_expr.pmod_desc {
        ParsedModuleExprDesc::Pmod_ident(lid) => {
            let longident = tctx.resolve_lid(lid.txt);
            let path = path_from_longident(longident, |idx| arena.get_string(idx));
            Some(ModuleType {
                mty_desc: crate::types::typedtree::ModuleTypeDesc::Tmty_ident(path, lid.clone()),
                mty_loc: mod_expr.pmod_loc,
                mty_attributes: mod_expr.pmod_attributes.clone(),
            })
        }
        ParsedModuleExprDesc::Pmod_constraint(inner, _) => {
            module_type_hint_from_parsed_module_expr(tctx, arena, arena.get_mod_expr(*inner))
        }
        _ => None,
    }
}

/// Find an embedded packed typed module expression inside a typed expression.
/// This mirrors `find_packed_module_expr` for parser expressions and is used when
/// recovering semantic module signatures from `Tmod_unpack`.
fn find_packed_typed_module_expr(expr: &Expression) -> Option<&ModuleExpr> {
    use crate::types::typedtree::ExpressionDesc;

    match &expr.exp_desc {
        ExpressionDesc::Texp_pack(mod_expr) => Some(mod_expr),
        ExpressionDesc::Texp_apply { funct, args, .. } => find_packed_typed_module_expr(funct)
            .or_else(|| {
                args.iter().find_map(|arg| {
                    arg.expression
                        .as_ref()
                        .and_then(find_packed_typed_module_expr)
                })
            }),
        ExpressionDesc::Texp_let(_, bindings, body) => bindings
            .iter()
            .find_map(|vb| find_packed_typed_module_expr(&vb.vb_expr))
            .or_else(|| find_packed_typed_module_expr(body)),
        ExpressionDesc::Texp_sequence(lhs, rhs) => {
            find_packed_typed_module_expr(lhs).or_else(|| find_packed_typed_module_expr(rhs))
        }
        ExpressionDesc::Texp_ifthenelse(cond, then_, else_) => find_packed_typed_module_expr(cond)
            .or_else(|| find_packed_typed_module_expr(then_))
            .or_else(|| else_.as_deref().and_then(find_packed_typed_module_expr)),
        _ => None,
    }
}

/// Extract semantic module type information from an unpack payload expression.
fn lookup_module_type_from_unpack_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    expr: &crate::parser::ast::Expression,
) -> Option<crate::types::decl::ModuleType> {
    // Match OCaml Pmod_unpack typing: inspect the unpack payload type and
    // derive the semantic module type from its package path + constraints.
    // OCaml does this from the typed package expression, not by peeking at
    // the packed parsed module expression.
    let typed_expr = type_expression(tctx, env, expr).ok()?;
    let expanded = crate::types::ctype::expand_head(tctx.type_ctx, env, typed_expr.exp_type);
    let package_info = {
        let desc = tctx.type_ctx.get_desc(tctx.type_ctx.repr(expanded));
        match &*desc {
            crate::types::type_expr::TypeDesc::Tpackage { path, lids, args } => {
                Some((path.clone(), lids.clone(), args.clone()))
            }
            _ => None,
        }
    }?;

    let (package_path, package_lids, package_args) = package_info;
    modtype_of_package(
        env,
        &package_path,
        &package_lids,
        &package_args,
        arena,
        &mut tctx.persistent_env,
        tctx.type_ctx,
    )
}

/// Look up semantic module type information for parsed module expressions.
/// This mirrors OCaml's behavior of using semantic module types for bindings.
pub fn lookup_module_type_from_parsed_module_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
) -> Option<crate::types::decl::ModuleType> {
    match &*mod_expr.pmod_desc {
        ParsedModuleExprDesc::Pmod_ident(lid) => {
            let longident = arena.get_longident(lid.txt);
            lookup_module_type_by_lid(
                longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
        }
        ParsedModuleExprDesc::Pmod_apply(functor_idx, arg_idx) => {
            let functor_expr = arena.get_mod_expr(*functor_idx);
            let arg_expr = arena.get_mod_expr(*arg_idx);
            extract_functor_result_type(tctx, &*functor_expr.pmod_desc, arg_expr, arena, env)
        }
        ParsedModuleExprDesc::Pmod_constraint(inner_idx, mty_idx) => {
            let inner = arena.get_mod_expr(*inner_idx);
            let mty = arena.get_mod_type(*mty_idx);
            translate_module_type_to_decl(tctx, env, arena, mty)
                .ok()
                .or_else(|| lookup_module_type_from_parsed_module_expr(tctx, env, arena, inner))
        }
        ParsedModuleExprDesc::Pmod_unpack(expr_idx) => {
            let expr = arena.get_expr(*expr_idx);
            lookup_module_type_from_unpack_expr(tctx, env, arena, expr)
        }
        _ => None,
    }
}

/// Translate a parsed module type (signature) into a decl::ModuleType.
/// Used for recursive module constraint signatures to populate the environment.
fn translate_module_type_to_decl<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mty: &crate::parser::ast::ModuleType,
) -> TypeModResult<crate::types::decl::ModuleType> {
    use crate::parser::ast::ModuleTypeDesc as PMtyDesc;
    use crate::types::decl::{
        AliasPresence, ModuleType as DeclMty, SignatureItem as SigItem, ValueDescription,
    };
    use crate::types::typemod::path_from_longident;

    match &*mty.pmty_desc {
        PMtyDesc::Pmty_signature(sig_items) => {
            let mut items = Vec::new();
            let mut sig_env = env.clone();
            for sig_item in sig_items.iter() {
                match &*sig_item.psig_desc {
                    crate::parser::ast::SignatureItemDesc::Psig_value(vd) => {
                        let val_name = arena.get_string(vd.pval_name.txt);
                        let val_id = Ident::create_persistent(val_name);
                        // Use transl_type_scheme pattern: begin_def/end_def/generalize
                        // OCaml: reset_type_variables() for each val declaration
                        tctx.type_variables.clear();
                        let ctx = tctx.type_ctx;
                        ctx.begin_def();
                        let (_typed_ct, val_type) = transl_type(tctx, &sig_env, arena.get_core_type(vd.pval_type))?;
                        let ctx = tctx.type_ctx;
                        ctx.end_def();
                        crate::types::ctype::generalize(ctx, val_type);
                        // Match OCaml transl_value_decl parse_arity/get_arity side effects:
                        // expanding the generalized head seeds simple abbreviations so later
                        // instance() calls preserve physical sharing on nullary aliases.
                        if std::env::var_os("RUST_SKIP_SIG_VALUE_EXPAND_HEAD").is_none() {
                            crate::types::ctype::expand_head(ctx, &sig_env, val_type);
                        }
                        items.push(SigItem::SigValue(
                            val_id,
                            ValueDescription {
                                val_type,
                                val_kind: if vd.pval_prim.is_empty() {
                                    crate::types::decl::ValueKind::ValReg
                                } else {
                                    crate::types::decl::ValueKind::ValPrim(
                                        crate::types::decl::PrimitiveDescription {
                                            prim_name: vd
                                                .pval_prim
                                                .first()
                                                .map(|s| arena.get_string(*s).to_string())
                                                .unwrap_or_default(),
                                            prim_arity: 1,
                                            prim_native_name: String::new(),
                                            prim_native_float: false,
                                        },
                                    )
                                },
                                val_loc: crate::location::Location::none(),
                                val_attributes: vec![],
                                val_path: None,
                            },
                        ));
                    }
                    crate::parser::ast::SignatureItemDesc::Psig_type(args) => {
                        let rec_flag = &args.0;
                        let decls = &args.1;
                        let mut declared_type_ids: Vec<Ident> = Vec::with_capacity(decls.len());

                        // Predeclare names so manifests can refer to siblings (matching OCaml).
                        for decl in decls {
                            let type_name = arena.get_string(decl.ptype_name.txt);
                            let type_id = Ident::create_local(type_name);
                            let placeholder_decl = crate::types::TypeDeclaration {
                                type_params: vec![],
                                type_arity: decl.ptype_params.len() as i32,
                                type_kind: crate::types::TypeKind::TypeAbstract,
                                type_private: crate::types::PrivateFlag::Public,
                                type_manifest: None,
                                type_variance: vec![
                                    crate::types::variance::Variance::null();
                                    decl.ptype_params.len()
                                ],
                                type_newtype_level: None,
                                type_loc: crate::location::Location::none(),
                                type_attributes: vec![],
                                type_immediate: false,
                                type_unboxed: crate::types::UnboxedStatus::default(),
                                type_inlined_types: vec![],
                                type_path: Some(Path::pident(type_id.clone())),
                            };
                            sig_env.add_type(type_id.clone(), placeholder_decl);
                            declared_type_ids.push(type_id);
                        }

                        let rec_status_for_index = |idx: usize| match rec_flag {
                            RecFlag::Recursive => {
                                if idx == 0 {
                                    crate::types::decl::RecStatus::TrecFirst
                                } else {
                                    crate::types::decl::RecStatus::TrecNext
                                }
                            }
                            RecFlag::Nonrecursive => crate::types::decl::RecStatus::TrecNot,
                        };

                        for (decl_idx, decl) in decls.iter().enumerate() {
                            let type_id = declared_type_ids[decl_idx].clone();
                            let saved_type_variables = std::mem::take(&mut tctx.type_variables);
                            // Match OCaml transl_type_decl: begin_def so params/manifest
                            // are created at elevated level, then end_def + generalize
                            // marks them as generic (needed for instance_parameterized_type).
                            tctx.type_ctx.begin_def();
                            let mut type_params = Vec::with_capacity(decl.ptype_params.len());
                            let mut type_variance = Vec::with_capacity(decl.ptype_params.len());
                            for (param_ty_idx, variance) in &decl.ptype_params {
                                let param_ty = arena.get_core_type(*param_ty_idx);
                                let param_ref = match &*param_ty.ptyp_desc {
                                    crate::parser::ast::CoreTypeDesc::Ptyp_any => {
                                        tctx.type_ctx.new_var(Some("_".to_string()))
                                    }
                                    crate::parser::ast::CoreTypeDesc::Ptyp_var(name) => {
                                        tctx.type_ctx.new_var(Some(name.to_string()))
                                    }
                                    _ => {
                                        let (_typed_param, param_ref) =
                                            transl_type(tctx, &sig_env, param_ty)?;
                                        param_ref
                                    }
                                };
                                type_params.push(param_ref);
                                if let crate::parser::ast::CoreTypeDesc::Ptyp_var(name) =
                                    &*param_ty.ptyp_desc
                                {
                                    tctx.type_variables.insert(name.to_string(), param_ref);
                                }
                                type_variance.push(match variance {
                                    crate::parser::ast::Variance::Covariant => {
                                        crate::types::variance::Variance::covariant()
                                    }
                                    crate::parser::ast::Variance::Contravariant => {
                                        crate::types::variance::Variance::contravariant()
                                    }
                                    crate::parser::ast::Variance::Invariant => {
                                        crate::types::variance::Variance::null()
                                    }
                                });
                            }

                            let type_manifest = match &decl.ptype_manifest {
                                Some(manifest_idx) => {
                                    let manifest = arena.get_core_type(*manifest_idx);
                                    let (_typed_manifest, manifest_ref) =
                                        transl_type(tctx, &sig_env, manifest)?;
                                    Some(manifest_ref)
                                }
                                None => None,
                            };

                            let type_kind = match &decl.ptype_kind {
                                crate::parser::ast::TypeKind::Ptype_abstract => {
                                    crate::types::TypeKind::TypeAbstract
                                }
                                crate::parser::ast::TypeKind::Ptype_open => {
                                    crate::types::TypeKind::TypeOpen
                                }
                                crate::parser::ast::TypeKind::Ptype_variant(cstrs) => {
                                    let mut constructors = Vec::with_capacity(cstrs.len());
                                    for cstr in cstrs {
                                        let cstr_name = arena.get_string(cstr.pcd_name.txt);
                                        let cstr_args = match &cstr.pcd_args {
                                            crate::parser::ast::ConstructorArguments::Pcstr_tuple(
                                                args,
                                            ) => {
                                                let mut tuple_args = Vec::with_capacity(args.len());
                                                for arg_idx in args {
                                                    let arg = arena.get_core_type(*arg_idx);
                                                    let (_typed_arg, arg_ref) =
                                                        transl_type(tctx, &sig_env, arg)?;
                                                    tuple_args.push(arg_ref);
                                                }
                                                crate::types::ConstructorArguments::CstrTuple(
                                                    tuple_args,
                                                )
                                            }
                                            crate::parser::ast::ConstructorArguments::Pcstr_record(
                                                labels,
                                            ) => {
                                                let mut record_labels =
                                                    Vec::with_capacity(labels.len());
                                                for label in labels {
                                                    let lbl_name = arena.get_string(label.pld_name.txt);
                                                    let (_typed_label_ty, mut lbl_type) =
                                                        transl_type(tctx, &sig_env, arena.get_core_type(label.pld_type))?;
                                                    if label.pld_optional {
                                                        let option_path =
                                                            Path::pident(Ident::create_persistent("option"));
                                                        lbl_type = tctx
                                                            .type_ctx
                                                            .new_constr(option_path, vec![lbl_type]);
                                                    }
                                                    let lbl_type =
                                                        tctx.type_ctx.new_poly(lbl_type, vec![]);
                                                    let mutable_flag = match label.pld_mutable {
                                                        crate::parser::ast::MutableFlag::Immutable => {
                                                            crate::types::MutableFlag::Immutable
                                                        }
                                                        crate::parser::ast::MutableFlag::Mutable => {
                                                            crate::types::MutableFlag::Mutable
                                                        }
                                                    };
                                                    record_labels.push(crate::types::LabelDeclaration {
                                                        ld_id: Ident::create_persistent(lbl_name),
                                                        ld_mutable: mutable_flag,
                                                        ld_optional: label.pld_optional,
                                                        ld_type: lbl_type,
                                                        ld_loc: arena.to_location(label.pld_loc),
                                                        ld_attributes: vec![],
                                                    });
                                                }
                                                crate::types::ConstructorArguments::CstrRecord(
                                                    record_labels,
                                                )
                                            }
                                        };
                                        constructors.push(crate::types::ConstructorDeclaration {
                                            cd_id: Ident::create_persistent(cstr_name),
                                            cd_args: cstr_args,
                                            cd_res: match &cstr.pcd_res {
                                                Some(res_core_type_idx) => {
                                                    let res_core_type = arena.get_core_type(*res_core_type_idx);
                                                    let (_typed_res, res_ref) =
                                                        transl_type(tctx, &sig_env, res_core_type)?;
                                                    Some(res_ref)
                                                }
                                                None => None,
                                            },
                                            cd_loc: arena.to_location(cstr.pcd_loc),
                                            cd_attributes: vec![],
                                        });
                                    }
                                    crate::types::TypeKind::TypeVariant(constructors)
                                }
                                crate::parser::ast::TypeKind::Ptype_record(labels) => {
                                    let mut record_labels = Vec::with_capacity(labels.len());
                                    for label in labels {
                                        let lbl_name = arena.get_string(label.pld_name.txt);
                                        let (_typed_label_ty, mut lbl_type) =
                                            transl_type(tctx, &sig_env, arena.get_core_type(label.pld_type))?;
                                        if label.pld_optional {
                                            let option_path =
                                                Path::pident(Ident::create_persistent("option"));
                                            lbl_type = tctx
                                                .type_ctx
                                                .new_constr(option_path, vec![lbl_type]);
                                        }
                                        let lbl_type = tctx.type_ctx.new_poly(lbl_type, vec![]);
                                        let mutable_flag = match label.pld_mutable {
                                            crate::parser::ast::MutableFlag::Immutable => {
                                                crate::types::MutableFlag::Immutable
                                            }
                                            crate::parser::ast::MutableFlag::Mutable => {
                                                crate::types::MutableFlag::Mutable
                                            }
                                        };
                                        record_labels.push(crate::types::LabelDeclaration {
                                            ld_id: Ident::create_persistent(lbl_name),
                                            ld_mutable: mutable_flag,
                                            ld_optional: label.pld_optional,
                                            ld_type: lbl_type,
                                            ld_loc: arena.to_location(label.pld_loc),
                                            ld_attributes: vec![],
                                        });
                                    }
                                    crate::types::TypeKind::TypeRecord(
                                        record_labels,
                                        crate::types::RecordRepresentation::RecordRegular,
                                    )
                                }
                            };

                            // end_def + generalize: mark params/manifest as generic
                            tctx.type_ctx.end_def();
                            for &p in &type_params {
                                crate::types::ctype::generalize(tctx.type_ctx, p);
                            }
                            crate::types::btype::iter_type_expr_kind(&type_kind, |ty| {
                                crate::types::ctype::generalize(tctx.type_ctx, ty);
                            });
                            if let Some(m) = type_manifest {
                                crate::types::ctype::generalize(tctx.type_ctx, m);
                            }

                            let type_decl = crate::types::TypeDeclaration {
                                type_params,
                                type_arity: decl.ptype_params.len() as i32,
                                type_kind,
                                type_private: match decl.ptype_private {
                                    crate::parser::ast::PrivateFlag::Public => {
                                        crate::types::PrivateFlag::Public
                                    }
                                    crate::parser::ast::PrivateFlag::Private => {
                                        crate::types::PrivateFlag::Private
                                    }
                                },
                                type_manifest,
                                type_variance,
                                type_newtype_level: None,
                                type_loc: arena.to_location(decl.ptype_loc),
                                type_attributes: vec![],
                                type_immediate: false,
                                type_unboxed: crate::types::UnboxedStatus::default(),
                                type_inlined_types: vec![],
                                type_path: Some(Path::pident(type_id.clone())),
                            };
                            sig_env.add_type(type_id.clone(), type_decl.clone());
                            items.push(SigItem::SigType(
                                type_id,
                                type_decl,
                                rec_status_for_index(decl_idx),
                            ));
                            tctx.type_variables = saved_type_variables;
                        }
                    }
                    crate::parser::ast::SignatureItemDesc::Psig_module(md) => {
                        let mod_name = arena.get_string(md.pmd_name.txt);
                        let mod_id = Ident::create_local(mod_name);
                        let inner_mty =
                            translate_module_type_to_decl(tctx, &sig_env, arena, arena.get_mod_type(md.pmd_type))?;
                        sig_env.add_module(
                            mod_id.clone(),
                            crate::types::decl::ModuleDeclaration {
                                md_type: inner_mty.clone(),
                                md_attributes: vec![],
                                md_loc: crate::location::Location::none(),
                                md_path: None,
                            },
                        );
                        items.push(SigItem::SigModule(
                            mod_id,
                            crate::types::decl::ModuleDeclaration {
                                md_type: inner_mty,
                                md_attributes: vec![],
                                md_loc: crate::location::Location::none(),
                                md_path: None,
                            },
                            crate::types::decl::RecStatus::TrecNot,
                        ));
                    }
                    crate::parser::ast::SignatureItemDesc::Psig_modtype(pmtd) => {
                        let modtype_name = arena.get_string(pmtd.pmtd_name.txt);
                        let modtype_id = Ident::create_local(modtype_name);
                        let mtd_type = pmtd
                            .pmtd_type
                            .as_ref()
                            .map(|inner_idx| {
                                translate_module_type_to_decl(tctx, &sig_env, arena, arena.get_mod_type(*inner_idx))
                            })
                            .transpose()?;
                        let mtd = crate::types::decl::ModtypeDeclaration {
                            mtd_type,
                            mtd_attributes: vec![],
                            mtd_loc: crate::location::Location::none(),
                        };
                        sig_env.add_modtype(modtype_id.clone(), mtd.clone());
                        items.push(SigItem::SigModtype(modtype_id, mtd));
                    }
                    crate::parser::ast::SignatureItemDesc::Psig_open(od) => {
                        // Process open declarations to extend sig_env with
                        // opened module's types, matching transl_signature behavior.
                        let longident = tctx.resolve_lid(od.popen_lid.txt).clone();
                        let open_lid = arena.get_longident(od.popen_lid.txt);
                        if let Some((resolved_path, sig_items)) =
                            sig_env.resolve_module_lid(open_lid, arena, &mut tctx.persistent_env, tctx.type_ctx)
                        {
                            crate::cmi::persistent_env::add_signature_to_env(
                                &sig_items,
                                &resolved_path,
                                &mut sig_env,
                                tctx.type_ctx,
                                true, // as_opened
                            );
                        }
                    }
                    _ => {}
                }
            }
            Ok(DeclMty::MtySignature(items))
        }
        PMtyDesc::Pmty_ident(lid) => {
            // Match OCaml transl_modtype: keep an identifier path and let later
            // signature scraping resolve aliases/expansions.
            let longident = tctx.resolve_lid(lid.txt).clone();
            let path = lookup_modtype_path_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or_else(|| path_from_longident(&longident, |idx| arena.get_string(idx)));
            Ok(DeclMty::MtyIdent(path))
        }
        PMtyDesc::Pmty_functor(args) => {
            let (name, param_type, result_type_idx) = &**args;
            let param_id = Ident::create_local(arena.get_string(name.txt));
            let param_decl = match param_type {
                Some(pt_idx) => Some(Box::new(translate_module_type_to_decl(
                    tctx, env, arena, arena.get_mod_type(*pt_idx),
                )?)),
                None => None,
            };
            let mut result_env = env.clone();
            result_env.add_module(
                param_id.clone(),
                crate::types::decl::ModuleDeclaration {
                    md_type: param_decl
                        .as_deref()
                        .cloned()
                        .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![])),
                    md_attributes: vec![],
                    md_loc: crate::location::Location::none(),
                    md_path: None,
                },
            );
            let result_decl = translate_module_type_to_decl(
                tctx,
                &result_env,
                arena,
                arena.get_mod_type(*result_type_idx),
            )?;
            Ok(DeclMty::MtyFunctor {
                param: param_id,
                param_type: param_decl,
                result: Box::new(result_decl),
            })
        }
        PMtyDesc::Pmty_with(args) => {
            let (body_idx, constraints) = &**args;
            let base_mty = translate_module_type_to_decl(tctx, env, arena, arena.get_mod_type(*body_idx))?;
            let type_constraints =
                collect_pmty_with_type_constraints(tctx, env, arena, constraints)?;
            if type_constraints.is_empty() {
                Ok(base_mty)
            } else {
                let parent_path = parent_path_for_module_type(&base_mty);
                Ok(apply_package_constraints_to_module_type(
                    env,
                    &base_mty,
                    &type_constraints,
                    parent_path.as_ref(),
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .unwrap_or(base_mty))
            }
        }
        PMtyDesc::Pmty_typeof(me_idx) => {
            let me = arena.get_mod_expr(*me_idx);
            lookup_module_type_from_parsed_module_expr(tctx, env, arena, me).ok_or(
                TypeModError::InvalidModuleExpr(arena.to_location(mty.pmty_loc)),
            )
        }
        PMtyDesc::Pmty_alias(lid) => {
            let longident = tctx.resolve_lid(lid.txt).clone();
            let path = lookup_module_path_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or_else(|| path_from_longident(&longident, |idx| arena.get_string(idx)));
            Ok(DeclMty::MtyAlias(AliasPresence::MtaAbsent, path))
        }
        PMtyDesc::Pmty_extension(_) => Ok(DeclMty::MtySignature(vec![])),
    }
}

/// Extract a `decl::ModuleType` from a typed module expression (public wrapper).
pub fn extract_module_type_from_mod_expr_pub(
    mod_expr: &ModuleExpr,
) -> Option<crate::types::decl::ModuleType> {
    let mut no_ident_resolver = |_lid: &Located<LidentIdx>,
                                 _env: Option<&Env>|
     -> Option<crate::types::decl::Signature> { None };
    extract_module_type_from_mod_expr_with_resolver(mod_expr, None, None, &mut no_ident_resolver)
}

fn anchor_local_module_aliases_to_owner(
    mty: &mut crate::types::decl::ModuleType,
    owner_path: &Path,
) {
    thread_local! {
        static ANCHOR_DEBUG_DEPTH: Cell<usize> = const { Cell::new(0) };
    }

    struct AnchorDebugGuard;
    impl Drop for AnchorDebugGuard {
        fn drop(&mut self) {
            ANCHOR_DEBUG_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
        }
    }

    let _anchor_debug_guard = if std::env::var_os("RUST_DEBUG_ANCHOR_DEPTH").is_some() {
        ANCHOR_DEBUG_DEPTH.with(|depth| {
            let next = depth.get() + 1;
            depth.set(next);
            if next > 200 {
                panic!(
                    "anchor_local_module_aliases_to_owner depth={} owner={}",
                    next,
                    owner_path.name()
                );
            }
        });
        Some(AnchorDebugGuard)
    } else {
        None
    };

    use crate::types::decl::ModuleType as DeclMty;
    use crate::types::decl::SignatureItem as SigItem;

    #[derive(Default)]
    struct LocalModuleTypePathMaps {
        module_stamp_map: HashMap<i32, Path>,
        module_name_map: HashMap<String, Path>,
        modtype_stamp_map: HashMap<i32, Path>,
        modtype_name_map: HashMap<String, Path>,
    }

    fn build_local_module_type_path_maps(
        sig: &[crate::types::decl::SignatureItem],
        owner_path: &Path,
    ) -> LocalModuleTypePathMaps {
        let mut maps = LocalModuleTypePathMaps::default();

        for item in sig {
            match item {
                SigItem::SigModule(id, _, _) => {
                    let qualified_path = Path::pdot(owner_path.clone(), id.name());
                    maps.module_name_map
                        .insert(id.name().to_string(), qualified_path.clone());
                    if id.stamp() != 0 {
                        maps.module_stamp_map.insert(id.stamp(), qualified_path);
                    }
                }
                SigItem::SigModtype(id, _) => {
                    let qualified_path = Path::pdot(owner_path.clone(), id.name());
                    maps.modtype_name_map
                        .insert(id.name().to_string(), qualified_path.clone());
                    if id.stamp() != 0 {
                        maps.modtype_stamp_map.insert(id.stamp(), qualified_path);
                    }
                }
                _ => {}
            }
        }

        maps
    }

    fn qualify_local_module_type_path(
        path: &Path,
        maps: &LocalModuleTypePathMaps,
    ) -> Path {
        match path {
            Path::Pident(id) => {
                if id.stamp() != 0 {
                    maps.modtype_stamp_map
                        .get(&id.stamp())
                        .cloned()
                        .or_else(|| maps.module_stamp_map.get(&id.stamp()).cloned())
                        .unwrap_or_else(|| path.clone())
                } else {
                    maps.modtype_name_map
                        .get(id.name())
                        .cloned()
                        .or_else(|| maps.module_name_map.get(id.name()).cloned())
                        .unwrap_or_else(|| path.clone())
                }
            }
            Path::Pdot(prefix, name, pos) => Path::Pdot(
                Box::new(qualify_local_module_type_path(prefix, maps)),
                name.clone(),
                *pos,
            ),
            Path::Papply(functor, arg) => Path::Papply(
                Box::new(qualify_local_module_type_path(functor, maps)),
                Box::new(qualify_local_module_type_path(arg, maps)),
            ),
        }
    }

    fn qualify_local_module_type_paths(
        mty: &mut crate::types::decl::ModuleType,
        maps: &LocalModuleTypePathMaps,
    ) {
        match mty {
            DeclMty::MtySignature(sig) => {
                for item in sig {
                    match item {
                        SigItem::SigModule(_, md, _) => {
                            qualify_local_module_type_paths(&mut md.md_type, maps);
                        }
                        SigItem::SigModtype(_, mtd) => {
                            if let Some(mty) = mtd.mtd_type.as_mut() {
                                qualify_local_module_type_paths(mty, maps);
                            }
                        }
                        _ => {}
                    }
                }
            }
            DeclMty::MtyIdent(path) | DeclMty::MtyAlias(_, path) => {
                *path = qualify_local_module_type_path(path, maps);
            }
            DeclMty::MtyFunctor {
                param_type, result, ..
            } => {
                if let Some(param_type) = param_type.as_mut() {
                    qualify_local_module_type_paths(param_type, maps);
                }
                qualify_local_module_type_paths(result, maps);
            }
        }
    }

    match mty {
        DeclMty::MtySignature(sig) => {
            let local_maps = build_local_module_type_path_maps(sig, owner_path);

            for item in sig {
                if let SigItem::SigModule(id, md, _) = item {
                    let child_owner_path = Path::pdot(owner_path.clone(), id.name());
                    md.md_path = Some(child_owner_path.clone());
                    qualify_local_module_type_paths(&mut md.md_type, &local_maps);
                    anchor_local_module_aliases_to_owner(&mut md.md_type, &child_owner_path);
                } else if let SigItem::SigModtype(id, mtd) = item {
                    if let Some(mty) = mtd.mtd_type.as_mut() {
                        qualify_local_module_type_paths(mty, &local_maps);
                        let modtype_owner_path = Path::pdot(owner_path.clone(), id.name());
                        anchor_local_module_aliases_to_owner(mty, &modtype_owner_path);
                    }
                }
            }
        }
        DeclMty::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                anchor_local_module_aliases_to_owner(param_type, owner_path);
            }
            anchor_local_module_aliases_to_owner(result, owner_path);
        }
        DeclMty::MtyIdent(_) | DeclMty::MtyAlias(_, _) => {}
    }
}

/// Extract a `decl::ModuleType` from a typed module expression.
/// For structure modules, builds a signature from the structure items.
/// Convert a typed tree ModuleType to a decl ModuleType.
/// Used both in extract_module_type_from_mod_expr and in transl_signature
/// to add modules to sig_env for subsequent items.
fn decl_module_type_from_typed(
    mty: &ModuleType,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::AliasPresence;
    use crate::types::decl::ExtStatus;
    use crate::types::decl::ModtypeDeclaration;
    use crate::types::decl::ModuleDeclaration;
    use crate::types::decl::RecStatus;
    use crate::types::decl::SignatureItem as SigItem;
    use crate::types::decl::ValueKind;
    use crate::types::decl::ModuleType as DeclMty;
    use crate::types::decl::ValueDescription;
    use crate::types::typedtree::ModuleTypeDesc;
    use crate::types::typedtree::TypedSignatureItemDesc;

    fn rec_status_for_index(rec_flag: RecFlag, index: usize) -> RecStatus {
        match rec_flag {
            RecFlag::Recursive => {
                if index == 0 {
                    RecStatus::TrecFirst
                } else {
                    RecStatus::TrecNext
                }
            }
            RecFlag::Nonrecursive => RecStatus::TrecNot,
        }
    }

    fn ext_status_for_index(index: usize) -> ExtStatus {
        if index == 0 {
            ExtStatus::TextFirst
        } else {
            ExtStatus::TextNext
        }
    }

    match &mty.mty_desc {
        ModuleTypeDesc::Tmty_ident(path, _) => Some(DeclMty::MtyIdent(path.clone())),
        ModuleTypeDesc::Tmty_alias(path, _) => {
            Some(DeclMty::MtyAlias(AliasPresence::MtaAbsent, path.clone()))
        }
        ModuleTypeDesc::Tmty_signature(sig) => {
            let mut out = Vec::new();
            for item in &sig.sig_items {
                match &item.sig_desc {
                    TypedSignatureItemDesc::Tsig_value(vd) => {
                        out.push(SigItem::SigValue(
                            vd.val_id.clone(),
                            ValueDescription {
                                val_type: vd.val_desc.ctyp_type,
                                val_kind: ValueKind::ValReg,
                                val_loc: crate::location::Location::none(),
                                val_attributes: vec![],
                                val_path: None,
                            },
                        ));
                    }
                    TypedSignatureItemDesc::Tsig_type(rec_flag, decls) => {
                        for (i, decl) in decls.iter().enumerate() {
                            out.push(SigItem::SigType(
                                decl.typ_id.clone(),
                                decl.typ_type.clone(),
                                rec_status_for_index(*rec_flag, i),
                            ));
                        }
                    }
                    TypedSignatureItemDesc::Tsig_typext(ext) => {
                        for (i, ext_cstr) in ext.tyext_constructors.iter().enumerate() {
                            out.push(SigItem::SigTypext(
                                ext_cstr.ext_id.clone(),
                                ext_cstr.ext_type.clone(),
                                ext_status_for_index(i),
                            ));
                        }
                    }
                    TypedSignatureItemDesc::Tsig_exception(ext) => {
                        out.push(SigItem::SigTypext(
                            ext.ext_id.clone(),
                            ext.ext_type.clone(),
                            ExtStatus::TextException,
                        ));
                    }
                    TypedSignatureItemDesc::Tsig_module(md) => {
                        let decl_mty = decl_module_type_from_typed(&md.md_type)
                            .unwrap_or(DeclMty::MtySignature(vec![]));
                        out.push(SigItem::SigModule(
                            md.md_id.clone(),
                            ModuleDeclaration {
                                md_type: decl_mty,
                                md_attributes: vec![],
                                md_loc: crate::location::Location::none(),
                                md_path: None,
                            },
                            RecStatus::TrecNot,
                        ));
                    }
                    TypedSignatureItemDesc::Tsig_recmodule(decls) => {
                        for (i, md) in decls.iter().enumerate() {
                            let decl_mty = decl_module_type_from_typed(&md.md_type)
                                .unwrap_or(DeclMty::MtySignature(vec![]));
                            out.push(SigItem::SigModule(
                                md.md_id.clone(),
                                ModuleDeclaration {
                                    md_type: decl_mty,
                                    md_attributes: vec![],
                                    md_loc: crate::location::Location::none(),
                                    md_path: None,
                                },
                                rec_status_for_index(RecFlag::Recursive, i),
                            ));
                        }
                    }
                    TypedSignatureItemDesc::Tsig_modtype(mtd) => {
                        out.push(SigItem::SigModtype(
                            mtd.mtd_id.clone(),
                            ModtypeDeclaration {
                                mtd_type: mtd
                                    .mtd_type
                                    .as_ref()
                                    .and_then(decl_module_type_from_typed),
                                mtd_attributes: vec![],
                                mtd_loc: crate::location::Location::none(),
                            },
                        ));
                    }
                    TypedSignatureItemDesc::Tsig_include(_incl) => {}
                    TypedSignatureItemDesc::Tsig_open(_)
                    | TypedSignatureItemDesc::Tsig_attribute(_) => {}
                }
            }
            Some(DeclMty::MtySignature(out))
        }
        ModuleTypeDesc::Tmty_functor(param, _name, param_mty, result_mty) => {
            let decl_param_mty = param_mty
                .as_ref()
                .and_then(|inner| decl_module_type_from_typed(inner))
                .map(Box::new);
            let decl_result = decl_module_type_from_typed(result_mty)?;
            Some(DeclMty::MtyFunctor {
                param: param.clone(),
                param_type: decl_param_mty,
                result: Box::new(decl_result),
            })
        }
        ModuleTypeDesc::Tmty_with(body, _constraints) => {
            decl_module_type_from_typed(body)
        }
        ModuleTypeDesc::Tmty_typeof(_) | ModuleTypeDesc::Tmty_placeholder => None,
    }
}

fn extract_module_type_from_mod_expr(
    mod_expr: &ModuleExpr,
    env: Option<&Env>,
) -> Option<crate::types::decl::ModuleType> {
    let mut no_ident_resolver = |_lid: &Located<LidentIdx>,
                                 _env: Option<&Env>|
     -> Option<crate::types::decl::Signature> { None };
    extract_module_type_from_mod_expr_with_resolver(mod_expr, env, None, &mut no_ident_resolver)
}

fn extract_module_type_from_mod_expr_with_ctx<'a>(
    mod_expr: &ModuleExpr,
    env: Option<&Env>,
    type_ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<crate::types::decl::ModuleType> {
    let mut no_ident_resolver = |_lid: &Located<LidentIdx>,
                                 _env: Option<&Env>|
     -> Option<crate::types::decl::Signature> { None };
    extract_module_type_from_mod_expr_with_resolver(
        mod_expr,
        env,
        Some(type_ctx),
        &mut no_ident_resolver,
    )
}

fn strip_self_module_prefix_in_sig(
    sig: &[crate::types::decl::SignatureItem],
    module_id: &Ident,
    type_ctx: &crate::types::context::TypeContext<'_>,
) {
    use crate::types::decl::SignatureItem;
    use crate::types::type_expr::{RowField, TypeDesc};

    let direct_items = sig
        .iter()
        .filter_map(|item| match item {
            SignatureItem::SigType(id, _, _)
            | SignatureItem::SigModule(id, _, _)
            | SignatureItem::SigModtype(id, _) => Some((id.name().to_string(), id.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();

    fn rewrite_self_path(
        path: &Path,
        module_id: &Ident,
        direct_items: &HashMap<String, Ident>,
    ) -> Option<Path> {
        match path {
            Path::Pdot(prefix, name, pos) => {
                if let Path::Pident(prefix_id) = prefix.as_ref() {
                    if prefix_id.name() == module_id.name() {
                        if let Some(local_id) = direct_items.get(name) {
                            return Some(Path::pident(local_id.clone()));
                        }
                    }
                }
                rewrite_self_path(prefix, module_id, direct_items)
                    .map(|rewritten_prefix| Path::Pdot(Box::new(rewritten_prefix), name.clone(), *pos))
            }
            _ => None,
        }
    }

    fn rewrite_type(
        ty_ref: crate::types::TypeExprRef,
        module_id: &Ident,
        direct_items: &HashMap<String, Ident>,
        type_ctx: &crate::types::context::TypeContext<'_>,
        visited: &mut HashSet<crate::types::TypeExprRef>,
    ) {
        let ty_ref = type_ctx.repr(ty_ref);
        if !visited.insert(ty_ref) {
            return;
        }

        let desc = type_ctx.get_desc(ty_ref);
        match &*desc {
            TypeDesc::Tconstr { path, args, abbrev } => {
                for arg in args {
                    rewrite_type(*arg, module_id, direct_items, type_ctx, visited);
                }
                if let Some(rewritten) = rewrite_self_path(path, module_id, direct_items) {
                    type_ctx.set_desc(
                        ty_ref,
                        TypeDesc::Tconstr {
                            path: rewritten,
                            args: args.clone(),
                            abbrev: *abbrev,
                        },
                    );
                }
            }
            TypeDesc::Tarrow { arg, ret, .. } => {
                rewrite_type(arg.typ, module_id, direct_items, type_ctx, visited);
                rewrite_type(*ret, module_id, direct_items, type_ctx, visited);
            }
            TypeDesc::Ttuple(items) => {
                for item in items {
                    rewrite_type(*item, module_id, direct_items, type_ctx, visited);
                }
            }
            TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                rewrite_type(*target, module_id, direct_items, type_ctx, visited);
            }
            TypeDesc::Tpoly { body, vars } => {
                rewrite_type(*body, module_id, direct_items, type_ctx, visited);
                for var in vars {
                    rewrite_type(*var, module_id, direct_items, type_ctx, visited);
                }
            }
            TypeDesc::Tobject { fields, .. } => {
                rewrite_type(*fields, module_id, direct_items, type_ctx, visited);
            }
            TypeDesc::Tfield { typ, rest, .. } => {
                rewrite_type(*typ, module_id, direct_items, type_ctx, visited);
                rewrite_type(*rest, module_id, direct_items, type_ctx, visited);
            }
            TypeDesc::Tvariant(row0) => {
                let row = crate::types::btype::row_repr(type_ctx, row0);
                rewrite_type(row.row_more, module_id, direct_items, type_ctx, visited);
                for (_, field) in &row.row_fields {
                    match field {
                        RowField::Rpresent(Some(arg)) => {
                            rewrite_type(*arg, module_id, direct_items, type_ctx, visited);
                        }
                        RowField::Reither { types, .. } => {
                            for ty in types {
                                rewrite_type(*ty, module_id, direct_items, type_ctx, visited);
                            }
                        }
                        RowField::Rpresent(None) | RowField::Rabsent => {}
                    }
                }
            }
            TypeDesc::Tpackage { path, args, lids } => {
                for arg in args {
                    rewrite_type(*arg, module_id, direct_items, type_ctx, visited);
                }
                if let Some(rewritten) = rewrite_self_path(path, module_id, direct_items) {
                    type_ctx.set_desc(
                        ty_ref,
                        TypeDesc::Tpackage {
                            path: rewritten,
                            args: args.clone(),
                            lids: lids.clone(),
                        },
                    );
                }
            }
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
        }
    }

    fn rewrite_sig(
        sig: &[crate::types::decl::SignatureItem],
        module_id: &Ident,
        direct_items: &HashMap<String, Ident>,
        type_ctx: &crate::types::context::TypeContext<'_>,
    ) {
        let mut visited = HashSet::new();
        for item in sig {
            match item {
                SignatureItem::SigValue(_, desc) => {
                    rewrite_type(desc.val_type, module_id, direct_items, type_ctx, &mut visited);
                }
                SignatureItem::SigType(_, decl, _) => {
                    for param in &decl.type_params {
                        rewrite_type(*param, module_id, direct_items, type_ctx, &mut visited);
                    }
                    if let Some(manifest) = decl.type_manifest {
                        rewrite_type(manifest, module_id, direct_items, type_ctx, &mut visited);
                    }
                }
                SignatureItem::SigTypext(_, ext, _) => {
                    for param in &ext.ext_type_params {
                        rewrite_type(*param, module_id, direct_items, type_ctx, &mut visited);
                    }
                    if let Some(ret) = ext.ext_ret_type {
                        rewrite_type(ret, module_id, direct_items, type_ctx, &mut visited);
                    }
                }
                SignatureItem::SigModule(_, md, _) => {
                    if let crate::types::decl::ModuleType::MtySignature(sub_sig) = &md.md_type {
                        rewrite_sig(sub_sig, module_id, direct_items, type_ctx);
                    }
                }
                SignatureItem::SigModtype(_, _)
                | SignatureItem::SigClass
                | SignatureItem::SigClassType => {}
            }
        }
    }

    rewrite_sig(sig, module_id, &direct_items, type_ctx);
}

fn localize_exported_structure_module_type(
    mty: crate::types::decl::ModuleType,
    local_id: &Ident,
    env: Option<&Env>,
    type_ctx: Option<&crate::types::context::TypeContext<'_>>,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;

    let (path, env, type_ctx) = match (mty.clone(), env, type_ctx) {
        (DeclMty::MtyAlias(_, path), Some(env), Some(type_ctx))
        | (DeclMty::MtyIdent(path), Some(env), Some(type_ctx)) => (path, env, type_ctx),
        _ => return mty,
    };

    let mut no_persistent_env = None;
    let resolved_sig = crate::types::ctype::resolve_module_type_through_env(type_ctx, env, &path)
        .and_then(|resolved_mty| {
            resolve_mod_type_to_sig(&resolved_mty, Some(env), &mut no_persistent_env, type_ctx)
        })
        .or_else(|| {
            resolve_mod_type_to_sig(
                &DeclMty::MtyIdent(path.clone()),
                Some(env),
                &mut no_persistent_env,
                type_ctx,
            )
        });
    let Some(sig) = resolved_sig else {
        return mty;
    };

    let sig = crate::types::typecore::copy_lookup_signature_for_subst(&sig, type_ctx);
    crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
        &sig,
        &path,
        &Path::pident(local_id.clone()),
        type_ctx,
    );
    strip_self_module_prefix_in_sig(&sig, local_id, type_ctx);
    DeclMty::MtySignature(sig)
}

fn module_expr_contains_unpack_for_sig_localization(mod_expr: &ModuleExpr) -> bool {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(_, _) => false,
        ModuleExprDesc::Tmod_structure(structure) => structure.str_items.iter().any(|item| {
            match &item.str_desc {
                StructureItemDesc::Tstr_module(mb) => {
                    module_expr_contains_unpack_for_sig_localization(&mb.mb_expr)
                }
                StructureItemDesc::Tstr_recmodule(mbs) => mbs.iter().any(|mb| {
                    module_expr_contains_unpack_for_sig_localization(&mb.mb_expr)
                }),
                StructureItemDesc::Tstr_include(include) => {
                    module_expr_contains_unpack_for_sig_localization(&include.incl_mod)
                }
                _ => false,
            }
        }),
        ModuleExprDesc::Tmod_apply(functor, arg, _) => {
            module_expr_contains_unpack_for_sig_localization(functor)
                || module_expr_contains_unpack_for_sig_localization(arg)
        }
        ModuleExprDesc::Tmod_functor(_, _, _, body) => {
            module_expr_contains_unpack_for_sig_localization(body)
        }
        ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
            module_expr_contains_unpack_for_sig_localization(inner)
        }
        ModuleExprDesc::Tmod_unpack(_, _) => true,
    }
}

fn localize_raw_unpack_module_type_family(
    sig: &[crate::types::decl::SignatureItem],
    local_id: &Ident,
    type_ctx: &crate::types::context::TypeContext<'_>,
) {
    use crate::types::decl::SignatureItem;
    use crate::types::type_expr::TypeDesc;

    let mut rewrites = Vec::<(Path, Path)>::new();
    for item in sig {
        if let SignatureItem::SigType(id, decl, _) = item {
            let new_path = Path::pdot(Path::pident(local_id.clone()), id.name());
            if let Some(old_path) = decl.type_path.as_ref() {
                if !old_path.same(&new_path) {
                    rewrites.push((old_path.clone(), new_path.clone()));
                }
            }
            if let Some(manifest) = decl.type_manifest {
                let manifest = type_ctx.repr(manifest);
                let manifest_desc = type_ctx.get_desc(manifest);
                if let TypeDesc::Tconstr { path, args, .. } = &*manifest_desc {
                    if path.last() == id.name()
                        && args.len() == decl.type_params.len()
                        && !path.same(&new_path)
                    {
                        rewrites.push((path.clone(), new_path.clone()));
                    }
                }
            }
        }
    }

    rewrites.sort_by(|(left_old, left_new), (right_old, right_new)| {
        left_old
            .name()
            .cmp(&right_old.name())
            .then_with(|| left_new.name().cmp(&right_new.name()))
    });
    rewrites.dedup_by(|(left_old, left_new), (right_old, right_new)| {
        left_old.same(right_old) && left_new.same(right_new)
    });

    for (old_path, new_path) in rewrites {
        crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
            sig,
            &old_path,
            &new_path,
            type_ctx,
        );
    }
    strip_self_module_prefix_in_sig(sig, local_id, type_ctx);
}

fn localize_raw_unpack_modules_in_structure_sig(
    sig: &[crate::types::decl::SignatureItem],
    structure: &Structure,
    type_ctx: &crate::types::context::TypeContext<'_>,
) {
    use crate::types::decl::{ModuleType as DeclMty, SignatureItem};

    let mut sig_cursor = 0usize;
    for item in &structure.str_items {
        match &item.str_desc {
            StructureItemDesc::Tstr_module(mb) => {
                while sig_cursor < sig.len() {
                    let current_index = sig_cursor;
                    sig_cursor += 1;
                    let SignatureItem::SigModule(id, md, _) = &sig[current_index] else {
                        continue;
                    };
                    if id.name() != mb.mb_id.name() {
                        continue;
                    }
                    if let DeclMty::MtySignature(sub_sig) = &md.md_type {
                        if module_expr_contains_unpack_for_sig_localization(&mb.mb_expr) {
                            localize_raw_unpack_module_type_family(sub_sig, &mb.mb_id, type_ctx);
                        }
                        if let ModuleExprDesc::Tmod_structure(sub_structure) = &mb.mb_expr.mod_desc {
                            localize_raw_unpack_modules_in_structure_sig(
                                sub_sig,
                                sub_structure,
                                type_ctx,
                            );
                        }
                    }
                    break;
                }
            }
            StructureItemDesc::Tstr_recmodule(mbs) => {
                for mb in mbs {
                    while sig_cursor < sig.len() {
                        let current_index = sig_cursor;
                        sig_cursor += 1;
                        let SignatureItem::SigModule(id, md, _) = &sig[current_index] else {
                            continue;
                        };
                        if id.name() != mb.mb_id.name() {
                            continue;
                        }
                        if let DeclMty::MtySignature(sub_sig) = &md.md_type {
                            if module_expr_contains_unpack_for_sig_localization(&mb.mb_expr) {
                                localize_raw_unpack_module_type_family(
                                    sub_sig,
                                    &mb.mb_id,
                                    type_ctx,
                                );
                            }
                            if let ModuleExprDesc::Tmod_structure(sub_structure) =
                                &mb.mb_expr.mod_desc
                            {
                                localize_raw_unpack_modules_in_structure_sig(
                                    sub_sig,
                                    sub_structure,
                                    type_ctx,
                                );
                            }
                        }
                        break;
                    }
                }
            }
            _ => {}
        }
    }
}

fn extract_module_type_from_mod_expr_with_resolver<F>(
    mod_expr: &ModuleExpr,
    env: Option<&Env>,
    type_ctx: Option<&crate::types::context::TypeContext<'_>>,
    resolve_ident_sig: &mut F,
) -> Option<crate::types::decl::ModuleType>
where
    F: FnMut(&Located<LidentIdx>, Option<&Env>) -> Option<crate::types::decl::Signature>,
{
    thread_local! {
        static EXTRACT_MTY_DEBUG_DEPTH: Cell<usize> = const { Cell::new(0) };
    }

    struct ExtractMtyDebugGuard;
    impl Drop for ExtractMtyDebugGuard {
        fn drop(&mut self) {
            EXTRACT_MTY_DEBUG_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
        }
    }

    let _extract_mty_debug_guard = if std::env::var_os("RUST_DEBUG_EXTRACT_MTY_DEPTH").is_some() {
        EXTRACT_MTY_DEBUG_DEPTH.with(|depth| {
            let next = depth.get() + 1;
            depth.set(next);
            if next > 200 {
                let kind = match &mod_expr.mod_desc {
                    ModuleExprDesc::Tmod_ident(_, _) => "ident",
                    ModuleExprDesc::Tmod_structure(_) => "structure",
                    ModuleExprDesc::Tmod_apply(_, _, _) => "apply",
                    ModuleExprDesc::Tmod_functor(_, _, _, _) => "functor",
                    ModuleExprDesc::Tmod_constraint(_, _, _, _) => "constraint",
                    ModuleExprDesc::Tmod_unpack(_, _) => "unpack",
                };
                panic!("extract_module_type_from_mod_expr_with_resolver depth={} kind={}", next, kind);
            }
        });
        Some(ExtractMtyDebugGuard)
    } else {
        None
    };

    fn preserve_structure_module_alias(
        mod_expr: &ModuleExpr,
    ) -> Option<crate::types::decl::ModuleType> {
        use crate::types::decl::{AliasPresence, ModuleType as DeclMty};

        match &mod_expr.mod_desc {
            ModuleExprDesc::Tmod_ident(path, _) => {
                Some(DeclMty::MtyAlias(AliasPresence::MtaAbsent, path.clone()))
            }
            _ => None,
        }
    }

    use crate::types::decl::ModuleType as DeclMty;
    use crate::types::decl::SignatureItem as SigItem;
    use crate::types::decl::ValueDescription;

    fn resolve_modtype_to_sig_in_env(
        mty: &crate::types::decl::ModuleType,
        env: &Env,
    ) -> Option<crate::types::decl::Signature> {
        use crate::types::decl::ModuleType as DeclMty;
        fn anchored(owner_path: &Path, mty: &crate::types::decl::ModuleType) -> crate::types::decl::ModuleType {
            let mut mty = mty.clone();
            anchor_local_module_aliases_to_owner(&mut mty, owner_path);
            mty
        }

        fn resolve_path(
            path: &Path,
            env: &Env,
            visiting: &mut HashSet<Path>,
        ) -> Option<crate::types::decl::Signature> {
            use crate::types::decl::SignatureItem as SigItem;

            thread_local! {
                static EXTRACT_RESOLVE_PATH_DEBUG_DEPTH: Cell<usize> = const { Cell::new(0) };
            }

            struct ExtractResolvePathDebugGuard;
            impl Drop for ExtractResolvePathDebugGuard {
                fn drop(&mut self) {
                    EXTRACT_RESOLVE_PATH_DEBUG_DEPTH
                        .with(|depth| depth.set(depth.get().saturating_sub(1)));
                }
            }

            let _extract_resolve_path_debug_guard =
                if std::env::var_os("RUST_DEBUG_EXTRACT_RESOLVE_PATH_DEPTH").is_some() {
                    EXTRACT_RESOLVE_PATH_DEBUG_DEPTH.with(|depth| {
                        let next = depth.get() + 1;
                        depth.set(next);
                        if next > 200 {
                            panic!(
                                "extract resolve_path depth={} path={}",
                                next,
                                path.name()
                            );
                        }
                    });
                    Some(ExtractResolvePathDebugGuard)
                } else {
                    None
                };

            if !visiting.insert(path.clone()) {
                return None;
            }

            let result = match path {
                Path::Pident(id) => {
                    if let Ok(md) = env.lookup_module(&Path::pident(id.clone())) {
                        let anchored_mty = anchored(&Path::pident(id.clone()), &md.md_type);
                        if let Some(sig) = resolve_mty(&anchored_mty, env, visiting) {
                            return Some(sig);
                        }
                    }
                    if let Ok(mtd) = env.lookup_modtype(&Path::pident(id.clone())) {
                        if let Some(mty) = &mtd.mtd_type {
                            let anchored_mty = anchored(&Path::pident(id.clone()), mty);
                            return resolve_mty(&anchored_mty, env, visiting);
                        }
                    }
                    None
                }
                Path::Pdot(parent, name, _) => {
                    let parent_sig = resolve_path(parent, env, visiting)?;
                    let owner_path = Path::pdot((**parent).clone(), name);
                    parent_sig.iter().find_map(|item| match item {
                        SigItem::SigModule(id, md, _) if id.name() == name.as_str() => {
                            let anchored_mty = anchored(&owner_path, &md.md_type);
                            resolve_mty(&anchored_mty, env, visiting)
                        }
                        SigItem::SigModtype(id, mtd) if id.name() == name.as_str() => mtd
                            .mtd_type
                            .as_ref()
                            .and_then(|mty| {
                                let anchored_mty = anchored(&owner_path, mty);
                                resolve_mty(&anchored_mty, env, visiting)
                            }),
                        _ => None,
                    })
                }
                Path::Papply(_, _) => None,
            };

            visiting.remove(path);
            result
        }

        fn resolve_mty(
            mty: &crate::types::decl::ModuleType,
            env: &Env,
            visiting: &mut HashSet<Path>,
        ) -> Option<crate::types::decl::Signature> {
            match mty {
                DeclMty::MtySignature(sig) => Some(sig.clone()),
                DeclMty::MtyIdent(path) | DeclMty::MtyAlias(_, path) => {
                    resolve_path(path, env, visiting)
                }
                _ => None,
            }
        }

        let mut visiting = HashSet::new();
        resolve_mty(mty, env, &mut visiting)
    }

    fn resolve_module_type_path_in_env(
        path: &Path,
        env: &Env,
    ) -> Option<crate::types::decl::ModuleType> {
        use crate::types::decl::ModuleType as DeclMty;
        use crate::types::decl::SignatureItem as SigItem;

        fn anchored(owner_path: &Path, mty: &crate::types::decl::ModuleType) -> crate::types::decl::ModuleType {
            let mut mty = mty.clone();
            anchor_local_module_aliases_to_owner(&mut mty, owner_path);
            mty
        }

        match path {
            Path::Pident(id) => {
                if let Ok(md) = env.lookup_module(&Path::pident(id.clone())) {
                    return Some(anchored(&Path::pident(id.clone()), &md.md_type));
                }
                if let Ok(mtd) = env.lookup_modtype(&Path::pident(id.clone())) {
                    if let Some(mty) = &mtd.mtd_type {
                        return Some(anchored(&Path::pident(id.clone()), mty));
                    }
                }
                None
            }
            Path::Pdot(parent, name, _) => {
                let parent_mty = resolve_module_type_path_in_env(parent, env)?;
                let parent_sig = resolve_modtype_to_sig_in_env(&parent_mty, env)?;
                let owner_path = Path::pdot((**parent).clone(), name);
                for item in &parent_sig {
                    match item {
                        SigItem::SigModule(id, md, _) if id.name() == name.as_str() => {
                            return Some(anchored(&owner_path, &md.md_type));
                        }
                        SigItem::SigModtype(id, mtd) if id.name() == name.as_str() => {
                            if let Some(mty) = &mtd.mtd_type {
                                return Some(anchored(&owner_path, mty));
                            }
                        }
                        _ => {}
                    }
                }
                None
            }
            Path::Papply(_, _) => Some(DeclMty::MtyIdent(path.clone())),
        }
    }

    fn decl_module_type_from_typed_module_type(
        mty: &ModuleType,
    ) -> Option<crate::types::decl::ModuleType> {
        decl_module_type_from_typed(mty)
    }

    fn add_sig_item_to_env(item: &SigItem, env: &mut Env) {
        match item {
            SigItem::SigValue(id, desc) => env.add_value(id.clone(), desc.clone()),
            SigItem::SigType(id, decl, _) => env.add_type(id.clone(), decl.clone()),
            SigItem::SigModule(id, md, _) => env.add_module(id.clone(), md.clone()),
            SigItem::SigModtype(id, mtd) => env.add_modtype(id.clone(), mtd.clone()),
            _ => {}
        }
    }

    fn module_expr_contains_unpack(mod_expr: &ModuleExpr) -> bool {
        match &mod_expr.mod_desc {
            ModuleExprDesc::Tmod_ident(_, _) => false,
            ModuleExprDesc::Tmod_structure(structure) => structure.str_items.iter().any(|item| {
                match &item.str_desc {
                    StructureItemDesc::Tstr_module(mb) => module_expr_contains_unpack(&mb.mb_expr),
                    StructureItemDesc::Tstr_recmodule(mbs) => mbs
                        .iter()
                        .any(|mb| module_expr_contains_unpack(&mb.mb_expr)),
                    StructureItemDesc::Tstr_include(include) => {
                        module_expr_contains_unpack(&include.incl_mod)
                    }
                    _ => false,
                }
            }),
            ModuleExprDesc::Tmod_apply(functor, arg, _) => {
                module_expr_contains_unpack(functor) || module_expr_contains_unpack(arg)
            }
            ModuleExprDesc::Tmod_functor(_, _, _, body) => module_expr_contains_unpack(body),
            ModuleExprDesc::Tmod_constraint(inner, _, _, _) => module_expr_contains_unpack(inner),
            ModuleExprDesc::Tmod_unpack(_, _) => true,
        }
    }

    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(path, lid) => {
            if let Some(env) = env {
                if let Some(mty) = resolve_module_type_path_in_env(path, env) {
                    return Some(mty);
                }
            }
            if let Some(env) = env {
                if let Some(sig) =
                    resolve_modtype_to_sig_in_env(&DeclMty::MtyIdent(path.clone()), env)
                {
                    return Some(DeclMty::MtySignature(sig));
                }
            }
            if let Some(sig) = resolve_ident_sig(lid, env) {
                return Some(DeclMty::MtySignature(sig));
            }
            Some(DeclMty::MtyIdent(path.clone()))
        }
        ModuleExprDesc::Tmod_unpack(expr, mty) => {
            if let Some(decl_mty) = decl_module_type_from_typed_module_type(mty) {
                return Some(decl_mty);
            }
            let packed_mod = find_packed_typed_module_expr(expr)?;
            extract_module_type_from_mod_expr_with_resolver(
                packed_mod,
                env,
                type_ctx,
                resolve_ident_sig,
            )
        }
        ModuleExprDesc::Tmod_structure(structure) => {
            let has_include = structure
                .str_items
                .iter()
                .any(|item| matches!(item.str_desc, StructureItemDesc::Tstr_include(_)));
            let needs_precise_structure_sig = structure.str_items.iter().any(|item| match &item.str_desc {
                StructureItemDesc::Tstr_recmodule(_) => true,
                StructureItemDesc::Tstr_module(mb) => {
                    !matches!(mb.mb_expr.mod_desc, ModuleExprDesc::Tmod_ident(_, _))
                }
                _ => false,
            });
            if !has_include && needs_precise_structure_sig {
                let sig = structure.str_type.clone();
                if let Some(type_ctx) = type_ctx {
                    localize_raw_unpack_modules_in_structure_sig(&sig, structure, type_ctx);
                }
                return Some(DeclMty::MtySignature(sig));
            }

            let mut sig_items = Vec::new();
            let mut local_env = env.cloned();
            for item in &structure.str_items {
                let current_env_snapshot = local_env.clone();
                let current_env = current_env_snapshot.as_ref().or(env);
                match &item.str_desc {
                    StructureItemDesc::Tstr_value(_, bindings) => {
                        for vb in bindings {
                            extract_sig_values_from_pattern(
                                &vb.vb_pat,
                                vb.vb_pat.pat_type,
                                &mut sig_items,
                            );
                        }
                    }
                    StructureItemDesc::Tstr_primitive(vd) => {
                        let id = vd.val_id.clone();
                        let value_desc = ValueDescription {
                            val_type: vd.val_desc.ctyp_type,
                            val_kind: crate::types::decl::ValueKind::ValReg,
                            val_loc: crate::location::Location::none(),
                            val_attributes: vec![],
                            val_path: None,
                        };
                        sig_items.push(SigItem::SigValue(id.clone(), value_desc.clone()));
                        if let Some(env_mut) = local_env.as_mut() {
                            env_mut.add_value(id, value_desc);
                        }
                    }
                    StructureItemDesc::Tstr_module(mb) => {
                        let inner_mty = preserve_structure_module_alias(&mb.mb_expr)
                            .and_then(|mty| match (&mty, current_env, type_ctx) {
                                (DeclMty::MtyAlias(_, path), Some(env), Some(type_ctx)) => {
                                    crate::types::ctype::resolve_module_type_through_env(
                                        type_ctx,
                                        env,
                                        path,
                                    )
                                        .or_else(|| resolve_module_type_path_in_env(path, env))
                                        .and_then(|resolved_mty| match resolved_mty {
                                            DeclMty::MtySignature(sig) => Some(sig),
                                            other => resolve_modtype_to_sig_in_env(&other, env),
                                        })
                                        .or_else(|| {
                                            resolve_modtype_to_sig_in_env(
                                                &DeclMty::MtyIdent(path.clone()),
                                                env,
                                            )
                                        })
                                        .map(|sig| {
                                        let sig = crate::types::typecore::copy_lookup_signature_for_subst(
                                            &sig,
                                            type_ctx,
                                        );
                                        crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                                            &sig,
                                            path,
                                            &Path::pident(mb.mb_id.clone()),
                                            type_ctx,
                                        );
                                        strip_self_module_prefix_in_sig(&sig, &mb.mb_id, type_ctx);
                                        DeclMty::MtySignature(sig)
                                    })
                                }
                                _ => Some(mty),
                            })
                            .or_else(|| {
                                extract_module_type_from_mod_expr_with_resolver(
                                    &mb.mb_expr,
                                    current_env,
                                    type_ctx,
                                    resolve_ident_sig,
                                )
                            })
                            .unwrap_or(DeclMty::MtySignature(vec![]));
                        let inner_mty = localize_exported_structure_module_type(
                            inner_mty,
                            &mb.mb_id,
                            current_env,
                            type_ctx,
                        );
                        let module_decl = crate::types::decl::ModuleDeclaration {
                            md_type: inner_mty,
                            md_attributes: vec![],
                            md_loc: crate::location::Location::none(),
                            md_path: None,
                        };
                        sig_items.push(SigItem::SigModule(
                            mb.mb_id.clone(),
                            module_decl.clone(),
                            crate::types::decl::RecStatus::TrecNot,
                        ));
                        if let Some(env_mut) = local_env.as_mut() {
                            env_mut.add_module(mb.mb_id.clone(), module_decl);
                        }
                    }
                    StructureItemDesc::Tstr_recmodule(mbs) => {
                        for mb in mbs {
                            let inner_mty = preserve_structure_module_alias(&mb.mb_expr)
                                .and_then(|mty| match (&mty, current_env, type_ctx) {
                                    (DeclMty::MtyAlias(_, path), Some(env), Some(type_ctx)) => {
                                        crate::types::ctype::resolve_module_type_through_env(
                                            type_ctx,
                                            env,
                                            path,
                                        )
                                            .or_else(|| resolve_module_type_path_in_env(path, env))
                                            .and_then(|resolved_mty| match resolved_mty {
                                                DeclMty::MtySignature(sig) => Some(sig),
                                                other => resolve_modtype_to_sig_in_env(&other, env),
                                            })
                                            .or_else(|| {
                                                resolve_modtype_to_sig_in_env(
                                                    &DeclMty::MtyIdent(path.clone()),
                                                    env,
                                                )
                                            })
                                            .map(|sig| {
                                            let sig = crate::types::typecore::copy_lookup_signature_for_subst(
                                                &sig,
                                                type_ctx,
                                            );
                                            crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                                                &sig,
                                                path,
                                                &Path::pident(mb.mb_id.clone()),
                                                type_ctx,
                                            );
                                            strip_self_module_prefix_in_sig(
                                                &sig,
                                                &mb.mb_id,
                                                type_ctx,
                                            );
                                            DeclMty::MtySignature(sig)
                                        })
                                    }
                                    _ => Some(mty),
                                })
                                .or_else(|| {
                                    extract_module_type_from_mod_expr_with_resolver(
                                        &mb.mb_expr,
                                        current_env,
                                        type_ctx,
                                        resolve_ident_sig,
                                    )
                                })
                                .unwrap_or(DeclMty::MtySignature(vec![]));
                            let inner_mty = localize_exported_structure_module_type(
                                inner_mty,
                                &mb.mb_id,
                                current_env,
                                type_ctx,
                            );
                            let module_decl = crate::types::decl::ModuleDeclaration {
                                md_type: inner_mty,
                                md_attributes: vec![],
                                md_loc: crate::location::Location::none(),
                                md_path: None,
                            };
                            sig_items.push(SigItem::SigModule(
                                mb.mb_id.clone(),
                                module_decl.clone(),
                                crate::types::decl::RecStatus::TrecFirst,
                            ));
                            if let Some(env_mut) = local_env.as_mut() {
                                env_mut.add_module(mb.mb_id.clone(), module_decl);
                            }
                        }
                    }
                    StructureItemDesc::Tstr_type(rec_flag, decls) => {
                        let rec_status = match rec_flag {
                            crate::parser::ast::RecFlag::Recursive => {
                                crate::types::decl::RecStatus::TrecFirst
                            }
                            crate::parser::ast::RecFlag::Nonrecursive => {
                                crate::types::decl::RecStatus::TrecNot
                            }
                        };
                        for decl in decls {
                            sig_items.push(SigItem::SigType(
                                decl.typ_id.clone(),
                                decl.typ_type.clone(),
                                rec_status,
                            ));
                            if let Some(env_mut) = local_env.as_mut() {
                                env_mut.add_type(decl.typ_id.clone(), decl.typ_type.clone());
                            }
                        }
                    }
                    StructureItemDesc::Tstr_exception(ext_cstr) => {
                        sig_items.push(SigItem::SigTypext(
                            ext_cstr.ext_id.clone(),
                            ext_cstr.ext_type.clone(),
                            crate::types::decl::ExtStatus::TextException,
                        ));
                    }
                    StructureItemDesc::Tstr_typext(type_ext) => {
                        for ext_cstr in &type_ext.tyext_constructors {
                            sig_items.push(SigItem::SigTypext(
                                ext_cstr.ext_id.clone(),
                                ext_cstr.ext_type.clone(),
                                crate::types::decl::ExtStatus::TextFirst,
                            ));
                        }
                    }
                    StructureItemDesc::Tstr_modtype(mtd) => {
                        let modtype_decl = crate::types::decl::ModtypeDeclaration {
                            mtd_type: mtd
                                .mtd_type
                                .as_ref()
                                .and_then(decl_module_type_from_typed_module_type),
                            mtd_attributes: vec![],
                            mtd_loc: crate::location::Location::none(),
                        };
                        sig_items.push(SigItem::SigModtype(
                            mtd.mtd_id.clone(),
                            modtype_decl.clone(),
                        ));
                        if let Some(env_mut) = local_env.as_mut() {
                            env_mut.add_modtype(mtd.mtd_id.clone(), modtype_decl);
                        }
                    }
                    StructureItemDesc::Tstr_include(incl) => {
                        let debug_extract_include =
                            std::env::var_os("RUST_DEBUG_EXTRACT_INCLUDE").is_some();
                        if debug_extract_include {
                            let incl_desc = match &incl.incl_mod.mod_desc {
                                ModuleExprDesc::Tmod_ident(path, _) => {
                                    format!("ident:{}", path.name())
                                }
                                ModuleExprDesc::Tmod_structure(_) => "structure".to_string(),
                                ModuleExprDesc::Tmod_functor(..) => "functor".to_string(),
                                ModuleExprDesc::Tmod_apply(..) => "apply".to_string(),
                                ModuleExprDesc::Tmod_constraint(..) => "constraint".to_string(),
                                ModuleExprDesc::Tmod_unpack(..) => "unpack".to_string(),
                            };
                            eprintln!(
                                "[extract-include] start desc={} incl_type_len={}",
                                incl_desc,
                                incl.incl_type.len()
                            );
                            if let ModuleExprDesc::Tmod_ident(path, _) = &incl.incl_mod.mod_desc {
                                let env_has_module = current_env
                                    .is_some_and(|env| env.lookup_module(path).is_ok());
                                eprintln!(
                                    "[extract-include] env_present={} env_has_module={} path={}",
                                    current_env.is_some(),
                                    env_has_module,
                                    path.name()
                                );
                            }
                        }
                        let mut included = false;
                        if !incl.incl_type.is_empty() {
                            for sig_item in incl.incl_type.clone() {
                                if let Some(env_mut) = local_env.as_mut() {
                                    add_sig_item_to_env(&sig_item, env_mut);
                                }
                                sig_items.push(sig_item);
                            }
                            included = true;
                        }
                        if !included {
                            if let Some(inner_mty) = extract_module_type_from_mod_expr_with_resolver(
                                &incl.incl_mod,
                                current_env,
                                type_ctx,
                                resolve_ident_sig,
                            ) {
                                if debug_extract_include {
                                    let kind = match &inner_mty {
                                        DeclMty::MtySignature(_) => "signature",
                                        DeclMty::MtyIdent(path) => {
                                            eprintln!("[extract-include] inner_mty=ident:{}", path.name());
                                            if let Some(env) = current_env {
                                                eprintln!(
                                                    "[extract-include] lookup_modtype({})={}",
                                                    path.name(),
                                                    env.lookup_modtype(path).is_ok()
                                                );
                                            }
                                            "ident"
                                        }
                                        DeclMty::MtyAlias(_, path) => {
                                            eprintln!("[extract-include] inner_mty=alias:{}", path.name());
                                            "alias"
                                        }
                                        DeclMty::MtyFunctor { .. } => "functor",
                                    };
                                    eprintln!("[extract-include] inner_mty_kind={}", kind);
                                }
                                let inner_sig_opt = match inner_mty {
                                    DeclMty::MtySignature(inner_sig) => Some(inner_sig),
                                    other => current_env
                                        .and_then(|env| resolve_modtype_to_sig_in_env(&other, env))
                                        .or_else(|| match &other {
                                            DeclMty::MtyIdent(path) | DeclMty::MtyAlias(_, path) => {
                                                let name = path.last();
                                                sig_items.iter().rev().find_map(|item| match item {
                                                    SigItem::SigModtype(id, mtd)
                                                        if id.name() == name =>
                                                    {
                                                        mtd.mtd_type.as_ref().and_then(|mty| match mty {
                                                            DeclMty::MtySignature(sig) => Some(sig.clone()),
                                                            other_mty => current_env.and_then(|env| {
                                                                resolve_modtype_to_sig_in_env(
                                                                    other_mty,
                                                                    env,
                                                                )
                                                            }),
                                                        })
                                                    }
                                                    _ => None,
                                                })
                                            }
                                            _ => None,
                                        }),
                                };
                                if let Some(inner_sig) = inner_sig_opt {
                                    if debug_extract_include {
                                        let items = inner_sig
                                            .iter()
                                            .map(|item| match item {
                                                SigItem::SigValue(id, _) => format!("val:{}", id.name()),
                                                SigItem::SigType(id, _, _) => format!("type:{}", id.name()),
                                                SigItem::SigModule(id, _, _) => format!("module:{}", id.name()),
                                                SigItem::SigModtype(id, _) => format!("modtype:{}", id.name()),
                                                SigItem::SigTypext(id, _, _) => format!("ext:{}", id.name()),
                                                SigItem::SigClass => "class".to_string(),
                                                SigItem::SigClassType => "class_type".to_string(),
                                            })
                                            .collect::<Vec<_>>()
                                            .join(", ");
                                        eprintln!(
                                            "[extract-include] resolved inner_sig items=[{}]",
                                            items
                                        );
                                    }
                                    for sig_item in inner_sig {
                                        if let Some(env_mut) = local_env.as_mut() {
                                            add_sig_item_to_env(&sig_item, env_mut);
                                        }
                                        sig_items.push(sig_item);
                                    }
                                    included = true;
                                }
                            }
                        }
                        if !included {
                            if let ModuleExprDesc::Tmod_ident(_, lid) = &incl.incl_mod.mod_desc {
                                if let Some(inner_sig) = resolve_ident_sig(lid, current_env) {
                                    if debug_extract_include {
                                        let items = inner_sig
                                            .iter()
                                            .map(|item| match item {
                                                SigItem::SigValue(id, _) => format!("val:{}", id.name()),
                                                SigItem::SigType(id, _, _) => format!("type:{}", id.name()),
                                                SigItem::SigModule(id, _, _) => format!("module:{}", id.name()),
                                                SigItem::SigModtype(id, _) => format!("modtype:{}", id.name()),
                                                SigItem::SigTypext(id, _, _) => format!("ext:{}", id.name()),
                                                SigItem::SigClass => "class".to_string(),
                                                SigItem::SigClassType => "class_type".to_string(),
                                            })
                                            .collect::<Vec<_>>()
                                            .join(", ");
                                        eprintln!(
                                            "[extract-include] resolve_ident_sig items=[{}]",
                                            items
                                        );
                                    }
                                    for sig_item in inner_sig {
                                        if let Some(env_mut) = local_env.as_mut() {
                                            add_sig_item_to_env(&sig_item, env_mut);
                                        }
                                        sig_items.push(sig_item);
                                    }
                                    included = true;
                                }
                            }
                        }
                        if !included {
                            if let ModuleExprDesc::Tmod_ident(path, _) = &incl.incl_mod.mod_desc {
                                let mod_name = match path {
                                    crate::types::Path::Pident(id) => Some(id.name().to_string()),
                                    crate::types::Path::Pdot(_, name, _) => Some(name.clone()),
                                    _ => None,
                                };
                                if let Some(mod_name) = mod_name {
                                    let found_sig: Option<Vec<SigItem>> = sig_items.iter().find_map(|si| {
                                        if let SigItem::SigModule(id, md, _) = si {
                                            if id.name() == mod_name.as_str() {
                                                return match &md.md_type {
                                                    DeclMty::MtySignature(inner) => Some(inner.clone()),
                                                    other => current_env.and_then(|env| {
                                                        resolve_modtype_to_sig_in_env(other, env)
                                                    }),
                                                };
                                            }
                                        }
                                        None
                                    });
                                    if let Some(inner_sig) = found_sig {
                                        if debug_extract_include {
                                            let items = inner_sig
                                                .iter()
                                                .map(|item| match item {
                                                    SigItem::SigValue(id, _) => format!("val:{}", id.name()),
                                                    SigItem::SigType(id, _, _) => format!("type:{}", id.name()),
                                                    SigItem::SigModule(id, _, _) => format!("module:{}", id.name()),
                                                    SigItem::SigModtype(id, _) => format!("modtype:{}", id.name()),
                                                    SigItem::SigTypext(id, _, _) => format!("ext:{}", id.name()),
                                                    SigItem::SigClass => "class".to_string(),
                                                    SigItem::SigClassType => "class_type".to_string(),
                                                })
                                                .collect::<Vec<_>>()
                                                .join(", ");
                                            eprintln!(
                                                "[extract-include] found_sig items=[{}]",
                                                items
                                            );
                                        }
                                        for sig_item in inner_sig {
                                            if let Some(env_mut) = local_env.as_mut() {
                                                add_sig_item_to_env(&sig_item, env_mut);
                                            }
                                            sig_items.push(sig_item);
                                        }
                                        included = true;
                                    }
                                }
                                if !included {
                                    if let Some(env) = current_env {
                                        if let Some(inner_sig) = resolve_modtype_to_sig_in_env(
                                            &DeclMty::MtyIdent(path.clone()),
                                            env,
                                        ) {
                                            if debug_extract_include {
                                                let items = inner_sig
                                                    .iter()
                                                    .map(|item| match item {
                                                        SigItem::SigValue(id, _) => format!("val:{}", id.name()),
                                                        SigItem::SigType(id, _, _) => format!("type:{}", id.name()),
                                                        SigItem::SigModule(id, _, _) => format!("module:{}", id.name()),
                                                        SigItem::SigModtype(id, _) => format!("modtype:{}", id.name()),
                                                        SigItem::SigTypext(id, _, _) => format!("ext:{}", id.name()),
                                                        SigItem::SigClass => "class".to_string(),
                                                        SigItem::SigClassType => "class_type".to_string(),
                                                    })
                                                    .collect::<Vec<_>>()
                                                    .join(", ");
                                                eprintln!(
                                                    "[extract-include] resolve_modtype_to_sig items=[{}]",
                                                    items
                                                );
                                            }
                                            for sig_item in inner_sig {
                                                if let Some(env_mut) = local_env.as_mut() {
                                                    add_sig_item_to_env(&sig_item, env_mut);
                                                }
                                                sig_items.push(sig_item);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if debug_extract_include {
                            eprintln!("[extract-include] end included={}", included);
                        }
                    }
                    _ => {}
                }
            }
            Some(DeclMty::MtySignature(sig_items))
        }
        ModuleExprDesc::Tmod_functor(param_id, _name, param_mty, body) => {
            let decl_param_mty = param_mty
                .as_deref()
                .and_then(decl_module_type_from_typed_module_type);

            let body_env_storage: Option<Env>;
            let body_env = if let Some(parent_env) = env {
                let mut extended = parent_env.clone();
                if let Some(ref param_decl) = decl_param_mty {
                    extended.add_module(
                        param_id.clone(),
                        crate::types::decl::ModuleDeclaration {
                            md_type: param_decl.clone(),
                            md_attributes: vec![],
                            md_loc: crate::location::Location::none(),
                            md_path: None,
                        },
                    );
                }
                body_env_storage = Some(extended);
                body_env_storage.as_ref()
            } else {
                None
            };

            let result_mty = extract_module_type_from_mod_expr_with_resolver(
                body,
                body_env,
                type_ctx,
                resolve_ident_sig,
            )?;
            Some(DeclMty::MtyFunctor {
                param: param_id.clone(),
                param_type: decl_param_mty.map(Box::new),
                result: Box::new(result_mty),
            })
        }
        ModuleExprDesc::Tmod_apply(functor, _arg, _) => {
            let extracted_functor_mty =
                extract_module_type_from_mod_expr_with_resolver(
                    functor,
                    env,
                    type_ctx,
                    resolve_ident_sig,
                );
            if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                let functor_desc = match &functor.mod_desc {
                    ModuleExprDesc::Tmod_ident(_, _) => "ident",
                    ModuleExprDesc::Tmod_structure(_) => "structure",
                    ModuleExprDesc::Tmod_functor(_, _, _, _) => "functor",
                    ModuleExprDesc::Tmod_apply(_, _, _) => "apply",
                    ModuleExprDesc::Tmod_constraint(_, _, _, _) => "constraint",
                    ModuleExprDesc::Tmod_unpack(_, _) => "unpack",
                };
                let extracted_kind = match extracted_functor_mty.as_ref() {
                    Some(DeclMty::MtySignature(_)) => "mty-signature",
                    Some(DeclMty::MtyFunctor { .. }) => "mty-functor",
                    Some(DeclMty::MtyIdent(_)) => "mty-ident",
                    Some(DeclMty::MtyAlias(_, _)) => "mty-alias",
                    None => "none",
                };
                eprintln!(
                    "[extract-apply] functor_desc={} extracted_functor_mty={}",
                    functor_desc, extracted_kind
                );
            }
            if let Some(functor_mty) = extracted_functor_mty {
                let resolved_functor_mty = match &functor_mty {
                    DeclMty::MtyIdent(path) | DeclMty::MtyAlias(_, path) => env
                        .and_then(|env| resolve_module_type_path_in_env(path, env))
                        .unwrap_or(functor_mty),
                    _ => functor_mty,
                };
                if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                    let resolved_kind = match &resolved_functor_mty {
                        DeclMty::MtySignature(_) => "mty-signature",
                        DeclMty::MtyFunctor { .. } => "mty-functor",
                        DeclMty::MtyIdent(_) => "mty-ident",
                        DeclMty::MtyAlias(_, _) => "mty-alias",
                    };
                    eprintln!("[extract-apply] resolved_functor_mty={}", resolved_kind);
                }
                if let DeclMty::MtyFunctor { result, .. } = resolved_functor_mty {
                    return Some(*result);
                }
            }
            if let (Some(env), ModuleExprDesc::Tmod_ident(path, _)) = (env, &functor.mod_desc) {
                if let Ok(md) = env.lookup_module(path) {
                    if let DeclMty::MtyFunctor { result, .. } = &md.md_type {
                        return Some((**result).clone());
                    }
                }
            }
            // Fallback: rely on the typed module expression's inferred module type.
            // This preserves include signature extraction for functor applications
            // whose functor shape cannot be reconstructed from nested expressions.
            decl_module_type_from_typed_module_type(&mod_expr.mod_type)
        }
        ModuleExprDesc::Tmod_constraint(inner, constrained_mty, modtype_constraint, _) => {
            // OCaml keeps the constrained module type as the semantic type
            // exposed by a constrained module expression.
            let constrained = match modtype_constraint {
                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(mty) => {
                    decl_module_type_from_typed_module_type(mty)
                }
                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit => {
                    decl_module_type_from_typed_module_type(constrained_mty)
                }
            };
            constrained.or_else(|| {
                extract_module_type_from_mod_expr_with_resolver(
                    inner,
                    env,
                    type_ctx,
                    resolve_ident_sig,
                )
            })
        }
    }
}

// ============================================================================
// Module Expression Type Checking
// ============================================================================

fn type_module_expr_with_alias<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
    alias: bool,
) -> TypeModResult<ModuleExpr> {
    let loc = mod_expr.pmod_loc;

    match &*mod_expr.pmod_desc {
        ParsedModuleExprDesc::Pmod_ident(lid) => {
            // Module identifier: M
            // Look up the module path in the environment
            let longident = tctx.resolve_lid(lid.txt).clone();
            let path = lookup_module_path_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or_else(|| path_from_longident(&longident, |idx| arena.get_string(idx)));
            let mod_type = lookup_module_type_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            );

            let ident_mod = ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_ident(path, lid.clone()),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            };

            if !alias
                && matches!(
                    mod_type,
                    Some(crate::types::decl::ModuleType::MtyAlias(_, _))
                )
            {
                Ok(ModuleExpr {
                    mod_desc: ModuleExprDesc::Tmod_constraint(
                        Box::new(ident_mod),
                        ModuleType::placeholder(),
                        crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
                        ModuleCoercion::Tcoerce_none,
                    ),
                    mod_loc: loc,
                    mod_type: ModuleType::placeholder(),
                    mod_env: EnvRef(0),
                    mod_attributes: mod_expr.pmod_attributes.clone(),
                })
            } else {
                Ok(ident_mod)
            }
        }

        ParsedModuleExprDesc::Pmod_structure(items) => {
            // Module structure: { ... }
            let (structure, new_env) = type_structure(tctx, env, arena, items)?;

            // Like OCaml: if simplify_signature would shrink the signature
            // (duplicate value names), wrap in Tmod_constraint implicit
            let needs_constraint = structure_has_duplicate_value_names(&structure, env, &new_env);

            let md = ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_structure(structure),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: Attributes::new(),
            };

            if needs_constraint {
                Ok(ModuleExpr {
                    mod_desc: ModuleExprDesc::Tmod_constraint(
                        Box::new(md),
                        ModuleType::placeholder(),
                        crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
                        ModuleCoercion::Tcoerce_none,
                    ),
                    mod_loc: loc,
                    mod_type: ModuleType::placeholder(),
                    mod_env: EnvRef(0),
                    mod_attributes: mod_expr.pmod_attributes.clone(),
                })
            } else {
                Ok(ModuleExpr {
                    mod_desc: md.mod_desc,
                    mod_loc: loc,
                    mod_type: ModuleType::placeholder(),
                    mod_env: EnvRef(0),
                    mod_attributes: mod_expr.pmod_attributes.clone(),
                })
            }
        }

        ParsedModuleExprDesc::Pmod_functor(inner) => {
            let (ref name, ref param_type, ref body_idx) = **inner;
            // Functor: (X: S) => ME
            let param_name = arena.get_string(name.txt).to_string();
            let param_id = Ident::create_local(&param_name);

            // Translate parameter type and extend environment with the functor parameter
            let typed_param_type = match param_type {
                Some(pt) => Some(Box::new(transl_modtype(tctx, env, arena, arena.get_mod_type(*pt))?)),
                None => None,
            };

            // Extend environment with the functor parameter module
            let mut functor_env = env.clone();
            if let Some(pt) = param_type {
                if let Ok(param_decl_type) = translate_module_type_to_decl(tctx, env, arena, arena.get_mod_type(*pt)) {
                    functor_env.add_module(
                        param_id.clone(),
                        crate::types::decl::ModuleDeclaration {
                            md_type: param_decl_type,
                            md_attributes: vec![],
                            md_loc: crate::location::Location::none(),
                            md_path: None,
                        },
                    );
                }
            }

            // OCaml typemod.ml calls Ctype.init_def(Ident.current_time()) before
            // typing functor bodies.
            let ctx = tctx.type_ctx;
            ctx.init_def(ctx.current_stamp());

            // Type check the functor body with the extended environment
            let body = arena.get_mod_expr(*body_idx);
            let typed_body = type_module_expr_with_alias(tctx, &functor_env, arena, body, false)?;

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_functor(
                    param_id,
                    Located {
                        txt: param_name,
                        loc: name.loc,
                    },
                    typed_param_type,
                    Box::new(typed_body),
                ),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_apply(functor_idx, arg_idx) => {
            // Functor application: F(M)
            let functor = arena.get_mod_expr(*functor_idx);
            let arg = arena.get_mod_expr(*arg_idx);
            let typed_functor = type_module_expr_with_alias(tctx, env, arena, functor, false)?;
            if std::env::var_os("RUST_DEBUG_FUNCTOR_APPLY_PROGRESS").is_some() {
                eprintln!("[functor-apply] typed_functor");
            }
            let typed_arg = type_module_expr_with_alias(tctx, env, arena, arg, false)?;
            if std::env::var_os("RUST_DEBUG_FUNCTOR_APPLY_PROGRESS").is_some() {
                eprintln!("[functor-apply] typed_arg");
                let desc = match &typed_arg.mod_desc {
                    ModuleExprDesc::Tmod_ident(_, _) => "ident",
                    ModuleExprDesc::Tmod_structure(_) => "structure",
                    ModuleExprDesc::Tmod_functor(_, _, _, _) => "functor",
                    ModuleExprDesc::Tmod_apply(_, _, _) => "apply",
                    ModuleExprDesc::Tmod_constraint(_, _, _, _) => "constraint",
                    ModuleExprDesc::Tmod_unpack(_, _) => "unpack",
                };
                eprintln!("[functor-apply] typed_arg_desc={}", desc);
            }

            let extracted_arg_mty = extract_module_type_from_mod_expr_with_ctx(
                &typed_arg,
                Some(env),
                tctx.type_ctx,
            );
            if std::env::var_os("RUST_DEBUG_FUNCTOR_APPLY_PROGRESS").is_some() {
                eprintln!(
                    "[functor-apply] extracted_arg_mty={}",
                    if extracted_arg_mty.is_some() { "some" } else { "none" }
                );
            }
            let arg_mty = extracted_arg_mty
                .or_else(|| decl_module_type_from_typed_module_expr_for_sig(&typed_arg))
                .ok_or_else(|| {
                    TypeModError::FunctorApplicationError(
                        "could not extract functor argument module type".to_string(),
                    )
                })?;
            if std::env::var_os("RUST_DEBUG_FUNCTOR_APPLY_PROGRESS").is_some() {
                let kind = match &arg_mty {
                    crate::types::decl::ModuleType::MtySignature(_) => "mty-signature",
                    crate::types::decl::ModuleType::MtyFunctor { .. } => "mty-functor",
                    crate::types::decl::ModuleType::MtyIdent(_) => "mty-ident",
                    crate::types::decl::ModuleType::MtyAlias(_, _) => "mty-alias",
                };
                eprintln!("[functor-apply] arg_mty={}", kind);
            }

            let functor_mty = extract_module_type_from_mod_expr_with_ctx(
                &typed_functor,
                Some(env),
                tctx.type_ctx,
            )
                .or_else(|| lookup_module_type_from_parsed_module_expr(tctx, env, arena, functor))
                .ok_or_else(|| {
                    TypeModError::FunctorApplicationError(
                        "could not extract functor module type".to_string(),
                    )
                })?;
            if std::env::var_os("RUST_DEBUG_FUNCTOR_APPLY_PROGRESS").is_some() {
                let kind = match &functor_mty {
                    crate::types::decl::ModuleType::MtySignature(_) => "mty-signature",
                    crate::types::decl::ModuleType::MtyFunctor { .. } => "mty-functor",
                    crate::types::decl::ModuleType::MtyIdent(_) => "mty-ident",
                    crate::types::decl::ModuleType::MtyAlias(_, _) => "mty-alias",
                };
                eprintln!("[functor-apply] functor_mty={}", kind);
            }

            let functor_mty = scrape_alias_module_type(
                &functor_mty,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or(functor_mty);
            if std::env::var_os("RUST_DEBUG_FUNCTOR_APPLY_PROGRESS").is_some() {
                let kind = match &functor_mty {
                    crate::types::decl::ModuleType::MtySignature(_) => "mty-signature",
                    crate::types::decl::ModuleType::MtyFunctor { .. } => "mty-functor",
                    crate::types::decl::ModuleType::MtyIdent(_) => "mty-ident",
                    crate::types::decl::ModuleType::MtyAlias(_, _) => "mty-alias",
                };
                eprintln!("[functor-apply] scraped_functor_mty={}", kind);
            }

            let coercion = match functor_mty {
                crate::types::decl::ModuleType::MtyFunctor { param_type, .. } => {
                    let param_mty = param_type.map(|inner| *inner).unwrap_or_else(|| {
                        crate::types::decl::ModuleType::MtySignature(vec![])
                    });
                    crate::types::includemod::modtypes(tctx.type_ctx, env, &arg_mty, &param_mty)
                        .map_err(|err| {
                            TypeModError::FunctorApplicationError(format!(
                                "functor argument mismatch: {:?}",
                                err
                            ))
                        })?
                }
                _ => {
                    return Err(TypeModError::FunctorApplicationError(
                        "applied module is not a functor".to_string(),
                    ));
                }
            };
            if std::env::var_os("RUST_DEBUG_FUNCTOR_APPLY_PROGRESS").is_some() {
                eprintln!("[functor-apply] coercion");
            }

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_apply(
                    Box::new(typed_functor),
                    Box::new(typed_arg),
                    coercion,
                ),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_constraint(mod_expr_inner_idx, mod_type_idx) => {
            // Constrained module: (ME: MT)
            let mod_expr_inner = arena.get_mod_expr(*mod_expr_inner_idx);
            let typed_mod = type_module_expr_with_alias(tctx, env, arena, mod_expr_inner, alias)?;
            let typed_mty = transl_modtype(tctx, env, arena, arena.get_mod_type(*mod_type_idx))?;

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_constraint(
                    Box::new(typed_mod),
                    typed_mty.clone(),
                    crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(Box::new(
                        typed_mty,
                    )),
                    ModuleCoercion::Tcoerce_none,
                ),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_unpack(expr_idx) => {
            // Unpack: unpack(E)
            let expr = arena.get_expr(*expr_idx);
            let typed_expr = type_expression(tctx, env, expr)?;
            let expanded =
                crate::types::ctype::expand_head(tctx.type_ctx, env, typed_expr.exp_type);
            let unpack_mty = match &*tctx.type_ctx.get_desc(tctx.type_ctx.repr(expanded)) {
                crate::types::type_expr::TypeDesc::Tpackage { path, .. } => ModuleType {
                    mty_desc: crate::types::typedtree::ModuleTypeDesc::Tmty_ident(
                        path.clone(),
                        arena.placeholder_located(loc),
                    ),
                    mty_loc: loc,
                    mty_attributes: Attributes::new(),
                },
                crate::types::type_expr::TypeDesc::Tvar(_)
                | crate::types::type_expr::TypeDesc::Tunivar(_) => {
                    return Err(TypeModError::CoreError(TypeCoreError::CannotInferSignature));
                }
                _ => {
                    return Err(TypeModError::CoreError(TypeCoreError::NotAPackedModule(
                        expanded,
                    )));
                }
            };

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_unpack(typed_expr, unpack_mty.clone()),
                mod_loc: loc,
                mod_type: unpack_mty,
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_extension(_ext) => {
            // Extension: [%id]
            // Extensions are typically handled by preprocessors
            let placeholder_lid = arena.placeholder_located(loc);
            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_ident(
                    Path::pident(Ident::create_local("extension")),
                    placeholder_lid,
                ),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }
    }
}

/// Type check a module expression.
pub fn type_module_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
) -> TypeModResult<ModuleExpr> {
    type_module_expr_with_alias(tctx, env, arena, mod_expr, false)
}

/// Type check a module expression with explicit alias-preservation mode.
pub fn type_module_expr_with_alias_mode<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
    alias: bool,
) -> TypeModResult<ModuleExpr> {
    type_module_expr_with_alias(tctx, env, arena, mod_expr, alias)
}

/// Match OCaml `type_module_type_of` behavior for `module type of`.
///
/// OCaml special-cases `Pmod_ident` to avoid the regular `type_module` path,
/// which can wrap aliases in an implicit `Tmod_constraint`.
/// See `compiler/ml/typemod.ml` (`type_module_type_of`).
fn type_module_type_of_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
) -> TypeModResult<ModuleExpr> {
    match &*mod_expr.pmod_desc {
        ParsedModuleExprDesc::Pmod_ident(lid) => {
            let longident = tctx.resolve_lid(lid.txt).clone();
            let path = lookup_module_path_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or_else(|| path_from_longident(&longident, |idx| arena.get_string(idx)));

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_ident(path, lid.clone()),
                mod_loc: mod_expr.pmod_loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }
        _ => type_module_expr(tctx, env, arena, mod_expr),
    }
}

// ============================================================================
// Module Type Translation
// ============================================================================

/// Translate a parsed module type to a typed module type.
/// This creates the structural tree needed for sexp output.
fn transl_modtype<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    smty: &crate::parser::ast::ModuleType,
) -> TypeModResult<crate::types::typedtree::ModuleType> {
    use crate::parser::ast::ModuleTypeDesc as PMtyDesc;
    use crate::types::typedtree::{ModuleType as TMty, ModuleTypeDesc as TMtyDesc};

    let loc = smty.pmty_loc;
    let attrs = smty.pmty_attributes.clone();

    let desc = match &*smty.pmty_desc {
        PMtyDesc::Pmty_ident(lid) => {
            let longident = tctx.resolve_lid(lid.txt).clone();
            let path = lookup_modtype_path_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or_else(|| path_from_longident(&longident, |idx| arena.get_string(idx)));
            TMtyDesc::Tmty_ident(path, lid.clone())
        }
        PMtyDesc::Pmty_signature(sig_items) => {
            let typed_sig = transl_signature(tctx, env, arena, sig_items)?;
            TMtyDesc::Tmty_signature(typed_sig)
        }
        PMtyDesc::Pmty_functor(inner) => {
            let (ref name, ref param_type, ref result_type_idx) = **inner;
            let param_id = Ident::create_local(arena.get_string(name.txt));
            let typed_param = match param_type {
                Some(pt) => Some(Box::new(transl_modtype(tctx, env, arena, arena.get_mod_type(*pt))?)),
                None => None,
            };
            let param_decl = match param_type {
                Some(pt) => Some(translate_module_type_to_decl(
                    tctx,
                    env,
                    arena,
                    arena.get_mod_type(*pt),
                )?),
                None => None,
            };
            let mut result_env = env.clone();
            result_env.add_module(
                param_id.clone(),
                crate::types::decl::ModuleDeclaration {
                    md_type: param_decl
                        .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![])),
                    md_attributes: vec![],
                    md_loc: crate::location::Location::none(),
                    md_path: None,
                },
            );
            let ctx = tctx.type_ctx;
            ctx.init_def(ctx.current_stamp());
            let result_type = arena.get_mod_type(*result_type_idx);
            let typed_result = transl_modtype(tctx, &result_env, arena, result_type)?;
            TMtyDesc::Tmty_functor(
                param_id,
                Located {
                    txt: arena.get_string(name.txt).to_string(),
                    loc: name.loc,
                },
                typed_param,
                Box::new(typed_result),
            )
        }
        PMtyDesc::Pmty_with(inner) => {
            let (ref body_idx, ref constraints) = **inner;
            let body = arena.get_mod_type(*body_idx);
            let typed_body = transl_modtype(tctx, env, arena, body)?;
            let typed_constraints = transl_with_constraints(tctx, env, arena, constraints)?;
            TMtyDesc::Tmty_with(Box::new(typed_body), typed_constraints)
        }
        PMtyDesc::Pmty_typeof(me_idx) => {
            let me = arena.get_mod_expr(*me_idx);
            let typed_me = type_module_type_of_expr(tctx, env, arena, me)?;
            TMtyDesc::Tmty_typeof(Box::new(typed_me))
        }
        PMtyDesc::Pmty_alias(lid) => {
            let longident = tctx.resolve_lid(lid.txt).clone();
            let path = lookup_module_path_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or_else(|| path_from_longident(&longident, |idx| arena.get_string(idx)));
            TMtyDesc::Tmty_alias(path, lid.clone())
        }
        PMtyDesc::Pmty_extension(_) => TMtyDesc::Tmty_placeholder,
    };

    Ok(TMty {
        mty_desc: desc,
        mty_loc: loc,
        mty_attributes: attrs,
    })
}

/// Translate a parsed signature into a typed signature.
pub fn transl_signature<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    items: &[crate::parser::ast::SignatureItem],
) -> TypeModResult<crate::types::typedtree::TypedSignature> {
    use crate::parser::ast::SignatureItemDesc as PSigDesc;
    use crate::types::typedtree::{
        EnvRef, TypedModuleDeclaration, TypedSignatureItem, TypedSignatureItemDesc as TSigDesc,
    };

    let mut typed_items = Vec::new();
    // Thread environment through the loop so Psig_open extends it
    // for subsequent items (matching OCaml's transl_signature behavior).
    let mut sig_env = env.clone();

    for item in items {
        let ctx = tctx.type_ctx;
        ctx.init_def(ctx.current_stamp());
        let loc = item.psig_loc;
        let desc = match &*item.psig_desc {
            PSigDesc::Psig_value(vd) => {
                let name_str = arena.get_string(vd.pval_name.txt).to_string();
                let id = Ident::create_local(&name_str);
                // Use transl_type_scheme pattern: begin_def/end_def/generalize
                // OCaml: reset_type_variables() for each val declaration
                tctx.type_variables.clear();
                let ctx = tctx.type_ctx;
                ctx.begin_def();
                let (typed_ctype, val_ty) = transl_type(tctx, &sig_env, arena.get_core_type(vd.pval_type))?;
                ctx.end_def();
                crate::types::ctype::generalize(ctx, val_ty);
                // Keep signature value declaration abbreviation memo side effects
                // aligned with OCaml transl_value_decl.
                if std::env::var_os("RUST_SKIP_SIG_VALUE_EXPAND_HEAD").is_none() {
                    crate::types::ctype::expand_head(ctx, &sig_env, val_ty);
                }
                // For primitives, we need the pval_prim as Vec<String> for the typed tree
                let val_prim: Vec<String> = vd
                    .pval_prim
                    .iter()
                    .map(|s| arena.get_string(*s).to_string())
                    .collect();
                TSigDesc::Tsig_value(crate::types::typedtree::TypedValueDescription {
                    val_id: id,
                    val_name: Located {
                        txt: name_str,
                        loc: vd.pval_name.loc,
                    },
                    val_desc: typed_ctype,
                    val_prim,
                    val_loc: vd.pval_loc,
                    val_attributes: vd.pval_attributes.clone(),
                })
            }
            PSigDesc::Psig_type(inner) => {
                let (ref rec_flag, ref decls) = **inner;
                let typed_decls = transl_sig_type_declarations(tctx, &sig_env, arena, decls)?;
                // Add types to sig_env so subsequent items see them.
                // This ensures locally-defined types shadow opened types
                // (e.g., type xy in Sprite shadows Actors.xy from open).
                // Only add non-abstract types (those with manifests or type_kind)
                // to avoid interfering with functor signature types.
                for td in &typed_decls {
                    if td.typ_type.type_manifest.is_some()
                        || !matches!(td.typ_type.type_kind, crate::types::TypeKind::TypeAbstract)
                    {
                        sig_env.add_type(td.typ_id.clone(), td.typ_type.clone());
                    }
                }
                TSigDesc::Tsig_type(*rec_flag, typed_decls)
            }
            PSigDesc::Psig_module(md) => {
                let name_str = arena.get_string(md.pmd_name.txt).to_string();
                let id = Ident::create_local(&name_str);
                let typed_mty = transl_modtype(tctx, &sig_env, arena, arena.get_mod_type(md.pmd_type))?;
                // Add module to sig_env so subsequent items (Psig_open etc.) can find it.
                // This matches OCaml's transl_sig: `let newenv = Env.enter_module_declaration id md env`.
                let decl_mty = decl_module_type_from_typed(&typed_mty)
                    .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![]));
                sig_env.add_module(
                    id.clone(),
                    crate::types::decl::ModuleDeclaration {
                        md_type: decl_mty,
                        md_attributes: vec![],
                        md_loc: crate::location::Location::none(),
                        md_path: None,
                    },
                );
                TSigDesc::Tsig_module(TypedModuleDeclaration {
                    md_id: id,
                    md_name: Located {
                        txt: name_str,
                        loc: md.pmd_name.loc,
                    },
                    md_type: typed_mty,
                    md_attributes: md.pmd_attributes.clone(),
                    md_loc: md.pmd_loc,
                })
            }
            PSigDesc::Psig_modtype(mtd) => {
                let name_str = arena.get_string(mtd.pmtd_name.txt).to_string();
                let id = Ident::create_local(&name_str);
                let typed_mty = match &mtd.pmtd_type {
                    Some(mt) => Some(transl_modtype(tctx, &sig_env, arena, arena.get_mod_type(*mt))?),
                    None => None,
                };
                let decl_mtd = crate::types::ModtypeDeclaration {
                    mtd_type: match &mtd.pmtd_type {
                        Some(mt) => Some(translate_module_type_to_decl(
                            tctx,
                            &sig_env,
                            arena,
                            arena.get_mod_type(*mt),
                        )?),
                        None => None,
                    },
                    mtd_attributes: vec![],
                    mtd_loc: crate::location::Location::none(),
                };
                sig_env.add_modtype(id.clone(), decl_mtd);
                TSigDesc::Tsig_modtype(crate::types::typedtree::ModuleTypeDeclaration {
                    mtd_id: id,
                    mtd_name: Located {
                        txt: name_str,
                        loc: mtd.pmtd_name.loc,
                    },
                    mtd_type: typed_mty,
                    mtd_attributes: mtd.pmtd_attributes.clone(),
                    mtd_loc: mtd.pmtd_loc,
                })
            }
            PSigDesc::Psig_open(od) => {
                let longident = tctx.resolve_lid(od.popen_lid.txt).clone();
                let open_lid = arena.get_longident(od.popen_lid.txt);
                // Resolve the module and extend the environment with opened bindings.
                // This matches OCaml's transl_signature which calls type_open/Env.open_signature.
                let path = if let Some((resolved_path, sig_items)) =
                    sig_env.resolve_module_lid(open_lid, arena, &mut tctx.persistent_env, tctx.type_ctx)
                {
                    crate::cmi::persistent_env::add_signature_to_env(
                        &sig_items,
                        &resolved_path,
                        &mut sig_env,
                        tctx.type_ctx,
                        true, // as_opened
                    );
                    resolved_path
                } else {
                    lookup_module_path_by_lid(
                        &longident,
                        arena,
                        &sig_env,
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )
                    .unwrap_or_else(|| path_from_longident(&longident, |idx| arena.get_string(idx)))
                };
                TSigDesc::Tsig_open(crate::types::typedtree::OpenDeclaration {
                    open_path: path,
                    open_txt: od.popen_lid.clone(),
                    open_override: od.popen_override,
                    open_attributes: od.popen_attributes.clone(),
                    open_loc: od.popen_loc,
                })
            }
            PSigDesc::Psig_attribute(attr) => TSigDesc::Tsig_attribute((**attr).clone()),
            // For unsupported signature items, use Tsig_attribute as placeholder
            _ => TSigDesc::Tsig_attribute((
                Located {
                    txt: crate::intern::StrIdx(0),
                    loc: LocIdx(0),
                },
                crate::parser::ast::Payload::PStr(Box::new(vec![])),
            )),
        };

        typed_items.push(TypedSignatureItem {
            sig_desc: desc,
            sig_env: EnvRef(0),
            sig_loc: loc,
        });
    }

    Ok(crate::types::typedtree::TypedSignature {
        sig_items: typed_items,
    })
}

// ============================================================================
// Config Processing
// ============================================================================

/// Check if a structure starts with @@config(no_export) or @@config({no_export: ...}).
/// Returns true if the no_export config is detected.
fn has_no_export_config(arena: &ParseArena, items: &[ParsedStructureItem]) -> bool {
    use crate::parser::ast::{ExpressionDesc, Payload};

    for item in items {
        match &*item.pstr_desc {
            ParsedStructureItemDesc::Pstr_attribute(attr) => {
                let (ref name, ref payload) = **attr;
                let attr_name = arena.get_string(name.txt);
                if attr_name == "config" {
                    // Check if payload contains no_export
                    if let Payload::PStr(str_items) = payload {
                        for si in str_items.iter() {
                            match &*si.pstr_desc {
                                ParsedStructureItemDesc::Pstr_eval(inner) => {
                                    let (ref expr_idx, ref _attrs) = **inner;
                                    let expr = arena.get_expr(*expr_idx);
                                    match &*expr.pexp_desc {
                                        // @@config(no_export)
                                        ExpressionDesc::Pexp_ident(lid) => {
                                            let longident = arena.get_longident(lid.txt);
                                            let lid_name = arena.get_string(longident.last_idx());
                                            if lid_name == "no_export" {
                                                return true;
                                            }
                                        }
                                        // @@config({no_export: ...})
                                        ExpressionDesc::Pexp_record(inner) => {
                                            let (ref fields, ref _spread) = **inner;
                                            for field in fields {
                                                let longident = arena.get_longident(field.lid.txt);
                                                let field_name =
                                                    arena.get_string(longident.last_idx());
                                                if field_name == "no_export" {
                                                    return true;
                                                }
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
                // Continue checking (@@config might not be the first attribute)
            }
            _ => break, // Stop at first non-attribute item
        }
    }
    false
}

// ============================================================================
// Structure Type Checking
// ============================================================================

/// Type check a structure (module body).
pub fn type_structure<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    items: &[ParsedStructureItem],
) -> TypeModResult<(Structure, Env)> {
    // Check for @@config(no_export) and apply the no_export transformation
    // like OCaml's js_implementation.ml no_export function.
    if has_no_export_config(arena, items) && !items.is_empty() {
        return type_structure_no_export(tctx, env, arena, items);
    }

    let mut typed_items = Vec::new();
    let mut sig_items = Vec::new();
    let mut current_env = env.clone();

    for item in items {
        let ctx = tctx.type_ctx;
        ctx.init_def(ctx.current_stamp());
        tctx.set_unify_env(&current_env);
        let (typed_item, item_sig, new_env) = type_structure_item(tctx, &current_env, arena, item)?;
        sig_items.extend(item_sig);
        typed_items.push(typed_item);
        current_env = new_env;
    }

    let structure = Structure {
        str_items: typed_items,
        str_type: sig_items,
        str_final_env: EnvRef(0),
    };

    Ok((structure, current_env))
}

/// Apply no_export wrapping: wraps entire structure in
/// Tstr_include(Tmod_constraint(Tmod_structure(items), explicit(Tmty_signature([]))))
fn type_structure_no_export<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    items: &[ParsedStructureItem],
) -> TypeModResult<(Structure, Env)> {
    let loc = items[0].pstr_loc;

    // Type check all items normally first
    let mut typed_items = Vec::new();
    let mut sig_items = Vec::new();
    let mut current_env = env.clone();

    for item in items {
        let ctx = tctx.type_ctx;
        ctx.init_def(ctx.current_stamp());
        tctx.set_unify_env(&current_env);
        let (typed_item, item_sig, new_env) = type_structure_item(tctx, &current_env, arena, item)?;
        sig_items.extend(item_sig);
        typed_items.push(typed_item);
        current_env = new_env;
    }

    let inner_structure = Structure {
        str_items: typed_items,
        str_type: sig_items,
        str_final_env: EnvRef(0),
    };

    // Like OCaml: if simplify_signature would shrink the signature
    // (duplicate value names), wrap in Tmod_constraint implicit first
    let needs_implicit_constraint = structure_has_duplicate_value_names(&inner_structure, env, &current_env);

    let mod_structure = ModuleExpr {
        mod_desc: ModuleExprDesc::Tmod_structure(inner_structure),
        mod_loc: loc,
        mod_type: ModuleType::placeholder(),
        mod_env: EnvRef(0),
        mod_attributes: Attributes::new(),
    };

    // If duplicates detected, wrap in Tmod_constraint(implicit) first
    let mod_structure = if needs_implicit_constraint {
        ModuleExpr {
            mod_desc: ModuleExprDesc::Tmod_constraint(
                Box::new(mod_structure),
                ModuleType::placeholder(),
                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
                ModuleCoercion::Tcoerce_none,
            ),
            mod_loc: loc,
            mod_type: ModuleType::placeholder(),
            mod_env: EnvRef(0),
            mod_attributes: Attributes::new(),
        }
    } else {
        mod_structure
    };

    // Build: Tmod_constraint(Tmod_structure(...), explicit(Tmty_signature([])))
    let empty_sig = crate::types::typedtree::ModuleType {
        mty_desc: crate::types::typedtree::ModuleTypeDesc::Tmty_signature(
            crate::types::typedtree::TypedSignature { sig_items: vec![] },
        ),
        mty_loc: loc,
        mty_attributes: Attributes::new(),
    };
    let mod_constraint = ModuleExpr {
        mod_desc: ModuleExprDesc::Tmod_constraint(
            Box::new(mod_structure),
            ModuleType::placeholder(),
            crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(Box::new(empty_sig)),
            ModuleCoercion::Tcoerce_none,
        ),
        mod_loc: loc,
        mod_type: ModuleType::placeholder(),
        mod_env: EnvRef(0),
        mod_attributes: Attributes::new(),
    };

    // Build: Tstr_include(include_declaration(...))
    let include_item = StructureItem {
        str_desc: StructureItemDesc::Tstr_include(IncludeDeclaration {
            incl_mod: mod_constraint,
            incl_type: vec![],
            incl_attributes: Attributes::new(),
            incl_loc: loc,
        }),
        str_loc: loc,
        str_env: EnvRef(0),
    };

    let structure = Structure {
        str_items: vec![include_item],
        str_type: vec![],
        str_final_env: EnvRef(0),
    };

    Ok((structure, current_env))
}

/// Type check a structure item.
fn type_structure_item<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    item: &ParsedStructureItem,
) -> TypeModResult<(StructureItem, Vec<crate::types::decl::SignatureItem>, Env)> {
    let loc = item.pstr_loc;

    match &*item.pstr_desc {
        ParsedStructureItemDesc::Pstr_eval(inner) => {
            let (ref expr, ref attrs) = **inner;
            // Evaluated expression: E
            let typed_expr = type_expression(tctx, env, arena.get_expr(*expr))?;

            let desc = StructureItemDesc::Tstr_eval(typed_expr, attrs.clone());
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                vec![],
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_value(inner) => {
            let (ref rec_flag, ref bindings) = **inner;
            // Value binding: let P = E
            let (typed_bindings, new_env) = type_value_bindings(tctx, env, *rec_flag, bindings)?;
            let mut sig_items = Vec::new();
            for vb in &typed_bindings {
                push_sig_values_from_env_pattern(&new_env, &vb.vb_pat, &mut sig_items);
            }

            let desc = StructureItemDesc::Tstr_value(*rec_flag, typed_bindings);
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                sig_items,
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_primitive(vd) => {
            // Primitive declaration: external f : t = "..."
            let name_str = arena.get_string(vd.pval_name.txt).to_string();
            let id = Ident::create_local(&name_str);

            // Translate the type annotation using transl_type_scheme pattern:
            // OCaml: reset_type_variables() clears type var map so each declaration
            // gets fresh Tvars (e.g., 'a in log and 'a in log2 are separate nodes).
            tctx.type_variables.clear();
            let ctx = tctx.type_ctx;
            ctx.begin_def();
            let (typed_ctype, val_ty) = transl_type(tctx, env, arena.get_core_type(vd.pval_type))?;
            ctx.end_def();
            crate::types::ctype::generalize(ctx, val_ty);

            if std::env::var_os("RUST_DEBUG_PRIM_LEVELS").is_some() {
                let repr_ty = ctx.repr(val_ty);
                let desc = ctx.get_desc(repr_ty);
                let desc_kind = match &*desc {
                    crate::types::TypeDesc::Tconstr { path, .. } => {
                        format!("Tconstr({})", path.name())
                    }
                    crate::types::TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                    crate::types::TypeDesc::Tvar(_) => "Tvar".to_string(),
                    crate::types::TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                    crate::types::TypeDesc::Tlink(t) => format!("Tlink({})", ctx.repr(*t).0),
                    crate::types::TypeDesc::Tsubst(t) => format!("Tsubst({})", ctx.repr(*t).0),
                    crate::types::TypeDesc::Ttuple(ts) => format!("Ttuple({})", ts.len()),
                    crate::types::TypeDesc::Tobject { .. } => "Tobject".to_string(),
                    crate::types::TypeDesc::Tfield { .. } => "Tfield".to_string(),
                    crate::types::TypeDesc::Tnil => "Tnil".to_string(),
                    crate::types::TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                    crate::types::TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                    crate::types::TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
                };
                let arg_levels = match &*desc {
                    crate::types::TypeDesc::Tconstr { args, .. } => Some(
                        args.iter()
                            .map(|arg| {
                                let r = ctx.repr(*arg);
                                format!("{}@{}", r.0, ctx.get_level(r))
                            })
                            .collect::<Vec<_>>()
                            .join(","),
                    ),
                    _ => None,
                };
                eprintln!(
                    "[prim-levels] stage=post_generalize name={} ty_id={} level={} desc={}",
                    name_str,
                    repr_ty.0,
                    ctx.get_level(repr_ty),
                    desc_kind
                );
                if let Some(arg_levels) = arg_levels {
                    eprintln!(
                        "[prim-levels] stage=post_generalize name={} args={}",
                        name_str, arg_levels
                    );
                }
            }

            // OCaml's transl_value_decl calls parse_arity -> get_arity ->
            // expand_head AFTER generalize. The expand_head side effect
            // populates simple_abbrevs with the nullary Tconstr expansion.
            // When instance() is later called for Pexp_ident, copy() finds
            // this entry via find_simple_abbrev and returns Tlink to the
            // original instead of a fresh copy — creating node sharing.
            crate::types::ctype::expand_head(ctx, env, val_ty);

            if std::env::var_os("RUST_DEBUG_PRIM_LEVELS").is_some() {
                let repr_ty = ctx.repr(val_ty);
                let desc = ctx.get_desc(repr_ty);
                let desc_kind = match &*desc {
                    crate::types::TypeDesc::Tconstr { path, .. } => {
                        format!("Tconstr({})", path.name())
                    }
                    crate::types::TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                    crate::types::TypeDesc::Tvar(_) => "Tvar".to_string(),
                    crate::types::TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                    crate::types::TypeDesc::Tlink(t) => format!("Tlink({})", ctx.repr(*t).0),
                    crate::types::TypeDesc::Tsubst(t) => format!("Tsubst({})", ctx.repr(*t).0),
                    crate::types::TypeDesc::Ttuple(ts) => format!("Ttuple({})", ts.len()),
                    crate::types::TypeDesc::Tobject { .. } => "Tobject".to_string(),
                    crate::types::TypeDesc::Tfield { .. } => "Tfield".to_string(),
                    crate::types::TypeDesc::Tnil => "Tnil".to_string(),
                    crate::types::TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                    crate::types::TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                    crate::types::TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
                };
                let arg_levels = match &*desc {
                    crate::types::TypeDesc::Tconstr { args, .. } => Some(
                        args.iter()
                            .map(|arg| {
                                let r = ctx.repr(*arg);
                                format!("{}@{}", r.0, ctx.get_level(r))
                            })
                            .collect::<Vec<_>>()
                            .join(","),
                    ),
                    _ => None,
                };
                eprintln!(
                    "[prim-levels] stage=post_expand_head name={} ty_id={} level={} desc={}",
                    name_str,
                    repr_ty.0,
                    ctx.get_level(repr_ty),
                    desc_kind
                );
                if let Some(arg_levels) = arg_levels {
                    eprintln!(
                        "[prim-levels] stage=post_expand_head name={} args={}",
                        name_str, arg_levels
                    );
                }
            }

            // PPX has already encoded the FFI attributes into pval_prim,
            // so just resolve StrIdx -> String for the typed tree
            let val_prim: Vec<String> = vd
                .pval_prim
                .iter()
                .map(|s| arena.get_string(*s).to_string())
                .collect();

            // Add the external value to the environment
            let mut new_env = env.clone();
            let val_desc_for_env = crate::types::ValueDescription {
                val_type: val_ty,
                val_kind: crate::types::ValueKind::ValPrim(
                    crate::types::PrimitiveDescription {
                        prim_name: val_prim.first().cloned().unwrap_or_default(),
                        prim_arity: 1,
                        prim_native_name: String::new(),
                        prim_native_float: false,
                    },
                ),
                val_loc: arena.to_location(loc),
                val_attributes: vec![],
                val_path: None,
            };
            let sig_item = crate::types::decl::SignatureItem::SigValue(
                id.clone(),
                val_desc_for_env.clone(),
            );
            new_env.add_value(id.clone(), val_desc_for_env);

            let desc =
                StructureItemDesc::Tstr_primitive(crate::types::typedtree::TypedValueDescription {
                    val_id: id,
                    val_name: Located {
                        txt: name_str,
                        loc: vd.pval_name.loc,
                    },
                    val_desc: typed_ctype,
                    val_prim,
                    val_loc: vd.pval_loc,
                    val_attributes: vd.pval_attributes.clone(),
                });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                vec![sig_item],
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_type(inner) => {
            let (ref rec_flag, ref decls) = **inner;
            // Type declaration: type t = ...
            let ctx = tctx.type_ctx;
            let mut new_env = env.clone();
            let mut typed_tree_decls: Vec<TypedTypeDeclaration> = Vec::new();
            let mut internal_decls_for_generalize: Vec<crate::types::TypeDeclaration> = Vec::new();
            // Collect env-description TypeExprRefs (cstr_res, label ty_res) that
            // are separate from the TypeKind and need explicit generalization.
            let mut env_desc_types_for_generalize: Vec<crate::types::TypeExprRef> = Vec::new();

            // OCaml: reset_type_variables() + Ctype.begin_def() before translating type declarations
            tctx.type_variables.clear();
            ctx.begin_def();

            // Predeclare type names in the environment so recursive references
            // resolve to the current declaration group (matching OCaml typedecl).
            // OCaml: enter_type only adds placeholders for Recursive types.
            // For Nonrecursive, types refer to previous definitions (e.g., opened types).
            let mut declared_type_ids: Vec<Ident> = Vec::with_capacity(decls.len());
            let needs_placeholder = matches!(rec_flag, crate::parser::ast::RecFlag::Recursive);
            for decl in decls.iter() {
                let type_name = decl.ptype_name.txt;
                let type_name_str = arena.get_string(type_name);
                let type_id = Ident::create_local(type_name_str);
                if needs_placeholder {
                    let placeholder_decl = crate::types::TypeDeclaration {
                        type_params: vec![],
                        type_arity: decl.ptype_params.len() as i32,
                        type_kind: crate::types::TypeKind::TypeAbstract,
                        type_private: crate::types::PrivateFlag::Public,
                        type_manifest: None,
                        type_variance: vec![
                            crate::types::variance::Variance::null();
                            decl.ptype_params.len()
                        ],
                        type_newtype_level: None,
                        type_loc: arena.to_location(decl.ptype_loc),
                        type_attributes: vec![],
                        type_immediate: false,
                        type_unboxed: crate::types::UnboxedStatus::default(),
                        type_inlined_types: vec![],
                        type_path: Some(Path::pident(type_id.clone())),
                    };
                    new_env.add_type(type_id.clone(), placeholder_decl);
                }
                declared_type_ids.push(type_id);
            }

            // OCaml: temp_env is the environment used for translating type bodies.
            // For Recursive, it has abstract placeholders so types can self-reference.
            // For Nonrecursive, it equals the original env — types in the same group
            // are NOT visible to each other (they resolve to outer scope definitions).
            // new_env accumulates the final declarations and is returned.
            let temp_env = new_env.clone();

            for (decl_idx, decl) in decls.iter().enumerate() {
                let type_name = decl.ptype_name.txt;
                let type_name_str = arena.get_string(type_name);
                let type_id = declared_type_ids[decl_idx].clone();
                let saved_type_variables = std::mem::take(&mut tctx.type_variables);

                // Create the type path for self-reference
                let type_path = Path::pident(type_id.clone());

                // Convert type parameters: (CoreType, Variance) -> (TypedCoreType, Variance)
                let mut typ_params: Vec<(TypedCoreType, TypesVariance)> = Vec::new();
                let mut internal_type_params: Vec<TypeExprRef> = Vec::new();
                for (core_type, parser_var) in &decl.ptype_params {
                    let core_type = arena.get_core_type(*core_type);
                    let (typed_core_type, type_ref) = match &*core_type.ptyp_desc {
                        crate::parser::ast::CoreTypeDesc::Ptyp_any => {
                            // Use new_var (current_level) instead of new_global_var so
                            // type params are at the elevated level from begin_def and
                            // get properly generalized by end_def + generalize.
                            // OCaml creates type params with newvar() at !current_level.
                            let type_ref = ctx.new_var(Some("_".to_string()));
                            (
                                TypedCoreType {
                                    ctyp_desc: TypedCoreTypeDesc::Ttyp_var(None),
                                    ctyp_type: type_ref,
                                    ctyp_env: EnvRef(0),
                                    ctyp_loc: core_type.ptyp_loc,
                                    ctyp_attributes: core_type.ptyp_attributes.clone(),
                                },
                                type_ref,
                            )
                        }
                        crate::parser::ast::CoreTypeDesc::Ptyp_var(name) => {
                            let type_ref = ctx.new_var(Some(name.to_string()));
                            (
                                TypedCoreType {
                                    ctyp_desc: TypedCoreTypeDesc::Ttyp_var(Some(name.to_string())),
                                    ctyp_type: type_ref,
                                    ctyp_env: EnvRef(0),
                                    ctyp_loc: core_type.ptyp_loc,
                                    ctyp_attributes: core_type.ptyp_attributes.clone(),
                                },
                                type_ref,
                            )
                        }
                        _ => transl_type(tctx, &temp_env, core_type)?,
                    };
                    internal_type_params.push(type_ref);
                    if let crate::parser::ast::CoreTypeDesc::Ptyp_var(name) = &*core_type.ptyp_desc {
                        tctx.type_variables.insert(name.to_string(), type_ref);
                        if std::env::var_os("RUST_DEBUG_COMPARE_DECL").is_some()
                            && type_name_str == "compare"
                        {
                            eprintln!(
                                "[compare-decl] insert type_var name={name} ty={}",
                                tctx.type_ctx.repr(type_ref).0
                            );
                        }
                    }
                    let types_var = match parser_var {
                        ParserVariance::Covariant => TypesVariance::covariant(),
                        ParserVariance::Contravariant => TypesVariance::contravariant(),
                        ParserVariance::Invariant => TypesVariance::null(),
                    };
                    typ_params.push((typed_core_type, types_var));
                }
                let type_arity = internal_type_params.len() as i32;

                // Convert type constraints
                let mut typ_cstrs: Vec<(TypedCoreType, TypedCoreType, LocIdx)> = Vec::new();
                for (ct1, ct2, cstr_loc) in &decl.ptype_cstrs {
                    let (typed_ct1, _) = transl_type(tctx, &temp_env, arena.get_core_type(*ct1))?;
                    let (typed_ct2, _) = transl_type(tctx, &temp_env, arena.get_core_type(*ct2))?;
                    typ_cstrs.push((typed_ct1, typed_ct2, *cstr_loc));
                }

                // Convert manifest type (type alias)
                let (mut typ_manifest, mut manifest_type_ref) = match &decl.ptype_manifest {
                    Some(manifest) => {
                        let manifest_ct = arena.get_core_type(*manifest);
                        let (typed_manifest, type_ref) = transl_type(tctx, &temp_env, manifest_ct)?;
                        if std::env::var_os("RUST_DEBUG_COMPARE_DECL").is_some()
                            && type_name_str == "compare"
                        {
                            let m = tctx.type_ctx.repr(type_ref);
                            let d = tctx.type_ctx.get_desc(m);
                            if let crate::types::type_expr::TypeDesc::Tpackage { args, .. } = &*d {
                                let parts: Vec<String> = args
                                    .iter()
                                    .map(|a| {
                                        let r = tctx.type_ctx.repr(*a);
                                        format!("raw{}->repr{}", a.0, r.0)
                                    })
                                    .collect();
                                eprintln!(
                                    "[compare-decl] manifest type={} args={}",
                                    m.0,
                                    parts.join(",")
                                );
                            } else {
                                eprintln!("[compare-decl] manifest type={} non-package", m.0);
                            }
                        }
                        (Some(typed_manifest), Some(type_ref))
                    }
                    None => (None, None),
                };

                // Convert the type kind - create both internal and typed tree versions
                let (internal_type_kind, typed_tree_kind, constructors) = match &decl.ptype_kind {
                    crate::parser::ast::TypeKind::Ptype_abstract => (
                        crate::types::TypeKind::TypeAbstract,
                        TypedTypeKind::Ttype_abstract,
                        vec![],
                    ),
                    crate::parser::ast::TypeKind::Ptype_variant(cstrs) => {
                        // OCaml copies @unboxed and @tag attributes from the type decl
                        // to each constructor (copy_tag_attr_from_decl in typedecl.ml)
                        let tag_attrs: Vec<_> = decl
                            .ptype_attributes
                            .iter()
                            .filter(|attr| {
                                let name = arena.get_string(attr.0.txt);
                                name == "unboxed" || name == "tag"
                            })
                            .cloned()
                            .collect();

                        // Collect spread source type info for variant spread expansion.
                        // Maps from spread index to the source type's constructor declarations.
                        // Uses transl_type to resolve the spread source type (handles qualified paths like S.x).
                        // (constructors, is_pdot) - is_pdot=true means source is from a sub-module,
                        // where OCaml's Subst.type_declaration creates fresh type copies
                        let spread_sources: Vec<Option<(Vec<crate::types::ConstructorDeclaration>, bool)>> = {
                            let mut sources = Vec::new();
                            for cstr in cstrs.iter() {
                                let cstr_name_str = arena.get_string(cstr.pcd_name.txt);
                                if cstr_name_str != "..." {
                                    sources.push(None);
                                    continue;
                                }
                                // Type-check the spread source type to resolve qualified paths
                                let mut found = None;
                                let mut is_pdot = false;
                                if let crate::parser::ast::ConstructorArguments::Pcstr_tuple(
                                    ref args,
                                ) = cstr.pcd_args
                                {
                                    if let Some(spread_type_ct) = args.first() {
                                        if let Ok((_typed_ct, type_ref)) =
                                            transl_type(tctx, &temp_env, arena.get_core_type(*spread_type_ct))
                                        {
                                            // Extract the type declaration from the resolved type
                                            let repr = ctx.repr(type_ref);
                                            if let crate::types::type_expr::TypeDesc::Tconstr {
                                                ref path,
                                                ..
                                            } = *ctx.get_desc(repr)
                                            {
                                                is_pdot = matches!(path, Path::Pdot(..));
                                                // Try path-accurate lookup in the current env first.
                                                // `Env.lookup_type` on Pdot falls back to leaf-name lookup,
                                                // which can pick an unrelated `t` from opened modules.
                                                // For spread (`...M.t`) we must resolve the parent module
                                                // signature and then select the exact type item.
                                                match path {
                                                    Path::Pdot(parent, type_name, _) => {
                                                        let mut visiting = HashSet::new();
                                                        if let Some(parent_sig) = resolve_path_to_sig_impl(
                                                            parent,
                                                            Some(&temp_env),
                                                            &mut tctx.persistent_env,
                                                            tctx.type_ctx,
                                                            &mut visiting,
                                                        ) {
                                                            for item in &parent_sig {
                                                                if let crate::types::decl::SignatureItem::SigType(
                                                                    id,
                                                                    decl,
                                                                    _,
                                                                ) = item
                                                                {
                                                                    if id.name() == type_name.as_str() {
                                                                        if let crate::types::TypeKind::TypeVariant(
                                                                            ref source_cstrs,
                                                                        ) = decl.type_kind
                                                                        {
                                                                            found = Some(source_cstrs.clone());
                                                                        }
                                                                        break;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                    _ => {
                                                        if let Ok(source_decl) = temp_env.lookup_type(path) {
                                                            if let crate::types::TypeKind::TypeVariant(
                                                                ref source_cstrs,
                                                            ) = source_decl.type_kind
                                                            {
                                                                found = Some(source_cstrs.clone());
                                                            }
                                                        }
                                                    }
                                                }
                                                // Try global type store by stamp (for Pident paths)
                                                if found.is_none() {
                                                    if let Path::Pident(id) = path {
                                                        if let Some(source_decl) =
                                                            ctx.find_type_decl_by_stamp(id.stamp())
                                                        {
                                                            if let crate::types::TypeKind::TypeVariant(ref source_cstrs) = source_decl.type_kind {
                                                                found = Some(source_cstrs.clone());
                                                            }
                                                        }
                                                    }
                                                }
                                                // Try global type store by full path string (for Pdot paths like S.s)
                                                if found.is_none() {
                                                    let path_str = path.name();
                                                    if let Some(source_decl) =
                                                        ctx.find_type_decl_by_path(&path_str)
                                                    {
                                                        if let crate::types::TypeKind::TypeVariant(
                                                            ref source_cstrs,
                                                        ) = source_decl.type_kind
                                                        {
                                                            found = Some(source_cstrs.clone());
                                                        }
                                                    }
                                                }
                                                // Try global type store by short name as last resort
                                                if found.is_none() {
                                                    let short_name = path.head_name();
                                                    if let Some(source_decl) =
                                                        ctx.find_type_decl(short_name)
                                                    {
                                                        if let crate::types::TypeKind::TypeVariant(
                                                            ref source_cstrs,
                                                        ) = source_decl.type_kind
                                                        {
                                                            found = Some(source_cstrs.clone());
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                sources.push(found.map(|cstrs| (cstrs, is_pdot)));
                            }
                            sources
                        };

                        let mut internal_cstrs = Vec::new();
                        let mut typed_tree_cstrs = Vec::new();
                        let mut cstr_descs = Vec::new();
                        // Count consts/nonconsts including expanded spreads
                        // Spread markers are NOT counted - only expanded constructors
                        let (num_consts, num_nonconsts) = {
                            let mut nc = 0i32;
                            let mut nnc = 0i32;
                            for (idx, cstr) in cstrs.iter().enumerate() {
                                if let Some((ref source_cstrs, _)) = spread_sources[idx] {
                                    // Count only the expanded source constructors (not the spread marker)
                                    for sc in source_cstrs {
                                        match &sc.cd_args {
                                            crate::types::ConstructorArguments::CstrTuple(args)
                                                if args.is_empty() =>
                                            {
                                                nc += 1
                                            }
                                            _ => nnc += 1,
                                        }
                                    }
                                } else {
                                    let is_const = matches!(cstr.pcd_args, crate::parser::ast::ConstructorArguments::Pcstr_tuple(ref args) if args.is_empty());
                                    if is_const { nc += 1 } else { nnc += 1 }
                                }
                            }
                            (nc, nnc)
                        };

                        let mut const_tag = 0i32;
                        let mut block_tag = 0i32;

                        for (cstr_idx, cstr) in cstrs.iter().enumerate() {
                            // Handle variant spread expansion
                            // Like OCaml's typedecl.ml: spread markers return None (filtered out)
                            // and expanded constructors get real types from the source type
                            if let Some((ref source_cstrs, is_pdot_source)) = spread_sources[cstr_idx] {
                                // Expand the source type's constructors into this type
                                // The spread marker itself is NOT included in any output
                                for source_cstr in source_cstrs {
                                    let sc_name = source_cstr.cd_id.name().to_string();
                                    let sc_id = Ident::create_persistent(&sc_name);
                                    let spread_constructor_attr = (
                                        Located::mknoloc(
                                            arena.constructor_from_spread_attr_str(),
                                        ),
                                        crate::parser::ast::Payload::PStr(Box::new(vec![])),
                                    );
                                    let source_cd_loc =
                                        find_existing_loc_idx(arena, &source_cstr.cd_loc)
                                            .unwrap_or(cstr.pcd_loc);
                                    let sc_is_const = matches!(&source_cstr.cd_args, crate::types::ConstructorArguments::CstrTuple(args) if args.is_empty());
                                    let sc_tag = if sc_is_const {
                                        let t = const_tag;
                                        const_tag += 1;
                                        crate::types::ConstructorTag::CstrConstant(t)
                                    } else {
                                        let t = block_tag;
                                        block_tag += 1;
                                        crate::types::ConstructorTag::CstrBlock(t)
                                    };

                                    // Use actual types from the source constructor (like OCaml's typedecl.ml lines 523-530)
                                    // ctyp_desc = Ttyp_var(None) acts as Ttyp_any placeholder, ctyp_type = real type from source
                                    let (
                                        sc_args,
                                        sc_internal_cd_args,
                                        sc_typed_tree_cd_args,
                                        sc_inlined_labels,
                                    ) =
                                        match &source_cstr.cd_args {
                                            crate::types::ConstructorArguments::CstrTuple(args) => {
                                                // Use the actual types from the source, not fresh vars
                                                // For Pdot sources (sub-module types), create fresh shallow copies
                                                // to match OCaml's Subst.type_declaration behavior
                                                let copied_args: Vec<TypeExprRef> = if is_pdot_source {
                                                    args.iter().map(|&texpr| {
                                                        ctx.new_type(ctx.get_desc(texpr).clone())
                                                    }).collect()
                                                } else {
                                                    args.clone()
                                                };
                                                let typed_tree_args: Vec<TypedCoreType> = copied_args
                                                    .iter()
                                                    .map(|&texpr| TypedCoreType {
                                                        ctyp_desc: TypedCoreTypeDesc::Ttyp_var(
                                                            None,
                                                        ),
                                                        ctyp_type: texpr,
                                                        ctyp_env: EnvRef(0),
                                                        ctyp_loc: source_cd_loc,
                                                        ctyp_attributes: decl_attrs_to_parser_attrs(
                                                            arena,
                                                            &source_cstr.cd_attributes,
                                                        ),
                                                    })
                                                    .collect();
                                                let internal_cd_args = if is_pdot_source {
                                                    crate::types::ConstructorArguments::CstrTuple(copied_args.clone())
                                                } else {
                                                    source_cstr.cd_args.clone()
                                                };
                                                (
                                                    copied_args,
                                                    internal_cd_args,
                                                    TypedConstructorArguments::Cstr_tuple(
                                                        typed_tree_args,
                                                    ),
                                                    None,
                                                )
                                            }
                                            crate::types::ConstructorArguments::CstrRecord(
                                                lbls,
                                            ) => {
                                                // OCaml strips top-level Tpoly wrappers from
                                                // internal spread label types (transl_labels lbls').
                                                // For Pdot sources, create fresh type copies to match
                                                // OCaml's Subst.type_declaration behavior.
                                                let normalized_lbls = lbls
                                                    .iter()
                                                    .map(|l| {
                                                        let mut normalized = l.clone();
                                                        let unwrapped = unwrap_poly_type(ctx, l.ld_type);
                                                        normalized.ld_type = if is_pdot_source {
                                                            ctx.new_type(ctx.get_desc(unwrapped).clone())
                                                        } else {
                                                            unwrapped
                                                        };
                                                        normalized
                                                    })
                                                    .collect::<Vec<_>>();
                                                let typed_lbls: Vec<TypedLabelDeclaration> = normalized_lbls
                                                    .iter()
                                                    .map(|l| TypedLabelDeclaration {
                                                        ld_id: l.ld_id.clone(),
                                                        ld_name: crate::parse_arena::Located {
                                                            txt: l.ld_id.name().to_string(),
                                                            loc: find_existing_loc_idx(
                                                                arena,
                                                                &l.ld_loc,
                                                            )
                                                            .unwrap_or(source_cd_loc),
                                                        },
                                                        ld_mutable: match l.ld_mutable {
                                                            crate::types::asttypes::MutableFlag::Mutable => crate::parser::ast::MutableFlag::Mutable,
                                                            crate::types::asttypes::MutableFlag::Immutable => crate::parser::ast::MutableFlag::Immutable,
                                                        },
                                                        ld_optional: l.ld_optional,
                                                        ld_type: TypedCoreType {
                                                            ctyp_desc: TypedCoreTypeDesc::Ttyp_var(
                                                                None,
                                                            ),
                                                            ctyp_type: l.ld_type,
                                                            ctyp_env: EnvRef(0),
                                                            ctyp_loc: find_existing_loc_idx(
                                                                arena,
                                                                &l.ld_loc,
                                                            )
                                                            .unwrap_or(source_cd_loc),
                                                            ctyp_attributes: Attributes::new(),
                                                        },
                                                        ld_loc: find_existing_loc_idx(
                                                            arena,
                                                            &l.ld_loc,
                                                        )
                                                        .unwrap_or(source_cd_loc),
                                                        ld_attributes: decl_attrs_to_parser_attrs(
                                                            arena,
                                                            &l.ld_attributes,
                                                        ),
                                                    })
                                                    .collect();
                                                let args_vec = normalized_lbls
                                                    .iter()
                                                    .map(|l| l.ld_type)
                                                    .collect::<Vec<_>>();
                                                let internal_cd_args = if is_pdot_source {
                                                    crate::types::ConstructorArguments::CstrRecord(normalized_lbls.clone())
                                                } else {
                                                    source_cstr.cd_args.clone()
                                                };
                                                (
                                                    args_vec,
                                                    internal_cd_args,
                                                    TypedConstructorArguments::Cstr_record(
                                                        typed_lbls,
                                                    ),
                                                    Some(normalized_lbls),
                                                )
                                            }
                                        };

                                    let res_ty = ctx.new_constr(type_path.clone(), internal_type_params.clone());
                                    // Spread constructor cstr_res must be generalized
                                    // (like non-spread constructors at line 5348) so that
                                    // instance_constructor creates fresh copies.
                                    env_desc_types_for_generalize.push(res_ty);
                                    let sc_arity = sc_args.len() as i32;

                                    internal_cstrs.push(crate::types::ConstructorDeclaration {
                                        cd_id: sc_id.clone(),
                                        cd_args: sc_internal_cd_args,
                                        cd_res: source_cstr.cd_res,
                                        cd_loc: source_cstr.cd_loc.clone(),
                                        cd_attributes: source_cstr.cd_attributes.clone(),
                                    });
                                    let spread_cd_res =
                                        source_cstr.cd_res.map(|ty| TypedCoreType {
                                            ctyp_desc: TypedCoreTypeDesc::Ttyp_var(None),
                                            ctyp_type: ty,
                                            ctyp_env: EnvRef(0),
                                            ctyp_loc: source_cd_loc,
                                            ctyp_attributes: Attributes::new(),
                                        });
                                    typed_tree_cstrs.push(TypedConstructorDeclaration {
                                        cd_id: sc_id.clone(),
                                        cd_name: crate::parse_arena::Located {
                                            txt: sc_name.clone(),
                                            loc: source_cd_loc,
                                        },
                                        cd_args: sc_typed_tree_cd_args,
                                        cd_res: spread_cd_res,
                                        cd_loc: source_cd_loc,
                                        cd_attributes: {
                                            let mut attrs = tag_attrs.clone();
                                            attrs.push(spread_constructor_attr.clone());
                                            attrs.extend(
                                                decl_attrs_to_parser_attrs(
                                                    arena,
                                                    &source_cstr.cd_attributes,
                                                )
                                                .iter()
                                                .cloned(),
                                            );
                                            Attributes::from_vec(attrs)
                                        },
                                    });
                                    let (sc_desc_args, sc_desc_arity, sc_desc_inlined) =
                                        if let Some(inline_lbls) = &sc_inlined_labels {
                                            // Mirror OCaml datarepr.constructor_args for inline records:
                                            // cstr_args = [Tconstr(type_path.Constructor, params)],
                                            // cstr_inlined = Some synthetic record declaration.
                                            let inline_params = inline_record_type_params(
                                                ctx,
                                                &internal_type_params,
                                                inline_lbls,
                                            );
                                            let inline_tag = match &sc_tag {
                                                crate::types::ConstructorTag::CstrBlock(tag) => *tag,
                                                _ => 0,
                                            };
                                            let inline_decl = crate::types::TypeDeclaration {
                                                type_params: inline_params.clone(),
                                                type_arity: inline_params.len() as i32,
                                                type_kind: crate::types::TypeKind::TypeRecord(
                                                    inline_lbls.clone(),
                                                    crate::types::RecordRepresentation::RecordInlined {
                                                        tag: inline_tag,
                                                        name: sc_name.clone(),
                                                        num_nonconsts,
                                                        attrs: source_cstr.cd_attributes.clone(),
                                                    },
                                                ),
                                                type_private: crate::types::PrivateFlag::Public,
                                                type_manifest: None,
                                                type_variance: inline_params
                                                    .iter()
                                                    .map(|_| TypesVariance::full())
                                                    .collect(),
                                                type_newtype_level: None,
                                                type_loc: Location::none(),
                                                type_attributes: vec![],
                                                type_immediate: false,
                                                type_unboxed:
                                                    crate::types::UnboxedStatus::default(),
                                                type_inlined_types: vec![],
                                                type_path: None,
                                            };
                                            let inline_constr = ctx.new_constr(
                                                Path::pdot(type_path.clone(), sc_name.clone()),
                                                inline_params,
                                            );
                                            (vec![inline_constr], 1, Some(Box::new(inline_decl)))
                                        } else {
                                            (sc_args, sc_arity, None)
                                        };
                                    let sc_desc_res = source_cstr.cd_res.unwrap_or(res_ty);

                                    let sc_existentials = crate::types::env::constructor_existentials(ctx, &sc_desc_args, source_cstr.cd_res);
                                    cstr_descs.push((
                                        sc_id,
                                        crate::types::ConstructorDescription {
                                            cstr_name: sc_name,
                                            cstr_res: sc_desc_res,
                                            cstr_existentials: sc_existentials,
                                            cstr_args: sc_desc_args,
                                            cstr_arity: sc_desc_arity,
                                            cstr_tag: sc_tag,
                                            cstr_consts: num_consts,
                                            cstr_nonconsts: num_nonconsts,
                                            cstr_generalized: source_cstr.cd_res.is_some(),
                                            cstr_private: crate::types::PrivateFlag::Public,
                                            cstr_loc: source_cstr.cd_loc.clone(),
                                            cstr_attributes: source_cstr.cd_attributes.clone(),
                                            cstr_inlined: sc_desc_inlined,
                                        },
                                    ));
                                }
                                continue;
                            }

                            let cstr_name_str = arena.get_string(cstr.pcd_name.txt);
                            let cstr_id = Ident::create_persistent(cstr_name_str);
                            let is_constant = matches!(cstr.pcd_args, crate::parser::ast::ConstructorArguments::Pcstr_tuple(ref args) if args.is_empty());

                            // Convert constructor arguments using transl_type
                            let (cstr_args, internal_cd_args, typed_tree_cd_args) = match &cstr
                                .pcd_args
                            {
                                crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                                    let mut typed_args: Vec<TypeExprRef> = Vec::new();
                                    let mut typed_tree_args: Vec<TypedCoreType> = Vec::new();
                                    for core_type in types {
                                        let (typed_core_type, type_ref) =
                                            transl_type(tctx, &temp_env, arena.get_core_type(*core_type))?;
                                        typed_args.push(type_ref);
                                        typed_tree_args.push(typed_core_type);
                                    }
                                    (
                                        typed_args.clone(),
                                        crate::types::ConstructorArguments::CstrTuple(typed_args),
                                        TypedConstructorArguments::Cstr_tuple(typed_tree_args),
                                    )
                                }
                                crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                                    let mut typed_labels: Vec<TypedLabelDeclaration> = Vec::new();
                                    let mut internal_labels: Vec<crate::types::LabelDeclaration> =
                                        Vec::new();
                                    for lbl in labels {
                                        let lbl_type = arena.get_core_type(lbl.pld_type);
                                        let (typed_core_type, type_ref) =
                                            transl_type(tctx, &temp_env, lbl_type)?;
                                        // OCaml wraps optional label types in option
                                        let (typed_core_type, type_ref) = if lbl.pld_optional {
                                            let option_path =
                                                Path::pident(Ident::create_persistent("option"));
                                            let option_type_ref =
                                                ctx.new_constr(option_path.clone(), vec![type_ref]);
                                            let option_lid = crate::parse_arena::Located {
                                                txt: arena.placeholder_lid(),
                                                loc: lbl_type.ptyp_loc,
                                            };
                                            let option_typed = TypedCoreType {
                                                ctyp_desc: TypedCoreTypeDesc::Ttyp_constr(
                                                    option_path,
                                                    option_lid,
                                                    vec![typed_core_type],
                                                ),
                                                ctyp_type: option_type_ref,
                                                ctyp_env: EnvRef(0),
                                                ctyp_loc: lbl_type.ptyp_loc,
                                                ctyp_attributes: Attributes::new(),
                                            };
                                            (option_typed, option_type_ref)
                                        } else {
                                            (typed_core_type, type_ref)
                                        };
                                        let mutable_flag = match lbl.pld_mutable {
                                            crate::parser::ast::MutableFlag::Immutable => {
                                                crate::types::MutableFlag::Immutable
                                            }
                                            crate::parser::ast::MutableFlag::Mutable => {
                                                crate::types::MutableFlag::Mutable
                                            }
                                        };
                                        // OCaml wraps label types in Tpoly via force_poly + transl_simple_type.
                                        // If the source type was already Ptyp_poly, transl_type already
                                        // produced Ttyp_poly/Tpoly — don't double-wrap.
                                        let (poly_typed_core_type, poly_type_ref) =
                                            force_poly_typed_core_type(ctx, typed_core_type, type_ref);
                                        let lbl_name_str = arena.get_string(lbl.pld_name.txt);
                                        // For internal labels, strip Tpoly(t, []) like OCaml transl_labels lbls'
                                        let internal_type_ref = match &*ctx.get_desc(poly_type_ref) {
                                            crate::types::type_expr::TypeDesc::Tpoly { body, vars } if vars.is_empty() => *body,
                                            _ => poly_type_ref,
                                        };
                                        internal_labels.push(crate::types::LabelDeclaration {
                                            ld_id: Ident::create_persistent(lbl_name_str),
                                            ld_mutable: mutable_flag,
                                            ld_optional: lbl.pld_optional,
                                            ld_type: internal_type_ref,
                                            ld_loc: arena.to_location(lbl.pld_loc),
                                            ld_attributes: parser_attrs_to_decl_attrs(
                                                arena,
                                                &lbl.pld_attributes,
                                            ),
                                        });
                                        typed_labels.push(TypedLabelDeclaration {
                                            ld_id: Ident::create_persistent(lbl_name_str),
                                            ld_name: crate::parse_arena::Located {
                                                txt: lbl_name_str.to_string(),
                                                loc: lbl.pld_name.loc,
                                            },
                                            ld_mutable: lbl.pld_mutable.clone(),
                                            ld_optional: lbl.pld_optional,
                                            ld_type: poly_typed_core_type,
                                            ld_loc: lbl.pld_loc,
                                            ld_attributes: lbl.pld_attributes.clone(),
                                        });
                                    }
                                    let has_spread = internal_labels
                                        .iter()
                                        .any(|label| label.ld_id.name() == "...");
                                    if has_spread {
                                        let mut expanded_internal_labels = Vec::new();
                                        let mut expanded_typed_labels = Vec::new();
                                        let mut all_spreads_resolved = true;

                                        for (internal_label, typed_label) in
                                            internal_labels.iter().zip(typed_labels.iter())
                                        {
                                            if internal_label.ld_id.name() != "..." {
                                                expanded_internal_labels
                                                    .push(internal_label.clone());
                                                expanded_typed_labels.push(typed_label.clone());
                                                continue;
                                            }

                                            let mut visited = HashSet::new();
                                            if let Some(resolved_fields) =
                                                expand_record_spread_label(
                                                    ctx,
                                                    &temp_env,
                                                    internal_label,
                                                    &mut visited,
                                                )
                                            {
                                                for resolved_field in resolved_fields {
                                                    expanded_typed_labels.push(
                                                        make_typed_spread_label(
                                                            arena,
                                                            ctx,
                                                            typed_label,
                                                            &resolved_field,
                                                        ),
                                                    );
                                                    expanded_internal_labels.push(resolved_field);
                                                }
                                            } else {
                                                all_spreads_resolved = false;
                                                expanded_internal_labels
                                                    .push(internal_label.clone());
                                                expanded_typed_labels.push(typed_label.clone());
                                            }
                                        }

                                        if all_spreads_resolved {
                                            (
                                                vec![],
                                                crate::types::ConstructorArguments::CstrRecord(
                                                    expanded_internal_labels,
                                                ),
                                                TypedConstructorArguments::Cstr_record(
                                                    expanded_typed_labels,
                                                ),
                                            )
                                        } else if labels.len() == 1
                                            && arena.get_string(labels[0].pld_name.txt) == "..."
                                        {
                                            let spread_type_idx = labels[0].pld_type;
                                            let spread_type = arena.get_core_type(spread_type_idx);
                                            let object_spread_type = crate::parser::ast::CoreType {
                                                ptyp_desc: Box::new(
                                                    crate::parser::ast::CoreTypeDesc::Ptyp_object(
                                                        Box::new((
                                                            vec![
                                                                crate::parser::ast::ObjectField::Oinherit(
                                                                    spread_type_idx,
                                                                ),
                                                            ],
                                                            crate::parser::ast::ClosedFlag::Closed,
                                                        )),
                                                    ),
                                                ),
                                                ptyp_loc: spread_type.ptyp_loc,
                                                ptyp_attributes: Attributes::new(),
                                            };
                                            let (typed_core_type, type_ref) =
                                                transl_type(tctx, &temp_env, &object_spread_type)?;
                                            (
                                                vec![type_ref],
                                                crate::types::ConstructorArguments::CstrTuple(
                                                    vec![type_ref],
                                                ),
                                                TypedConstructorArguments::Cstr_tuple(vec![
                                                    typed_core_type,
                                                ]),
                                            )
                                        } else {
                                            (
                                                vec![],
                                                crate::types::ConstructorArguments::CstrRecord(
                                                    internal_labels,
                                                ),
                                                TypedConstructorArguments::Cstr_record(
                                                    typed_labels,
                                                ),
                                            )
                                        }
                                    } else {
                                        (
                                            vec![],
                                            crate::types::ConstructorArguments::CstrRecord(
                                                internal_labels,
                                            ),
                                            TypedConstructorArguments::Cstr_record(typed_labels),
                                        )
                                    }
                                }
                            };

                            // Determine constructor result type (GADT constructors carry `pcd_res`).
                            let (typed_cd_res, internal_cd_res) = match &cstr.pcd_res {
                                Some(res_core_type) => {
                                    let (typed_res, res_ty) =
                                        transl_type(tctx, &temp_env, arena.get_core_type(*res_core_type))?;
                                    (Some(typed_res), Some(res_ty))
                                }
                                None => (None, None),
                            };

                            // Determine the tag
                            let tag = if is_constant {
                                let t = const_tag;
                                const_tag += 1;
                                crate::types::ConstructorTag::CstrConstant(t)
                            } else {
                                let t = block_tag;
                                block_tag += 1;
                                crate::types::ConstructorTag::CstrBlock(t)
                            };

                            // For inline records, create a synthetic type declaration and
                            // set cstr_args to [Tconstr(path, type_params)] matching OCaml's datarepr.ml
                            let (cstr_args, cstr_inlined) =
                                if let crate::types::ConstructorArguments::CstrRecord(ref lbls) =
                                    internal_cd_args
                                {
                                    let inline_params =
                                        inline_record_type_params(ctx, &internal_type_params, lbls);
                                    // Build path: Pdot(Pident(type_name), cstr_name)
                                    let inline_path =
                                        Path::pdot(type_path.clone(), cstr_name_str.to_string());
                                    // Create synthetic inline type declaration
                                    let inline_decl = crate::types::TypeDeclaration {
                                        type_params: inline_params.clone(),
                                        type_arity: inline_params.len() as i32,
                                        type_kind: crate::types::TypeKind::TypeRecord(
                                            lbls.clone(),
                                            crate::types::RecordRepresentation::RecordInlined {
                                                tag: block_tag - 1, // use the tag just assigned
                                                name: cstr_name_str.to_string(),
                                                num_nonconsts,
                                                attrs: vec![], // simplified - parser attrs vs types attrs
                                            },
                                        ),
                                        type_private: crate::types::PrivateFlag::Public,
                                        type_manifest: None,
                                        type_variance: inline_params
                                            .iter()
                                            .map(|_| TypesVariance::full())
                                            .collect(),
                                        type_newtype_level: None,
                                        type_loc: Location::none(),
                                        type_attributes: vec![],
                                        type_immediate: false,
                                        type_unboxed: crate::types::UnboxedStatus::default(),
                                        type_inlined_types: vec![],
                                        type_path: None,
                                    };
                                    // cstr_args: single Tconstr pointing to the inline record path
                                    // OCaml's datarepr.ml creates this via newgenconstr (generic_level)
                                    // so instance_constructor's copy creates fresh nodes each time.
                                    let inline_constr =
                                        ctx.new_generic_constr(inline_path, inline_params.clone());
                                    (vec![inline_constr], Some(Box::new(inline_decl)))
                                } else {
                                    (cstr_args, None)
                                };

                            // Create internal constructor declaration
                            internal_cstrs.push(crate::types::ConstructorDeclaration {
                                cd_id: cstr_id.clone(),
                                cd_args: internal_cd_args,
                                cd_res: internal_cd_res,
                                cd_loc: arena.to_location(cstr.pcd_loc),
                                cd_attributes: {
                                    let mut attrs = tag_attrs.clone();
                                    attrs.extend(cstr.pcd_attributes.iter().cloned());
                                    parser_attrs_to_decl_attrs(
                                        arena,
                                        &Attributes::from_vec(attrs),
                                    )
                                },
                            });

                            // Create typed tree constructor declaration
                            typed_tree_cstrs.push(TypedConstructorDeclaration {
                                cd_id: cstr_id.clone(),
                                cd_name: crate::parse_arena::Located {
                                    txt: cstr_name_str.to_string(),
                                    loc: cstr.pcd_name.loc,
                                },
                                cd_args: typed_tree_cd_args,
                                cd_res: typed_cd_res,
                                cd_loc: cstr.pcd_loc,
                                cd_attributes: {
                                    let mut attrs = tag_attrs.clone();
                                    attrs.extend(cstr.pcd_attributes.iter().cloned());
                                    Attributes::from_vec(attrs)
                                },
                            });

                            // Create constructor description for the environment
                            let cstr_arity = cstr_args.len() as i32;
                            let cstr_desc_res = internal_cd_res.unwrap_or_else(|| {
                                ctx.new_constr(type_path.clone(), internal_type_params.clone())
                            });
                            env_desc_types_for_generalize.push(cstr_desc_res);
                            // Constructor description argument types are stored
                            // separately from `TypeKind` in `ConstructorDescription`.
                            // Ensure they are generalized with the declaration
                            // group so later `instance_constructor` calls can
                            // instantiate fresh per-use copies like OCaml.
                            env_desc_types_for_generalize.extend(cstr_args.iter().copied());
                            let cstr_existentials = crate::types::env::constructor_existentials(ctx, &cstr_args, internal_cd_res);
                            cstr_descs.push((
                                cstr_id,
                                crate::types::ConstructorDescription {
                                    cstr_name: cstr_name_str.to_string(),
                                    cstr_res: cstr_desc_res,
                                    cstr_existentials,
                                    cstr_args,
                                    cstr_arity,
                                    cstr_tag: tag,
                                    cstr_consts: num_consts,
                                    cstr_nonconsts: num_nonconsts,
                                    cstr_generalized: internal_cd_res.is_some(),
                                    cstr_private: crate::types::PrivateFlag::Public,
                                    cstr_loc: arena.to_location(cstr.pcd_loc),
                                    cstr_attributes: vec![],
                                    cstr_inlined,
                                },
                            ));
                        }

                        (
                            crate::types::TypeKind::TypeVariant(internal_cstrs),
                            TypedTypeKind::Ttype_variant(typed_tree_cstrs),
                            cstr_descs,
                        )
                    }
                    crate::parser::ast::TypeKind::Ptype_record(labels) => {
                        let mut internal_labels: Vec<crate::types::LabelDeclaration> = Vec::new();
                        let mut typed_tree_labels: Vec<TypedLabelDeclaration> = Vec::new();
                        for lbl in labels {
                            let lbl_name_str = arena.get_string(lbl.pld_name.txt);
                            let lbl_type = arena.get_core_type(lbl.pld_type);
                            let (typed_core_type, type_ref) =
                                transl_type(tctx, &temp_env, lbl_type)?;
                            // OCaml wraps optional label types in option (typedecl.ml lines 616-628)
                            let (typed_core_type, type_ref) = if lbl.pld_optional {
                                let option_path = Path::pident(Ident::create_persistent("option"));
                                let option_type_ref =
                                    ctx.new_constr(option_path.clone(), vec![type_ref]);
                                let option_lid = crate::parse_arena::Located {
                                    txt: arena.placeholder_lid(),
                                    loc: lbl_type.ptyp_loc,
                                };
                                let option_typed = TypedCoreType {
                                    ctyp_desc: TypedCoreTypeDesc::Ttyp_constr(
                                        option_path,
                                        option_lid,
                                        vec![typed_core_type],
                                    ),
                                    ctyp_type: option_type_ref,
                                    ctyp_env: EnvRef(0),
                                    ctyp_loc: lbl_type.ptyp_loc,
                                    ctyp_attributes: Attributes::new(),
                                };
                                (option_typed, option_type_ref)
                            } else {
                                (typed_core_type, type_ref)
                            };
                            let mutable_flag = match lbl.pld_mutable {
                                crate::parser::ast::MutableFlag::Immutable => {
                                    crate::types::MutableFlag::Immutable
                                }
                                crate::parser::ast::MutableFlag::Mutable => {
                                    crate::types::MutableFlag::Mutable
                                }
                            };
                            // OCaml wraps label types in Tpoly via force_poly + transl_simple_type.
                            let (poly_typed_core_type, poly_type_ref) =
                                force_poly_typed_core_type(ctx, typed_core_type, type_ref);
                            let internal_type_ref = match &*ctx.get_desc(poly_type_ref) {
                                crate::types::type_expr::TypeDesc::Tpoly { body, vars } if vars.is_empty() => *body,
                                _ => poly_type_ref,
                            };
                            internal_labels.push(crate::types::LabelDeclaration {
                                ld_id: Ident::create_persistent(lbl_name_str),
                                ld_mutable: mutable_flag,
                                ld_optional: lbl.pld_optional,
                                ld_type: internal_type_ref,
                                ld_loc: arena.to_location(lbl.pld_loc),
                                ld_attributes: parser_attrs_to_decl_attrs(
                                    arena,
                                    &lbl.pld_attributes,
                                ),
                            });
                            typed_tree_labels.push(TypedLabelDeclaration {
                                ld_id: Ident::create_persistent(lbl_name_str),
                                ld_name: crate::parse_arena::Located {
                                    txt: lbl_name_str.to_string(),
                                    loc: lbl.pld_name.loc,
                                },
                                ld_mutable: lbl.pld_mutable.clone(),
                                ld_optional: lbl.pld_optional,
                                ld_type: poly_typed_core_type,
                                ld_loc: lbl.pld_loc,
                                ld_attributes: lbl.pld_attributes.clone(),
                            });
                        }
                        // Match OCaml typedecl + record_type_spread behavior:
                        // spreads must expand in BOTH the internal type declaration and typed tree.
                        let has_spread = internal_labels
                            .iter()
                            .any(|label| label.ld_id.name() == "...");
                        let (internal_labels, typed_tree_labels, spread_only_object_manifest) =
                            if has_spread {
                                let mut expanded_internal = Vec::new();
                                let mut expanded_typed = Vec::new();
                                let mut all_spreads_resolved = true;
                                for (internal_label, typed_label) in
                                    internal_labels.iter().zip(typed_tree_labels.iter())
                                {
                                    if internal_label.ld_id.name() != "..." {
                                        expanded_internal.push(internal_label.clone());
                                        expanded_typed.push(typed_label.clone());
                                        continue;
                                    }
                                    let mut visited = HashSet::new();
                                    if let Some(resolved_fields) = expand_record_spread_label(
                                        ctx,
                                        &temp_env,
                                        internal_label,
                                        &mut visited,
                                    ) {
                                        for resolved_field in resolved_fields {
                                            expanded_typed.push(make_typed_spread_label(
                                                arena,
                                                ctx,
                                                typed_label,
                                                &resolved_field,
                                            ));
                                            expanded_internal.push(resolved_field);
                                        }
                                    } else {
                                        all_spreads_resolved = false;
                                        expanded_internal.push(internal_label.clone());
                                        expanded_typed.push(typed_label.clone());
                                    }
                                }
                                if all_spreads_resolved {
                                    (expanded_internal, expanded_typed, None)
                                } else {
                                    let only_spreads = labels
                                        .iter()
                                        .all(|label| arena.get_string(label.pld_name.txt) == "...");
                                    if only_spreads {
                                        let object_fields = labels
                                            .iter()
                                            .filter_map(|label| {
                                                if arena.get_string(label.pld_name.txt) == "..." {
                                                    Some(crate::parser::ast::ObjectField::Oinherit(
                                                        label.pld_type.clone(),
                                                    ))
                                                } else {
                                                    None
                                                }
                                            })
                                            .collect::<Vec<_>>();
                                        let object_manifest = crate::parser::ast::CoreType {
                                            ptyp_desc: Box::new(
                                                crate::parser::ast::CoreTypeDesc::Ptyp_object(
                                                    Box::new((
                                                        object_fields,
                                                        crate::parser::ast::ClosedFlag::Closed,
                                                    )),
                                                ),
                                            ),
                                            ptyp_loc: decl.ptype_loc,
                                            ptyp_attributes: Attributes::new(),
                                        };
                                        (expanded_internal, expanded_typed, Some(object_manifest))
                                    } else {
                                        (expanded_internal, expanded_typed, None)
                                    }
                                }
                            } else {
                                (internal_labels, typed_tree_labels, None)
                            };
                        if let Some(object_manifest) = spread_only_object_manifest {
                            let (typed_manifest, manifest_ref) =
                                transl_type(tctx, &temp_env, &object_manifest)?;
                            typ_manifest = Some(typed_manifest);
                            manifest_type_ref = Some(manifest_ref);
                            (
                                crate::types::TypeKind::TypeAbstract,
                                TypedTypeKind::Ttype_abstract,
                                vec![],
                            )
                        } else {
                            (
                                crate::types::TypeKind::TypeRecord(
                                    internal_labels,
                                    crate::types::RecordRepresentation::RecordRegular,
                                ),
                                TypedTypeKind::Ttype_record(typed_tree_labels),
                                vec![],
                            )
                        }
                    }
                    crate::parser::ast::TypeKind::Ptype_open => (
                        crate::types::TypeKind::TypeOpen,
                        TypedTypeKind::Ttype_open,
                        vec![],
                    ),
                };

                // Create internal type declaration for the environment
                let mut internal_decl = crate::types::TypeDeclaration {
                    type_params: internal_type_params,
                    type_arity,
                    type_kind: internal_type_kind,
                    type_private: crate::types::PrivateFlag::Public,
                    type_manifest: manifest_type_ref,
                    type_variance: typ_params.iter().map(|(_, v)| *v).collect(),
                    type_newtype_level: None,
                    type_loc: arena.to_location(decl.ptype_loc),
                    type_attributes: parser_attrs_to_decl_attrs(arena, &decl.ptype_attributes),
                    type_immediate: false,
                    type_unboxed: crate::types::UnboxedStatus::default(),
                    type_inlined_types: vec![],
                    type_path: None,
                };

                // Save for generalization after the loop
                internal_decls_for_generalize.push(internal_decl.clone());

                // Add type to environment
                new_env.add_type(type_id.clone(), internal_decl.clone());

                // Also register in global type store for alias expansion
                ctx.register_type_decl(type_name_str, internal_decl.clone());
                if type_id.stamp() != 0 {
                    ctx.register_type_decl_by_stamp(type_id.stamp(), internal_decl.clone());
                }

                // Add constructors to environment, and add inline record labels
                for (cstr_id, cstr_desc) in constructors {
                    // For inline records, add the labels to the environment
                    if let Some(ref inlined_decl) = cstr_desc.cstr_inlined {
                        if let crate::types::TypeKind::TypeRecord(ref labels, ref repres) =
                            inlined_decl.type_kind
                        {
                            // Build the inline record type path: Pdot(type_path, cstr_name)
                            let inline_path =
                                Path::pdot(type_path.clone(), cstr_desc.cstr_name.clone());
                            let ty_res =
                                ctx.new_constr(inline_path, inlined_decl.type_params.clone());
                            env_desc_types_for_generalize.push(ty_res);
                            for (pos, ld) in labels.iter().enumerate() {
                                let lbl_desc = crate::types::LabelDescription {
                                    lbl_name: ld.ld_id.name().to_string(),
                                    lbl_res: ty_res,
                                    lbl_arg: crate::types::ctype::remap_label_type_to_params(
                                        ctx,
                                        ld.ld_type,
                                        &inlined_decl.type_params,
                                    ),
                                    lbl_mut: ld.ld_mutable.clone(),
                                    lbl_optional: ld.ld_optional,
                                    lbl_pos: pos as i32,
                                    lbl_all: crate::types::LabelArrayRef(0),
                                    lbl_repres: repres.clone(),
                                    lbl_private: crate::types::PrivateFlag::Public,
                                    lbl_loc: ld.ld_loc.clone(),
                                    lbl_attributes: ld.ld_attributes.clone(),
                                };
                                new_env.add_label(ld.ld_id.clone(), lbl_desc);
                            }
                        }
                    }
                    new_env.add_constructor(cstr_id, cstr_desc);
                }

                // Add record labels to environment
                if let crate::types::TypeKind::TypeRecord(ref labels, ref repres) =
                    internal_decl.type_kind
                {
                    // Create the record type reference: Tconstr(type_path, type_params)
                    let ty_res =
                        ctx.new_constr(type_path.clone(), internal_decl.type_params.clone());
                    env_desc_types_for_generalize.push(ty_res);
                    for (pos, ld) in labels.iter().enumerate() {
                        let lbl_desc = crate::types::LabelDescription {
                            lbl_name: ld.ld_id.name().to_string(),
                            lbl_res: ty_res,
                            lbl_arg: crate::types::ctype::remap_label_type_to_params(
                                ctx,
                                ld.ld_type,
                                &internal_decl.type_params,
                            ),
                            lbl_mut: ld.ld_mutable.clone(),
                            lbl_optional: ld.ld_optional,
                            lbl_pos: pos as i32,
                            lbl_all: crate::types::LabelArrayRef(0), // Placeholder for now
                            lbl_repres: repres.clone(),
                            lbl_private: crate::types::PrivateFlag::Public,
                            lbl_loc: ld.ld_loc.clone(),
                            lbl_attributes: ld.ld_attributes.clone(),
                        };
                        new_env.add_label(ld.ld_id.clone(), lbl_desc);
                    }
                }

                // Convert private flag
                let typ_private = match decl.ptype_private {
                    crate::parser::ast::PrivateFlag::Public => {
                        crate::parser::ast::PrivateFlag::Public
                    }
                    crate::parser::ast::PrivateFlag::Private => {
                        crate::parser::ast::PrivateFlag::Private
                    }
                };

                // Create typed tree type declaration
                let typed_tree_decl = TypedTypeDeclaration {
                    typ_id: type_id,
                    typ_name: crate::parse_arena::Located {
                        txt: type_name_str.to_string(),
                        loc: decl.ptype_name.loc,
                    },
                    typ_params,
                    typ_type: internal_decl,
                    typ_cstrs,
                    typ_kind: typed_tree_kind,
                    typ_private,
                    typ_manifest,
                    typ_loc: decl.ptype_loc,
                    typ_attributes: decl.ptype_attributes.clone(),
                };

                typed_tree_decls.push(typed_tree_decl);
                tctx.type_variables = saved_type_variables;
            }

            // OCaml: Ctype.end_def() + generalize_decl for each declaration
            ctx.end_def();
            for decl in &internal_decls_for_generalize {
                // generalize type_params
                for &param in &decl.type_params {
                    crate::types::ctype::generalize(ctx, param);
                }
                // generalize all types in type_kind
                crate::types::btype::iter_type_expr_kind(&decl.type_kind, |ty| {
                    crate::types::ctype::generalize(ctx, ty);
                });
                // generalize type_manifest if present
                if let Some(manifest) = decl.type_manifest {
                    crate::types::ctype::generalize(ctx, manifest);
                }
            }
            // Generalize env-description types (cstr_res, label ty_res) that are
            // separate from the TypeKind and won't be reached by iter_type_expr_kind.
            // In OCaml these are created by datarepr.ml constructors_of_type/labels_of_type
            // inside Env.add_type, sharing the same type_params which get generalized
            // by generalize_decl. The Tconstr wrapper nodes themselves stay non-generic
            // in OCaml (copy returns identity for them). In Rust, copy_type_cached creates
            // new copies of non-generic Tconstr preserving their level, which contaminates
            // pattern type variables via update_level_expand during unification.
            for ty in &env_desc_types_for_generalize {
                if std::env::var_os("RUST_DEBUG_GENERALIZE_CSTR_ARGS").is_some() {
                    let repr = ctx.repr(*ty);
                    let desc = ctx.get_desc(repr);
                    if let crate::types::type_expr::TypeDesc::Tconstr { path, .. } = &*desc {
                        if path.last() == "spawn_typ"
                            || path.last() == "pl_typ"
                            || path.last() == "player_typ"
                            || path.last() == "enemy_typ"
                        {
                            eprintln!(
                                "[generalize-cstr-args] before path={} ty={} level={} current={}",
                                path.name(),
                                repr.0,
                                ctx.get_level(repr),
                                ctx.current_level()
                            );
                        }
                    }
                }
                crate::types::ctype::generalize(ctx, *ty);
                if std::env::var_os("RUST_DEBUG_GENERALIZE_CSTR_ARGS").is_some() {
                    let repr = ctx.repr(*ty);
                    let desc = ctx.get_desc(repr);
                    if let crate::types::type_expr::TypeDesc::Tconstr { path, .. } = &*desc {
                        if path.last() == "spawn_typ"
                            || path.last() == "pl_typ"
                            || path.last() == "player_typ"
                            || path.last() == "enemy_typ"
                        {
                            eprintln!(
                                "[generalize-cstr-args] after path={} ty={} level={} current={}",
                                path.name(),
                                repr.0,
                                ctx.get_level(repr),
                                ctx.current_level()
                            );
                        }
                    }
                }
            }

            // OCaml typedecl.ml compute_properties_fixpoint:
            // recompute variances for the whole declaration group as a fixpoint.
            let resolved_variances =
                compute_type_variance_fixpoint(ctx, &new_env, &declared_type_ids);
            if resolved_variances.len() == declared_type_ids.len() {
                for (idx, type_id) in declared_type_ids.iter().enumerate() {
                    let Some(variance_row) = resolved_variances.get(idx) else {
                        continue;
                    };
                    let path = Path::pident(type_id.clone());
                    let Ok(updated_decl_ref) = new_env.lookup_type(&path) else {
                        continue;
                    };
                    let mut updated_decl = updated_decl_ref.clone();
                    updated_decl.type_variance = variance_row.clone();
                    new_env.add_type(type_id.clone(), updated_decl.clone());

                    if let Some(typed_decl) = typed_tree_decls.get_mut(idx) {
                        typed_decl.typ_type.type_variance = variance_row.clone();
                    }
                    if let Some(internal_decl) = internal_decls_for_generalize.get_mut(idx) {
                        internal_decl.type_variance = variance_row.clone();
                    }

                    let type_name = arena.get_string(decls[idx].ptype_name.txt);
                    ctx.register_type_decl(type_name, updated_decl.clone());
                    if type_id.stamp() != 0 {
                        ctx.register_type_decl_by_stamp(type_id.stamp(), updated_decl.clone());
                    }
                }
            }

            let item_sig = sig_type_rec_statuses(*rec_flag, typed_tree_decls.as_slice())
                .into_iter()
                .zip(typed_tree_decls.iter())
                .zip(internal_decls_for_generalize.iter())
                .map(|((rec_status, typed_decl), decl)| {
                    crate::types::decl::SignatureItem::SigType(
                        typed_decl.typ_id.clone(),
                        decl.clone(),
                        rec_status,
                    )
                })
                .collect();
            let desc = StructureItemDesc::Tstr_type(*rec_flag, typed_tree_decls);
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                item_sig,
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_typext(ext) => {
            let ctx = tctx.type_ctx;
            // Type extension: type t += ...
            let resolved_lid = tctx.resolve_lid(ext.ptyext_path.txt);
            let path = match resolved_lid {
                Longident::Lident(name_idx) => {
                    let type_name = arena.get_string(*name_idx);
                    match env.find_type_with_id(type_name) {
                        Ok((type_id, _)) => Path::pident(type_id.clone()),
                        Err(_) => path_from_longident(resolved_lid, |idx| arena.get_string(idx)),
                    }
                }
                _ => path_from_longident(resolved_lid, |idx| arena.get_string(idx)),
            };

            // The result type for the extension constructors
            let ext_res_ty = tctx.type_ctx.new_generic_constr(path.clone(), vec![]);

            // OCaml typedecl.ml: begin_def/end_def/generalize around type extension
            // constructor translation, matching Pstr_exception treatment. This ensures
            // arg types are at GENERIC_LEVEL so instance() creates fresh copies.
            tctx.type_variables.clear();
            ctx.begin_def();

            // Translate constructors and register them in the environment
            let mut typed_constructors = Vec::new();
            let mut ext_types_to_generalize: Vec<TypeExprRef> = Vec::new();
            let mut new_env = env.clone();
            for ec in &ext.ptyext_constructors {
                let name_str = arena.get_string(ec.pext_name.txt).to_string();
                let id = Ident::create_local(&name_str);

                let (typed_args, typed_ret, ext_args, cstr_args, cstr_inlined, ext_ret_ty) = match &ec.pext_kind
                {
                    crate::parser::ast::ExtensionConstructorKind::Pext_decl(args, ret) => {
                        let mut arg_ty_refs = Vec::new();
                        let (typed_args, ext_args, cstr_args, cstr_inlined) = match args {
                            crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                                let mut typed = Vec::new();
                                for ty in types {
                                    let (typed_ct, ty_ref) = transl_type(tctx, env, arena.get_core_type(*ty))?;
                                    arg_ty_refs.push(ty_ref);
                                    typed.push(typed_ct);
                                }
                                (
                                    crate::types::typedtree::ConstructorArgument::Cstr_tuple(typed),
                                    crate::types::ConstructorArguments::CstrTuple(
                                        arg_ty_refs.clone(),
                                    ),
                                    arg_ty_refs.clone(),
                                    None,
                                )
                            }
                            crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                                let mut typed_labels = Vec::new();
                                let mut decl_labels = Vec::new();
                                for label in labels {
                                    let label_name =
                                        arena.get_string(label.pld_name.txt).to_string();
                                    let (typed_ct, ty_ref) =
                                        transl_type(tctx, env, arena.get_core_type(label.pld_type))?;
                                    let (poly_typed_ct, poly_ty_ref) =
                                        force_poly_typed_core_type(ctx, typed_ct, ty_ref);
                                    let internal_ty_ref = match &*ctx.get_desc(poly_ty_ref) {
                                        crate::types::type_expr::TypeDesc::Tpoly { body, vars } if vars.is_empty() => *body,
                                        _ => poly_ty_ref,
                                    };
                                    typed_labels.push(crate::types::typedtree::LabelDeclaration {
                                        ld_id: Ident::create_local(&label_name),
                                        ld_name: crate::parse_arena::Located {
                                            txt: label_name.clone(),
                                            loc: label.pld_name.loc,
                                        },
                                        ld_mutable: label.pld_mutable,
                                        ld_optional: label.pld_optional,
                                        ld_type: poly_typed_ct,
                                        ld_loc: label.pld_loc,
                                        ld_attributes: label.pld_attributes.clone(),
                                    });
                                    decl_labels.push(crate::types::LabelDeclaration {
                                        ld_id: Ident::create_local(&label_name),
                                        ld_mutable: match label.pld_mutable {
                                            crate::parser::ast::MutableFlag::Immutable => {
                                                crate::types::MutableFlag::Immutable
                                            }
                                            crate::parser::ast::MutableFlag::Mutable => {
                                                crate::types::MutableFlag::Mutable
                                            }
                                        },
                                        ld_optional: label.pld_optional,
                                        ld_type: internal_ty_ref,
                                        ld_loc: arena.to_location(label.pld_loc),
                                        ld_attributes: vec![],
                                    });
                                }
                                let inline_path = Path::pident(id.clone());
                                let inline_ty = ctx.new_generic_constr(inline_path.clone(), vec![]);
                                let inline_decl = crate::types::TypeDeclaration {
                                    type_params: vec![],
                                    type_arity: 0,
                                    type_kind: crate::types::TypeKind::TypeRecord(
                                        decl_labels.clone(),
                                        crate::types::RecordRepresentation::RecordExtension,
                                    ),
                                    type_private: crate::types::PrivateFlag::Public,
                                    type_manifest: None,
                                    type_variance: vec![],
                                    type_newtype_level: None,
                                    type_loc: Location::none(),
                                    type_attributes: vec![],
                                    type_immediate: false,
                                    type_unboxed: crate::types::UnboxedStatus::default(),
                                    type_inlined_types: vec![],
                                    type_path: None,
                                };
                                (
                                    crate::types::typedtree::ConstructorArgument::Cstr_record(
                                        typed_labels,
                                    ),
                                    crate::types::ConstructorArguments::CstrRecord(decl_labels),
                                    vec![inline_ty],
                                    Some(Box::new(inline_decl)),
                                )
                            }
                        };
                        let (typed_ret, ext_ret_ty) = match ret {
                            Some(ct) => {
                                let (typed_ct, ty_ref) =
                                    transl_type(tctx, env, arena.get_core_type(*ct))?;
                                (Some(typed_ct), Some(ty_ref))
                            }
                            None => (None, None),
                        };
                        (
                            typed_args,
                            typed_ret,
                            ext_args,
                            cstr_args,
                            cstr_inlined,
                            ext_ret_ty,
                        )
                    }
                    crate::parser::ast::ExtensionConstructorKind::Pext_rebind(_lid) => (
                        crate::types::typedtree::ConstructorArgument::Cstr_tuple(vec![]),
                        None,
                        crate::types::ConstructorArguments::CstrTuple(vec![]),
                        vec![],
                        None,
                        None,
                    ),
                };

                crate::types::btype::iter_type_expr_cstr_args(&ext_args, |ty| {
                    ext_types_to_generalize.push(ty);
                });
                if let Some(ret_ty) = ext_ret_ty {
                    ext_types_to_generalize.push(ret_ty);
                }

                // Register the extension constructor in the environment
                let ext_path = Path::pident(id.clone());
                let cstr_desc = crate::types::decl::ConstructorDescription {
                    cstr_name: name_str.clone(),
                    cstr_res: ext_res_ty,
                    cstr_existentials: vec![],
                    cstr_args: cstr_args.clone(),
                    cstr_arity: cstr_args.len() as i32,
                    cstr_tag: crate::types::decl::ConstructorTag::CstrExtension(ext_path),
                    cstr_consts: 0,
                    cstr_nonconsts: 0,
                    cstr_generalized: false,
                    cstr_private: crate::types::PrivateFlag::Public,
                    cstr_loc: crate::location::Location::none(),
                    cstr_attributes: vec![],
                    cstr_inlined: cstr_inlined.clone(),
                };
                if let Some(ref inlined_decl) = cstr_inlined {
                    if let crate::types::TypeKind::TypeRecord(ref labels, ref repres) =
                        inlined_decl.type_kind
                    {
                        let ty_res = ctx
                            .new_generic_constr(
                                Path::pident(id.clone()),
                                inlined_decl.type_params.clone(),
                            );
                        for (pos, ld) in labels.iter().enumerate() {
                            let lbl_desc = crate::types::LabelDescription {
                                lbl_name: ld.ld_id.name().to_string(),
                                lbl_res: ty_res,
                                lbl_arg: crate::types::ctype::remap_label_type_to_params(
                                    ctx,
                                    ld.ld_type,
                                    &inlined_decl.type_params,
                                ),
                                lbl_mut: ld.ld_mutable,
                                lbl_optional: ld.ld_optional,
                                lbl_pos: pos as i32,
                                lbl_all: crate::types::LabelArrayRef(0),
                                lbl_repres: repres.clone(),
                                lbl_private: inlined_decl.type_private,
                                lbl_loc: ld.ld_loc.clone(),
                                lbl_attributes: ld.ld_attributes.clone(),
                            };
                            new_env.add_label(ld.ld_id.clone(), lbl_desc);
                        }
                    }
                }
                new_env.add_constructor(id.clone(), cstr_desc);

                typed_constructors.push(crate::types::typedtree::ExtensionConstructor {
                    ext_id: id,
                    ext_name: crate::parse_arena::Located {
                        txt: name_str,
                        loc: ec.pext_name.loc,
                    },
                    ext_type: crate::types::ExtensionConstructor {
                        ext_type_path: path.clone(),
                        ext_type_params: vec![],
                        ext_args,
                        ext_ret_type: None,
                        ext_private: crate::types::PrivateFlag::Public,
                        ext_loc: arena.to_location(loc),
                        ext_attributes: vec![],
                        ext_is_exception: false,
                    },
                    ext_kind: crate::types::typedtree::ExtensionConstructorKind::Text_decl(
                        typed_args, typed_ret,
                    ),
                    ext_loc: ec.pext_loc,
                    ext_attributes: ec.pext_attributes.clone(),
                });
            }

            // OCaml typedecl.ml: end_def and generalize constructor arg types
            ctx.end_def();
            for ty_ref in &ext_types_to_generalize {
                crate::types::generalize(ctx, *ty_ref);
            }

            // Translate params
            let mut typed_params = Vec::new();
            for (ct, v) in &ext.ptyext_params {
                let (typed_ct, _) = transl_type(tctx, env, arena.get_core_type(*ct))?;
                let variance = match v {
                    ParserVariance::Covariant => TypesVariance::covariant(),
                    ParserVariance::Contravariant => TypesVariance::contravariant(),
                    ParserVariance::Invariant => TypesVariance::null(),
                };
                typed_params.push((typed_ct, variance));
            }

            let item_sig = typed_constructors
                .iter()
                .enumerate()
                .map(|(index, ext_cstr)| {
                    crate::types::decl::SignatureItem::SigTypext(
                        ext_cstr.ext_id.clone(),
                        ext_cstr.ext_type.clone(),
                        sig_ext_status(index),
                    )
                })
                .collect();
            let desc = StructureItemDesc::Tstr_typext(TypeExtension {
                tyext_path: path,
                tyext_txt: ext.ptyext_path.clone(),
                tyext_params: typed_params,
                tyext_constructors: typed_constructors,
                tyext_private: ext.ptyext_private,
                tyext_loc: loc,
                tyext_attributes: ext.ptyext_attributes.clone(),
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                item_sig,
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_exception(ext_constr) => {
            let ctx = tctx.type_ctx;
            // Exception declaration: exception C
            let name_str = arena.get_string(ext_constr.pext_name.txt).to_string();
            let id = Ident::create_local(&name_str);

            // OCaml typedecl.ml:1839-1846: begin_def/end_def/generalize around
            // exception constructor type translation. This ensures arg types are
            // at GENERIC_LEVEL so instance() creates fresh copies, preventing
            // declaration types from being linked to use-site aliases.
            // OCaml: reset_type_variables() at start of transl_exception
            tctx.type_variables.clear();
            ctx.begin_def();

            // Translate constructor arguments and collect type refs for env registration
            let (typed_args, _ext_ret, ext_args, cstr_args, cstr_inlined, ext_ret_ty) = match &ext_constr
                .pext_kind
            {
                crate::parser::ast::ExtensionConstructorKind::Pext_decl(args, ret) => {
                    let mut arg_ty_refs = Vec::new();
                    let (typed_args, ext_args, cstr_args, cstr_inlined) = match args {
                        crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                            let mut typed = Vec::new();
                            for ty in types {
                                let (typed_ct, ty_ref) = transl_type(tctx, env, arena.get_core_type(*ty))?;
                                arg_ty_refs.push(ty_ref);
                                typed.push(typed_ct);
                            }
                            (
                                crate::types::typedtree::ConstructorArgument::Cstr_tuple(typed),
                                crate::types::ConstructorArguments::CstrTuple(arg_ty_refs.clone()),
                                arg_ty_refs.clone(),
                                None,
                            )
                        }
                        crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                            let mut typed_labels = Vec::new();
                            let mut decl_labels = Vec::new();
                            for label in labels {
                                let label_name = arena.get_string(label.pld_name.txt).to_string();
                                let (typed_ct, ty_ref) = transl_type(tctx, env, arena.get_core_type(label.pld_type))?;
                                let (poly_typed_ct, poly_ty_ref) =
                                    force_poly_typed_core_type(ctx, typed_ct, ty_ref);
                                let internal_ty_ref = match &*ctx.get_desc(poly_ty_ref) {
                                    crate::types::type_expr::TypeDesc::Tpoly { body, vars } if vars.is_empty() => *body,
                                    _ => poly_ty_ref,
                                };
                                typed_labels.push(crate::types::typedtree::LabelDeclaration {
                                    ld_id: Ident::create_local(&label_name),
                                    ld_name: crate::parse_arena::Located {
                                        txt: label_name.clone(),
                                        loc: label.pld_name.loc,
                                    },
                                    ld_mutable: label.pld_mutable,
                                    ld_optional: label.pld_optional,
                                    ld_type: poly_typed_ct,
                                    ld_loc: label.pld_loc,
                                    ld_attributes: label.pld_attributes.clone(),
                                });
                                decl_labels.push(crate::types::LabelDeclaration {
                                    ld_id: Ident::create_local(&label_name),
                                    ld_mutable: match label.pld_mutable {
                                        crate::parser::ast::MutableFlag::Immutable => {
                                            crate::types::MutableFlag::Immutable
                                        }
                                        crate::parser::ast::MutableFlag::Mutable => {
                                            crate::types::MutableFlag::Mutable
                                        }
                                    },
                                    ld_optional: label.pld_optional,
                                    ld_type: internal_ty_ref,
                                    ld_loc: arena.to_location(label.pld_loc),
                                    ld_attributes: vec![],
                                });
                            }
                            let inline_path = Path::pident(id.clone());
                            let inline_ty = ctx.new_generic_constr(inline_path.clone(), vec![]);
                            let inline_decl = crate::types::TypeDeclaration {
                                type_params: vec![],
                                type_arity: 0,
                                type_kind: crate::types::TypeKind::TypeRecord(
                                    decl_labels.clone(),
                                    crate::types::RecordRepresentation::RecordExtension,
                                ),
                                type_private: crate::types::PrivateFlag::Public,
                                type_manifest: None,
                                type_variance: vec![],
                                type_newtype_level: None,
                                type_loc: Location::none(),
                                type_attributes: vec![],
                                type_immediate: false,
                                type_unboxed: crate::types::UnboxedStatus::default(),
                                type_inlined_types: vec![],
                                type_path: None,
                            };
                            (
                                crate::types::typedtree::ConstructorArgument::Cstr_record(
                                    typed_labels,
                                ),
                                crate::types::ConstructorArguments::CstrRecord(decl_labels),
                                vec![inline_ty],
                                Some(Box::new(inline_decl)),
                            )
                        }
                    };
                    let (typed_ret, ext_ret_ty) = match ret {
                        Some(ct) => {
                            let (typed_ct, ty_ref) =
                                transl_type(tctx, env, arena.get_core_type(*ct))?;
                            (Some(typed_ct), Some(ty_ref))
                        }
                        None => (None, None),
                    };
                    (
                        typed_args,
                        typed_ret,
                        ext_args,
                        cstr_args,
                        cstr_inlined,
                        ext_ret_ty,
                    )
                }
                crate::parser::ast::ExtensionConstructorKind::Pext_rebind(_lid) => (
                    crate::types::typedtree::ConstructorArgument::Cstr_tuple(vec![]),
                    None,
                    crate::types::ConstructorArguments::CstrTuple(vec![]),
                    vec![],
                    None,
                    None,
                ),
            };

            // OCaml typedecl.ml:1843-1846: end_def and generalize args
            ctx.end_def();
            let mut ext_types_to_generalize = Vec::new();
            crate::types::btype::iter_type_expr_cstr_args(&ext_args, |ty| {
                ext_types_to_generalize.push(ty);
            });
            if let Some(ret_ty) = ext_ret_ty {
                ext_types_to_generalize.push(ret_ty);
            }
            for ty_ref in &ext_types_to_generalize {
                crate::types::generalize(ctx, *ty_ref);
            }

            // Register the exception constructor in the environment
            let exn_ty = tctx
                .type_ctx
                .new_generic_constr(Path::pident(Ident::create_persistent("exn")), vec![]);
            let exn_path = Path::pident(id.clone());
            let cstr_desc = crate::types::decl::ConstructorDescription {
                cstr_name: name_str.clone(),
                cstr_res: exn_ty,
                cstr_existentials: vec![],
                cstr_args: cstr_args.clone(),
                cstr_arity: cstr_args.len() as i32,
                cstr_tag: crate::types::decl::ConstructorTag::CstrExtension(exn_path),
                cstr_consts: 0,
                cstr_nonconsts: 0,
                cstr_generalized: false,
                cstr_private: crate::types::PrivateFlag::Public,
                cstr_loc: crate::location::Location::none(),
                cstr_attributes: vec![],
                cstr_inlined: cstr_inlined.clone(),
            };
            let mut new_env = env.clone();
            if let Some(ref inlined_decl) = cstr_inlined {
                if let crate::types::TypeKind::TypeRecord(ref labels, ref repres) =
                    inlined_decl.type_kind
                {
                    let ty_res = ctx.new_generic_constr(
                        Path::pident(id.clone()),
                        inlined_decl.type_params.clone(),
                    );
                    for (pos, ld) in labels.iter().enumerate() {
                        let lbl_desc = crate::types::LabelDescription {
                            lbl_name: ld.ld_id.name().to_string(),
                            lbl_res: ty_res,
                            lbl_arg: crate::types::ctype::remap_label_type_to_params(
                                ctx,
                                ld.ld_type,
                                &inlined_decl.type_params,
                            ),
                            lbl_mut: ld.ld_mutable,
                            lbl_optional: ld.ld_optional,
                            lbl_pos: pos as i32,
                            lbl_all: crate::types::LabelArrayRef(0),
                            lbl_repres: repres.clone(),
                            lbl_private: inlined_decl.type_private,
                            lbl_loc: ld.ld_loc.clone(),
                            lbl_attributes: ld.ld_attributes.clone(),
                        };
                        new_env.add_label(ld.ld_id.clone(), lbl_desc);
                    }
                }
            }
            new_env.add_constructor(id.clone(), cstr_desc);

            let ext_type = crate::types::ExtensionConstructor {
                ext_type_path: Path::pident(Ident::create_persistent("exn")),
                ext_type_params: vec![],
                ext_args,
                ext_ret_type: None,
                ext_private: crate::types::PrivateFlag::Public,
                ext_loc: arena.to_location(loc),
                ext_attributes: vec![],
                ext_is_exception: true,
            };
            let desc =
                StructureItemDesc::Tstr_exception(crate::types::typedtree::ExtensionConstructor {
                    ext_id: id.clone(),
                    ext_name: crate::parse_arena::Located {
                        txt: name_str,
                        loc: ext_constr.pext_name.loc,
                    },
                    ext_type: ext_type.clone(),
                    ext_kind: crate::types::typedtree::ExtensionConstructorKind::Text_decl(
                        typed_args, _ext_ret,
                    ),
                    ext_loc: loc,
                    ext_attributes: ext_constr.pext_attributes.clone(),
                });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                vec![crate::types::decl::SignatureItem::SigTypext(
                    id,
                    ext_type,
                    crate::types::decl::ExtStatus::TextException,
                )],
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_module(mb) => {
            // Module binding: module M = ME
            // Compute the semantic module type BEFORE type-checking the module expr,
            // so we can use it to extend the environment.
            let semantic_mod_type = match &*arena.get_mod_expr(mb.pmb_expr).pmod_desc {
                // Match OCaml typemod: module aliases keep an alias semantic type
                // (Mty_alias) instead of eagerly replacing it with the aliased
                // signature. This is required so later Pmod_ident uses can receive
                // implicit Tmod_constraint wrapping.
                ParsedModuleExprDesc::Pmod_ident(lid) => {
                    let longident = arena.get_longident(lid.txt);
                    let path = lookup_module_path_by_lid(
                        longident,
                        arena,
                        env,
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )
                    .unwrap_or_else(|| path_from_longident(longident, |idx| arena.get_string(idx)));
                    Some(crate::types::decl::ModuleType::MtyAlias(
                        crate::types::decl::AliasPresence::MtaAbsent,
                        path,
                    ))
                }
                _ => lookup_module_type_from_parsed_module_expr(
                    tctx,
                    env,
                    arena,
                    arena.get_mod_expr(mb.pmb_expr),
                ),
            };

            // Create module ident BEFORE typing body (matches OCaml typemod.ml:1454)
            // This ensures binding_time < all internal idents, so
            // lower_nongen(binding_time - 1) can reach internal non-generic Tvars.
            let mod_name_str = arena.get_string(mb.pmb_name.txt);
            let mod_id = Ident::create_local(mod_name_str);

            let typed_mod =
                type_module_expr_with_alias(tctx, env, arena, arena.get_mod_expr(mb.pmb_expr), true)?;

            // Extend environment with the new module
            // Use semantic_mod_type from Pmod_ident, or extract from typed structure
            let final_mod_type = semantic_mod_type.or_else(|| {
                let mut resolve_ident_sig =
                    |lid: &Located<LidentIdx>,
                     include_env: Option<&Env>|
                     -> Option<crate::types::decl::Signature> {
                        let include_env = include_env?;
                        let longident = arena.get_longident(lid.txt);
                        let mod_type = lookup_module_type_by_lid(
                            longident,
                            arena,
                            include_env,
                            &mut tctx.persistent_env,
                            tctx.type_ctx,
                        )?;
                        resolve_mod_type_to_sig(
                            &mod_type,
                            Some(include_env),
                            &mut tctx.persistent_env,
                            tctx.type_ctx,
                        )
                    };
                extract_module_type_from_mod_expr_with_resolver(
                    &typed_mod,
                    Some(env),
                    Some(tctx.type_ctx),
                    &mut resolve_ident_sig,
                )
            });
            if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                let mod_name = mod_name_str;
                match &final_mod_type {
                    Some(crate::types::decl::ModuleType::MtySignature(sig)) => {
                        eprintln!(
                            "[module-type] module={} kind=signature items={}",
                            mod_name,
                            sig.len()
                        );
                        for item in sig {
                            if let crate::types::decl::SignatureItem::SigValue(id, _) = item {
                                eprintln!("[module-type] module={} sigvalue {}", mod_name, id.name());
                            }
                        }
                    }
                    Some(crate::types::decl::ModuleType::MtyFunctor { .. }) => {
                        eprintln!("[module-type] module={} kind=functor", mod_name);
                    }
                    Some(crate::types::decl::ModuleType::MtyIdent(path)) => {
                        eprintln!("[module-type] module={} kind=ident path={}", mod_name, path.name());
                    }
                    Some(crate::types::decl::ModuleType::MtyAlias(_, path)) => {
                        eprintln!("[module-type] module={} kind=alias path={}", mod_name, path.name());
                    }
                    None => eprintln!("[module-type] module={} kind=none", mod_name),
                }
            }
            if std::env::var_os("RUST_DEBUG_CSV_MODULE_SIG").is_some() && mod_name_str == "Csv" {
                if let Some(crate::types::decl::ModuleType::MtySignature(sig)) = &final_mod_type {
                    eprintln!("[csv-module-sig] raw module=Csv items={}", sig.len());
                    for item in sig {
                        match item {
                            crate::types::decl::SignatureItem::SigType(id, decl, _) => {
                                let manifest = decl.type_manifest.map(|ty| {
                                    let ty = tctx.type_ctx.repr(ty);
                                    let desc = tctx.type_ctx.get_desc(ty);
                                    match &*desc {
                                        crate::types::type_expr::TypeDesc::Tconstr { path, .. } => {
                                            path.name()
                                        }
                                        crate::types::type_expr::TypeDesc::Tvariant(row) => {
                                            let mut fields = Vec::new();
                                            for (label, field) in &row.row_fields {
                                                let entry = match field {
                                                    crate::types::type_expr::RowField::Rpresent(Some(arg)) => {
                                                        let arg = tctx.type_ctx.repr(*arg);
                                                        let arg_desc = tctx.type_ctx.get_desc(arg);
                                                        match &*arg_desc {
                                                            crate::types::type_expr::TypeDesc::Tconstr { path, .. } => {
                                                                format!("{}:{}", label, path.name())
                                                            }
                                                            other => format!("{}:{:?}", label, other),
                                                        }
                                                    }
                                                    crate::types::type_expr::RowField::Rpresent(None) => {
                                                        format!("{}:None", label)
                                                    }
                                                    other => format!("{}:{:?}", label, other),
                                                };
                                                fields.push(entry);
                                            }
                                            format!("Tvariant[{}]", fields.join(","))
                                        }
                                        other => format!("{:?}", other),
                                    }
                                }).unwrap_or_else(|| "None".to_string());
                                eprintln!(
                                    "[csv-module-sig] raw type name={} type_path={} manifest={}",
                                    id.name(),
                                    decl.type_path
                                        .as_ref()
                                        .map(|p| p.name())
                                        .unwrap_or_else(|| "<none>".to_string()),
                                    manifest
                                );
                            }
                            crate::types::decl::SignatureItem::SigValue(id, vd) => {
                                if id.name() == "success" {
                                    let mut cursor = tctx.type_ctx.repr(vd.val_type);
                                    let mut parts = Vec::new();
                                    for _ in 0..8 {
                                        let desc = tctx.type_ctx.get_desc(cursor);
                                        match &*desc {
                                            crate::types::type_expr::TypeDesc::Tarrow { arg, ret, .. } => {
                                                let arg = tctx.type_ctx.repr(arg.typ);
                                                let arg_desc = tctx.type_ctx.get_desc(arg);
                                                let arg_summary = match &*arg_desc {
                                                    crate::types::type_expr::TypeDesc::Tconstr { path, .. } => path.name(),
                                                    other => format!("{:?}", other),
                                                };
                                                parts.push(format!("arg:{}", arg_summary));
                                                cursor = tctx.type_ctx.repr(*ret);
                                            }
                                            crate::types::type_expr::TypeDesc::Tconstr { path, .. } => {
                                                parts.push(format!("ret:{}", path.name()));
                                                break;
                                            }
                                            other => {
                                                parts.push(format!("ret:{:?}", other));
                                                break;
                                            }
                                        }
                                    }
                                    eprintln!("[csv-module-sig] raw value success {}", parts.join(" -> "));
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            let mut new_env = env.clone();
            let item_sig_mod_type = if let Some(decl_mod_type) = final_mod_type {
                let mut decl_mod_type = decl_mod_type;
                anchor_local_module_aliases_to_owner(
                    &mut decl_mod_type,
                    &Path::pident(mod_id.clone()),
                );
                if let crate::types::decl::ModuleType::MtySignature(sig) = &decl_mod_type {
                    let should_substitute_sig_paths = !matches!(
                        &*arena.get_mod_expr(mb.pmb_expr).pmod_desc,
                        ParsedModuleExprDesc::Pmod_structure(_)
                    );
                    if should_substitute_sig_paths {
                        let sig =
                            crate::types::typecore::copy_lookup_signature_for_subst(sig, tctx.type_ctx);
                        crate::cmi::persistent_env::substitute_type_paths_in_sig(
                            &sig,
                            &Path::pident(mod_id.clone()),
                            tctx.type_ctx,
                        );
                        decl_mod_type = crate::types::decl::ModuleType::MtySignature(sig);
                    }
                }
                // Match OCaml typemod.ml:
                // Mtype.lower_nongen (Ident.binding_time id - 1) md.md_type
                crate::types::ctype::lower_nongen_module_type(
                    tctx.type_ctx,
                    mod_id.binding_time() - 1,
                    &decl_mod_type,
                );
                let item_sig_mod_type = match &decl_mod_type {
                    crate::types::decl::ModuleType::MtyIdent(_)
                    | crate::types::decl::ModuleType::MtyAlias(_, _) => resolve_mod_type_to_sig(
                        &decl_mod_type,
                        Some(env),
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )
                    .map(|sig| {
                        let sig = crate::types::typecore::copy_lookup_signature_for_subst(
                            &sig,
                            tctx.type_ctx,
                        );
                        crate::cmi::persistent_env::substitute_type_paths_in_sig(
                            &sig,
                            &Path::pident(mod_id.clone()),
                            tctx.type_ctx,
                        );
                        crate::types::decl::ModuleType::MtySignature(sig)
                    })
                    .unwrap_or_else(|| decl_mod_type.clone()),
                    _ => decl_mod_type.clone(),
                };
                new_env.add_module(
                    mod_id.clone(),
                    crate::types::decl::ModuleDeclaration {
                        md_type: decl_mod_type.clone(),
                        md_attributes: vec![],
                        md_loc: crate::location::Location::none(),
                        md_path: None,
                    },
                );
                item_sig_mod_type
            } else {
                decl_module_type_from_typed_module_expr_for_sig(&typed_mod)
                    .unwrap_or_else(|| crate::types::decl::ModuleType::MtySignature(vec![]))
            };
            let item_sig = vec![crate::types::decl::SignatureItem::SigModule(
                mod_id.clone(),
                crate::types::decl::ModuleDeclaration {
                    md_type: item_sig_mod_type,
                    md_attributes: vec![],
                    md_loc: crate::location::Location::none(),
                    md_path: None,
                },
                crate::types::decl::RecStatus::TrecNot,
            )];

            let desc = StructureItemDesc::Tstr_module(ModuleBinding {
                mb_id: mod_id,
                mb_name: Located {
                    txt: mod_name_str.to_string(),
                    loc: mb.pmb_name.loc,
                },
                mb_expr: typed_mod,
                mb_attributes: mb.pmb_attributes.clone(),
                mb_loc: mb.pmb_loc,
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                item_sig,
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_recmodule(mbs) => {
            // Recursive modules: module rec M = ...
            let ctx = tctx.type_ctx;
            ctx.init_def(ctx.current_stamp());
            // First pass: extract module types from constraints and add to env
            let mut rec_env = env.clone();
            let mut mod_ids = Vec::new();
            for mb in mbs.iter() {
                let mod_name_str = arena.get_string(mb.pmb_name.txt);
                let mod_id = Ident::create_local(mod_name_str);
                // Try to extract type from Pmod_constraint (module rec A: SIG = BODY)
                let init_mod_type = match &*arena.get_mod_expr(mb.pmb_expr).pmod_desc {
                    ParsedModuleExprDesc::Pmod_constraint(_, mty) => {
                        translate_module_type_to_decl(tctx, env, arena, arena.get_mod_type(*mty))
                            .ok()
                    }
                    _ => None,
                }
                .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![]));
                crate::types::ctype::lower_nongen_module_type(
                    tctx.type_ctx,
                    mod_id.binding_time() - 1,
                    &init_mod_type,
                );
                rec_env.add_module(
                    mod_id.clone(),
                    crate::types::decl::ModuleDeclaration {
                        md_type: init_mod_type,
                        md_attributes: vec![],
                        md_loc: crate::location::Location::none(),
                        md_path: None,
                    },
                );
                mod_ids.push(mod_id);
            }

            // Second pass: type-check each module body with the env containing all modules
            // Match OCaml: for Pmod_constraint(expr, typ), type-check only expr (inner body),
            // then wrap in Tmod_constraint with mod_loc from the inner module (not the
            // constraint wrapper). OCaml does this in check_recmodule_inclusion.
            let mut typed_bindings = Vec::new();
            let mut binding_mod_types = Vec::new();
            let mut new_env = env.clone();
            for (i, mb) in mbs.iter().enumerate() {
                let typed_mod = match &*arena.get_mod_expr(mb.pmb_expr).pmod_desc {
                    ParsedModuleExprDesc::Pmod_constraint(inner_expr, mty) => {
                        let typed_inner =
                            type_module_expr(tctx, &rec_env, arena, arena.get_mod_expr(*inner_expr))?;
                        let typed_mty =
                            transl_modtype(tctx, &rec_env, arena, arena.get_mod_type(*mty))?;
                        let inner_loc = typed_inner.mod_loc;
                        ModuleExpr {
                            mod_desc: ModuleExprDesc::Tmod_constraint(
                                Box::new(typed_inner),
                                typed_mty.clone(),
                                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(
                                    Box::new(typed_mty),
                                ),
                                ModuleCoercion::Tcoerce_none,
                            ),
                            mod_loc: inner_loc,
                            mod_type: ModuleType::placeholder(),
                            mod_env: EnvRef(0),
                            mod_attributes: Attributes::new(),
                        }
                    }
                    _ => type_module_expr(tctx, &rec_env, arena, arena.get_mod_expr(mb.pmb_expr))?,
                };
                let mod_id = mod_ids[i].clone();
                let mod_name_str = arena.get_string(mb.pmb_name.txt);

                // Extract real module type and add to returned environment.
                // Fall back to the declared recmodule signature when extraction fails,
                // or when the body is a self-identifier alias (`module rec M = M`) so we
                // don't lose the explicit signature.
                let fallback_mod_type = rec_env
                    .find_module(mod_name_str)
                    .ok()
                    .map(|md| md.md_type.clone());
                let extracted_mod_type = {
                    let mut resolve_ident_sig =
                        |lid: &Located<LidentIdx>,
                         include_env: Option<&Env>|
                         -> Option<crate::types::decl::Signature> {
                            let include_env = include_env?;
                            let longident = arena.get_longident(lid.txt);
                            let mod_type = lookup_module_type_by_lid(
                                longident,
                                arena,
                                include_env,
                                &mut tctx.persistent_env,
                                tctx.type_ctx,
                            )?;
                            resolve_mod_type_to_sig(
                                &mod_type,
                                Some(include_env),
                                &mut tctx.persistent_env,
                                tctx.type_ctx,
                            )
                        };
                    extract_module_type_from_mod_expr_with_resolver(
                        &typed_mod,
                        Some(&rec_env),
                        Some(tctx.type_ctx),
                        &mut resolve_ident_sig,
                    )
                };
                let mod_type = match extracted_mod_type {
                    Some(crate::types::decl::ModuleType::MtyIdent(Path::Pident(id)))
                        if id.name() == mod_name_str =>
                    {
                        fallback_mod_type.clone()
                    }
                    Some(crate::types::decl::ModuleType::MtyAlias(_, Path::Pident(id)))
                        if id.name() == mod_name_str =>
                    {
                        fallback_mod_type.clone()
                    }
                    Some(mty) => Some(mty),
                    None => fallback_mod_type.clone(),
                }
                .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![]));
                crate::types::ctype::lower_nongen_module_type(
                    tctx.type_ctx,
                    mod_id.binding_time() - 1,
                    &mod_type,
                );
                new_env.add_module(
                    mod_id.clone(),
                    crate::types::decl::ModuleDeclaration {
                        md_type: mod_type.clone(),
                        md_attributes: vec![],
                        md_loc: crate::location::Location::none(),
                        md_path: None,
                    },
                );
                binding_mod_types.push(mod_type.clone());

                typed_bindings.push(ModuleBinding {
                    mb_id: mod_id,
                    mb_name: Located {
                        txt: mod_name_str.to_string(),
                        loc: mb.pmb_name.loc,
                    },
                    mb_expr: typed_mod,
                    mb_attributes: mb.pmb_attributes.clone(),
                    mb_loc: mb.pmb_loc,
                });
            }
            let item_sig = typed_bindings
                .iter()
                .enumerate()
                .map(|(index, mb)| {
                    crate::types::decl::SignatureItem::SigModule(
                        mb.mb_id.clone(),
                        crate::types::decl::ModuleDeclaration {
                            md_type: binding_mod_types[index].clone(),
                            md_attributes: vec![],
                            md_loc: crate::location::Location::none(),
                            md_path: None,
                        },
                        sig_rec_status(RecFlag::Recursive, index),
                    )
                })
                .collect();
            let desc = StructureItemDesc::Tstr_recmodule(typed_bindings);
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                item_sig,
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_modtype(mtd) => {
            // Module type declaration: module type S = MT
            let mtd_name_str = arena.get_string(mtd.pmtd_name.txt);
            let mtd_id = Ident::create_local(mtd_name_str);

            let typed_mty = match &mtd.pmtd_type {
                Some(mt) => Some(transl_modtype(tctx, env, arena, arena.get_mod_type(*mt))?),
                None => None,
            };

            // Convert the typed module type to a decl-level modtype declaration
            let decl_mtd_type = if let Some(mt) = &mtd.pmtd_type {
                translate_module_type_to_decl(tctx, env, arena, arena.get_mod_type(*mt)).ok()
            } else {
                None
            };

            let desc = StructureItemDesc::Tstr_modtype(ModuleTypeDeclaration {
                mtd_id: mtd_id.clone(),
                mtd_name: Located {
                    txt: mtd_name_str.to_string(),
                    loc: mtd.pmtd_name.loc,
                },
                mtd_type: typed_mty,
                mtd_attributes: mtd.pmtd_attributes.clone(),
                mtd_loc: mtd.pmtd_loc,
            });

            // Add the module type to the environment
            let mut new_env = env.clone();
            let decl_mtd = crate::types::decl::ModtypeDeclaration {
                mtd_type: decl_mtd_type,
                mtd_attributes: vec![],
                mtd_loc: crate::location::Location::none(),
            };
            new_env.add_modtype(mtd_id.clone(), decl_mtd.clone());

            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                vec![crate::types::decl::SignatureItem::SigModtype(
                    mtd_id,
                    decl_mtd,
                )],
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_open(open_desc) => {
            // Open declaration: open M
            let longident = tctx.resolve_lid(open_desc.popen_lid.txt).clone();
            let fallback_path = lookup_module_path_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or_else(|| path_from_longident(&longident, |idx| arena.get_string(idx)));

            // Extend the environment with the opened module's bindings using the
            // same alias-rewritten module resolution path as value lookup.
            let open_lid = arena.get_longident(open_desc.popen_lid.txt);
            let mut new_env = env.clone();
            let path = if let Some((resolved_path, sig_items)) =
                env.resolve_module_lid(open_lid, arena, &mut tctx.persistent_env, tctx.type_ctx)
            {
                crate::cmi::persistent_env::add_signature_to_env(
                    &sig_items,
                    &resolved_path,
                    &mut new_env,
                    tctx.type_ctx,
                    true,
                );
                resolved_path
            } else {
                fallback_path
            };

            let desc = StructureItemDesc::Tstr_open(OpenDeclaration {
                open_path: path,
                open_txt: open_desc.popen_lid.clone(),
                open_override: open_desc.popen_override,
                open_loc: open_desc.popen_loc,
                open_attributes: open_desc.popen_attributes.clone(),
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                vec![],
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_include(incl) => {
            // Include declaration: include ME
            // Resolve the module's signature to extend the environment
            let include_sig = {
                let parsed_include_mod = arena.get_mod_expr(incl.pincl_mod);
                let include_mty = match &*parsed_include_mod.pmod_desc {
                    // Keep parsed-path resolution for identifiers and functor applications
                    // where typed-module extraction often lacks a concrete module type.
                    ParsedModuleExprDesc::Pmod_ident(_)
                    | ParsedModuleExprDesc::Pmod_apply(_, _) => lookup_module_type_from_parsed_module_expr(
                        tctx,
                        env,
                        arena,
                        parsed_include_mod,
                    ),
                    // For constrained/structured includes, prefer typed extraction below;
                    // parsed module-type translation can carry nongeneralized vars.
                    _ => None,
                };
                if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                    let include_mty_kind = match include_mty.as_ref() {
                        Some(crate::types::decl::ModuleType::MtySignature(_)) => "mty-signature",
                        Some(crate::types::decl::ModuleType::MtyFunctor { .. }) => "mty-functor",
                        Some(crate::types::decl::ModuleType::MtyIdent(_)) => "mty-ident",
                        Some(crate::types::decl::ModuleType::MtyAlias(_, _)) => "mty-alias",
                        None => "none",
                    };
                    let include_mty_path = match include_mty.as_ref() {
                        Some(crate::types::decl::ModuleType::MtyIdent(path))
                        | Some(crate::types::decl::ModuleType::MtyAlias(_, path)) => path.name(),
                        _ => "<none>".to_string(),
                    };
                    eprintln!(
                        "[include-labels] parsed_include_mty={} path={}",
                        include_mty_kind, include_mty_path
                    );
                }
                include_mty
                    .and_then(|mt| {
                        resolve_mod_type_to_sig(
                            &mt,
                            Some(env),
                            &mut tctx.persistent_env,
                            tctx.type_ctx,
                        )
                    })
            };

            let typed_mod =
                type_module_expr(tctx, env, arena, arena.get_mod_expr(incl.pincl_mod))?;

            // Extend environment with all bindings from the included module
            // Also try to extract signature from typed module expr if not from Pmod_ident
            let mut resolve_ident_sig =
                |lid: &Located<LidentIdx>,
                 include_env: Option<&Env>|
                 -> Option<crate::types::decl::Signature> {
                    let include_env = include_env?;
                    let longident = arena.get_longident(lid.txt);
                    let mod_type = lookup_module_type_by_lid(
                        longident,
                        arena,
                        include_env,
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )?;
                    resolve_mod_type_to_sig(
                        &mod_type,
                        Some(include_env),
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )
                };
            let extracted_include_mty = extract_module_type_from_mod_expr_with_resolver(
                &typed_mod,
                Some(env),
                Some(tctx.type_ctx),
                &mut resolve_ident_sig,
            );
            if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                let typed_mod_kind = match &typed_mod.mod_desc {
                    crate::types::typedtree::ModuleExprDesc::Tmod_ident(_, _) => "ident",
                    crate::types::typedtree::ModuleExprDesc::Tmod_structure(_) => "structure",
                    crate::types::typedtree::ModuleExprDesc::Tmod_functor(_, _, _, _) => "functor",
                    crate::types::typedtree::ModuleExprDesc::Tmod_apply(_, _, _) => "apply",
                    crate::types::typedtree::ModuleExprDesc::Tmod_constraint(_, _, _, _) => "constraint",
                    crate::types::typedtree::ModuleExprDesc::Tmod_unpack(_, _) => "unpack",
                };
                let typed_mty_kind = match &typed_mod.mod_type.mty_desc {
                    crate::types::typedtree::ModuleTypeDesc::Tmty_ident(_, _) => "mty-ident",
                    crate::types::typedtree::ModuleTypeDesc::Tmty_alias(_, _) => "mty-alias",
                    crate::types::typedtree::ModuleTypeDesc::Tmty_signature(_) => "mty-signature",
                    crate::types::typedtree::ModuleTypeDesc::Tmty_functor(_, _, _, _) => "mty-functor",
                    crate::types::typedtree::ModuleTypeDesc::Tmty_with(_, _) => "mty-with",
                    crate::types::typedtree::ModuleTypeDesc::Tmty_typeof(_) => "mty-typeof",
                    crate::types::typedtree::ModuleTypeDesc::Tmty_placeholder => "mty-placeholder",
                };
                let extracted_kind = match extracted_include_mty.as_ref() {
                    Some(crate::types::decl::ModuleType::MtySignature(_)) => "mty-signature",
                    Some(crate::types::decl::ModuleType::MtyFunctor { .. }) => "mty-functor",
                    Some(crate::types::decl::ModuleType::MtyIdent(_)) => "mty-ident",
                    Some(crate::types::decl::ModuleType::MtyAlias(_, _)) => "mty-alias",
                    None => "none",
                };
                eprintln!(
                    "[include-labels] typed_mod={} typed_mty={} extracted_mty={}",
                    typed_mod_kind,
                    typed_mty_kind,
                    extracted_kind
                );
            }
            let final_include_sig = include_sig.or_else(|| {
                extracted_include_mty.and_then(|mty| {
                    resolve_mod_type_to_sig(
                        &mty,
                        Some(env),
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )
                })
            });
            let localized_include_sig = final_include_sig.as_ref().map(|sig_items| {
                let mut sig =
                    crate::types::typecore::copy_lookup_signature_for_subst(sig_items, tctx.type_ctx);
                let include_root_path = include_module_root_path(&typed_mod);
                let include_flat_name = include_module_flat_name(&typed_mod);
                let local_include_types: HashMap<String, Ident> = sig
                    .iter()
                    .filter_map(|item| match item {
                        crate::types::decl::SignatureItem::SigType(id, _, _) => {
                            Some((id.name().to_string(), id.clone()))
                        }
                        _ => None,
                    })
                    .collect();
                let local_include_modules: HashMap<String, Ident> = sig
                    .iter()
                    .filter_map(|item| match item {
                        crate::types::decl::SignatureItem::SigModule(id, _, _) => {
                            Some((id.name().to_string(), id.clone()))
                        }
                        _ => None,
                    })
                    .collect();
                let local_include_modtypes: HashMap<String, Ident> = sig
                    .iter()
                    .filter_map(|item| match item {
                        crate::types::decl::SignatureItem::SigModtype(id, _) => {
                            Some((id.name().to_string(), id.clone()))
                        }
                        _ => None,
                    })
                    .collect();
                if include_root_path.is_some() || include_flat_name.is_some() {
                    let mut visited = HashSet::new();
                    rewrite_included_signature_paths_to_local(
                        tctx.type_ctx,
                        &mut sig,
                        include_root_path.as_ref(),
                        include_flat_name.as_deref(),
                        &local_include_types,
                        &local_include_modules,
                        &local_include_modtypes,
                        &mut visited,
                    );
                }
                sig
            });
            let mut new_env = env.clone();
            if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                match &localized_include_sig {
                    Some(sig_items) => {
                        eprintln!("[include-labels] include-sig-items={}", sig_items.len())
                    }
                    None => eprintln!("[include-labels] include-sig-items=NONE"),
                }
            }
            if let Some(sig_items) = &localized_include_sig {
                // OCaml's include adds all signature items directly to the environment
                // as if they were defined locally (Pident paths, not Pdot paths).
                // This matches OCaml's Env.add_signature behavior.
                for item in sig_items {
                    match item {
                        crate::types::decl::SignatureItem::SigValue(id, desc) => {
                            if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                                eprintln!("[include-labels] sigvalue {}", id.name());
                            }
                            new_env.add_value(id.clone(), desc.clone());
                        }
                        crate::types::decl::SignatureItem::SigType(id, decl, _) => {
                            if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                                let kind = match &decl.type_kind {
                                    crate::types::TypeKind::TypeRecord(_, _) => "record",
                                    crate::types::TypeKind::TypeVariant(_) => "variant",
                                    crate::types::TypeKind::TypeAbstract => "abstract",
                                    crate::types::TypeKind::TypeOpen => "open",
                                };
                                eprintln!("[include-labels] sigtype {} kind={}", id.name(), kind);
                            }
                            new_env.add_type(id.clone(), decl.clone());
                            if let crate::types::TypeKind::TypeVariant(constructors) =
                                &decl.type_kind
                            {
                                // Include should expose constructors from included variant types
                                // in the current scope, matching OCaml's Env.add_signature.
                                let ty_res = tctx.type_ctx.new_constr(
                                    crate::types::path::Path::Pident(id.clone()),
                                    decl.type_params.clone(),
                                );
                                crate::types::ctype::force_generalize_sig_type(
                                    tctx.type_ctx,
                                    ty_res,
                                );

                                let num_consts = constructors
                                    .iter()
                                    .filter(|c| {
                                        matches!(
                                            c.cd_args,
                                            crate::types::decl::ConstructorArguments::CstrTuple(
                                                ref args
                                            ) if args.is_empty()
                                        ) && c.cd_res.is_none()
                                    })
                                    .count() as i32;
                                let num_nonconsts = constructors.len() as i32 - num_consts;
                                let mut const_idx = 0i32;
                                let mut nonconst_idx = 0i32;

                                for cd in constructors {
                                    let is_constant = matches!(
                                        cd.cd_args,
                                        crate::types::decl::ConstructorArguments::CstrTuple(
                                            ref args
                                        ) if args.is_empty()
                                    ) && cd.cd_res.is_none();

                                    let cstr_tag = if is_constant {
                                        let tag =
                                            crate::types::decl::ConstructorTag::CstrConstant(const_idx);
                                        const_idx += 1;
                                        tag
                                    } else {
                                        let tag =
                                            crate::types::decl::ConstructorTag::CstrBlock(nonconst_idx);
                                        nonconst_idx += 1;
                                        tag
                                    };

                                    let (cstr_args, cstr_arity) = match &cd.cd_args {
                                        crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                            (args.clone(), args.len() as i32)
                                        }
                                        crate::types::decl::ConstructorArguments::CstrRecord(
                                            labels,
                                        ) => {
                                            let args: Vec<crate::types::TypeExprRef> =
                                                labels.iter().map(|l| l.ld_type).collect();
                                            (args.clone(), args.len() as i32)
                                        }
                                    };
                                    for arg in &cstr_args {
                                        crate::types::ctype::force_generalize_sig_type(
                                            tctx.type_ctx,
                                            *arg,
                                        );
                                    }

                                    let cstr_res = if let Some(res_ty) = cd.cd_res {
                                        crate::types::ctype::force_generalize_sig_type(
                                            tctx.type_ctx,
                                            res_ty,
                                        );
                                        res_ty
                                    } else {
                                        ty_res
                                    };

                                    let cstr_existentials =
                                        crate::types::env::constructor_existentials(
                                            tctx.type_ctx,
                                            &cstr_args,
                                            cd.cd_res,
                                        );
                                    let cstr_desc = crate::types::ConstructorDescription {
                                        cstr_name: cd.cd_id.name().to_string(),
                                        cstr_res,
                                        cstr_existentials,
                                        cstr_args,
                                        cstr_arity,
                                        cstr_tag,
                                        cstr_consts: num_consts,
                                        cstr_nonconsts: num_nonconsts,
                                        cstr_generalized: cd.cd_res.is_some(),
                                        cstr_private: decl.type_private,
                                        cstr_loc: cd.cd_loc,
                                        cstr_attributes: cd.cd_attributes.clone(),
                                        cstr_inlined: None,
                                    };
                                    new_env.add_constructor(cd.cd_id.clone(), cstr_desc);
                                }
                            }
                            if let crate::types::TypeKind::TypeRecord(labels, repres) =
                                &decl.type_kind
                            {
                                if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                                    eprintln!(
                                        "[include-labels] type={} labels={}",
                                        id.name(),
                                        labels.len()
                                    );
                                }
                                // Include should expose record labels from included types
                                // in the current scope, matching OCaml's Env.add_signature.
                                let ty_res = tctx.type_ctx.new_constr(
                                    crate::types::path::Path::Pident(id.clone()),
                                    decl.type_params.clone(),
                                );
                                // Include signatures can carry non-generic nodes in Rust.
                                // Promote the shared label scheme to generic-level so
                                // instance_label can instantiate fresh per-use copies.
                                crate::types::ctype::force_generalize_sig_type(tctx.type_ctx, ty_res);
                                for (pos, ld) in labels.iter().enumerate() {
                                    let lbl_arg = crate::types::ctype::remap_label_type_to_params(
                                        tctx.type_ctx,
                                        ld.ld_type,
                                        &decl.type_params,
                                    );
                                    crate::types::ctype::force_generalize_sig_type(
                                        tctx.type_ctx,
                                        lbl_arg,
                                    );
                                    let lbl_desc = crate::types::LabelDescription {
                                        lbl_name: ld.ld_id.name().to_string(),
                                        lbl_res: ty_res,
                                        lbl_arg,
                                        lbl_mut: ld.ld_mutable.clone(),
                                        lbl_optional: ld.ld_optional,
                                        lbl_pos: pos as i32,
                                        lbl_all: crate::types::LabelArrayRef(0),
                                        lbl_repres: repres.clone(),
                                        lbl_private: decl.type_private,
                                        lbl_loc: ld.ld_loc.clone(),
                                        lbl_attributes: ld.ld_attributes.clone(),
                                    };
                                    if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                                        eprintln!(
                                            "[include-labels] add {} for type {}",
                                            ld.ld_id.name(),
                                            id.name()
                                        );
                                    }
                                    new_env.add_label(ld.ld_id.clone(), lbl_desc);
                                }
                            }
                        }
                        crate::types::decl::SignatureItem::SigModule(id, md, _) => {
                            if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                                eprintln!("[include-labels] sigmodule {}", id.name());
                            }
                            new_env.add_module(id.clone(), md.clone());
                        }
                        crate::types::decl::SignatureItem::SigModtype(id, mtd) => {
                            if std::env::var_os("RUST_DEBUG_INCLUDE_LABELS").is_some() {
                                eprintln!("[include-labels] sigmodtype {}", id.name());
                            }
                            new_env.add_modtype(id.clone(), mtd.clone());
                        }
                        _ => {}
                    }
                }
            }

            let item_sig = localized_include_sig.unwrap_or_default();
            let desc = StructureItemDesc::Tstr_include(IncludeDeclaration {
                incl_mod: typed_mod,
                incl_type: item_sig.clone(),
                incl_attributes: incl.pincl_attributes.clone(),
                incl_loc: incl.pincl_loc,
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                item_sig,
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_attribute(attr) => {
            // Attribute: @@attr
            let desc = StructureItemDesc::Tstr_attribute((**attr).clone());
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                vec![],
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_extension(inner) => {
            let (ref _ext, ref _attrs) = **inner;
            // Extension: [%%id]
            // Extensions like %%raw are expanded by the PPX pass before type checking.
            // If we get here, the extension wasn't expanded. Return a placeholder.
            let ctx = tctx.type_ctx;
            let unit_ty = ctx.new_tuple(vec![]);
            let desc = StructureItemDesc::Tstr_eval(
                Expression::new(
                    crate::types::typedtree::ExpressionDesc::Texp_constant(
                        crate::types::typedtree::Constant::Int(0),
                    ),
                    loc.clone(),
                    unit_ty,
                    EnvRef(0),
                    Attributes::new(),
                ),
                Attributes::new(),
            );
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                vec![],
                env.clone(),
            ))
        }
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Type check value bindings in a structure.
fn type_value_bindings<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    rec_flag: RecFlag,
    bindings: &[crate::parser::ast::ValueBinding],
) -> TypeModResult<(Vec<ValueBinding>, Env)> {
    // Match OCaml typemod.ml Pstr_value:
    // use the environment returned by type_binding directly.
    let (typed_bindings, new_env) = type_binding(tctx, env, rec_flag, bindings)?;
    Ok((typed_bindings, new_env))
}

// ============================================================================
// Signature Type Declaration Translation
// ============================================================================

/// Translate type declarations in a signature.
/// Simplified version of the Pstr_type handler for use in signature items.
fn transl_sig_type_declarations<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    decls: &[crate::parser::ast::TypeDeclaration],
) -> TypeModResult<Vec<TypedTypeDeclaration>> {
    let ctx = tctx.type_ctx;
    let mut typed_tree_decls = Vec::new();
    let mut internal_decls_for_generalize: Vec<crate::types::TypeDeclaration> = Vec::new();

    // Match OCaml Typedecl.transl_type_decl flow for signatures:
    // translate inside begin_def/end_def, then generalize declarations.
    ctx.begin_def();
    let loop_result: TypeModResult<()> = (|| {
    for decl in decls {
        let type_name = decl.ptype_name.txt;
        let type_name_str = arena.get_string(type_name);
        let type_id = Ident::create_local(type_name_str);

        // OCaml: reset_type_variables() before each type declaration
        tctx.type_variables.clear();

        // Convert type parameters
        let mut typ_params: Vec<(TypedCoreType, TypesVariance)> = Vec::new();
        let mut internal_type_params: Vec<TypeExprRef> = Vec::new();
        for (core_type_idx, parser_var) in &decl.ptype_params {
            let core_type = arena.get_core_type(*core_type_idx);
            let (typed_core_type, type_ref) = match &*core_type.ptyp_desc {
                crate::parser::ast::CoreTypeDesc::Ptyp_any => {
                    let type_ref = ctx.new_var(Some("_".to_string()));
                    (
                        TypedCoreType {
                            ctyp_desc: TypedCoreTypeDesc::Ttyp_var(None),
                            ctyp_type: type_ref,
                            ctyp_env: EnvRef(0),
                            ctyp_loc: core_type.ptyp_loc,
                            ctyp_attributes: core_type.ptyp_attributes.clone(),
                        },
                        type_ref,
                    )
                }
                crate::parser::ast::CoreTypeDesc::Ptyp_var(name) => {
                    let type_ref = ctx.new_var(Some(name.to_string()));
                    (
                        TypedCoreType {
                            ctyp_desc: TypedCoreTypeDesc::Ttyp_var(Some(name.to_string())),
                            ctyp_type: type_ref,
                            ctyp_env: EnvRef(0),
                            ctyp_loc: core_type.ptyp_loc,
                            ctyp_attributes: core_type.ptyp_attributes.clone(),
                        },
                        type_ref,
                    )
                }
                _ => transl_type(tctx, env, core_type)?,
            };
            internal_type_params.push(type_ref);
            // Insert type params into type_variables so record field/manifest
            // translation can find them and share the same Tvar node.
            // Matches OCaml's transl_type_param which inserts into type_variables.
            if let crate::parser::ast::CoreTypeDesc::Ptyp_var(name) = &*core_type.ptyp_desc {
                tctx.type_variables.insert(name.to_string(), type_ref);
            }
            let types_var = match parser_var {
                ParserVariance::Covariant => TypesVariance::covariant(),
                ParserVariance::Contravariant => TypesVariance::contravariant(),
                ParserVariance::Invariant => TypesVariance::null(),
            };
            typ_params.push((typed_core_type, types_var));
        }

        // Convert type constraints
        let mut typ_cstrs: Vec<(TypedCoreType, TypedCoreType, LocIdx)> = Vec::new();
        for (ct1, ct2, cstr_loc) in &decl.ptype_cstrs {
            let (typed_ct1, _) = transl_type(tctx, env, arena.get_core_type(*ct1))?;
            let (typed_ct2, _) = transl_type(tctx, env, arena.get_core_type(*ct2))?;
            typ_cstrs.push((typed_ct1, typed_ct2, *cstr_loc));
        }

        // Convert manifest type (type alias)
        let (typ_manifest, manifest_type_ref) = match &decl.ptype_manifest {
            Some(manifest) => {
                let (typed_manifest, manifest_ref) = transl_type(tctx, env, arena.get_core_type(*manifest))?;
                (Some(typed_manifest), Some(manifest_ref))
            }
            None => (None, None),
        };

        // Preserve signature type kind like OCaml transl_signature -> Typedecl.transl_type_decl.
        let (internal_type_kind, typed_tree_kind) = match &decl.ptype_kind {
            crate::parser::ast::TypeKind::Ptype_abstract => {
                (crate::types::TypeKind::TypeAbstract, TypedTypeKind::Ttype_abstract)
            }
            crate::parser::ast::TypeKind::Ptype_open => {
                (crate::types::TypeKind::TypeOpen, TypedTypeKind::Ttype_open)
            }
            crate::parser::ast::TypeKind::Ptype_record(labels) => {
                let mut internal_labels = Vec::with_capacity(labels.len());
                let mut typed_tree_labels = Vec::with_capacity(labels.len());

                for label in labels {
                    let lbl_name = arena.get_string(label.pld_name.txt);
                    let (typed_label_ty, mut lbl_type) = transl_type(tctx, env, arena.get_core_type(label.pld_type))?;
                    if label.pld_optional {
                        let option_path = Path::pident(Ident::create_persistent("option"));
                        lbl_type = tctx.type_ctx.new_constr(option_path, vec![lbl_type]);
                    }
                    let (poly_typed_core_type, poly_lbl_type) =
                        force_poly_typed_core_type(tctx.type_ctx, typed_label_ty, lbl_type);
                    let internal_lbl_type = match &*tctx.type_ctx.get_desc(poly_lbl_type) {
                        crate::types::type_expr::TypeDesc::Tpoly { body, vars } if vars.is_empty() => *body,
                        _ => poly_lbl_type,
                    };
                    let mutable_flag = match label.pld_mutable {
                        crate::parser::ast::MutableFlag::Immutable => {
                            crate::types::MutableFlag::Immutable
                        }
                        crate::parser::ast::MutableFlag::Mutable => {
                            crate::types::MutableFlag::Mutable
                        }
                    };
                    internal_labels.push(crate::types::LabelDeclaration {
                        ld_id: Ident::create_persistent(lbl_name),
                        ld_mutable: mutable_flag,
                        ld_optional: label.pld_optional,
                        ld_type: internal_lbl_type,
                        ld_loc: arena.to_location(label.pld_loc),
                        ld_attributes: parser_attrs_to_decl_attrs(
                            arena,
                            &label.pld_attributes,
                        ),
                    });

                    typed_tree_labels.push(TypedLabelDeclaration {
                        ld_id: Ident::create_persistent(lbl_name),
                        ld_name: Located {
                            txt: lbl_name.to_string(),
                            loc: label.pld_name.loc,
                        },
                        ld_mutable: label.pld_mutable,
                        ld_optional: label.pld_optional,
                        ld_type: poly_typed_core_type,
                        ld_loc: label.pld_loc,
                        ld_attributes: label.pld_attributes.clone(),
                    });
                }

                (
                    crate::types::TypeKind::TypeRecord(
                        internal_labels,
                        crate::types::RecordRepresentation::RecordRegular,
                    ),
                    TypedTypeKind::Ttype_record(typed_tree_labels),
                )
            }
            crate::parser::ast::TypeKind::Ptype_variant(cstrs) => {
                let mut internal_cstrs = Vec::with_capacity(cstrs.len());
                let mut typed_tree_cstrs = Vec::with_capacity(cstrs.len());
                let tag_attrs: Vec<_> = decl
                    .ptype_attributes
                    .iter()
                    .filter(|attr| {
                        let name = arena.get_string(attr.0.txt);
                        name == "unboxed" || name == "tag"
                    })
                    .cloned()
                    .collect();

                for cstr in cstrs {
                    let cstr_name = arena.get_string(cstr.pcd_name.txt);
                    let (internal_args, typed_args) = match &cstr.pcd_args {
                        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
                            let mut internal_tuple_args = Vec::with_capacity(args.len());
                            let mut typed_tuple_args = Vec::with_capacity(args.len());
                            for arg in args {
                                let (typed_arg, arg_ref) = transl_type(tctx, env, arena.get_core_type(*arg))?;
                                internal_tuple_args.push(arg_ref);
                                typed_tuple_args.push(typed_arg);
                            }
                            (
                                crate::types::ConstructorArguments::CstrTuple(internal_tuple_args),
                                TypedConstructorArguments::Cstr_tuple(typed_tuple_args),
                            )
                        }
                        crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                            let mut internal_record_labels = Vec::with_capacity(labels.len());
                            let mut typed_record_labels = Vec::with_capacity(labels.len());
                            for label in labels {
                                let lbl_name = arena.get_string(label.pld_name.txt);
                                let (typed_label_ty, mut lbl_type) =
                                    transl_type(tctx, env, arena.get_core_type(label.pld_type))?;
                                if label.pld_optional {
                                    let option_path =
                                        Path::pident(Ident::create_persistent("option"));
                                    lbl_type = tctx.type_ctx.new_constr(option_path, vec![lbl_type]);
                                }
                                let (poly_typed_core_type, poly_lbl_type) =
                                    force_poly_typed_core_type(tctx.type_ctx, typed_label_ty, lbl_type);
                                let internal_lbl_type = match &*tctx.type_ctx.get_desc(poly_lbl_type) {
                                    crate::types::type_expr::TypeDesc::Tpoly { body, vars } if vars.is_empty() => *body,
                                    _ => poly_lbl_type,
                                };
                                let mutable_flag = match label.pld_mutable {
                                    crate::parser::ast::MutableFlag::Immutable => {
                                        crate::types::MutableFlag::Immutable
                                    }
                                    crate::parser::ast::MutableFlag::Mutable => {
                                        crate::types::MutableFlag::Mutable
                                    }
                                };
                                internal_record_labels.push(crate::types::LabelDeclaration {
                                    ld_id: Ident::create_persistent(lbl_name),
                                    ld_mutable: mutable_flag,
                                    ld_optional: label.pld_optional,
                                    ld_type: internal_lbl_type,
                                    ld_loc: arena.to_location(label.pld_loc),
                                    ld_attributes: parser_attrs_to_decl_attrs(
                                        arena,
                                        &label.pld_attributes,
                                    ),
                                });
                                typed_record_labels.push(TypedLabelDeclaration {
                                    ld_id: Ident::create_persistent(lbl_name),
                                    ld_name: Located {
                                        txt: lbl_name.to_string(),
                                        loc: label.pld_name.loc,
                                    },
                                    ld_mutable: label.pld_mutable,
                                    ld_optional: label.pld_optional,
                                    ld_type: poly_typed_core_type,
                                    ld_loc: label.pld_loc,
                                    ld_attributes: label.pld_attributes.clone(),
                                });
                            }
                            (
                                crate::types::ConstructorArguments::CstrRecord(
                                    internal_record_labels,
                                ),
                                TypedConstructorArguments::Cstr_record(typed_record_labels),
                            )
                        }
                    };

                    let (typed_res, internal_res) = match &cstr.pcd_res {
                        Some(res_type) => {
                            let (typed, internal) = transl_type(tctx, env, arena.get_core_type(*res_type))?;
                            (Some(typed), Some(internal))
                        }
                        None => (None, None),
                    };

                    internal_cstrs.push(crate::types::ConstructorDeclaration {
                        cd_id: Ident::create_persistent(cstr_name),
                        cd_args: internal_args,
                        cd_res: internal_res,
                        cd_loc: arena.to_location(cstr.pcd_loc),
                        cd_attributes: {
                            let mut attrs = tag_attrs.clone();
                            attrs.extend(cstr.pcd_attributes.iter().cloned());
                            parser_attrs_to_decl_attrs(
                                arena,
                                &Attributes::from_vec(attrs),
                            )
                        },
                    });
                    typed_tree_cstrs.push(TypedConstructorDeclaration {
                        cd_id: Ident::create_persistent(cstr_name),
                        cd_name: Located {
                            txt: cstr_name.to_string(),
                            loc: cstr.pcd_name.loc,
                        },
                        cd_args: typed_args,
                        cd_res: typed_res,
                        cd_loc: cstr.pcd_loc,
                        cd_attributes: {
                            let mut attrs = tag_attrs.clone();
                            attrs.extend(cstr.pcd_attributes.iter().cloned());
                            Attributes::from_vec(attrs)
                        },
                    });
                }

                (
                    crate::types::TypeKind::TypeVariant(internal_cstrs),
                    TypedTypeKind::Ttype_variant(typed_tree_cstrs),
                )
            }
        };

        let typ_private = decl.ptype_private;

        // Keep internal declaration shape aligned with parsed signature declaration.
        let internal_decl = crate::types::TypeDeclaration {
            type_params: internal_type_params,
            type_arity: decl.ptype_params.len() as i32,
            type_kind: internal_type_kind,
            type_private: match typ_private {
                crate::parser::ast::PrivateFlag::Public => crate::types::PrivateFlag::Public,
                crate::parser::ast::PrivateFlag::Private => crate::types::PrivateFlag::Private,
            },
            type_manifest: manifest_type_ref,
            type_variance: typ_params.iter().map(|(_, variance)| *variance).collect(),
            type_newtype_level: None,
            type_loc: arena.to_location(decl.ptype_loc),
            type_attributes: parser_attrs_to_decl_attrs(arena, &decl.ptype_attributes),
            type_immediate: false,
            type_unboxed: crate::types::UnboxedStatus {
                unboxed: false,
                default: false,
            },
            type_inlined_types: vec![],
            type_path: Some(Path::pident(type_id.clone())),
        };
        internal_decls_for_generalize.push(internal_decl.clone());

        typed_tree_decls.push(TypedTypeDeclaration {
            typ_id: type_id,
            typ_name: crate::parse_arena::Located {
                txt: type_name_str.to_string(),
                loc: decl.ptype_name.loc,
            },
            typ_params,
            typ_type: internal_decl,
            typ_cstrs,
            typ_kind: typed_tree_kind,
            typ_private: typ_private,
            typ_manifest,
            typ_loc: decl.ptype_loc,
            typ_attributes: decl.ptype_attributes.clone(),
        });
    }
    Ok(())
    })();
    ctx.end_def();
    loop_result?;

    for decl in &internal_decls_for_generalize {
        for &param in &decl.type_params {
            crate::types::ctype::generalize(ctx, param);
        }
        crate::types::btype::iter_type_expr_kind(&decl.type_kind, |ty| {
            crate::types::ctype::generalize(ctx, ty);
        });
        if let Some(manifest) = decl.type_manifest {
            crate::types::ctype::generalize(ctx, manifest);
        }
    }

    Ok(typed_tree_decls)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_module_error_conversion() {
        let core_error = TypeCoreError::MultiplyBoundVariable("x".to_string());
        let mod_error: TypeModError = core_error.into();
        match mod_error {
            TypeModError::CoreError(_) => {}
            _ => panic!("Expected CoreError"),
        }
    }
}
