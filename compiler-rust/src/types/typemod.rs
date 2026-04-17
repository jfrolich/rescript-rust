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
    Attribute as ParsedAttribute, ModuleExpr as ParsedModuleExpr,
    ModuleExprDesc as ParsedModuleExprDesc, Payload as ParsedPayload,
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
use ahash::{AHashMap as HashMap, AHashSet as HashSet};

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
        ParsedPayload::PStr(items) => {
            // OCaml's Lambda.find_name: extract string from @as("name") payloads.
            // PStr with a single Pstr_eval(Pexp_constant(String(value, _)), _) → Str(value)
            if let [item] = items.as_slice() {
                if let crate::parser::ast::StructureItemDesc::Pstr_eval(eval_box) =
                    item.pstr_desc.as_ref()
                {
                    let (expr_idx, _attrs) = eval_box.as_ref();
                    let expr = arena.get_expr(*expr_idx);
                    if let crate::parser::ast::ExpressionDesc::Pexp_constant(c) =
                        expr.pexp_desc.as_ref()
                    {
                        match c.as_ref() {
                            crate::parser::ast::Constant::String(value, _) => {
                                crate::types::decl::AttributePayload::Str(value.to_string())
                            }
                            crate::parser::ast::Constant::Integer(value, suffix) => match suffix {
                                Some('n') => {
                                    crate::types::decl::AttributePayload::BigInt(value.to_string())
                                }
                                Some(_) => crate::types::decl::AttributePayload::Structure(vec![]),
                                None => value
                                    .parse::<i32>()
                                    .map(crate::types::decl::AttributePayload::Int)
                                    .unwrap_or_else(|_| {
                                        crate::types::decl::AttributePayload::Structure(vec![])
                                    }),
                            },
                            crate::parser::ast::Constant::Float(value, _) => {
                                crate::types::decl::AttributePayload::Float(value.to_string())
                            }
                            _ => crate::types::decl::AttributePayload::Structure(vec![]),
                        }
                    } else if let crate::parser::ast::ExpressionDesc::Pexp_ident(lid) =
                        expr.pexp_desc.as_ref()
                    {
                        // @as(undefined), @as(null) — identifier payloads
                        let name = arena.lident_last(lid.txt);
                        match name {
                            "true" => crate::types::decl::AttributePayload::Bool(true),
                            "false" => crate::types::decl::AttributePayload::Bool(false),
                            _ => crate::types::decl::AttributePayload::Ident(name.to_string()),
                        }
                    } else if let crate::parser::ast::ExpressionDesc::Pexp_construct(lid, None) =
                        expr.pexp_desc.as_ref()
                    {
                        match arena.lident_last(lid.txt) {
                            "true" => crate::types::decl::AttributePayload::Bool(true),
                            "false" => crate::types::decl::AttributePayload::Bool(false),
                            _ => crate::types::decl::AttributePayload::Structure(vec![]),
                        }
                    } else {
                        crate::types::decl::AttributePayload::Structure(vec![])
                    }
                } else {
                    crate::types::decl::AttributePayload::Structure(vec![])
                }
            } else {
                crate::types::decl::AttributePayload::Structure(vec![])
            }
        }
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
    attrs
        .iter()
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

fn arity_from_arrow_core_type(arena: &ParseArena, core_type: &crate::parser::ast::CoreType) -> i32 {
    match &*core_type.ptyp_desc {
        crate::parser::ast::CoreTypeDesc::Ptyp_arrow(inner) => {
            let (_, ret, _) = inner.as_ref();
            1 + arity_from_arrow_core_type(arena, arena.get_core_type(*ret))
        }
        _ => 0,
    }
}

fn get_primitive_arity_from_type(
    ctx: &crate::types::context::TypeContext<'_>,
    env: &Env,
    ty: TypeExprRef,
) -> Option<i32> {
    get_primitive_arity_from_type_depth(ctx, env, ty, 0)
}

fn get_primitive_arity_from_type_depth(
    ctx: &crate::types::context::TypeContext<'_>,
    env: &Env,
    ty: TypeExprRef,
    depth: u32,
) -> Option<i32> {
    if depth > 100 {
        return None;
    }
    let repr = ctx.repr(ty);
    match &*ctx.get_desc(repr) {
        crate::types::TypeDesc::Tarrow { arity, .. } => *arity,
        crate::types::TypeDesc::Tlink(next) | crate::types::TypeDesc::Tsubst(next) => {
            get_primitive_arity_from_type_depth(ctx, env, *next, depth + 1)
        }
        crate::types::TypeDesc::Tconstr { .. } => {
            let expanded = crate::types::ctype::expand_head(ctx, env, repr);
            let expanded_repr = ctx.repr(expanded);
            if expanded_repr == repr {
                None
            } else {
                get_primitive_arity_from_type_depth(ctx, env, expanded_repr, depth + 1)
            }
        }
        _ => None,
    }
}

/// Check if a type is a Tconstr (type alias) at the top level.
/// Used to determine prim_from_constructor for external declarations.
fn is_type_constructor(ctx: &crate::types::context::TypeContext<'_>, ty: TypeExprRef) -> bool {
    let repr = ctx.repr(ty);
    matches!(&*ctx.get_desc(repr), crate::types::TypeDesc::Tconstr { .. })
}

fn primitive_description_from_value_decl(
    arena: &ParseArena,
    ctx: &crate::types::context::TypeContext<'_>,
    env: &Env,
    val_prim: &[StrIdx],
    core_type_idx: crate::parse_arena::CoreTypeIdx,
    val_ty: TypeExprRef,
) -> crate::types::PrimitiveDescription {
    let prim_name = val_prim
        .first()
        .map(|s| arena.get_string(*s).to_string())
        .unwrap_or_default();
    let prim_native_name = val_prim
        .get(1)
        .map(|s| arena.get_string(*s).to_string())
        .unwrap_or_default();
    let arity_from_type = get_primitive_arity_from_type(ctx, env, val_ty);
    // OCaml: from_constructor = true when get_arity returns Some AND type is Tconstr
    let prim_from_constructor = arity_from_type.is_some() && is_type_constructor(ctx, val_ty);
    let prim_arity = arity_from_type
        .unwrap_or_else(|| arity_from_arrow_core_type(arena, arena.get_core_type(core_type_idx)));

    crate::types::PrimitiveDescription {
        prim_name,
        prim_arity,
        prim_native_name,
        prim_native_float: false,
        prim_from_constructor,
    }
}

fn primitive_arity_from_typed_core_type(ty: &crate::types::typedtree::TypedCoreType) -> i32 {
    match &ty.ctyp_desc {
        crate::types::typedtree::TypedCoreTypeDesc::Ttyp_arrow(_, ret, Some(arity)) => *arity,
        crate::types::typedtree::TypedCoreTypeDesc::Ttyp_arrow(_, ret, None) => {
            1 + primitive_arity_from_typed_core_type(ret)
        }
        crate::types::typedtree::TypedCoreTypeDesc::Ttyp_poly(_, inner)
        | crate::types::typedtree::TypedCoreTypeDesc::Ttyp_alias(inner, _) => {
            primitive_arity_from_typed_core_type(inner)
        }
        _ => 0,
    }
}

fn primitive_description_from_typed_value_desc(
    ctx: Option<&crate::types::context::TypeContext<'_>>,
    env: Option<&Env>,
    vd: &crate::types::typedtree::TypedValueDescription,
) -> crate::types::PrimitiveDescription {
    let prim_name = vd.val_prim.first().cloned().unwrap_or_default();
    let prim_native_name = vd.val_prim.get(1).cloned().unwrap_or_default();
    let (prim_arity, prim_from_constructor) = match (ctx, env) {
        (Some(ctx), Some(env)) => {
            let arity_from_type = get_primitive_arity_from_type(ctx, env, vd.val_desc.ctyp_type);
            let from_constructor =
                arity_from_type.is_some() && is_type_constructor(ctx, vd.val_desc.ctyp_type);
            let arity = arity_from_type
                .unwrap_or_else(|| primitive_arity_from_typed_core_type(&vd.val_desc));
            (arity, from_constructor)
        }
        _ => (primitive_arity_from_typed_core_type(&vd.val_desc), false),
    };

    crate::types::PrimitiveDescription {
        prim_name,
        prim_arity,
        prim_native_name,
        prim_native_float: false,
        prim_from_constructor,
    }
}

fn decl_attrs_to_parser_attrs(
    arena: &ParseArena,
    attrs: &[crate::types::decl::Attribute],
) -> Attributes {
    Attributes::from_vec(
        attrs
            .iter()
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
        ParsedModuleExprDesc::Pmod_constraint(inner, _) => {
            path_of_parsed_module_expr(arena.get_mod_expr(*inner), arena)
        }
        _ => None,
    }
}

/// Try to convert a typed module expression to a module path.
/// Mirrors OCaml `Typemod.path_of_module` for applicative functor paths.
fn path_of_typed_module_expr(mod_expr: &ModuleExpr) -> Option<Path> {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(path, _) => Some(path.clone()),
        ModuleExprDesc::Tmod_apply(functor, arg, _) => {
            let functor_path = path_of_typed_module_expr(functor)?;
            let arg_path = path_of_typed_module_expr(arg)?;
            Some(Path::papply(functor_path, arg_path))
        }
        ModuleExprDesc::Tmod_constraint(inner, _, _, _) => path_of_typed_module_expr(inner),
        ModuleExprDesc::Tmod_structure(_)
        | ModuleExprDesc::Tmod_functor(_, _, _, _)
        | ModuleExprDesc::Tmod_unpack(_, _) => None,
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
                let arg_path = resolved_path_of_parsed_module_expr(
                    tctx,
                    env,
                    arena.get_mod_expr(*arg),
                    arena,
                )?;
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
            param_type, result, ..
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
                if md.md_path.is_none() {
                    md.md_path = Some(Path::Pident(id.clone()));
                }
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
                    substitute_functor_param_in_module_type(&md.md_type, old_param, arg_path, ctx);
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
                            *ty,
                            old_param,
                            arg_aliases,
                            ctx,
                            copy_cache,
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
                rewritten_md.md_type = substitute_functor_param_aliases_in_module_type(
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
            path,
            old_param,
            arg_aliases,
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
            | crate::types::TypeDesc::Tunivar(Some(name)) => find_substitution(name).unwrap_or(ty),
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
                break Some((
                    inner_fields.clone(),
                    source_decl.type_params.clone(),
                    source_args.clone(),
                ));
            }
            let manifest = match source_decl.type_manifest {
                Some(manifest) => manifest,
                None => break None,
            };
            let manifest =
                unwrap_poly_type(ctx, crate::types::ctype::expand_head(ctx, env, manifest));
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
    let paths: Vec<Path> = type_ids.iter().map(|id| Path::pident(id.clone())).collect();

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
        for ((type_id, template), variance) in
            type_ids.iter().zip(templates.iter()).zip(variances.iter())
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
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, p, _) in fields {
                push_sig_values_from_env_pattern(env, p, sig_items);
            }
        }
        PatternDesc::Tpat_construct(_, _, pats) | PatternDesc::Tpat_array(pats) => {
            for p in pats {
                push_sig_values_from_env_pattern(env, p, sig_items);
            }
        }
        PatternDesc::Tpat_variant(_, Some(inner), _) => {
            push_sig_values_from_env_pattern(env, inner, sig_items);
        }
        PatternDesc::Tpat_or(left, _, _) => {
            push_sig_values_from_env_pattern(env, left, sig_items);
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
        ModuleExprDesc::Tmod_constraint(
            inner,
            _,
            crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
            _,
        ) => match &inner.mod_desc {
            ModuleExprDesc::Tmod_structure(structure) => {
                Some(crate::types::decl::ModuleType::MtySignature(
                    crate::types::includemod::simplify_signature(&structure.str_type),
                ))
            }
            _ => Some(mod_expr.mod_type.clone()),
        },
        _ => Some(mod_expr.mod_type.clone()),
    }
}

pub(crate) fn decl_module_type_from_typed_module_expr_for_constraint_arg(
    mod_expr: &ModuleExpr,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::AliasPresence;
    use crate::types::decl::ModuleType as DeclMty;

    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(path, _)
            if matches!(mod_expr.mod_type, DeclMty::MtyAlias(_, _)) =>
        {
            // OCaml feeds Mty_alias(Mta_absent, path) into wrap_constraint for
            // constrained alias modules. Keeping the alias absent here lets
            // includemod emit the required Tcoerce_alias instead of collapsing
            // the constrained alias back to a bare module-alias constant.
            Some(DeclMty::MtyAlias(AliasPresence::MtaAbsent, path.clone()))
        }
        ModuleExprDesc::Tmod_structure(structure) => {
            Some(DeclMty::MtySignature(structure.str_type.clone()))
        }
        ModuleExprDesc::Tmod_constraint(
            inner,
            _,
            crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
            _,
        ) => match &inner.mod_desc {
            ModuleExprDesc::Tmod_structure(structure) => {
                Some(DeclMty::MtySignature(structure.str_type.clone()))
            }
            _ => Some(mod_expr.mod_type.clone()),
        },
        _ => Some(mod_expr.mod_type.clone()),
    }
}

fn simplified_structure_signature(structure: &Structure) -> Option<crate::types::decl::Signature> {
    let simplified = crate::types::includemod::simplify_signature(&structure.str_type);
    if simplified.len() == structure.str_type.len() {
        None
    } else {
        Some(simplified)
    }
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
            if let Some(path) = crate::types::typecore::with_resolved_module_components_for_lid(
                lid,
                arena,
                env,
                pers_env,
                ctx,
                |components| components.access_path().clone(),
            ) {
                return Some(path);
            }
            let parent_path = lookup_module_path_by_lid(prefix, arena, env, pers_env, ctx)?;
            crate::types::typecore::lookup_module_in_resolved_path(
                &parent_path,
                submod_name,
                env,
                pers_env,
                ctx,
            )
            .map(|(_, child_path, _)| child_path)
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
            if let Some(path) = crate::types::typecore::with_resolved_module_components_for_lid(
                prefix,
                arena,
                env,
                pers_env,
                ctx,
                |components| {
                    components.lookup_qualified_modtype(submodtype_name, ctx).map(|_| {
                        Path::pdot(components.access_path().clone(), submodtype_name.to_string())
                    })
                },
            )
            .flatten()
            {
                return Some(path);
            }
            let parent_path = lookup_module_path_by_lid(prefix, arena, env, pers_env, ctx)?;
            crate::types::typecore::lookup_modtype_in_resolved_path(
                &parent_path,
                submodtype_name,
                env,
                pers_env,
                ctx,
            )
            .map(|(resolved_parent_path, _)| Path::pdot(resolved_parent_path, submodtype_name))
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
    match lid {
        Longident::Lident(mod_idx) => {
            let mod_name = arena.get_string(*mod_idx);
            // Try local env first
            if let Ok(md) = env.find_module(mod_name) {
                return Some(md.md_type.clone());
            }
            let persistent_path = Path::pident(Ident::create_persistent(mod_name));
            if let Some((_, sig)) = crate::types::typecore::resolve_module_signature_for_path(
                &persistent_path,
                env,
                pers_env,
                ctx,
            ) {
                return Some(DeclMty::MtySignature(sig));
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
            if let Some(found) = crate::types::typecore::with_resolved_module_components_for_lid(
                prefix,
                arena,
                env,
                pers_env,
                ctx,
                |components| {
                    if let Some((_, _, sub_md)) =
                        components.lookup_qualified_module(submod_name, ctx)
                    {
                        if let Some((alias_presence, alias_path)) = parent_alias.clone() {
                            if let DeclMty::MtyAlias(child_presence, child_path) = &sub_md.md_type {
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
                        return Some(sub_md.md_type.clone());
                    }
                    if let Some((_, mtd)) = components.lookup_qualified_modtype(submod_name, ctx) {
                        let child_mty = mtd.mtd_type.clone()?;
                        return Some(child_mty);
                    }
                    None
                },
            )
            .flatten()
            {
                return Some(found);
            }
            let parent_path = lookup_module_path_by_lid(prefix, arena, env, pers_env, ctx)?;
            crate::types::typecore::with_resolved_module_components_for_path(
                &parent_path,
                env,
                pers_env,
                ctx,
                |components| {
                    if let Some((_, _, sub_md)) =
                        components.lookup_qualified_module(submod_name, ctx)
                    {
                        if let Some((alias_presence, alias_path)) = parent_alias.clone() {
                            if let DeclMty::MtyAlias(child_presence, child_path) = &sub_md.md_type {
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
                        return Some(sub_md.md_type.clone());
                    }
                    if let Some((_, mtd)) = components.lookup_qualified_modtype(submod_name, ctx) {
                        let child_mty = mtd.mtd_type.clone()?;
                        return Some(child_mty);
                    }
                    None
                },
            )
            .flatten()
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

                if id.is_persistent() || id.stamp() == 0 {
                    let persistent_path = Path::pident(Ident::create_persistent(name));
                    if let Some((_, sig)) =
                        crate::types::typecore::resolve_module_signature_for_path(
                            &persistent_path,
                            local_env,
                            pers_env,
                            ctx,
                        )
                    {
                        visiting.remove(path);
                        return Some(sig);
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
            if let Some(local_env) = env {
                if let Some((_, sig)) = crate::types::typecore::resolve_module_signature_for_path(
                    path, local_env, pers_env, ctx,
                ) {
                    visiting.remove(path);
                    return Some(sig);
                }

                if let Some((_, mtd)) = crate::types::typecore::lookup_modtype_in_resolved_path(
                    parent,
                    name.as_str(),
                    local_env,
                    pers_env,
                    ctx,
                ) {
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

            let parent_sig = if let Some(local_env) = env {
                match crate::types::typecore::resolve_module_signature_for_path(
                    parent,
                    local_env,
                    pers_env,
                    ctx,
                ) {
                    Some((_, sig)) => sig,
                    None => resolve_path_to_sig_impl(parent, env, pers_env, ctx, visiting)?,
                }
            } else {
                resolve_path_to_sig_impl(parent, env, pers_env, ctx, visiting)?
            };
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

fn rewrite_package_freshened_type_path(path: &Path, fresh_type_ids: &HashMap<i32, Ident>) -> Path {
    match path {
        Path::Pident(id) => fresh_type_ids
            .get(&id.stamp())
            .cloned()
            .map(Path::pident)
            .unwrap_or_else(|| path.clone()),
        Path::Pdot(prefix, name, pos) => Path::Pdot(
            Box::new(rewrite_package_freshened_type_path(prefix, fresh_type_ids)),
            name.clone(),
            *pos,
        ),
        Path::Papply(functor, arg) => Path::Papply(
            Box::new(rewrite_package_freshened_type_path(functor, fresh_type_ids)),
            Box::new(rewrite_package_freshened_type_path(arg, fresh_type_ids)),
        ),
    }
}

fn rewrite_package_freshened_type_expr(
    ctx: &crate::types::context::TypeContext<'_>,
    ty_ref: TypeExprRef,
    fresh_type_ids: &HashMap<i32, Ident>,
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
            let rewritten_path = rewrite_package_freshened_type_path(path, fresh_type_ids);
            if rewritten_path != *path {
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
                rewrite_package_freshened_type_expr(ctx, *arg, fresh_type_ids, visited);
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            rewrite_package_freshened_type_expr(ctx, arg.typ, fresh_type_ids, visited);
            rewrite_package_freshened_type_expr(ctx, *ret, fresh_type_ids, visited);
        }
        TypeDesc::Ttuple(types) => {
            for ty in types {
                rewrite_package_freshened_type_expr(ctx, *ty, fresh_type_ids, visited);
            }
        }
        TypeDesc::Tlink(ty) | TypeDesc::Tsubst(ty) => {
            rewrite_package_freshened_type_expr(ctx, *ty, fresh_type_ids, visited);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_package_freshened_type_expr(ctx, *body, fresh_type_ids, visited);
            for var in vars {
                rewrite_package_freshened_type_expr(ctx, *var, fresh_type_ids, visited);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_package_freshened_type_expr(ctx, *fields, fresh_type_ids, visited);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_package_freshened_type_expr(ctx, *typ, fresh_type_ids, visited);
            rewrite_package_freshened_type_expr(ctx, *rest, fresh_type_ids, visited);
        }
        TypeDesc::Tvariant(row) => {
            rewrite_package_freshened_type_expr(ctx, row.row_more, fresh_type_ids, visited);
            for (_, field) in &row.row_fields {
                match field {
                    RowField::Rpresent(Some(ty)) => {
                        rewrite_package_freshened_type_expr(ctx, *ty, fresh_type_ids, visited);
                    }
                    RowField::Reither { types, .. } => {
                        for ty in types {
                            rewrite_package_freshened_type_expr(ctx, *ty, fresh_type_ids, visited);
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { args, .. } => {
            for arg in args {
                rewrite_package_freshened_type_expr(ctx, *arg, fresh_type_ids, visited);
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

fn rewrite_package_freshened_constructor_args(
    args: &mut crate::types::decl::ConstructorArguments,
    ctx: &crate::types::context::TypeContext<'_>,
    fresh_type_ids: &HashMap<i32, Ident>,
    visited: &mut HashSet<TypeExprRef>,
) {
    match args {
        crate::types::decl::ConstructorArguments::CstrTuple(args) => {
            for arg in args {
                rewrite_package_freshened_type_expr(ctx, *arg, fresh_type_ids, visited);
            }
        }
        crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
            for label in labels {
                rewrite_package_freshened_type_expr(ctx, label.ld_type, fresh_type_ids, visited);
            }
        }
    }
}

fn rewrite_package_freshened_type_kind(
    kind: &mut crate::types::TypeKind,
    ctx: &crate::types::context::TypeContext<'_>,
    fresh_type_ids: &HashMap<i32, Ident>,
    visited: &mut HashSet<TypeExprRef>,
) {
    match kind {
        crate::types::TypeKind::TypeAbstract | crate::types::TypeKind::TypeOpen => {}
        crate::types::TypeKind::TypeRecord(labels, _) => {
            for label in labels {
                rewrite_package_freshened_type_expr(ctx, label.ld_type, fresh_type_ids, visited);
            }
        }
        crate::types::TypeKind::TypeVariant(constructors) => {
            for ctor in constructors {
                rewrite_package_freshened_constructor_args(
                    &mut ctor.cd_args,
                    ctx,
                    fresh_type_ids,
                    visited,
                );
                if let Some(res) = ctor.cd_res {
                    rewrite_package_freshened_type_expr(ctx, res, fresh_type_ids, visited);
                }
            }
        }
    }
}

fn rewrite_package_freshened_type_inlined(
    inlined: &mut crate::types::decl::TypeInlinedType,
    ctx: &crate::types::context::TypeContext<'_>,
    fresh_type_ids: &HashMap<i32, Ident>,
    visited: &mut HashSet<TypeExprRef>,
) {
    match inlined {
        crate::types::decl::TypeInlinedType::Record { labels, .. } => {
            for label in labels {
                rewrite_package_freshened_type_expr(ctx, label.ld_type, fresh_type_ids, visited);
            }
        }
    }
}

fn collect_package_fresh_type_ids_in_module_type(
    mty: &crate::types::decl::ModuleType,
    ctx: &crate::types::context::TypeContext<'_>,
    fresh_type_ids: &mut HashMap<i32, Ident>,
) {
    use crate::types::decl::ModuleType as DeclMty;

    match mty {
        DeclMty::MtySignature(sig_items) => {
            for item in sig_items {
                match item {
                    crate::types::decl::SignatureItem::SigType(id, _, _) => {
                        if id.stamp() != 0 {
                            fresh_type_ids
                                .entry(id.stamp())
                                .or_insert_with(|| ctx.create_ident(id.name()));
                        }
                    }
                    crate::types::decl::SignatureItem::SigModule(_, md, _) => {
                        collect_package_fresh_type_ids_in_module_type(
                            &md.md_type,
                            ctx,
                            fresh_type_ids,
                        );
                    }
                    crate::types::decl::SignatureItem::SigModtype(_, mtd) => {
                        if let Some(inner) = &mtd.mtd_type {
                            collect_package_fresh_type_ids_in_module_type(
                                inner,
                                ctx,
                                fresh_type_ids,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        DeclMty::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_deref() {
                collect_package_fresh_type_ids_in_module_type(param_type, ctx, fresh_type_ids);
            }
            collect_package_fresh_type_ids_in_module_type(result, ctx, fresh_type_ids);
        }
        DeclMty::MtyIdent(_) | DeclMty::MtyAlias(_, _) => {}
    }
}

fn freshen_package_type_ids_in_module_type(
    mty: &mut crate::types::decl::ModuleType,
    ctx: &crate::types::context::TypeContext<'_>,
    fresh_type_ids: &HashMap<i32, Ident>,
    visited: &mut HashSet<TypeExprRef>,
) {
    use crate::types::decl::ModuleType as DeclMty;

    match mty {
        DeclMty::MtySignature(sig_items) => {
            for item in sig_items {
                match item {
                    crate::types::decl::SignatureItem::SigValue(_, desc) => {
                        rewrite_package_freshened_type_expr(
                            ctx,
                            desc.val_type,
                            fresh_type_ids,
                            visited,
                        );
                    }
                    crate::types::decl::SignatureItem::SigType(id, decl, _) => {
                        if let Some(new_id) = fresh_type_ids.get(&id.stamp()) {
                            *id = new_id.clone();
                            decl.type_path = Some(Path::pident(new_id.clone()));
                        }
                        for param in &decl.type_params {
                            rewrite_package_freshened_type_expr(
                                ctx,
                                *param,
                                fresh_type_ids,
                                visited,
                            );
                        }
                        if let Some(manifest) = decl.type_manifest {
                            rewrite_package_freshened_type_expr(
                                ctx,
                                manifest,
                                fresh_type_ids,
                                visited,
                            );
                        }
                        rewrite_package_freshened_type_kind(
                            &mut decl.type_kind,
                            ctx,
                            fresh_type_ids,
                            visited,
                        );
                        for inlined in &mut decl.type_inlined_types {
                            rewrite_package_freshened_type_inlined(
                                inlined,
                                ctx,
                                fresh_type_ids,
                                visited,
                            );
                        }
                    }
                    crate::types::decl::SignatureItem::SigTypext(_, ext, _) => {
                        ext.ext_type_path =
                            rewrite_package_freshened_type_path(&ext.ext_type_path, fresh_type_ids);
                        for param in &ext.ext_type_params {
                            rewrite_package_freshened_type_expr(
                                ctx,
                                *param,
                                fresh_type_ids,
                                visited,
                            );
                        }
                        rewrite_package_freshened_constructor_args(
                            &mut ext.ext_args,
                            ctx,
                            fresh_type_ids,
                            visited,
                        );
                        if let Some(ret) = ext.ext_ret_type {
                            rewrite_package_freshened_type_expr(ctx, ret, fresh_type_ids, visited);
                        }
                    }
                    crate::types::decl::SignatureItem::SigModule(_, md, _) => {
                        freshen_package_type_ids_in_module_type(
                            &mut md.md_type,
                            ctx,
                            fresh_type_ids,
                            visited,
                        );
                    }
                    crate::types::decl::SignatureItem::SigModtype(_, mtd) => {
                        if let Some(inner) = mtd.mtd_type.as_mut() {
                            freshen_package_type_ids_in_module_type(
                                inner,
                                ctx,
                                fresh_type_ids,
                                visited,
                            );
                        }
                    }
                    crate::types::decl::SignatureItem::SigClass
                    | crate::types::decl::SignatureItem::SigClassType => {}
                }
            }
        }
        DeclMty::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                freshen_package_type_ids_in_module_type(param_type, ctx, fresh_type_ids, visited);
            }
            freshen_package_type_ids_in_module_type(result, ctx, fresh_type_ids, visited);
        }
        DeclMty::MtyIdent(_) | DeclMty::MtyAlias(_, _) => {}
    }
}

fn copy_signature_for_package_constraints(
    sig_items: &[crate::types::decl::SignatureItem],
    ctx: &crate::types::context::TypeContext<'_>,
) -> crate::types::decl::Signature {
    let dummy_param = Ident::create_local("__pkg_copy_param__");
    let dummy_path = Path::pident(Ident::create_local("__pkg_copy_path__"));
    let copied = substitute_functor_param_in_signature(sig_items, &dummy_param, &dummy_path, ctx);
    let mut fresh_type_ids = HashMap::new();
    let mut copied_mty = crate::types::decl::ModuleType::MtySignature(copied);
    collect_package_fresh_type_ids_in_module_type(&copied_mty, ctx, &mut fresh_type_ids);
    let mut visited = HashSet::new();
    freshen_package_type_ids_in_module_type(&mut copied_mty, ctx, &fresh_type_ids, &mut visited);
    match copied_mty {
        crate::types::decl::ModuleType::MtySignature(sig) => sig,
        _ => unreachable!(),
    }
}

fn apply_package_constraints_to_module_type<'b>(
    env: &Env,
    mty: &crate::types::decl::ModuleType,
    constraints: &[PackageConstraint],
    _package_parent_path: Option<&Path>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::SignatureItem;

    if constraints.is_empty() {
        return Some(mty.clone());
    }

    fn rewrite_package_constraints_over_sig(
        sig: &[crate::types::decl::SignatureItem],
        constraints: &[PackageConstraint],
    ) -> (
        crate::types::decl::Signature,
        Vec<(usize, Vec<PackageConstraint>)>,
    ) {
        let mut rewritten_sig = Vec::with_capacity(sig.len());
        let mut nested_modules = Vec::new();

        for item in sig {
            match item {
                SignatureItem::SigValue(id, vd) => {
                    rewritten_sig.push(SignatureItem::SigValue(id.clone(), vd.clone()))
                }
                SignatureItem::SigType(id, td, rec_status) => {
                    let mut td = td.clone();
                    if td.type_params.is_empty() {
                        if let Some((_, manifest_ty)) = constraints
                            .iter()
                            .find(|(path, _)| path.len() == 1 && path[0] == id.name())
                        {
                            td.type_manifest = Some(*manifest_ty);
                        }
                    }
                    rewritten_sig.push(SignatureItem::SigType(id.clone(), td, *rec_status));
                }
                SignatureItem::SigModule(id, md, rec_status) => {
                    let nested = nested_package_constraints(id.name(), constraints);
                    if !nested.is_empty() {
                        nested_modules.push((rewritten_sig.len(), nested));
                    }
                    rewritten_sig.push(SignatureItem::SigModule(id.clone(), md.clone(), *rec_status));
                }
                other => rewritten_sig.push(other.clone()),
            }
        }

        (rewritten_sig, nested_modules)
    }

    fn finish_rewritten_package_sig<'b>(
        env: &Env,
        mut rewritten_sig: crate::types::decl::Signature,
        nested_modules: Vec<(usize, Vec<PackageConstraint>)>,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> Option<crate::types::decl::ModuleType> {
        for (idx, nested) in nested_modules {
            let Some(SignatureItem::SigModule(_, md, _)) = rewritten_sig.get_mut(idx) else {
                continue;
            };
            md.md_type =
                apply_package_constraints_to_module_type(env, &md.md_type, &nested, None, pers_env, ctx)?;
        }

        Some(crate::types::decl::ModuleType::MtySignature(rewritten_sig))
    }

    fn resolve_path_package_constraints<'b>(
        env: &Env,
        path: &Path,
        constraints: &[PackageConstraint],
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
        visiting: &mut HashSet<Path>,
    ) -> Option<crate::types::decl::ModuleType> {
        if !visiting.insert(path.clone()) {
            return None;
        }

        let result = match path {
            Path::Pident(id) => {
                let ident_path = Path::pident(id.clone());
                if let Ok(mtd) = env.lookup_modtype(&ident_path) {
                    if let Some(mty) = mtd.mtd_type.as_ref() {
                        apply_package_constraints_impl(
                            env,
                            mty,
                            constraints,
                            pers_env,
                            ctx,
                            visiting,
                        )
                    } else {
                        None
                    }
                } else if let Ok(md) = env.lookup_module(&ident_path) {
                    apply_package_constraints_impl(
                        env,
                        &md.md_type,
                        constraints,
                        pers_env,
                        ctx,
                        visiting,
                    )
                } else {
                    let persistent_path = Path::pident(Ident::create_persistent(id.name()));
                    crate::types::typecore::with_resolved_module_components_for_path(
                        &persistent_path,
                        env,
                        pers_env,
                        ctx,
                        |components| rewrite_package_constraints_over_sig(
                            components.signature(),
                            constraints,
                        ),
                    )
                    .and_then(|(rewritten_sig, nested_modules)| {
                        finish_rewritten_package_sig(
                            env,
                            rewritten_sig,
                            nested_modules,
                            pers_env,
                            ctx,
                        )
                    })
                }
            }
            Path::Pdot(parent, name, _) => {
                if let Some((rewritten_sig, nested_modules)) =
                    crate::types::typecore::with_resolved_module_components_for_path(
                        path,
                        env,
                        pers_env,
                        ctx,
                        |components| rewrite_package_constraints_over_sig(components.signature(), constraints),
                    )
                {
                    finish_rewritten_package_sig(
                        env,
                        rewritten_sig,
                        nested_modules,
                        pers_env,
                        ctx,
                    )
                } else if let Some((_, mtd)) = crate::types::typecore::lookup_modtype_in_resolved_path(
                    parent,
                    name.as_str(),
                    env,
                    pers_env,
                    ctx,
                ) {
                    if let Some(mty) = mtd.mtd_type.as_ref() {
                        apply_package_constraints_impl(
                            env,
                            mty,
                            constraints,
                            pers_env,
                            ctx,
                            visiting,
                        )
                    } else {
                        None
                    }
                } else {
                    let sig = resolve_path_to_sig_impl(path, Some(env), pers_env, ctx, visiting)?;
                    let (rewritten_sig, nested_modules) =
                        rewrite_package_constraints_over_sig(&sig, constraints);
                    finish_rewritten_package_sig(
                        env,
                        rewritten_sig,
                        nested_modules,
                        pers_env,
                        ctx,
                    )
                }
            }
            Path::Papply(_, _) => None,
        };

        visiting.remove(path);
        result
    }

    fn apply_package_constraints_impl<'b>(
        env: &Env,
        mty: &crate::types::decl::ModuleType,
        constraints: &[PackageConstraint],
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
        visiting: &mut HashSet<Path>,
    ) -> Option<crate::types::decl::ModuleType> {
        use crate::types::decl::ModuleType as DeclMty;

        match mty {
            DeclMty::MtySignature(sig) => {
                let (rewritten_sig, nested_modules) =
                    rewrite_package_constraints_over_sig(sig, constraints);
                finish_rewritten_package_sig(
                    env,
                    rewritten_sig,
                    nested_modules,
                    pers_env,
                    ctx,
                )
            }
            DeclMty::MtyAlias(_, path) | DeclMty::MtyIdent(path) => {
                resolve_path_package_constraints(env, path, constraints, pers_env, ctx, visiting)
            }
            _ => None,
        }
    }

    // Direct port of OCaml Typemod.package_constraints, but preserve the
    // env_lazy/shared signature view as the source of truth instead of cloning
    // a detached signature before doing the one-pass rewrite.
    let mut visiting = HashSet::new();
    apply_package_constraints_impl(env, mty, constraints, pers_env, ctx, &mut visiting)
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

    let base_mty = match package_path {
        Path::Pident(_) => env.lookup_modtype(package_path).ok()?.mtd_type.clone()?,
        Path::Pdot(parent, modtype_name, _) => crate::types::typecore::lookup_modtype_in_resolved_path(
            parent,
            modtype_name,
            env,
            pers_env,
            ctx,
        )
        .and_then(|(_, mtd)| mtd.mtd_type)
        .or_else(|| env.lookup_modtype(package_path).ok()?.mtd_type.clone())?,
        Path::Papply(_, _) => return None,
    };
    let package_parent_path = parent_path_for_module_type(&base_mty);
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

enum ResolvedWithConstraintTarget {
    Type { path: Path, id: Ident },
    Module { path: Path },
}

fn resolved_constraint_path(prefix: Option<&Path>, id: &Ident) -> Path {
    match prefix {
        Some(prefix) => Path::pdot(prefix.clone(), id.name()),
        None => Path::pident(id.clone()),
    }
}

fn resolve_with_constraint_target_in_sig(
    components: &[String],
    sig_items: &[crate::types::decl::SignatureItem],
    prefix: Option<&Path>,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext<'_>,
) -> Option<ResolvedWithConstraintTarget> {
    use crate::types::decl::SignatureItem;

    let (head, tail) = components.split_first()?;

    for item in sig_items {
        match item {
            SignatureItem::SigType(id, _, _) if id.name() == head.as_str() && tail.is_empty() => {
                return Some(ResolvedWithConstraintTarget::Type {
                    path: resolved_constraint_path(prefix, id),
                    id: id.clone(),
                });
            }
            SignatureItem::SigModule(id, md, _) if id.name() == head.as_str() => {
                let module_path = resolved_constraint_path(prefix, id);
                if tail.is_empty() {
                    return Some(ResolvedWithConstraintTarget::Module { path: module_path });
                }
                let child_sig = resolve_mod_type_to_sig(&md.md_type, Some(env), pers_env, ctx)?;
                return resolve_with_constraint_target_in_sig(
                    tail,
                    &child_sig,
                    Some(&module_path),
                    env,
                    pers_env,
                    ctx,
                );
            }
            _ => {}
        }
    }

    None
}

fn resolve_with_constraint_target<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    base_mty: Option<&crate::types::decl::ModuleType>,
    lid: &Longident,
) -> Option<ResolvedWithConstraintTarget> {
    let base_mty = base_mty?;
    let sig_items =
        resolve_mod_type_to_sig(base_mty, Some(env), &mut tctx.persistent_env, tctx.type_ctx)?;
    let components: Vec<String> = lid
        .flatten_idx()
        .into_iter()
        .map(|idx| arena.get_string(idx).to_string())
        .collect();
    resolve_with_constraint_target_in_sig(
        &components,
        &sig_items,
        None,
        env,
        &mut tctx.persistent_env,
        tctx.type_ctx,
    )
}

fn transl_with_constraints<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    base_mty: Option<&crate::types::decl::ModuleType>,
    constraints: &[crate::parser::ast::WithConstraint],
) -> TypeModResult<
    Vec<(
        Path,
        Located<LidentIdx>,
        crate::types::typedtree::WithConstraint,
    )>,
> {
    use crate::parser::ast::WithConstraint as ParsedWithConstraint;
    use crate::types::typedtree::WithConstraint as TypedWithConstraint;

    let mut typed_constraints = Vec::with_capacity(constraints.len());
    for constraint in constraints {
        match constraint {
            ParsedWithConstraint::Pwith_type(lid, decl) => {
                let longident = tctx.resolve_lid(lid.txt).clone();
                if let Some(ResolvedWithConstraintTarget::Type { path, id }) =
                    resolve_with_constraint_target(tctx, env, arena, base_mty, &longident)
                {
                    let mut typed_decls = transl_sig_type_declarations_with_ids(
                        tctx,
                        env,
                        arena,
                        std::slice::from_ref(decl),
                        Some(std::slice::from_ref(&id)),
                    )?;
                    if let Some(typed_decl) = typed_decls.pop() {
                        typed_constraints.push((
                            path,
                            lid.clone(),
                            TypedWithConstraint::Twith_type(typed_decl),
                        ));
                    }
                    continue;
                }
                let path = path_from_longident(&longident, |idx| arena.get_string(idx));
                let mut typed_decls = transl_sig_type_declarations_with_ids(
                    tctx,
                    env,
                    arena,
                    std::slice::from_ref(decl),
                    None,
                )?;
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
                if let Some(ResolvedWithConstraintTarget::Type { path, id }) =
                    resolve_with_constraint_target(tctx, env, arena, base_mty, &longident)
                {
                    let mut typed_decls = transl_sig_type_declarations_with_ids(
                        tctx,
                        env,
                        arena,
                        std::slice::from_ref(decl),
                        Some(std::slice::from_ref(&id)),
                    )?;
                    if let Some(typed_decl) = typed_decls.pop() {
                        typed_constraints.push((
                            path,
                            lid.clone(),
                            TypedWithConstraint::Twith_typesubst(typed_decl),
                        ));
                    }
                    continue;
                }
                let path = path_from_longident(&longident, |idx| arena.get_string(idx));
                let mut typed_decls = transl_sig_type_declarations_with_ids(
                    tctx,
                    env,
                    arena,
                    std::slice::from_ref(decl),
                    None,
                )?;
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
                let lhs_path = match resolve_with_constraint_target(
                    tctx,
                    env,
                    arena,
                    base_mty,
                    &lhs_longident,
                ) {
                    Some(ResolvedWithConstraintTarget::Module { path }) => path,
                    _ => path_from_longident(&lhs_longident, |idx| arena.get_string(idx)),
                };
                let rhs_longident = tctx.resolve_lid(rhs_lid.txt).clone();
                let rhs_path = lookup_module_path_by_lid(
                    &rhs_longident,
                    arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .unwrap_or_else(|| {
                    path_from_longident(&rhs_longident, |idx| arena.get_string(idx))
                });
                typed_constraints.push((
                    lhs_path,
                    lid.clone(),
                    TypedWithConstraint::Twith_module(rhs_path, rhs_lid.clone()),
                ));
            }
            ParsedWithConstraint::Pwith_modsubst(lid, rhs_lid) => {
                let lhs_longident = tctx.resolve_lid(lid.txt).clone();
                let lhs_path = match resolve_with_constraint_target(
                    tctx,
                    env,
                    arena,
                    base_mty,
                    &lhs_longident,
                ) {
                    Some(ResolvedWithConstraintTarget::Module { path }) => path,
                    _ => path_from_longident(&lhs_longident, |idx| arena.get_string(idx)),
                };
                let rhs_longident = tctx.resolve_lid(rhs_lid.txt).clone();
                let rhs_path = lookup_module_path_by_lid(
                    &rhs_longident,
                    arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .unwrap_or_else(|| {
                    path_from_longident(&rhs_longident, |idx| arena.get_string(idx))
                });
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
                rewrite_functor_param_type_paths_in_type(
                    arg,
                    param_name,
                    manifests,
                    ctx,
                    visited,
                    manifest_subst_cache,
                );
            }

            if let Path::Pdot(prefix, type_name, _) = path {
                if let Path::Pident(id) = prefix.as_ref() {
                    if id.name() == param_name && !has_args {
                        if let Some(manifest_ty) = manifests.get(type_name.as_str()) {
                            // Cache manifest substitution results so all occurrences of
                            // the same functor parameter type (e.g. S.elt) map to the
                            // SAME substituted node, matching OCaml's Subst.typexp sharing.
                            let manifest_copy = if let Some(&cached) =
                                manifest_subst_cache.get(type_name.as_str())
                            {
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
            rewrite_functor_param_type_paths_in_type(
                arg.typ,
                param_name,
                manifests,
                ctx,
                visited,
                manifest_subst_cache,
            );
            rewrite_functor_param_type_paths_in_type(
                ret,
                param_name,
                manifests,
                ctx,
                visited,
                manifest_subst_cache,
            );
        }
        TypeDesc::Ttuple(types) => {
            for inner in types {
                rewrite_functor_param_type_paths_in_type(
                    inner,
                    param_name,
                    manifests,
                    ctx,
                    visited,
                    manifest_subst_cache,
                );
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_functor_param_type_paths_in_type(
                fields,
                param_name,
                manifests,
                ctx,
                visited,
                manifest_subst_cache,
            );
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_functor_param_type_paths_in_type(
                typ,
                param_name,
                manifests,
                ctx,
                visited,
                manifest_subst_cache,
            );
            rewrite_functor_param_type_paths_in_type(
                rest,
                param_name,
                manifests,
                ctx,
                visited,
                manifest_subst_cache,
            );
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
                        row_ty,
                        param_name,
                        manifests,
                        ctx,
                        visited,
                        manifest_subst_cache,
                    );
                }
            }
            for (_label, row_field) in row.row_fields {
                match row_field {
                    RowField::Rpresent(Some(row_ty)) => {
                        rewrite_functor_param_type_paths_in_type(
                            row_ty,
                            param_name,
                            manifests,
                            ctx,
                            visited,
                            manifest_subst_cache,
                        );
                    }
                    RowField::Reither { types, .. } => {
                        for row_ty in types {
                            rewrite_functor_param_type_paths_in_type(
                                row_ty,
                                param_name,
                                manifests,
                                ctx,
                                visited,
                                manifest_subst_cache,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_functor_param_type_paths_in_type(
                body,
                param_name,
                manifests,
                ctx,
                visited,
                manifest_subst_cache,
            );
            for var in vars {
                rewrite_functor_param_type_paths_in_type(
                    var,
                    param_name,
                    manifests,
                    ctx,
                    visited,
                    manifest_subst_cache,
                );
            }
        }
        TypeDesc::Tpackage { args, .. } => {
            for arg in args {
                rewrite_functor_param_type_paths_in_type(
                    arg,
                    param_name,
                    manifests,
                    ctx,
                    visited,
                    manifest_subst_cache,
                );
            }
        }
        TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
            rewrite_functor_param_type_paths_in_type(
                target,
                param_name,
                manifests,
                ctx,
                visited,
                manifest_subst_cache,
            );
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
    rewrite_functor_param_type_paths_in_type(
        copied,
        param_name,
        manifests,
        ctx,
        &mut visited,
        manifest_subst_cache,
    );
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
                                *ty,
                                param_name,
                                manifests,
                                ctx,
                                copy_cache,
                                manifest_subst_cache,
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
                            specialize_label_decl(
                                label,
                                param_name,
                                manifests,
                                ctx,
                                copy_cache,
                                manifest_subst_cache,
                            )
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
                            specialize_label_decl(
                                label,
                                param_name,
                                manifests,
                                ctx,
                                copy_cache,
                                manifest_subst_cache,
                            )
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
                                    ty,
                                    param_name,
                                    manifests,
                                    ctx,
                                    copy_cache,
                                    manifest_subst_cache,
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
                            specialize_label_decl(
                                label,
                                param_name,
                                manifests,
                                ctx,
                                copy_cache,
                                manifest_subst_cache,
                            )
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
                                specialize_inner(
                                    inner,
                                    param_name,
                                    manifests,
                                    ctx,
                                    copy_cache,
                                    manifest_subst_cache,
                                )
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
                        inner,
                        param_name,
                        manifests,
                        ctx,
                        copy_cache,
                        manifest_subst_cache,
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
                            result,
                            param_name,
                            manifests,
                            ctx,
                            copy_cache,
                            manifest_subst_cache,
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
    specialize_inner(
        mty,
        param_name,
        manifests,
        ctx,
        &mut copy_cache,
        &mut manifest_subst_cache,
    )
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
                } else {
                    let persistent_path = Path::pident(Ident::create_persistent(name));
                    crate::types::typecore::resolve_module_signature_for_path(
                        &persistent_path,
                        env,
                        pers_env,
                        ctx,
                    )
                    .map(|(_, sig)| {
                        anchored(
                            &persistent_path,
                            &DeclMty::MtySignature(sig),
                        )
                    })
                }
            }
            Path::Pdot(parent, submod, _) => {
                if let Some((_, owner_path, md)) =
                    crate::types::typecore::lookup_module_in_resolved_path(
                        parent, submod, env, pers_env, ctx,
                    )
                {
                    match &md.md_type {
                        DeclMty::MtyAlias(_, alias_path) | DeclMty::MtyIdent(alias_path) => {
                            resolve_path(alias_path, env, pers_env, ctx, visiting)
                        }
                        other => Some(anchored(&owner_path, other)),
                    }
                } else {
                    None
                }
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
    let functor_mty = match scrape_alias_module_type(
        &functor_mty,
        env,
        &mut tctx.persistent_env,
        tctx.type_ctx,
    ) {
        Some(scraped) => scraped,
        None => functor_mty,
    };
    // Extract the result type if it's a functor
    match functor_mty {
        DeclMty::MtyFunctor { param, result, .. } => {
            let mut result = *result;
            // Functor result module types may carry an unqualified local modtype
            // identifier (e.g. `S`) from the defining module signature. Qualify
            // it with the functor's owner module path when needed so downstream
            // signature scraping can resolve it (e.g. `DB__Key.S`).
            if let DeclMty::MtyIdent(path) = &result {
                if resolve_mod_type_to_sig(
                    &result,
                    Some(env),
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
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
                                let qualified = DeclMty::MtyIdent(Path::pdot(
                                    owner_path,
                                    path.last().to_string(),
                                ));
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
            // Resolve the argument path through the env to get the local ident
            // (e.g. Path/1028) instead of a persistent one (Path/0).
            let arg_path = if let ParsedModuleExprDesc::Pmod_ident(lid) = &*arg_expr.pmod_desc {
                let longident = arena.get_longident(lid.txt);
                lookup_module_path_by_lid(
                    longident,
                    arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
            } else {
                None
            }
            .or_else(|| path_of_parsed_module_expr(arg_expr, arena));
            if let Some(arg_path) = arg_path {
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
fn find_packed_module_expr<'a>(
    expr: &'a crate::parser::ast::Expression,
    arena: &'a ParseArena,
) -> Option<&'a ParsedModuleExpr> {
    use crate::parser::ast::ExpressionDesc;

    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_pack(mod_expr_idx) => Some(arena.get_mod_expr(*mod_expr_idx)),
        ExpressionDesc::Pexp_constraint(inner) => {
            find_packed_module_expr(arena.get_expr(inner.0), arena)
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            find_packed_module_expr(arena.get_expr(inner.0), arena)
        }
        ExpressionDesc::Pexp_await(inner) => find_packed_module_expr(arena.get_expr(*inner), arena),
        ExpressionDesc::Pexp_apply(apply) => {
            find_packed_module_expr(arena.get_expr(apply.funct), arena).or_else(|| {
                apply
                    .args
                    .iter()
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
                mty_desc: crate::types::typedtree::ModuleTypeDesc::Tmty_ident(
                    path.clone(),
                    lid.clone(),
                ),
                mty_type: crate::types::decl::ModuleType::MtyIdent(path),
                mty_env: EnvRef(0),
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

fn typed_module_type(
    desc: crate::types::typedtree::ModuleTypeDesc,
    mty_type: crate::types::decl::ModuleType,
    mty_env: EnvRef,
    mty_loc: LocIdx,
    mty_attributes: Attributes,
) -> ModuleType {
    ModuleType {
        mty_desc: desc,
        mty_type,
        mty_env,
        mty_loc,
        mty_attributes,
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
fn module_type_from_typed_unpack_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    typed_expr: &Expression,
) -> Option<crate::types::decl::ModuleType> {
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

/// Extract semantic module type information from an unpack payload expression.
fn lookup_module_type_from_unpack_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    expr: &crate::parser::ast::Expression,
) -> Option<crate::types::decl::ModuleType> {
    let typed_expr = type_expression(tctx, env, expr).ok()?;
    module_type_from_typed_unpack_expr(tctx, env, arena, &typed_expr)
}

fn remove_module_type_aliases_for_typeof<'b>(
    mty: &crate::types::decl::ModuleType,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;
    use crate::types::decl::SignatureItem as SigItem;

    match mty {
        DeclMty::MtySignature(sig) => {
            let mut env = env.clone();
            let mut out = Vec::with_capacity(sig.len());
            for item in sig {
                match item {
                    SigItem::SigModule(id, md, rs) => {
                        let child_mty = match &md.md_type {
                            DeclMty::MtyAlias(_, _) => {
                                match scrape_alias_module_type(&md.md_type, &env, pers_env, ctx) {
                                    Some(scraped @ DeclMty::MtyAlias(_, _))
                                    | Some(scraped @ DeclMty::MtyIdent(_)) => scraped,
                                    Some(scraped) => remove_module_type_aliases_for_typeof(
                                        &scraped, &env, pers_env, ctx,
                                    ),
                                    None => md.md_type.clone(),
                                }
                            }
                            DeclMty::MtyIdent(_) => md.md_type.clone(),
                            other => {
                                remove_module_type_aliases_for_typeof(other, &env, pers_env, ctx)
                            }
                        };
                        let md = crate::types::decl::ModuleDeclaration {
                            md_type: child_mty.clone(),
                            ..md.clone()
                        };
                        env.add_module(id.clone(), md.clone());
                        out.push(SigItem::SigModule(id.clone(), md, *rs));
                    }
                    SigItem::SigModtype(id, mtd) => {
                        env.add_modtype(id.clone(), mtd.clone());
                        out.push(item.clone());
                    }
                    _ => out.push(item.clone()),
                }
            }
            DeclMty::MtySignature(out)
        }
        DeclMty::MtyAlias(_, _) => match scrape_alias_module_type(mty, env, pers_env, ctx) {
            Some(scraped @ DeclMty::MtyAlias(_, _)) | Some(scraped @ DeclMty::MtyIdent(_)) => {
                scraped
            }
            Some(scraped) => remove_module_type_aliases_for_typeof(&scraped, env, pers_env, ctx),
            None => mty.clone(),
        },
        DeclMty::MtyIdent(_) => mty.clone(),
        _ => mty.clone(),
    }
}

/// Look up semantic module type information for parsed module expressions.
/// This mirrors OCaml's behavior of using semantic module types for bindings.
pub fn lookup_module_type_from_parsed_module_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
) -> Option<crate::types::decl::ModuleType> {
    if let Some(cached) = tctx
        .module_expr_semantic_types
        .get(&mod_expr.pmod_loc)
        .cloned()
    {
        return Some(cached);
    }

    fn semantic_module_type_for_ident_expr<'a>(
        tctx: &mut TypeCheckContext<'a>,
        env: &Env,
        arena: &'a ParseArena,
        lid: &Located<LidentIdx>,
    ) -> Option<crate::types::decl::ModuleType> {
        let longident = arena.get_longident(lid.txt);
        let path = lookup_module_path_by_lid(
            longident,
            arena,
            env,
            &mut tctx.persistent_env,
            tctx.type_ctx,
        )?;
        let semantic_mty = lookup_module_type_by_lid(
            longident,
            arena,
            env,
            &mut tctx.persistent_env,
            tctx.type_ctx,
        )?;
        Some(strengthen_semantic_ident_module_type(
            env,
            &path,
            semantic_mty,
            &mut tctx.persistent_env,
            tctx.type_ctx,
        ))
    }

    let result = match &*mod_expr.pmod_desc {
        ParsedModuleExprDesc::Pmod_ident(lid) => semantic_module_type_for_ident_expr(
            tctx, env, arena, lid,
        ),
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
    };

    if let Some(ref semantic_mty) = result {
        tctx.module_expr_semantic_types
            .insert(mod_expr.pmod_loc, semantic_mty.clone());
    }
    result
}

fn strengthen_semantic_ident_module_type<'a>(
    env: &Env,
    path: &Path,
    semantic_mty: crate::types::decl::ModuleType,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;

    let mut semantic_mty = semantic_mty;
    let strengthen_path = match semantic_mty.clone() {
        DeclMty::MtyAlias(_, alias_path) => {
            let mut normalized = alias_path;
            while let Some(next) = crate::types::typecore::alias_target_for_module_path(
                &normalized,
                env,
                pers_env,
                ctx,
            ) {
                if next.same(&normalized) {
                    break;
                }
                normalized = next;
            }
            semantic_mty =
                scrape_alias_module_type(&semantic_mty, env, pers_env, ctx).unwrap_or(semantic_mty);
            env.normalize_path(&normalized)
        }
        _ => path.clone(),
    };
    crate::types::ctype::strengthen_module_type_for_inclusion_path(
        ctx,
        env,
        &strengthen_path,
        &semantic_mty,
    )
}

/// Translate a parsed module type (signature) into a decl::ModuleType.
/// Used for recursive module constraint signatures to populate the environment.
fn translate_module_type_to_decl_with_typed_hint<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mty: &crate::parser::ast::ModuleType,
    typed_hint: Option<&crate::types::typedtree::ModuleType>,
) -> TypeModResult<crate::types::decl::ModuleType> {
    use crate::parser::ast::ModuleTypeDesc as PMtyDesc;
    use crate::types::decl::{
        AliasPresence, ModuleType as DeclMty, SignatureItem as SigItem, ValueDescription,
    };
    use crate::types::typedtree::ModuleTypeDesc as TypedMtyDesc;
    use crate::types::typedtree::TypedSignatureItemDesc as TypedSigDesc;
    use crate::types::typemod::path_from_longident;

    match &*mty.pmty_desc {
        PMtyDesc::Pmty_signature(sig_items) => {
            let mut items = Vec::new();
            let mut sig_env = env.clone();
            let typed_sig_items = match typed_hint.map(|hint| &hint.mty_desc) {
                Some(TypedMtyDesc::Tmty_signature(sig)) => Some(sig.sig_items.as_slice()),
                _ => None,
            };
            for (sig_index, sig_item) in sig_items.iter().enumerate() {
                let typed_sig_item = typed_sig_items.and_then(|items| items.get(sig_index));
                match &*sig_item.psig_desc {
                    crate::parser::ast::SignatureItemDesc::Psig_value(vd) => {
                        let val_name = arena.get_string(vd.pval_name.txt);
                        let val_id = match typed_sig_item.map(|item| &item.sig_desc) {
                            Some(TypedSigDesc::Tsig_value(typed_vd)) => typed_vd.val_id.clone(),
                            _ => tctx.type_ctx.create_ident(val_name),
                        };
                        // Use transl_type_scheme pattern: begin_def/end_def/generalize
                        // OCaml: reset_type_variables() for each val declaration
                        tctx.type_variables.clear();
                        let ctx = tctx.type_ctx;
                        ctx.begin_def();
                        let (_typed_ct, val_type) =
                            transl_type(tctx, &sig_env, arena.get_core_type(vd.pval_type))?;
                        let ctx = tctx.type_ctx;
                        ctx.end_def();
                        crate::types::ctype::generalize(ctx, val_type);
                        // Match OCaml transl_value_decl parse_arity/get_arity side effects:
                        // expanding the generalized head seeds simple abbreviations so later
                        // instance() calls preserve physical sharing on nullary aliases.
                        crate::types::ctype::expand_head(ctx, &sig_env, val_type);
                        items.push(SigItem::SigValue(
                            val_id,
                            ValueDescription {
                                val_type,
                                val_kind: if vd.pval_prim.is_empty() {
                                    crate::types::decl::ValueKind::ValReg
                                } else {
                                    crate::types::decl::ValueKind::ValPrim(
                                        primitive_description_from_value_decl(
                                            arena,
                                            ctx,
                                            &sig_env,
                                            &vd.pval_prim,
                                            vd.pval_type,
                                            val_type,
                                        ),
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
                        let typed_type_decls = match typed_sig_item.map(|item| &item.sig_desc) {
                            Some(TypedSigDesc::Tsig_type(_, typed_decls))
                                if typed_decls.len() == decls.len() =>
                            {
                                Some(typed_decls.as_slice())
                            }
                            _ => None,
                        };

                        // Predeclare names so manifests can refer to siblings (matching OCaml).
                        for (decl_idx, decl) in decls.iter().enumerate() {
                            let type_id = typed_type_decls
                                .and_then(|typed_decls| typed_decls.get(decl_idx))
                                .map(|typed_decl| typed_decl.typ_id.clone())
                                .unwrap_or_else(|| {
                                    let type_name = arena.get_string(decl.ptype_name.txt);
                                    tctx.type_ctx.create_ident(type_name)
                                });
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
                                                            crate::types::predef::path_option();
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
                                                    let label_id = tctx.type_ctx.create_ident(lbl_name);
                                                    record_labels.push(crate::types::LabelDeclaration {
                                                        ld_id: label_id,
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
                                        let cstr_id = tctx.type_ctx.create_ident(cstr_name);
                                        constructors.push(crate::types::ConstructorDeclaration {
                                            cd_id: cstr_id,
                                            cd_args: cstr_args,
                                            cd_res: match &cstr.pcd_res {
                                                Some(res_core_type_idx) => {
                                                    let res_core_type =
                                                        arena.get_core_type(*res_core_type_idx);
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
                                        let (_typed_label_ty, mut lbl_type) = transl_type(
                                            tctx,
                                            &sig_env,
                                            arena.get_core_type(label.pld_type),
                                        )?;
                                        if label.pld_optional {
                                            let option_path = crate::types::predef::path_option();
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
                                        let label_id = tctx.type_ctx.create_ident(lbl_name);
                                        record_labels.push(crate::types::LabelDeclaration {
                                            ld_id: label_id,
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
                                type_variance: typed_type_decls
                                    .and_then(|typed_decls| typed_decls.get(decl_idx))
                                    .map(|typed_decl| typed_decl.typ_type.type_variance.clone())
                                    .unwrap_or(type_variance),
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
                        let (mod_id, typed_inner_mty) =
                            match typed_sig_item.map(|item| &item.sig_desc) {
                                Some(TypedSigDesc::Tsig_module(typed_md)) => {
                                    (typed_md.md_id.clone(), Some(&typed_md.md_type))
                                }
                                _ => (tctx.type_ctx.create_ident(mod_name), None),
                            };
                        let inner_mty = translate_module_type_to_decl_with_typed_hint(
                            tctx,
                            &sig_env,
                            arena,
                            arena.get_mod_type(md.pmd_type),
                            typed_inner_mty,
                        )?;
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
                        let (modtype_id, typed_inner_mty) =
                            match typed_sig_item.map(|item| &item.sig_desc) {
                                Some(TypedSigDesc::Tsig_modtype(typed_mtd)) => {
                                    (typed_mtd.mtd_id.clone(), typed_mtd.mtd_type.as_ref())
                                }
                                _ => (tctx.type_ctx.create_ident(modtype_name), None),
                            };
                        let mtd_type = pmtd
                            .pmtd_type
                            .as_ref()
                            .map(|inner_idx| {
                                translate_module_type_to_decl_with_typed_hint(
                                    tctx,
                                    &sig_env,
                                    arena,
                                    arena.get_mod_type(*inner_idx),
                                    typed_inner_mty,
                                )
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
                        if let Some((resolved_path, sig_items)) = sig_env.resolve_module_lid(
                            open_lid,
                            arena,
                            &mut tctx.persistent_env,
                            tctx.type_ctx,
                        ) {
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
            Ok(DeclMty::MtySignature(
                crate::types::includemod::simplify_signature(&items),
            ))
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
            let (param_id, typed_param_mty, typed_result_mty) =
                match typed_hint.map(|hint| &hint.mty_desc) {
                    Some(TypedMtyDesc::Tmty_functor(param, _name, param_mty, result_mty)) => (
                        param.clone(),
                        param_mty.as_deref(),
                        Some(result_mty.as_ref()),
                    ),
                    _ => (
                        tctx.type_ctx.create_ident(arena.get_string(name.txt)),
                        None,
                        None,
                    ),
                };
            let param_decl = match param_type {
                Some(pt_idx) => Some(Box::new(translate_module_type_to_decl_with_typed_hint(
                    tctx,
                    env,
                    arena,
                    arena.get_mod_type(*pt_idx),
                    typed_param_mty,
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
            let result_decl = translate_module_type_to_decl_with_typed_hint(
                tctx,
                &result_env,
                arena,
                arena.get_mod_type(*result_type_idx),
                typed_result_mty,
            )?;
            Ok(DeclMty::MtyFunctor {
                param: param_id,
                param_type: param_decl,
                result: Box::new(result_decl),
            })
        }
        PMtyDesc::Pmty_with(args) => {
            let (body_idx, constraints) = &**args;
            let typed_body_hint = match typed_hint.map(|hint| &hint.mty_desc) {
                Some(TypedMtyDesc::Tmty_with(body, _constraints)) => Some(body.as_ref()),
                _ => None,
            };
            let base_mty = translate_module_type_to_decl_with_typed_hint(
                tctx,
                env,
                arena,
                arena.get_mod_type(*body_idx),
                typed_body_hint,
            )?;
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
            lookup_module_type_from_parsed_module_expr(tctx, env, arena, me)
                .map(|mty| {
                    remove_module_type_aliases_for_typeof(
                        &mty,
                        env,
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )
                })
                .ok_or(TypeModError::InvalidModuleExpr(
                    arena.to_location(mty.pmty_loc),
                ))
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

fn translate_module_type_to_decl<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mty: &crate::parser::ast::ModuleType,
) -> TypeModResult<crate::types::decl::ModuleType> {
    translate_module_type_to_decl_with_typed_hint(tctx, env, arena, mty, None)
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

    fn qualify_local_module_type_path(path: &Path, maps: &LocalModuleTypePathMaps) -> Path {
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

    fn path_contains_apply(path: &Path) -> bool {
        match path {
            Path::Pident(_) => false,
            Path::Pdot(prefix, _, _) => path_contains_apply(prefix),
            Path::Papply(_, _) => true,
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
            let qualify_local_paths = !path_contains_apply(owner_path);

            for item in sig {
                if let SigItem::SigModule(id, md, _) = item {
                    let child_owner_path = Path::pdot(owner_path.clone(), id.name());
                    md.md_path = Some(child_owner_path.clone());
                    if qualify_local_paths {
                        qualify_local_module_type_paths(&mut md.md_type, &local_maps);
                    }
                    anchor_local_module_aliases_to_owner(&mut md.md_type, &child_owner_path);
                } else if let SigItem::SigModtype(id, mtd) = item {
                    if let Some(mty) = mtd.mtd_type.as_mut() {
                        if qualify_local_paths {
                            qualify_local_module_type_paths(mty, &local_maps);
                        }
                        let modtype_owner_path = Path::pdot(owner_path.clone(), id.name());
                        anchor_local_module_aliases_to_owner(mty, &modtype_owner_path);
                    }
                }
            }
        }
        DeclMty::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            if let Some(param_type) = param_type.as_mut() {
                anchor_local_module_aliases_to_owner(param_type, owner_path);
            }
            let result_owner_path = if param.name() != "*" {
                Path::Papply(
                    Box::new(owner_path.clone()),
                    Box::new(Path::pident(param.clone())),
                )
            } else {
                owner_path.clone()
            };
            anchor_local_module_aliases_to_owner(result, &result_owner_path);
        }
        DeclMty::MtyIdent(_) | DeclMty::MtyAlias(_, _) => {}
    }
}

/// Extract a `decl::ModuleType` from a typed module expression.
/// For structure modules, builds a signature from the structure items.
/// Convert a typed tree ModuleType to a decl ModuleType.
/// Used both in extract_module_type_from_mod_expr and in transl_signature
/// to add modules to sig_env for subsequent items.
pub(crate) fn decl_signature_from_typed_signature(
    sig: &crate::types::typedtree::TypedSignature,
) -> crate::types::decl::Signature {
    use crate::types::decl::{
        ModtypeDeclaration, ModuleDeclaration, SignatureItem as SigItem, ValueDescription,
        ValueKind,
    };
    use crate::types::typedtree::TypedSignatureItemDesc;

    let mut out = Vec::new();
    for item in &sig.sig_items {
        match &item.sig_desc {
            TypedSignatureItemDesc::Tsig_value(vd) => {
                let val_kind = if vd.val_prim.is_empty() {
                    ValueKind::ValReg
                } else {
                    ValueKind::ValPrim(crate::types::PrimitiveDescription {
                        prim_name: vd.val_prim.first().cloned().unwrap_or_default(),
                        prim_arity: 0,
                        prim_native_name: vd.val_prim.get(1).cloned().unwrap_or_default(),
                        prim_native_float: false,
                        prim_from_constructor: false,
                    })
                };
                out.push(SigItem::SigValue(
                    vd.val_id.clone(),
                    ValueDescription {
                        val_type: vd.val_desc.ctyp_type,
                        val_kind,
                        val_loc: crate::location::Location::none(),
                        val_attributes: vec![],
                        val_path: None,
                    },
                ));
            }
            TypedSignatureItemDesc::Tsig_type(rec_flag, decls) => {
                let statuses = sig_type_rec_statuses(*rec_flag, decls);
                for (decl, status) in decls.iter().zip(statuses) {
                    out.push(SigItem::SigType(
                        decl.typ_id.clone(),
                        decl.typ_type.clone(),
                        status,
                    ));
                }
            }
            TypedSignatureItemDesc::Tsig_typext(ext) => {
                for (i, ext_cstr) in ext.tyext_constructors.iter().enumerate() {
                    out.push(SigItem::SigTypext(
                        ext_cstr.ext_id.clone(),
                        ext_cstr.ext_type.clone(),
                        sig_ext_status(i),
                    ));
                }
            }
            TypedSignatureItemDesc::Tsig_exception(ext) => {
                out.push(SigItem::SigTypext(
                    ext.ext_id.clone(),
                    ext.ext_type.clone(),
                    crate::types::decl::ExtStatus::TextException,
                ));
            }
            TypedSignatureItemDesc::Tsig_module(md) => {
                out.push(SigItem::SigModule(
                    md.md_id.clone(),
                    ModuleDeclaration {
                        md_type: decl_module_type_from_typed(&md.md_type)
                            .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![])),
                        md_attributes: vec![],
                        md_loc: crate::location::Location::none(),
                        md_path: None,
                    },
                    crate::types::decl::RecStatus::TrecNot,
                ));
            }
            TypedSignatureItemDesc::Tsig_recmodule(decls) => {
                for (i, md) in decls.iter().enumerate() {
                    out.push(SigItem::SigModule(
                        md.md_id.clone(),
                        ModuleDeclaration {
                            md_type: decl_module_type_from_typed(&md.md_type)
                                .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![])),
                            md_attributes: vec![],
                            md_loc: crate::location::Location::none(),
                            md_path: None,
                        },
                        if i == 0 {
                            crate::types::decl::RecStatus::TrecFirst
                        } else {
                            crate::types::decl::RecStatus::TrecNext
                        },
                    ));
                }
            }
            TypedSignatureItemDesc::Tsig_modtype(mtd) => {
                out.push(SigItem::SigModtype(
                    mtd.mtd_id.clone(),
                    ModtypeDeclaration {
                        mtd_type: mtd.mtd_type.as_ref().and_then(decl_module_type_from_typed),
                        mtd_attributes: vec![],
                        mtd_loc: crate::location::Location::none(),
                    },
                ));
            }
            TypedSignatureItemDesc::Tsig_include(_)
            | TypedSignatureItemDesc::Tsig_open(_)
            | TypedSignatureItemDesc::Tsig_attribute(_) => {}
        }
    }
    crate::types::includemod::simplify_signature(&out)
}

pub(crate) fn decl_module_type_from_typed(
    mty: &ModuleType,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::typedtree::ModuleTypeDesc;
    match &mty.mty_desc {
        ModuleTypeDesc::Tmty_placeholder => None,
        _ => Some(mty.mty_type.clone()),
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

pub(crate) fn extract_module_type_from_mod_expr_with_ctx<'a>(
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
                rewrite_self_path(prefix, module_id, direct_items).map(|rewritten_prefix| {
                    Path::Pdot(Box::new(rewritten_prefix), name.clone(), *pos)
                })
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
                    rewrite_type(
                        desc.val_type,
                        module_id,
                        direct_items,
                        type_ctx,
                        &mut visited,
                    );
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
    let resolved_sig = crate::types::typecore::copy_resolved_module_signature_for_path(
        &path,
        env,
        &mut no_persistent_env,
        type_ctx,
    )
    .map(|(_, sig)| sig)
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

    let mut sig = sig;
    crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
        &sig,
        &path,
        &Path::pident(local_id.clone()),
        type_ctx,
    );
    crate::cmi::persistent_env::rewrite_sig_paths_by_path_prefix(
        &mut sig,
        &path,
        &Path::pident(local_id.clone()),
    );
    strip_self_module_prefix_in_sig(&sig, local_id, type_ctx);
    DeclMty::MtySignature(sig)
}

fn localize_alias_child_module_sig_paths_in_structure_sig(
    sig: &mut [crate::types::decl::SignatureItem],
    structure: &Structure,
    module_path: &Path,
    type_ctx: &crate::types::context::TypeContext<'_>,
) {
    use crate::types::decl::{ModuleType as DeclMty, SignatureItem};

    fn localize_alias_child_module_sig(
        sub_sig: &mut [crate::types::decl::SignatureItem],
        child_path: &Path,
        mod_expr: &ModuleExpr,
        type_ctx: &crate::types::context::TypeContext<'_>,
    ) {
        if matches!(
            mod_expr.mod_desc,
            ModuleExprDesc::Tmod_ident(Path::Pdot(..), _)
        ) {
            crate::types::typecore::rebind_direct_sig_type_family_to_access_path(
                type_ctx, child_path, sub_sig, true,
            );
            crate::cmi::persistent_env::substitute_type_paths_in_sig(sub_sig, child_path, type_ctx);
            crate::cmi::persistent_env::substitute_sig_decl_paths_in_place(sub_sig, child_path);
        }

        if let ModuleExprDesc::Tmod_structure(sub_structure) = &mod_expr.mod_desc {
            localize_alias_child_module_sig_paths_in_structure_sig(
                sub_sig,
                sub_structure,
                child_path,
                type_ctx,
            );
        }
    }

    let mut sig_cursor = 0usize;
    for item in &structure.str_items {
        match &item.str_desc {
            StructureItemDesc::Tstr_module(mb) => {
                while sig_cursor < sig.len() {
                    let current_index = sig_cursor;
                    sig_cursor += 1;
                    let SignatureItem::SigModule(id, md, _) = &mut sig[current_index] else {
                        continue;
                    };
                    if id.name() != mb.mb_id.name() {
                        continue;
                    }
                    if let DeclMty::MtySignature(sub_sig) = &mut md.md_type {
                        let child_path = Path::pdot(module_path.clone(), id.name());
                        localize_alias_child_module_sig(
                            sub_sig,
                            &child_path,
                            &mb.mb_expr,
                            type_ctx,
                        );
                    }
                    break;
                }
            }
            StructureItemDesc::Tstr_recmodule(mbs) => {
                for mb in mbs {
                    while sig_cursor < sig.len() {
                        let current_index = sig_cursor;
                        sig_cursor += 1;
                        let SignatureItem::SigModule(id, md, _) = &mut sig[current_index] else {
                            continue;
                        };
                        if id.name() != mb.mb_id.name() {
                            continue;
                        }
                        if let DeclMty::MtySignature(sub_sig) = &mut md.md_type {
                            let child_path = Path::pdot(module_path.clone(), id.name());
                            localize_alias_child_module_sig(
                                sub_sig,
                                &child_path,
                                &mb.mb_expr,
                                type_ctx,
                            );
                        }
                        break;
                    }
                }
            }
            _ => {}
        }
    }
}

fn module_expr_has_dotted_alias_child_modules(mod_expr: &ModuleExpr) -> bool {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(Path::Pdot(..), _) => true,
        ModuleExprDesc::Tmod_structure(structure) => {
            structure_has_dotted_alias_child_modules(structure)
        }
        ModuleExprDesc::Tmod_ident(_, _)
        | ModuleExprDesc::Tmod_apply(_, _, _)
        | ModuleExprDesc::Tmod_functor(_, _, _, _)
        | ModuleExprDesc::Tmod_constraint(_, _, _, _)
        | ModuleExprDesc::Tmod_unpack(_, _) => false,
    }
}

fn structure_has_dotted_alias_child_modules(structure: &Structure) -> bool {
    structure.str_items.iter().any(|item| match &item.str_desc {
        StructureItemDesc::Tstr_module(mb) => {
            module_expr_has_dotted_alias_child_modules(&mb.mb_expr)
        }
        StructureItemDesc::Tstr_recmodule(mbs) => mbs
            .iter()
            .any(|mb| module_expr_has_dotted_alias_child_modules(&mb.mb_expr)),
        _ => false,
    })
}

fn module_expr_contains_unpack_for_sig_localization(mod_expr: &ModuleExpr) -> bool {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(_, _) => false,
        ModuleExprDesc::Tmod_structure(structure) => {
            structure.str_items.iter().any(|item| match &item.str_desc {
                StructureItemDesc::Tstr_module(mb) => {
                    module_expr_contains_unpack_for_sig_localization(&mb.mb_expr)
                }
                StructureItemDesc::Tstr_recmodule(mbs) => mbs
                    .iter()
                    .any(|mb| module_expr_contains_unpack_for_sig_localization(&mb.mb_expr)),
                StructureItemDesc::Tstr_include(include) => {
                    module_expr_contains_unpack_for_sig_localization(&include.incl_mod)
                }
                _ => false,
            })
        }
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
        crate::cmi::persistent_env::rewrite_sig_by_path_prefix(sig, &old_path, &new_path, type_ctx);
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
                        if let ModuleExprDesc::Tmod_structure(sub_structure) = &mb.mb_expr.mod_desc
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
                                    sub_sig, &mb.mb_id, type_ctx,
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
        type_ctx: Option<&crate::types::context::TypeContext<'_>>,
    ) -> Option<crate::types::decl::Signature> {
        use crate::types::decl::ModuleType as DeclMty;
        fn anchored(
            owner_path: &Path,
            mty: &crate::types::decl::ModuleType,
        ) -> crate::types::decl::ModuleType {
            let mut mty = mty.clone();
            anchor_local_module_aliases_to_owner(&mut mty, owner_path);
            mty
        }

        fn substituted_and_anchored(
            parent_sig: &[crate::types::decl::SignatureItem],
            parent_path: &Path,
            owner_path: &Path,
            mty: &crate::types::decl::ModuleType,
            ctx: &crate::types::context::TypeContext<'_>,
        ) -> crate::types::decl::ModuleType {
            let mut mty = mty.clone();
            crate::cmi::persistent_env::substitute_type_paths_in_child_module_type(
                &mut mty,
                parent_sig,
                parent_path,
                ctx,
            );
            anchor_local_module_aliases_to_owner(&mut mty, owner_path);
            mty
        }

        fn resolve_path(
            path: &Path,
            env: &Env,
            type_ctx: Option<&crate::types::context::TypeContext<'_>>,
            visiting: &mut HashSet<Path>,
        ) -> Option<crate::types::decl::Signature> {
            use crate::types::decl::SignatureItem as SigItem;

            if !visiting.insert(path.clone()) {
                return None;
            }

            let result = match path {
                Path::Pident(id) => {
                    if let Ok(md) = env.lookup_module(&Path::pident(id.clone())) {
                        let anchored_mty = anchored(&Path::pident(id.clone()), &md.md_type);
                        if let Some(sig) = resolve_mty(&anchored_mty, env, type_ctx, visiting) {
                            return Some(sig);
                        }
                    }
                    if let Ok(mtd) = env.lookup_modtype(&Path::pident(id.clone())) {
                        if let Some(mty) = &mtd.mtd_type {
                            let anchored_mty = anchored(&Path::pident(id.clone()), mty);
                            return resolve_mty(&anchored_mty, env, type_ctx, visiting);
                        }
                    }
                    None
                }
                Path::Pdot(parent, name, _) => {
                    if let Some(type_ctx) = type_ctx {
                        let mut no_persistent_env = None;
                        if let Some((_, owner_path, md)) =
                            crate::types::typecore::lookup_module_in_resolved_path(
                                parent,
                                name,
                                env,
                                &mut no_persistent_env,
                                type_ctx,
                            )
                        {
                            let child_mty = anchored(&owner_path, &md.md_type);
                            return resolve_mty(&child_mty, env, Some(type_ctx), visiting);
                        }
                        if let Some((parent_access_path, mtd)) =
                            crate::types::typecore::lookup_modtype_in_resolved_path(
                                parent,
                                name,
                                env,
                                &mut no_persistent_env,
                                type_ctx,
                            )
                        {
                            if let Some(mty) = &mtd.mtd_type {
                                let owner_path = Path::pdot(parent_access_path, name.to_string());
                                let child_mty = anchored(&owner_path, mty);
                                return resolve_mty(&child_mty, env, Some(type_ctx), visiting);
                            }
                        }
                    }

                    let parent_sig = resolve_path(parent, env, type_ctx, visiting)?;
                    let owner_path = Path::pdot((**parent).clone(), name);
                    parent_sig.iter().find_map(|item| match item {
                        SigItem::SigModule(id, md, _) if id.name() == name.as_str() => {
                            let child_mty = if let Some(type_ctx) = type_ctx {
                                substituted_and_anchored(
                                    &parent_sig,
                                    parent,
                                    &owner_path,
                                    &md.md_type,
                                    type_ctx,
                                )
                            } else {
                                anchored(&owner_path, &md.md_type)
                            };
                            resolve_mty(&child_mty, env, type_ctx, visiting)
                        }
                        SigItem::SigModtype(id, mtd) if id.name() == name.as_str() => {
                            mtd.mtd_type.as_ref().and_then(|mty| {
                                let child_mty = if let Some(type_ctx) = type_ctx {
                                    substituted_and_anchored(
                                        &parent_sig,
                                        parent,
                                        &owner_path,
                                        mty,
                                        type_ctx,
                                    )
                                } else {
                                    anchored(&owner_path, mty)
                                };
                                resolve_mty(&child_mty, env, type_ctx, visiting)
                            })
                        }
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
            type_ctx: Option<&crate::types::context::TypeContext<'_>>,
            visiting: &mut HashSet<Path>,
        ) -> Option<crate::types::decl::Signature> {
            match mty {
                DeclMty::MtySignature(sig) => Some(sig.clone()),
                DeclMty::MtyIdent(path) | DeclMty::MtyAlias(_, path) => {
                    resolve_path(path, env, type_ctx, visiting)
                }
                _ => None,
            }
        }

        let mut visiting = HashSet::new();
        resolve_mty(mty, env, type_ctx, &mut visiting)
    }

    fn resolve_module_type_path_in_env(
        path: &Path,
        env: &Env,
        type_ctx: Option<&crate::types::context::TypeContext<'_>>,
    ) -> Option<crate::types::decl::ModuleType> {
        use crate::types::decl::ModuleType as DeclMty;
        use crate::types::decl::SignatureItem as SigItem;

        fn anchored(
            owner_path: &Path,
            mty: &crate::types::decl::ModuleType,
        ) -> crate::types::decl::ModuleType {
            let mut mty = mty.clone();
            anchor_local_module_aliases_to_owner(&mut mty, owner_path);
            mty
        }

        fn substituted_and_anchored(
            parent_sig: &[crate::types::decl::SignatureItem],
            parent_path: &Path,
            owner_path: &Path,
            mty: &crate::types::decl::ModuleType,
            ctx: &crate::types::context::TypeContext<'_>,
        ) -> crate::types::decl::ModuleType {
            let mut mty = mty.clone();
            crate::cmi::persistent_env::substitute_type_paths_in_child_module_type(
                &mut mty,
                parent_sig,
                parent_path,
                ctx,
            );
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
                if let Some(type_ctx) = type_ctx {
                    let mut no_persistent_env = None;
                    if let Some((_, owner_path, md)) =
                        crate::types::typecore::lookup_module_in_resolved_path(
                            parent,
                            name,
                            env,
                            &mut no_persistent_env,
                            type_ctx,
                        )
                    {
                        return Some(anchored(&owner_path, &md.md_type));
                    }
                    if let Some((parent_access_path, mtd)) =
                        crate::types::typecore::lookup_modtype_in_resolved_path(
                            parent,
                            name,
                            env,
                            &mut no_persistent_env,
                            type_ctx,
                        )
                    {
                        if let Some(mty) = &mtd.mtd_type {
                            let owner_path = Path::pdot(parent_access_path, name.to_string());
                            return Some(anchored(&owner_path, mty));
                        }
                    }
                }

                let parent_mty = resolve_module_type_path_in_env(parent, env, type_ctx)?;
                let parent_sig = resolve_modtype_to_sig_in_env(&parent_mty, env, type_ctx)?;
                let owner_path = Path::pdot((**parent).clone(), name);
                for item in &parent_sig {
                    match item {
                        SigItem::SigModule(id, md, _) if id.name() == name.as_str() => {
                            if let Some(type_ctx) = type_ctx {
                                return Some(substituted_and_anchored(
                                    &parent_sig,
                                    parent,
                                    &owner_path,
                                    &md.md_type,
                                    type_ctx,
                                ));
                            }
                            return Some(anchored(&owner_path, &md.md_type));
                        }
                        SigItem::SigModtype(id, mtd) if id.name() == name.as_str() => {
                            if let Some(mty) = &mtd.mtd_type {
                                if let Some(type_ctx) = type_ctx {
                                    return Some(substituted_and_anchored(
                                        &parent_sig,
                                        parent,
                                        &owner_path,
                                        mty,
                                        type_ctx,
                                    ));
                                }
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
            ModuleExprDesc::Tmod_structure(structure) => {
                structure.str_items.iter().any(|item| match &item.str_desc {
                    StructureItemDesc::Tstr_module(mb) => module_expr_contains_unpack(&mb.mb_expr),
                    StructureItemDesc::Tstr_recmodule(mbs) => mbs
                        .iter()
                        .any(|mb| module_expr_contains_unpack(&mb.mb_expr)),
                    StructureItemDesc::Tstr_include(include) => {
                        module_expr_contains_unpack(&include.incl_mod)
                    }
                    _ => false,
                })
            }
            ModuleExprDesc::Tmod_apply(functor, arg, _) => {
                module_expr_contains_unpack(functor) || module_expr_contains_unpack(arg)
            }
            ModuleExprDesc::Tmod_functor(_, _, _, body) => module_expr_contains_unpack(body),
            ModuleExprDesc::Tmod_constraint(inner, _, _, _) => module_expr_contains_unpack(inner),
            ModuleExprDesc::Tmod_unpack(_, _) => true,
        }
    }

    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(_, _) => Some(mod_expr.mod_type.clone()),
        ModuleExprDesc::Tmod_unpack(_, mty) => Some(mty.clone()),
        ModuleExprDesc::Tmod_structure(structure) => {
            let has_include = structure
                .str_items
                .iter()
                .any(|item| matches!(item.str_desc, StructureItemDesc::Tstr_include(_)));
            let needs_precise_structure_sig =
                structure.str_items.iter().any(|item| match &item.str_desc {
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
                            val_kind: crate::types::decl::ValueKind::ValPrim(
                                primitive_description_from_typed_value_desc(
                                    type_ctx,
                                    current_env,
                                    vd,
                                ),
                            ),
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
                            .or_else(|| {
                                extract_module_type_from_mod_expr_with_resolver(
                                    &mb.mb_expr,
                                    current_env,
                                    type_ctx,
                                    resolve_ident_sig,
                                )
                            })
                            .unwrap_or(DeclMty::MtySignature(vec![]));
                        let inner_mty = if matches!(inner_mty, DeclMty::MtyAlias(..)) {
                            inner_mty
                        } else {
                            localize_exported_structure_module_type(
                                inner_mty,
                                &mb.mb_id,
                                current_env,
                                type_ctx,
                            )
                        };
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
                                .or_else(|| {
                                    extract_module_type_from_mod_expr_with_resolver(
                                        &mb.mb_expr,
                                        current_env,
                                        type_ctx,
                                        resolve_ident_sig,
                                    )
                                })
                                .unwrap_or(DeclMty::MtySignature(vec![]));
                            let inner_mty = if matches!(inner_mty, DeclMty::MtyAlias(..)) {
                                inner_mty
                            } else {
                                localize_exported_structure_module_type(
                                    inner_mty,
                                    &mb.mb_id,
                                    current_env,
                                    type_ctx,
                                )
                            };
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
                                let inner_sig_opt = match inner_mty {
                                    DeclMty::MtySignature(inner_sig) => Some(inner_sig),
                                    other => current_env
                                        .and_then(|env| resolve_modtype_to_sig_in_env(&other, env, type_ctx))
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
                                                                    type_ctx,
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
                                    let found_sig: Option<Vec<SigItem>> =
                                        sig_items.iter().find_map(|si| {
                                            if let SigItem::SigModule(id, md, _) = si {
                                                if id.name() == mod_name.as_str() {
                                                    return match &md.md_type {
                                                        DeclMty::MtySignature(inner) => {
                                                            Some(inner.clone())
                                                        }
                                                        other => current_env.and_then(|env| {
                                                            resolve_modtype_to_sig_in_env(
                                                                other, env, type_ctx,
                                                            )
                                                        }),
                                                    };
                                                }
                                            }
                                            None
                                        });
                                    if let Some(inner_sig) = found_sig {
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
                                            type_ctx,
                                        ) {
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
            let extracted_functor_mty = extract_module_type_from_mod_expr_with_resolver(
                functor,
                env,
                type_ctx,
                resolve_ident_sig,
            );
            if let Some(functor_mty) = extracted_functor_mty {
                let resolved_functor_mty = match &functor_mty {
                    DeclMty::MtyIdent(path) | DeclMty::MtyAlias(_, path) => env
                        .and_then(|env| resolve_module_type_path_in_env(path, env, type_ctx))
                        .unwrap_or(functor_mty),
                    _ => functor_mty,
                };
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
            Some(mod_expr.mod_type.clone())
        }
        ModuleExprDesc::Tmod_constraint(inner, constrained_mty, modtype_constraint, _) => {
            // OCaml keeps the constrained module type as the semantic type
            // exposed by a constrained module expression.
            let constrained = match modtype_constraint {
                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(mty) => {
                    decl_module_type_from_typed_module_type(mty)
                }
                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit => {
                    Some(constrained_mty.clone()).or_else(
                        || match &inner.mod_desc {
                            ModuleExprDesc::Tmod_structure(structure) => {
                                Some(DeclMty::MtySignature(
                                    crate::types::includemod::simplify_signature(
                                        &structure.str_type,
                                    ),
                                ))
                            }
                            _ => None,
                        },
                    )
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
            let path_clone = path.clone();
            let env_ref = tctx.type_ctx.store_typed_env(env);
            let alias_mod_type = crate::types::decl::ModuleType::MtyAlias(
                crate::types::decl::AliasPresence::MtaAbsent,
                path.clone(),
            );
            let semantic_mod_type = if alias {
                alias_mod_type.clone()
            } else {
                mod_type
                    .clone()
                    .map(|mty| {
                        strengthen_semantic_ident_module_type(
                            env,
                            &path,
                            mty,
                            &mut tctx.persistent_env,
                            tctx.type_ctx,
                        )
                    })
                    .unwrap_or_else(|| crate::types::decl::ModuleType::MtyIdent(path.clone()))
            };
            let ident_mod = ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_ident(path, lid.clone()),
                mod_loc: loc,
                mod_type: semantic_mod_type,
                mod_env: env_ref,
                mod_attributes: mod_expr.pmod_attributes.clone(),
            };

            if !alias
                && matches!(
                    mod_type,
                    Some(crate::types::decl::ModuleType::MtyAlias(_, _))
                )
            {
                // OCaml (typemod.ml line 1245-1252): when the module type is an alias
                // and we're not in alias mode, wrap with Tcoerce_alias(p1, Tcoerce_none)
                // where p1 is the alias target path. The inner Tmod_ident should have
                // mod_type = Mty_alias(Mta_absent, path).
                let alias_target = match &mod_type {
                    Some(crate::types::decl::ModuleType::MtyAlias(_, p1)) => {
                        // Match OCaml typemod.ml line 1246: normalize the alias target
                        let mut normalized = p1.clone();
                        while let Some(next) = crate::types::typecore::alias_target_for_module_path(
                            &normalized,
                            env,
                            &mut tctx.persistent_env,
                            tctx.type_ctx,
                        ) {
                            if next.same(&normalized) {
                                break;
                            }
                            normalized = next;
                        }
                        env.normalize_path(&normalized)
                    }
                    _ => path_clone.clone(),
                };
                let mut inner = ident_mod;
                inner.mod_type = crate::types::decl::ModuleType::MtyAlias(
                    crate::types::decl::AliasPresence::MtaAbsent,
                    path_clone.clone(),
                );
                let constrained_mod_type = scrape_alias_module_type(
                    &crate::types::decl::ModuleType::MtyIdent(alias_target.clone()),
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .unwrap_or_else(|| crate::types::decl::ModuleType::MtyIdent(alias_target.clone()));
                let outer_mod_type = strengthen_semantic_ident_module_type(
                    env,
                    &alias_target,
                    constrained_mod_type.clone(),
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                );

                Ok(ModuleExpr {
                    mod_desc: ModuleExprDesc::Tmod_constraint(
                        Box::new(inner),
                        constrained_mod_type,
                        crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
                        ModuleCoercion::Tcoerce_alias(
                            env_ref,
                            alias_target,
                            Box::new(ModuleCoercion::Tcoerce_none),
                        ),
                    ),
                    mod_loc: loc,
                    mod_type: outer_mod_type,
                    mod_env: env_ref,
                    mod_attributes: mod_expr.pmod_attributes.clone(),
                })
            } else {
                Ok(ident_mod)
            }
        }

        ParsedModuleExprDesc::Pmod_structure(items) => {
            // Module structure: { ... }
            let (structure, _new_env) = type_structure(tctx, env, arena, items)?;
            let env_ref = tctx.type_ctx.store_typed_env(env);
            let structure_mty =
                crate::types::decl::ModuleType::MtySignature(structure.str_type.clone());

            // Like OCaml: if simplify_signature would shrink the signature
            // (duplicate value names), wrap in Tmod_constraint implicit
            let needs_constraint = simplified_structure_signature(&structure).is_some();

            let md = ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_structure(structure),
                mod_loc: loc,
                mod_type: structure_mty.clone(),
                mod_env: env_ref,
                mod_attributes: Attributes::new(),
            };

            if needs_constraint {
                let simplified =
                    crate::types::decl::ModuleType::MtySignature(
                        match &md.mod_type {
                            crate::types::decl::ModuleType::MtySignature(sig) => {
                                crate::types::includemod::simplify_signature(sig)
                            }
                            _ => unreachable!("structure modules always produce signatures"),
                        },
                    );
                Ok(ModuleExpr {
                    mod_desc: ModuleExprDesc::Tmod_constraint(
                        Box::new(md),
                        simplified.clone(),
                        crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
                        ModuleCoercion::Tcoerce_none,
                    ),
                    mod_loc: loc,
                    mod_type: simplified,
                    mod_env: env_ref,
                    mod_attributes: mod_expr.pmod_attributes.clone(),
                })
            } else {
                Ok(ModuleExpr {
                    mod_desc: md.mod_desc,
                    mod_loc: loc,
                    mod_type: md.mod_type,
                    mod_env: env_ref,
                    mod_attributes: mod_expr.pmod_attributes.clone(),
                })
            }
        }

        ParsedModuleExprDesc::Pmod_functor(inner) => {
            let (ref name, ref param_type, ref body_idx) = **inner;
            // Functor: (X: S) => ME
            let param_name = arena.get_string(name.txt).to_string();
            let param_id = tctx.type_ctx.create_ident(&param_name);

            // Translate parameter type and extend environment with the functor parameter
            let typed_param_type = match param_type {
                Some(pt) => Some(Box::new(transl_modtype(
                    tctx,
                    env,
                    arena,
                    arena.get_mod_type(*pt),
                )?)),
                None => None,
            };

            // Extend environment with the functor parameter module
            let mut functor_env = env.clone();
            if let Some(pt) = param_type {
                if let Ok(param_decl_type) =
                    translate_module_type_to_decl(tctx, env, arena, arena.get_mod_type(*pt))
                {
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
            let env_ref = tctx.type_ctx.store_typed_env(env);

            // Type check the functor body with the extended environment
            let body = arena.get_mod_expr(*body_idx);
            let typed_body = type_module_expr_with_alias(tctx, &functor_env, arena, body, false)?;
            let functor_mty = crate::types::decl::ModuleType::MtyFunctor {
                param: param_id.clone(),
                param_type: typed_param_type
                    .as_ref()
                    .map(|mty| Box::new(mty.mty_type.clone())),
                result: Box::new(typed_body.mod_type.clone()),
            };

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
                mod_type: functor_mty,
                mod_env: env_ref,
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_apply(functor_idx, arg_idx) => {
            // Functor application: F(M)
            let functor = arena.get_mod_expr(*functor_idx);
            let arg = arena.get_mod_expr(*arg_idx);
            let typed_functor = type_module_expr_with_alias(tctx, env, arena, functor, false)?;
            let typed_arg = type_module_expr_with_alias(tctx, env, arena, arg, false)?;
            let arg_path = path_of_typed_module_expr(&typed_arg);
            let arg_mty = typed_arg.mod_type.clone();
            let functor_mty = typed_functor.mod_type.clone();
            let functor_mty = scrape_alias_module_type(
                &functor_mty,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or(functor_mty);
            let env_ref = tctx.type_ctx.store_typed_env(env);
            let coercion = match &functor_mty {
                crate::types::decl::ModuleType::MtyFunctor { param_type, .. } => {
                    let param_mty = param_type
                        .as_ref()
                        .map(|inner| (**inner).clone())
                        .unwrap_or_else(|| crate::types::decl::ModuleType::MtySignature(vec![]));
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
            let applied_mty = match &functor_mty {
                crate::types::decl::ModuleType::MtyFunctor { param, result, .. } => arg_path
                    .as_ref()
                    .map(|path| {
                        substitute_functor_param_in_module_type(result, param, path, tctx.type_ctx)
                    })
                    .unwrap_or_else(|| (**result).clone()),
                _ => crate::types::decl::ModuleType::MtySignature(vec![]),
            };
            let typed_apply = ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_apply(
                    Box::new(typed_functor),
                    Box::new(typed_arg),
                    coercion,
                ),
                mod_loc: loc,
                mod_type: applied_mty.clone(),
                mod_env: env_ref,
                mod_attributes: mod_expr.pmod_attributes.clone(),
            };
            tctx.module_expr_semantic_types
                .insert(mod_expr.pmod_loc, applied_mty);
            Ok(typed_apply)
        }

        ParsedModuleExprDesc::Pmod_constraint(mod_expr_inner_idx, mod_type_idx) => {
            // Constrained module: (ME: MT)
            let mod_expr_inner = arena.get_mod_expr(*mod_expr_inner_idx);
            let typed_mod = type_module_expr_with_alias(tctx, env, arena, mod_expr_inner, alias)?;
            let typed_mty = transl_modtype(tctx, env, arena, arena.get_mod_type(*mod_type_idx))?;
            let parsed_mty = arena.get_mod_type(*mod_type_idx);
            let decl_mty = translate_module_type_to_decl_with_typed_hint(
                tctx,
                env,
                arena,
                parsed_mty,
                Some(&typed_mty),
            )?;
            wrap_constraint_with_decl_mty(
                tctx,
                env,
                typed_mod,
                typed_mty.clone(),
                decl_mty,
                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(Box::new(
                    typed_mty,
                )),
                loc,
                mod_expr.pmod_attributes.clone(),
            )
        }

        ParsedModuleExprDesc::Pmod_unpack(expr_idx) => {
            // Unpack: unpack(E)
            let expr = arena.get_expr(*expr_idx);
            let typed_expr = type_expression(tctx, env, expr)?;
            let expanded =
                crate::types::ctype::expand_head(tctx.type_ctx, env, typed_expr.exp_type);
            let unpack_mty = match &*tctx.type_ctx.get_desc(tctx.type_ctx.repr(expanded)) {
                crate::types::type_expr::TypeDesc::Tpackage { path, lids, args } => {
                    module_type_from_typed_unpack_expr(tctx, env, arena, &typed_expr).unwrap_or_else(
                        || {
                            modtype_of_package(
                                env,
                                path,
                                lids,
                                args,
                                arena,
                                &mut tctx.persistent_env,
                                tctx.type_ctx,
                            )
                            .unwrap_or_else(|| crate::types::decl::ModuleType::MtyIdent(path.clone()))
                        },
                    )
                }
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
            let env_ref = tctx.type_ctx.store_typed_env(env);
            tctx.module_expr_semantic_types
                .insert(mod_expr.pmod_loc, unpack_mty.clone());

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_unpack(typed_expr, unpack_mty.clone()),
                mod_loc: loc,
                mod_type: unpack_mty,
                mod_env: env_ref,
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
                mod_type: crate::types::decl::ModuleType::MtySignature(vec![]),
                mod_env: tctx.type_ctx.store_typed_env(env),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }
    }
}

fn wrap_constraint<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arg: ModuleExpr,
    mty: ModuleType,
    explicit: crate::types::typedtree::ModuleTypeConstraint,
    mod_loc: LocIdx,
    mod_attributes: Attributes,
) -> TypeModResult<ModuleExpr> {
    let decl_mty = decl_module_type_from_typed(&mty)
        .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![]));
    let arg_mty = extract_module_type_from_mod_expr_with_ctx(&arg, Some(env), tctx.type_ctx)
        .or_else(|| Some(arg.mod_type.clone()))
        .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![]));
    wrap_constraint_with_decl_and_arg_mty(
        tctx,
        env,
        arg,
        mty,
        arg_mty,
        decl_mty,
        explicit,
        mod_loc,
        mod_attributes,
    )
}

fn wrap_constraint_with_decl_mty<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arg: ModuleExpr,
    mty: ModuleType,
    decl_mty: crate::types::decl::ModuleType,
    explicit: crate::types::typedtree::ModuleTypeConstraint,
    mod_loc: LocIdx,
    mod_attributes: Attributes,
) -> TypeModResult<ModuleExpr> {
    let arg_mty = decl_module_type_from_typed_module_expr_for_constraint_arg(&arg)
        .or_else(|| extract_module_type_from_mod_expr_with_ctx(&arg, Some(env), tctx.type_ctx))
        .or_else(|| Some(arg.mod_type.clone()))
        .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![]));
    wrap_constraint_with_decl_and_arg_mty(
        tctx,
        env,
        arg,
        mty,
        arg_mty,
        decl_mty,
        explicit,
        mod_loc,
        mod_attributes,
    )
}

fn wrap_constraint_with_decl_and_arg_mty<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arg: ModuleExpr,
    mty: ModuleType,
    arg_mty: crate::types::decl::ModuleType,
    decl_mty: crate::types::decl::ModuleType,
    explicit: crate::types::typedtree::ModuleTypeConstraint,
    mod_loc: LocIdx,
    mod_attributes: Attributes,
) -> TypeModResult<ModuleExpr> {
    let coercion = crate::types::includemod::modtypes(tctx.type_ctx, env, &arg_mty, &decl_mty)
        .map_err(|err| TypeModError::SignatureMismatch {
            expected: format!("{decl_mty:?}"),
            found: format!("{err:?}"),
        })?;
    let env_ref = tctx.type_ctx.store_typed_env(env);

    Ok(ModuleExpr {
        mod_desc: ModuleExprDesc::Tmod_constraint(
            Box::new(arg),
            decl_mty.clone(),
            explicit,
            coercion,
        ),
        mod_loc,
        mod_type: decl_mty,
        mod_env: env_ref,
        mod_attributes,
    })
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
            let semantic_mty = lookup_module_type_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or_else(|| crate::types::decl::ModuleType::MtyIdent(path.clone()));

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_ident(path, lid.clone()),
                mod_loc: mod_expr.pmod_loc,
                mod_type: semantic_mty,
                mod_env: tctx.type_ctx.store_typed_env(env),
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
    let env_ref = tctx.type_ctx.store_typed_env(env);

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
            let param_id = tctx.type_ctx.create_ident(arena.get_string(name.txt));
            let typed_param = match param_type {
                Some(pt) => Some(Box::new(transl_modtype(
                    tctx,
                    env,
                    arena,
                    arena.get_mod_type(*pt),
                )?)),
                None => None,
            };
            let param_decl = match param_type {
                Some(pt) => Some(translate_module_type_to_decl_with_typed_hint(
                    tctx,
                    env,
                    arena,
                    arena.get_mod_type(*pt),
                    typed_param.as_deref(),
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
            let base_mty = decl_module_type_from_typed(&typed_body);
            let typed_constraints =
                transl_with_constraints(tctx, env, arena, base_mty.as_ref(), constraints)?;
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
    let mut typed = TMty {
        mty_desc: desc,
        mty_type: crate::types::decl::ModuleType::MtySignature(vec![]),
        mty_env: env_ref,
        mty_loc: loc,
        mty_attributes: attrs,
    };
    typed.mty_type = translate_module_type_to_decl_with_typed_hint(
        tctx,
        env,
        arena,
        smty,
        Some(&typed),
    )
    .unwrap_or_else(|_| crate::types::decl::ModuleType::MtySignature(vec![]));
    Ok(typed)
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
                let id = ctx.create_ident(&name_str);
                // Use transl_type_scheme pattern: begin_def/end_def/generalize
                // OCaml: reset_type_variables() for each val declaration
                tctx.type_variables.clear();
                let ctx = tctx.type_ctx;
                ctx.begin_def();
                let (typed_ctype, val_ty) =
                    transl_type(tctx, &sig_env, arena.get_core_type(vd.pval_type))?;
                ctx.end_def();
                crate::types::ctype::generalize(ctx, val_ty);
                // Keep signature value declaration abbreviation memo side effects
                // aligned with OCaml transl_value_decl.
                crate::types::ctype::expand_head(ctx, &sig_env, val_ty);
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
                // Match OCaml transl_signature/Typedecl.transl_type_decl:
                // all signature types, including abstract ones, enter the
                // threaded environment for subsequent signature items.
                for td in &typed_decls {
                    sig_env.add_type(td.typ_id.clone(), td.typ_type.clone());
                }
                TSigDesc::Tsig_type(*rec_flag, typed_decls)
            }
            PSigDesc::Psig_module(md) => {
                let name_str = arena.get_string(md.pmd_name.txt).to_string();
                let id = ctx.create_ident(&name_str);
                let typed_mty =
                    transl_modtype(tctx, &sig_env, arena, arena.get_mod_type(md.pmd_type))?;
                // Add module to sig_env so subsequent items (Psig_open etc.) can find it.
                // This matches OCaml's transl_sig: `let newenv = Env.enter_module_declaration id md env`.
                let decl_mty = translate_module_type_to_decl_with_typed_hint(
                    tctx,
                    &sig_env,
                    arena,
                    arena.get_mod_type(md.pmd_type),
                    Some(&typed_mty),
                )?;
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
                let id = ctx.create_ident(&name_str);
                let typed_mty = match &mtd.pmtd_type {
                    Some(mt) => Some(transl_modtype(
                        tctx,
                        &sig_env,
                        arena,
                        arena.get_mod_type(*mt),
                    )?),
                    None => None,
                };
                let decl_mtd = crate::types::ModtypeDeclaration {
                    mtd_type: match &mtd.pmtd_type {
                        Some(mt) => Some(translate_module_type_to_decl_with_typed_hint(
                            tctx,
                            &sig_env,
                            arena,
                            arena.get_mod_type(*mt),
                            typed_mty.as_ref(),
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
                let path = if let Some((resolved_path, sig_items)) = sig_env.resolve_module_lid(
                    open_lid,
                    arena,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                ) {
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
    let mut current_env = env.clone_preserve_id();

    for item in items {
        let ctx = tctx.type_ctx;
        ctx.init_def(ctx.current_stamp());
        tctx.set_unify_env(&current_env);
        let (typed_item, item_sig, new_env) = type_structure_item(tctx, &current_env, arena, item)?;
        sig_items.extend(item_sig);
        typed_items.push(typed_item);
        current_env = new_env;

        // Check for @comptime.derive attributes on type declarations.
        // When a registered derive handler exists for an attribute, it will be
        // called with the typeInfo value for the type. For now, derive handlers
        // are registered but not yet invoked (waiting for predefined typeInfo type).
        if let ParsedStructureItemDesc::Pstr_type(inner) = &*item.pstr_desc {
            let (_, ref decls) = **inner;
            for decl in decls {
                for (attr_name_loc, _payload) in decl.ptype_attributes.iter() {
                    let attr_name = arena.get_string(attr_name_loc.txt);
                    if tctx.comptime_functions.contains_key(attr_name) {
                        // TODO: invoke the derive handler with @typeInfo for this type.
                        // Once typeInfo is a predefined type, this will:
                        // 1. Build typeInfo value for the type
                        // 2. Call the registered handler with it
                        // 3. Splice the result after the type declaration
                    }
                }
            }
        }
    }

    // Evaluate pending @comptime type-builder bindings and emit type decls.
    // (Currently unused — type builders are emitted inline at their Pstr_value.
    //  This path reserved for future use, e.g., generic type builders.)
    let pending: Vec<_> = std::mem::take(&mut tctx.pending_type_builders);
    for (name, expr_idx) in pending {
        let body_expr = arena.get_expr(expr_idx).clone();
        match crate::types::typecore::evaluate_type_builder(tctx, &current_env, &body_expr) {
            Ok(crate::types::comptime::TypeBuilderResult::Variant(ctor_names)) => {
                let ctx = tctx.type_ctx;
                let type_id = ctx.create_ident(&name);

                // Build internal ConstructorDeclarations
                let mut constructors = Vec::new();
                for cname in &ctor_names {
                    let cid = ctx.create_ident(cname);
                    constructors.push(crate::types::decl::ConstructorDeclaration {
                        cd_id: cid,
                        cd_args: crate::types::decl::ConstructorArguments::CstrTuple(vec![]),
                        cd_res: None,
                        cd_loc: crate::location::Location::none(),
                        cd_attributes: vec![],
                    });
                }

                let decl = crate::types::TypeDeclaration {
                    type_params: vec![],
                    type_arity: 0,
                    type_kind: crate::types::TypeKind::TypeVariant(constructors),
                    type_private: crate::types::asttypes::PrivateFlag::Public,
                    type_manifest: None,
                    type_variance: vec![],
                    type_newtype_level: None,
                    type_loc: crate::location::Location::none(),
                    type_attributes: vec![],
                    type_immediate: false,
                    type_unboxed: crate::types::UnboxedStatus::default(),
                    type_inlined_types: vec![],
                    type_path: Some(crate::types::Path::pident(type_id.clone())),
                };
                current_env.add_type(type_id.clone(), decl.clone());

                // Also register in global type store so @typeInfo can find it
                ctx.register_type_decl(&name, decl.clone());
                if type_id.stamp() != 0 {
                    ctx.register_type_decl_by_stamp(type_id.stamp(), decl.clone());
                }

                // Add constructors to environment so they can be referenced
                let type_path = crate::types::Path::pident(type_id.clone());
                let num_consts = ctor_names.len() as i32;
                for (i, cname) in ctor_names.iter().enumerate() {
                    let cstr_desc = crate::types::ConstructorDescription {
                        cstr_name: cname.clone(),
                        cstr_res: ctx.new_generic_constr(type_path.clone(), vec![]),
                        cstr_existentials: vec![],
                        cstr_args: vec![],
                        cstr_arity: 0,
                        cstr_tag: crate::types::decl::ConstructorTag::CstrConstant(i as i32),
                        cstr_consts: num_consts,
                        cstr_nonconsts: 0,
                        cstr_generalized: false,
                        cstr_private: crate::types::asttypes::PrivateFlag::Public,
                        cstr_loc: crate::location::Location::none(),
                        cstr_attributes: vec![],
                        cstr_inlined: None,
                    };
                    let cid = ctx.create_ident(cname);
                    current_env.add_constructor(cid, cstr_desc);
                }

                // Build typed constructor declarations
                let mut typed_cds = Vec::new();
                for cname in &ctor_names {
                    typed_cds.push(crate::types::typedtree::TypedConstructorDeclaration {
                        cd_id: ctx.create_ident(cname),
                        cd_name: crate::parse_arena::Located { txt: cname.clone(), loc: LocIdx(0) },
                        cd_args: crate::types::typedtree::TypedConstructorArguments::Cstr_tuple(vec![]),
                        cd_res: None,
                        cd_loc: LocIdx(0),
                        cd_attributes: crate::parser::ast::Attributes::new(),
                    });
                }

                let typed_decl = crate::types::typedtree::TypedTypeDeclaration {
                    typ_id: type_id.clone(),
                    typ_name: crate::parse_arena::Located { txt: name.clone(), loc: LocIdx(0) },
                    typ_params: vec![],
                    typ_cstrs: vec![],
                    typ_kind: crate::types::typedtree::TypedTypeKind::Ttype_variant(typed_cds),
                    typ_private: crate::parser::ast::PrivateFlag::Public,
                    typ_manifest: None,
                    typ_loc: LocIdx(0),
                    typ_attributes: crate::parser::ast::Attributes::new(),
                    typ_type: decl.clone(),
                };

                // Register in signature
                sig_items.push(crate::types::decl::SignatureItem::SigType(
                    type_id.clone(),
                    decl,
                    crate::types::decl::RecStatus::TrecNot,
                ));

                typed_items.push(StructureItem {
                    str_desc: StructureItemDesc::Tstr_type(RecFlag::Nonrecursive, vec![typed_decl]),
                    str_loc: LocIdx(0),
                    str_env: crate::types::typedtree::EnvRef(0),
                });
            }
            Ok(crate::types::comptime::TypeBuilderResult::Record(_)) => {
                // Deferred record emission not yet wired — use early-emit path
                return Err(TypeModError::CoreError(crate::types::TypeCoreError::Other(
                    "deferred @buildRecord emission not implemented — use top-level form".into(),
                )));
            }
            Err(e) => {
                return Err(TypeModError::CoreError(e));
            }
        }
    }

    // Emit monomorphized comptime functions as structure items.
    // Each generated function is a specialized version of a @comptime function
    // for a specific type (e.g., encode$user, encode$address).
    let generated_fns: Vec<_> = tctx.monomorph_cache.generated.drain(..).collect();
    for gen_fn in generated_fns {
        if gen_fn.name.is_empty() {
            continue; // Skip dummy entries from inline-only specializations
        }

        let ctx = tctx.type_ctx;
        let func_type = ctx.new_arrow_simple(gen_fn.param_type, gen_fn.return_type);

        // Pattern: let encode$user = ...
        let pat = crate::types::typedtree::Pattern {
            pat_desc: crate::types::typedtree::PatternDesc::Tpat_var(
                gen_fn.ident.clone(),
                crate::parse_arena::Located { txt: gen_fn.name.clone(), loc: LocIdx(0) },
            ),
            pat_loc: LocIdx(0),
            pat_extra: vec![],
            pat_type: func_type,
            pat_env: crate::types::typedtree::EnvRef(0),
            pat_attributes: crate::parser::ast::Attributes::new(),
        };

        // Use the same param ident that was used during body type-checking
        let param_ident = gen_fn.param_ident.clone();
        let param_pat = crate::types::typedtree::Pattern {
            pat_desc: crate::types::typedtree::PatternDesc::Tpat_var(
                param_ident.clone(),
                crate::parse_arena::Located { txt: gen_fn.param_name.clone(), loc: LocIdx(0) },
            ),
            pat_loc: LocIdx(0),
            pat_extra: vec![],
            pat_type: gen_fn.param_type,
            pat_env: crate::types::typedtree::EnvRef(0),
            pat_attributes: crate::parser::ast::Attributes::new(),
        };

        // Function body: (value) => specialized_body
        // Use static_arity_1 — no mutable arena needed
        let body_case = crate::types::typedtree::Case::simple(param_pat, gen_fn.body);
        let func_expr = crate::types::typedtree::Expression::new(
            crate::types::typedtree::ExpressionDesc::Texp_function {
                params: vec![crate::types::typedtree::FunctionParam {
                    param_id: param_ident,
                    label: crate::parser::ast::ArgLabel::Nolabel,
                    default: None,
                    pat: crate::types::typedtree::FunctionParamPattern::Simple(
                        body_case.c_lhs.clone(),
                    ),
                }],
                body: vec![body_case],
                partial: crate::types::typedtree::Partial::Total,
                arity: arena.static_arity_1(),
                async_: false,
            },
            LocIdx(0),
            func_type,
            crate::types::typedtree::EnvRef(0),
            crate::parser::ast::Attributes::new(),
        );

        let vb = crate::types::typedtree::ValueBinding {
            vb_pat: pat,
            vb_expr: func_expr,
            vb_attributes: crate::parser::ast::Attributes::new(),
            vb_loc: LocIdx(0),
        };

        let rec_flag = if gen_fn.recursive { RecFlag::Recursive } else { RecFlag::Nonrecursive };

        // Add to signature
        sig_items.push(crate::types::decl::SignatureItem::SigValue(
            gen_fn.ident.clone(),
            crate::types::decl::ValueDescription {
                val_type: func_type,
                val_kind: crate::types::decl::ValueKind::ValReg,
                val_loc: crate::location::Location::none(),
                val_attributes: vec![],
                val_path: None,
            },
        ));

        typed_items.push(StructureItem {
            str_desc: StructureItemDesc::Tstr_value(rec_flag, vec![vb]),
            str_loc: LocIdx(0),
            str_env: crate::types::typedtree::EnvRef(0),
        });
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
    let mut current_env = env.clone_preserve_id();

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
    let needs_implicit_constraint = simplified_structure_signature(&inner_structure).is_some();
    let structure_mty = crate::types::decl::ModuleType::MtySignature(inner_structure.str_type.clone());

    let mod_structure = ModuleExpr {
        mod_desc: ModuleExprDesc::Tmod_structure(inner_structure),
        mod_loc: loc,
        mod_type: structure_mty.clone(),
        mod_env: EnvRef(0),
        mod_attributes: Attributes::new(),
    };

    // If duplicates detected, wrap in Tmod_constraint(implicit) first
    let mod_structure = if needs_implicit_constraint {
        let simplified_mty = match &mod_structure.mod_type {
            crate::types::decl::ModuleType::MtySignature(sig) => {
                crate::types::decl::ModuleType::MtySignature(
                    crate::types::includemod::simplify_signature(sig),
                )
            }
            _ => unreachable!("structure modules always produce signatures"),
        };
        ModuleExpr {
            mod_desc: ModuleExprDesc::Tmod_constraint(
                Box::new(mod_structure),
                simplified_mty.clone(),
                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
                ModuleCoercion::Tcoerce_none,
            ),
            mod_loc: loc,
            mod_type: simplified_mty,
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
        mty_type: crate::types::decl::ModuleType::MtySignature(vec![]),
        mty_env: tctx.type_ctx.store_typed_env(env),
        mty_loc: loc,
        mty_attributes: Attributes::new(),
    };
    let mod_constraint = wrap_constraint(
        tctx,
        env,
        mod_structure,
        empty_sig.clone(),
        crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(Box::new(empty_sig)),
        loc,
        Attributes::new(),
    )?;

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

            // Early detection: @comptime let that builds a type declaration.
            // When we see `@comptime let foo = @buildVariant(...)` (possibly
            // wrapped in switch/match), evaluate the body NOW and return a
            // Tstr_type item instead of going through normal let-binding.
            for vb in bindings {
                let is_comptime = vb.pvb_attributes.iter().any(|(name, _)| {
                    arena.get_string(name.txt) == "comptime"
                });
                if !is_comptime { continue; }
                let body_expr = arena.get_expr(vb.pvb_expr);
                if !crate::types::typecore::contains_build_variant_with_registry(
                    body_expr, arena, Some(&tctx.comptime_functions),
                ) {
                    continue;
                }
                let pat = arena.get_pat(vb.pvb_pat);
                let name = if let crate::parser::ast::PatternDesc::Ppat_var(name_loc) = &*pat.ppat_desc {
                    arena.get_string(name_loc.txt).to_string()
                } else {
                    continue;
                };

                // Evaluate the body to produce a TypeBuilderResult
                let body_clone = body_expr.clone();
                let result = crate::types::typecore::evaluate_type_builder(tctx, env, &body_clone)
                    .map_err(TypeModError::CoreError)?;

                let ctx = tctx.type_ctx;
                let type_id = ctx.create_ident(&name);
                match result {
                    crate::types::comptime::TypeBuilderResult::Variant(ctor_names) => {
                        let mut constructors = Vec::new();
                        for cname in &ctor_names {
                            let cid = ctx.create_ident(cname);
                            constructors.push(crate::types::decl::ConstructorDeclaration {
                                cd_id: cid,
                                cd_args: crate::types::decl::ConstructorArguments::CstrTuple(vec![]),
                                cd_res: None,
                                cd_loc: crate::location::Location::none(),
                                cd_attributes: vec![],
                            });
                        }
                        let decl = crate::types::TypeDeclaration {
                            type_params: vec![],
                            type_arity: 0,
                            type_kind: crate::types::TypeKind::TypeVariant(constructors),
                            type_private: crate::types::asttypes::PrivateFlag::Public,
                            type_manifest: None,
                            type_variance: vec![],
                            type_newtype_level: None,
                            type_loc: crate::location::Location::none(),
                            type_attributes: vec![],
                            type_immediate: false,
                            type_unboxed: crate::types::UnboxedStatus::default(),
                            type_inlined_types: vec![],
                            type_path: Some(crate::types::Path::pident(type_id.clone())),
                        };

                        let mut new_env = env.clone();
                        new_env.add_type(type_id.clone(), decl.clone());
                        ctx.register_type_decl(&name, decl.clone());
                        if type_id.stamp() != 0 {
                            ctx.register_type_decl_by_stamp(type_id.stamp(), decl.clone());
                        }

                        let type_path = crate::types::Path::pident(type_id.clone());
                        let num_consts = ctor_names.len() as i32;
                        for (i, cname) in ctor_names.iter().enumerate() {
                            let cstr_desc = crate::types::ConstructorDescription {
                                cstr_name: cname.clone(),
                                cstr_res: ctx.new_generic_constr(type_path.clone(), vec![]),
                                cstr_existentials: vec![],
                                cstr_args: vec![],
                                cstr_arity: 0,
                                cstr_tag: crate::types::decl::ConstructorTag::CstrConstant(i as i32),
                                cstr_consts: num_consts,
                                cstr_nonconsts: 0,
                                cstr_generalized: false,
                                cstr_private: crate::types::asttypes::PrivateFlag::Public,
                                cstr_loc: crate::location::Location::none(),
                                cstr_attributes: vec![],
                                cstr_inlined: None,
                            };
                            let cid = ctx.create_ident(cname);
                            new_env.add_constructor(cid, cstr_desc);
                        }

                        let mut typed_cds = Vec::new();
                        for cname in &ctor_names {
                            typed_cds.push(crate::types::typedtree::TypedConstructorDeclaration {
                                cd_id: ctx.create_ident(cname),
                                cd_name: crate::parse_arena::Located { txt: cname.clone(), loc: LocIdx(0) },
                                cd_args: crate::types::typedtree::TypedConstructorArguments::Cstr_tuple(vec![]),
                                cd_res: None,
                                cd_loc: LocIdx(0),
                                cd_attributes: crate::parser::ast::Attributes::new(),
                            });
                        }

                        let typed_decl = crate::types::typedtree::TypedTypeDeclaration {
                            typ_id: type_id.clone(),
                            typ_name: crate::parse_arena::Located { txt: name.clone(), loc: LocIdx(0) },
                            typ_params: vec![],
                            typ_cstrs: vec![],
                            typ_kind: crate::types::typedtree::TypedTypeKind::Ttype_variant(typed_cds),
                            typ_private: crate::parser::ast::PrivateFlag::Public,
                            typ_manifest: None,
                            typ_loc: LocIdx(0),
                            typ_attributes: crate::parser::ast::Attributes::new(),
                            typ_type: decl.clone(),
                        };

                        let sig_item = crate::types::decl::SignatureItem::SigType(
                            type_id.clone(),
                            decl,
                            crate::types::decl::RecStatus::TrecNot,
                        );

                        return Ok((
                            StructureItem {
                                str_desc: StructureItemDesc::Tstr_type(RecFlag::Nonrecursive, vec![typed_decl]),
                                str_loc: loc,
                                str_env: EnvRef(0),
                            },
                            vec![sig_item],
                            new_env,
                        ));
                    }
                    crate::types::comptime::TypeBuilderResult::Record(field_specs) => {
                        // Convert each RecordFieldSpec to a LabelDeclaration
                        let mut labels = Vec::new();
                        for fs in &field_specs {
                            // Build a real TypeExprRef from the field's TypeInfo
                            let field_ty = crate::types::comptime::type_info_to_type_expr(ctx, env, &fs.typ)
                                .ok_or_else(|| TypeModError::CoreError(crate::types::TypeCoreError::Other(
                                    format!("@recordField: could not resolve type for '{}'", fs.name)
                                )))?;
                            labels.push(crate::types::decl::LabelDeclaration {
                                ld_id: ctx.create_ident(&fs.name),
                                ld_mutable: if fs.mutable_ {
                                    crate::types::MutableFlag::Mutable
                                } else {
                                    crate::types::MutableFlag::Immutable
                                },
                                ld_optional: fs.optional,
                                ld_type: field_ty,
                                ld_loc: crate::location::Location::none(),
                                ld_attributes: vec![],
                            });
                        }

                        let decl = crate::types::TypeDeclaration {
                            type_params: vec![],
                            type_arity: 0,
                            type_kind: crate::types::TypeKind::TypeRecord(
                                labels.clone(),
                                crate::types::RecordRepresentation::RecordRegular,
                            ),
                            type_private: crate::types::asttypes::PrivateFlag::Public,
                            type_manifest: None,
                            type_variance: vec![],
                            type_newtype_level: None,
                            type_loc: crate::location::Location::none(),
                            type_attributes: vec![],
                            type_immediate: false,
                            type_unboxed: crate::types::UnboxedStatus::default(),
                            type_inlined_types: vec![],
                            type_path: Some(crate::types::Path::pident(type_id.clone())),
                        };

                        let mut new_env = env.clone();
                        new_env.add_type(type_id.clone(), decl.clone());
                        ctx.register_type_decl(&name, decl.clone());
                        if type_id.stamp() != 0 {
                            ctx.register_type_decl_by_stamp(type_id.stamp(), decl.clone());
                        }

                        // Register labels so they can be referenced
                        let type_path = crate::types::Path::pident(type_id.clone());
                        let res_ty = ctx.new_constr(type_path.clone(), vec![]);
                        for (pos, label) in labels.iter().enumerate() {
                            let lbl_desc = crate::types::LabelDescription {
                                lbl_name: label.ld_id.name().to_string(),
                                lbl_res: res_ty,
                                lbl_arg: label.ld_type,
                                lbl_mut: label.ld_mutable.clone(),
                                lbl_optional: label.ld_optional,
                                lbl_pos: pos as i32,
                                lbl_all: crate::types::LabelArrayRef(0),
                                lbl_repres: crate::types::RecordRepresentation::RecordRegular,
                                lbl_private: crate::types::asttypes::PrivateFlag::Public,
                                lbl_loc: crate::location::Location::none(),
                                lbl_attributes: vec![],
                            };
                            new_env.add_label(label.ld_id.clone(), lbl_desc);
                        }

                        // Build typed labels
                        let mut typed_labels = Vec::new();
                        for label in &labels {
                            let parser_mutable = match &label.ld_mutable {
                                crate::types::MutableFlag::Mutable => crate::parser::ast::MutableFlag::Mutable,
                                crate::types::MutableFlag::Immutable => crate::parser::ast::MutableFlag::Immutable,
                            };
                            typed_labels.push(crate::types::typedtree::TypedLabelDeclaration {
                                ld_id: label.ld_id.clone(),
                                ld_name: crate::parse_arena::Located { txt: label.ld_id.name().to_string(), loc: LocIdx(0) },
                                ld_mutable: parser_mutable,
                                ld_optional: label.ld_optional,
                                ld_type: crate::types::typedtree::TypedCoreType {
                                    ctyp_desc: crate::types::typedtree::TypedCoreTypeDesc::Ttyp_var(None),
                                    ctyp_loc: LocIdx(0),
                                    ctyp_type: label.ld_type,
                                    ctyp_env: crate::types::typedtree::EnvRef(0),
                                    ctyp_attributes: crate::parser::ast::Attributes::new(),
                                },
                                ld_loc: LocIdx(0),
                                ld_attributes: crate::parser::ast::Attributes::new(),
                            });
                        }

                        let typed_decl = crate::types::typedtree::TypedTypeDeclaration {
                            typ_id: type_id.clone(),
                            typ_name: crate::parse_arena::Located { txt: name.clone(), loc: LocIdx(0) },
                            typ_params: vec![],
                            typ_cstrs: vec![],
                            typ_kind: crate::types::typedtree::TypedTypeKind::Ttype_record(typed_labels),
                            typ_private: crate::parser::ast::PrivateFlag::Public,
                            typ_manifest: None,
                            typ_loc: LocIdx(0),
                            typ_attributes: crate::parser::ast::Attributes::new(),
                            typ_type: decl.clone(),
                        };

                        let sig_item = crate::types::decl::SignatureItem::SigType(
                            type_id.clone(),
                            decl,
                            crate::types::decl::RecStatus::TrecNot,
                        );

                        return Ok((
                            StructureItem {
                                str_desc: StructureItemDesc::Tstr_type(RecFlag::Nonrecursive, vec![typed_decl]),
                                str_loc: loc,
                                str_env: EnvRef(0),
                            },
                            vec![sig_item],
                            new_env,
                        ));
                    }
                }
            }

            // Check for @comptime bindings BEFORE type-checking.
            // Comptime function bodies contain comptime-only expressions
            // (@typeInfo, inline for, etc.) that can't be type-checked
            // without concrete type arguments. Store them for later
            // specialization at call sites.
            let mut has_comptime = false;
            for vb in bindings {
                let is_comptime = vb.pvb_attributes.iter().any(|(name, _)| {
                    let attr_name = arena.get_string(name.txt);
                    attr_name == "comptime" || attr_name == "comptime.derive" || attr_name == "comptime.inline"
                });
                let is_inline = vb.pvb_attributes.iter().any(|(name, _)| {
                    arena.get_string(name.txt) == "comptime.inline"
                });
                if is_comptime {
                    has_comptime = true;
                    let pat = arena.get_pat(vb.pvb_pat);
                    if let crate::parser::ast::PatternDesc::Ppat_var(name_loc) = &*pat.ppat_desc {
                        let name = arena.get_string(name_loc.txt).to_string();

                        // Check if this is a @comptime.derive("deriveName") registration.
                        // If so, register under the derive name (from the payload) so
                        // @deriveName on a type triggers this handler.
                        let derive_name = vb.pvb_attributes.iter().find_map(|(attr_name, payload)| {
                            if arena.get_string(attr_name.txt) == "comptime.derive" {
                                // Extract the derive name from the string payload
                                if let crate::parser::ast::Payload::PStr(items) = payload {
                                    if let Some(item) = items.first() {
                                        if let crate::parser::ast::StructureItemDesc::Pstr_eval(inner) = &*item.pstr_desc {
                                            let (expr_idx, _) = &**inner;
                                            let expr = arena.get_expr(*expr_idx);
                                            if let crate::parser::ast::ExpressionDesc::Pexp_constant(c) = &*expr.pexp_desc {
                                                if let crate::parser::ast::Constant::String(s, _) = &**c {
                                                    return Some(s.to_string());
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            None
                        });

                        let comptime_fn = crate::types::comptime::ComptimeFunction {
                            body_expr_idx: vb.pvb_expr,
                            params: Vec::new(),
                            name: name.clone(),
                            is_inline,
                        };

                        // Register under the function name (for @comptime calls)
                        tctx.comptime_functions.insert(name.clone(), comptime_fn.clone());

                        // Also register under the derive name if it's a @comptime.derive
                        if let Some(derive_name) = derive_name {
                            tctx.comptime_functions.insert(derive_name, comptime_fn);
                        }
                    }
                }
            }

            // Skip comptime-only bindings in normal type checking
            let bindings_to_check: Vec<_> = if has_comptime {
                bindings.iter().filter(|vb| {
                    !vb.pvb_attributes.iter().any(|(name, _)| {
                        arena.get_string(name.txt) == "comptime"
                    })
                }).cloned().collect()
            } else {
                bindings.to_vec()
            };

            // Value binding: let P = E
            let (typed_bindings, mut new_env) = if bindings_to_check.is_empty() {
                // All bindings are comptime — no normal type checking needed
                (vec![], env.clone())
            } else {
                type_value_bindings(tctx, env, *rec_flag, &bindings_to_check)?
            };

            // Add comptime functions to the environment so call sites can find them
            if has_comptime {
                for vb in bindings {
                    let is_comptime = vb.pvb_attributes.iter().any(|(name, _)| {
                        arena.get_string(name.txt) == "comptime"
                    });
                    if is_comptime {
                        let pat = arena.get_pat(vb.pvb_pat);
                        if let crate::parser::ast::PatternDesc::Ppat_var(name_loc) = &*pat.ppat_desc {
                            let name = arena.get_string(name_loc.txt).to_string();
                            let fn_id = tctx.type_ctx.create_ident(&name);
                            let fn_ty = tctx.type_ctx.new_var(None);
                            let vd = crate::types::decl::ValueDescription {
                                val_type: fn_ty,
                                val_kind: crate::types::decl::ValueKind::ValReg,
                                val_loc: arena.to_location(vb.pvb_loc),
                                val_attributes: vec![],
                                val_path: None,
                            };
                            new_env.add_value(fn_id, vd);
                        }
                    }
                }
            }

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
            let id = tctx.type_ctx.create_ident(&name_str);

            // Translate the type annotation using transl_type_scheme pattern:
            // OCaml: reset_type_variables() clears type var map so each declaration
            // gets fresh Tvars (e.g., 'a in log and 'a in log2 are separate nodes).
            tctx.type_variables.clear();
            let ctx = tctx.type_ctx;
            ctx.begin_def();
            let (typed_ctype, val_ty) = transl_type(tctx, env, arena.get_core_type(vd.pval_type))?;
            ctx.end_def();
            crate::types::ctype::generalize(ctx, val_ty);

            // OCaml's transl_value_decl calls parse_arity -> get_arity ->
            // expand_head AFTER generalize. The expand_head side effect
            // populates simple_abbrevs with the nullary Tconstr expansion.
            // When instance() is later called for Pexp_ident, copy() finds
            // this entry via find_simple_abbrev and returns Tlink to the
            // original instead of a fresh copy — creating node sharing.
            crate::types::ctype::expand_head(ctx, env, val_ty);

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
                val_kind: crate::types::ValueKind::ValPrim(primitive_description_from_value_decl(
                    arena,
                    ctx,
                    env,
                    &vd.pval_prim,
                    vd.pval_type,
                    val_ty,
                )),
                val_loc: arena.to_location(loc),
                val_attributes: vec![],
                val_path: None,
            };
            let sig_item =
                crate::types::decl::SignatureItem::SigValue(id.clone(), val_desc_for_env.clone());
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
                let type_id = ctx.create_ident(type_name_str);
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
                    if let crate::parser::ast::CoreTypeDesc::Ptyp_var(name) = &*core_type.ptyp_desc
                    {
                        tctx.type_variables.insert(name.to_string(), type_ref);
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
                        (Some(typed_manifest), Some(type_ref))
                    }
                    None => (None, None),
                };

                // Check for @unboxed attribute (only applies to single-constructor variants)
                let decl_has_unboxed_attr = decl
                    .ptype_attributes
                    .iter()
                    .any(|attr| arena.get_string(attr.0.txt) == "unboxed");

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
                        let spread_sources: Vec<
                            Option<(Vec<crate::types::ConstructorDeclaration>, bool)>,
                        > = {
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
                                        if let Ok((_typed_ct, type_ref)) = transl_type(
                                            tctx,
                                            &temp_env,
                                            arena.get_core_type(*spread_type_ct),
                                        ) {
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
                                                        if let Some(parent_sig) =
                                                            resolve_path_to_sig_impl(
                                                                parent,
                                                                Some(&temp_env),
                                                                &mut tctx.persistent_env,
                                                                tctx.type_ctx,
                                                                &mut visiting,
                                                            )
                                                        {
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
                                                        if let Ok(source_decl) =
                                                            temp_env.lookup_type(path)
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
                        // @unboxed is only the single-constructor OCaml-style unboxed
                        // when there's exactly one constructor. Multi-constructor
                        // @unboxed is ReScript's "untagged variants" which uses different handling.
                        let has_unboxed = decl_has_unboxed_attr && num_consts + num_nonconsts == 1;

                        for (cstr_idx, cstr) in cstrs.iter().enumerate() {
                            // Handle variant spread expansion
                            // Like OCaml's typedecl.ml: spread markers return None (filtered out)
                            // and expanded constructors get real types from the source type
                            if let Some((ref source_cstrs, is_pdot_source)) =
                                spread_sources[cstr_idx]
                            {
                                // Expand the source type's constructors into this type
                                // The spread marker itself is NOT included in any output
                                for source_cstr in source_cstrs {
                                    let sc_name = source_cstr.cd_id.name().to_string();
                                    let sc_id = ctx.create_ident(&sc_name);
                                    let spread_constructor_attr = (
                                        Located::mknoloc(arena.constructor_from_spread_attr_str()),
                                        crate::parser::ast::Payload::PStr(Box::new(vec![])),
                                    );
                                    let source_cd_loc =
                                        find_existing_loc_idx(arena, &source_cstr.cd_loc)
                                            .unwrap_or(cstr.pcd_loc);
                                    let sc_is_const = matches!(&source_cstr.cd_args, crate::types::ConstructorArguments::CstrTuple(args) if args.is_empty());
                                    let sc_tag = if has_unboxed {
                                        crate::types::ConstructorTag::CstrUnboxed
                                    } else if sc_is_const {
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
                                    ) = match &source_cstr.cd_args {
                                        crate::types::ConstructorArguments::CstrTuple(args) => {
                                            // Use the actual types from the source, not fresh vars
                                            // For Pdot sources (sub-module types), create fresh shallow copies
                                            // to match OCaml's Subst.type_declaration behavior
                                            let copied_args: Vec<TypeExprRef> = if is_pdot_source {
                                                args.iter()
                                                    .map(|&texpr| {
                                                        ctx.new_type(ctx.get_desc(texpr).clone())
                                                    })
                                                    .collect()
                                            } else {
                                                args.clone()
                                            };
                                            let typed_tree_args: Vec<TypedCoreType> = copied_args
                                                .iter()
                                                .map(|&texpr| TypedCoreType {
                                                    ctyp_desc: TypedCoreTypeDesc::Ttyp_var(None),
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
                                                crate::types::ConstructorArguments::CstrTuple(
                                                    copied_args.clone(),
                                                )
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
                                        crate::types::ConstructorArguments::CstrRecord(lbls) => {
                                            // OCaml strips top-level Tpoly wrappers from
                                            // internal spread label types (transl_labels lbls').
                                            // For Pdot sources, create fresh type copies to match
                                            // OCaml's Subst.type_declaration behavior.
                                            let normalized_lbls = lbls
                                                .iter()
                                                .map(|l| {
                                                    let mut normalized = l.clone();
                                                    let unwrapped =
                                                        unwrap_poly_type(ctx, l.ld_type);
                                                    normalized.ld_type = if is_pdot_source {
                                                        ctx.new_type(
                                                            ctx.get_desc(unwrapped).clone(),
                                                        )
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
                                                crate::types::ConstructorArguments::CstrRecord(
                                                    normalized_lbls.clone(),
                                                )
                                            } else {
                                                source_cstr.cd_args.clone()
                                            };
                                            (
                                                args_vec,
                                                internal_cd_args,
                                                TypedConstructorArguments::Cstr_record(typed_lbls),
                                                Some(normalized_lbls),
                                            )
                                        }
                                    };

                                    let res_ty = ctx.new_constr(
                                        type_path.clone(),
                                        internal_type_params.clone(),
                                    );
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
                                                crate::types::ConstructorTag::CstrBlock(tag) => {
                                                    *tag
                                                }
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

                                    let sc_existentials =
                                        crate::types::env::constructor_existentials(
                                            ctx,
                                            &sc_desc_args,
                                            source_cstr.cd_res,
                                        );
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
                            let cstr_id = ctx.create_ident(cstr_name_str);
                            let is_constant = matches!(cstr.pcd_args, crate::parser::ast::ConstructorArguments::Pcstr_tuple(ref args) if args.is_empty());

                            // Convert constructor arguments using transl_type
                            let (cstr_args, internal_cd_args, typed_tree_cd_args) = match &cstr
                                .pcd_args
                            {
                                crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                                    let mut typed_args: Vec<TypeExprRef> = Vec::new();
                                    let mut typed_tree_args: Vec<TypedCoreType> = Vec::new();
                                    for core_type in types {
                                        let (typed_core_type, type_ref) = transl_type(
                                            tctx,
                                            &temp_env,
                                            arena.get_core_type(*core_type),
                                        )?;
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
                                            let option_path = crate::types::predef::path_option();
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
                                            force_poly_typed_core_type(
                                                ctx,
                                                typed_core_type,
                                                type_ref,
                                            );
                                        let lbl_name_str = arena.get_string(lbl.pld_name.txt);
                                        // For internal labels, strip Tpoly(t, []) like OCaml transl_labels lbls'
                                        let internal_type_ref = match &*ctx.get_desc(poly_type_ref)
                                        {
                                            crate::types::type_expr::TypeDesc::Tpoly {
                                                body,
                                                vars,
                                            } if vars.is_empty() => *body,
                                            _ => poly_type_ref,
                                        };
                                        let label_id = ctx.create_ident(lbl_name_str);
                                        internal_labels.push(crate::types::LabelDeclaration {
                                            ld_id: label_id.clone(),
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
                                            ld_id: label_id,
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
                                    let (typed_res, res_ty) = transl_type(
                                        tctx,
                                        &temp_env,
                                        arena.get_core_type(*res_core_type),
                                    )?;
                                    (Some(typed_res), Some(res_ty))
                                }
                                None => (None, None),
                            };

                            // Determine the tag
                            let tag = if has_unboxed {
                                crate::types::ConstructorTag::CstrUnboxed
                            } else if is_constant {
                                let t = const_tag;
                                const_tag += 1;
                                crate::types::ConstructorTag::CstrConstant(t)
                            } else {
                                let t = block_tag;
                                block_tag += 1;
                                crate::types::ConstructorTag::CstrBlock(t)
                            };
                            let mut combined_parser_attrs = tag_attrs.clone();
                            combined_parser_attrs.extend(cstr.pcd_attributes.iter().cloned());
                            let combined_typed_attrs =
                                Attributes::from_vec(combined_parser_attrs.clone());
                            let combined_decl_attrs =
                                parser_attrs_to_decl_attrs(arena, &combined_typed_attrs);

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
                                    let inline_repres = if has_unboxed {
                                        crate::types::RecordRepresentation::RecordUnboxed(false)
                                    } else {
                                        crate::types::RecordRepresentation::RecordInlined {
                                            tag: block_tag - 1, // use the tag just assigned
                                            name: cstr_name_str.to_string(),
                                            num_nonconsts,
                                            attrs: combined_decl_attrs.clone(),
                                        }
                                    };
                                    let inline_decl = crate::types::TypeDeclaration {
                                        type_params: inline_params.clone(),
                                        type_arity: inline_params.len() as i32,
                                        type_kind: crate::types::TypeKind::TypeRecord(
                                            lbls.clone(),
                                            inline_repres,
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
                                cd_attributes: combined_decl_attrs.clone(),
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
                                cd_attributes: combined_typed_attrs,
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
                            let cstr_existentials = crate::types::env::constructor_existentials(
                                ctx,
                                &cstr_args,
                                internal_cd_res,
                            );
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
                                    cstr_attributes:
                                        crate::types::decl::constructor_description_attrs_for_variant(
                                            &internal_cstrs,
                                            internal_cstrs.last().expect("constructor just pushed"),
                                        ),
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
                                let option_path = crate::types::predef::path_option();
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
                                crate::types::type_expr::TypeDesc::Tpoly { body, vars }
                                    if vars.is_empty() =>
                                {
                                    *body
                                }
                                _ => poly_type_ref,
                            };
                            let label_id = ctx.create_ident(lbl_name_str);
                            internal_labels.push(crate::types::LabelDeclaration {
                                ld_id: label_id.clone(),
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
                                ld_id: label_id,
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
                            let repres = if decl_has_unboxed_attr && internal_labels.len() == 1 {
                                crate::types::RecordRepresentation::RecordUnboxed(false)
                            } else {
                                crate::types::RecordRepresentation::RecordRegular
                            };
                            (
                                crate::types::TypeKind::TypeRecord(internal_labels, repres),
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
                    type_unboxed: if decl_has_unboxed_attr && constructors.len() <= 1 {
                        crate::types::UnboxedStatus::TRUE_FALSE
                    } else {
                        crate::types::UnboxedStatus::default()
                    },
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
                crate::types::ctype::generalize(ctx, *ty);
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
                let id = ctx.create_ident(&name_str);

                let (typed_args, typed_ret, ext_args, cstr_args, cstr_inlined, ext_ret_ty) =
                    match &ec.pext_kind {
                        crate::parser::ast::ExtensionConstructorKind::Pext_decl(args, ret) => {
                            let mut arg_ty_refs = Vec::new();
                            let (typed_args, ext_args, cstr_args, cstr_inlined) = match args {
                                crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                                    let mut typed = Vec::new();
                                    for ty in types {
                                        let (typed_ct, ty_ref) =
                                            transl_type(tctx, env, arena.get_core_type(*ty))?;
                                        arg_ty_refs.push(ty_ref);
                                        typed.push(typed_ct);
                                    }
                                    (
                                        crate::types::typedtree::ConstructorArgument::Cstr_tuple(
                                            typed,
                                        ),
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
                                        let (typed_ct, ty_ref) = transl_type(
                                            tctx,
                                            env,
                                            arena.get_core_type(label.pld_type),
                                        )?;
                                        let (poly_typed_ct, poly_ty_ref) =
                                            force_poly_typed_core_type(ctx, typed_ct, ty_ref);
                                        let internal_ty_ref = match &*ctx.get_desc(poly_ty_ref) {
                                            crate::types::type_expr::TypeDesc::Tpoly {
                                                body,
                                                vars,
                                            } if vars.is_empty() => *body,
                                            _ => poly_ty_ref,
                                        };
                                        let label_id = ctx.create_ident(&label_name);
                                        typed_labels.push(
                                            crate::types::typedtree::LabelDeclaration {
                                                ld_id: label_id.clone(),
                                                ld_name: crate::parse_arena::Located {
                                                    txt: label_name.clone(),
                                                    loc: label.pld_name.loc,
                                                },
                                                ld_mutable: label.pld_mutable,
                                                ld_optional: label.pld_optional,
                                                ld_type: poly_typed_ct,
                                                ld_loc: label.pld_loc,
                                                ld_attributes: label.pld_attributes.clone(),
                                            },
                                        );
                                        decl_labels.push(crate::types::LabelDeclaration {
                                            ld_id: label_id,
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
                                    let inline_ty =
                                        ctx.new_generic_constr(inline_path.clone(), vec![]);
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
                    cstr_consts: -1,
                    cstr_nonconsts: -1,
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
            let id = ctx.create_ident(&name_str);

            // OCaml typedecl.ml:1839-1846: begin_def/end_def/generalize around
            // exception constructor type translation. This ensures arg types are
            // at GENERIC_LEVEL so instance() creates fresh copies, preventing
            // declaration types from being linked to use-site aliases.
            // OCaml: reset_type_variables() at start of transl_exception
            tctx.type_variables.clear();
            ctx.begin_def();

            // Translate constructor arguments and collect type refs for env registration
            let (typed_args, _ext_ret, ext_args, cstr_args, cstr_inlined, ext_ret_ty) =
                match &ext_constr.pext_kind {
                    crate::parser::ast::ExtensionConstructorKind::Pext_decl(args, ret) => {
                        let mut arg_ty_refs = Vec::new();
                        let (typed_args, ext_args, cstr_args, cstr_inlined) = match args {
                            crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                                let mut typed = Vec::new();
                                for ty in types {
                                    let (typed_ct, ty_ref) =
                                        transl_type(tctx, env, arena.get_core_type(*ty))?;
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
                                    let (typed_ct, ty_ref) = transl_type(
                                        tctx,
                                        env,
                                        arena.get_core_type(label.pld_type),
                                    )?;
                                    let (poly_typed_ct, poly_ty_ref) =
                                        force_poly_typed_core_type(ctx, typed_ct, ty_ref);
                                    let internal_ty_ref = match &*ctx.get_desc(poly_ty_ref) {
                                        crate::types::type_expr::TypeDesc::Tpoly { body, vars }
                                            if vars.is_empty() =>
                                        {
                                            *body
                                        }
                                        _ => poly_ty_ref,
                                    };
                                    let label_id = ctx.create_ident(&label_name);
                                    typed_labels.push(crate::types::typedtree::LabelDeclaration {
                                        ld_id: label_id.clone(),
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
                                        ld_id: label_id,
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
                .new_generic_constr(crate::types::predef::path_exn(), vec![]);
            let exn_path = Path::pident(id.clone());
            let cstr_desc = crate::types::decl::ConstructorDescription {
                cstr_name: name_str.clone(),
                cstr_res: exn_ty,
                cstr_existentials: vec![],
                cstr_args: cstr_args.clone(),
                cstr_arity: cstr_args.len() as i32,
                cstr_tag: crate::types::decl::ConstructorTag::CstrExtension(exn_path),
                cstr_consts: -1,
                cstr_nonconsts: -1,
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
                ext_type_path: crate::types::predef::path_exn(),
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
            // Match OCaml typemod.ml:1454: create the module ident before any
            // body typing that might allocate additional identifiers.
            let mod_name_str = arena.get_string(mb.pmb_name.txt);
            let mod_id = tctx.type_ctx.create_ident(mod_name_str);

            // Module binding: module M = ME
            let typed_mod = type_module_expr_with_alias(
                tctx,
                env,
                arena,
                arena.get_mod_expr(mb.pmb_expr),
                true,
            )?;

            // Extend environment with the new module
            let mut new_env = env.clone();
            let mut decl_mod_type = decl_module_type_from_typed_module_expr_for_sig(&typed_mod)
                .unwrap_or_else(|| crate::types::decl::ModuleType::MtySignature(vec![]));
            anchor_local_module_aliases_to_owner(&mut decl_mod_type, &Path::pident(mod_id.clone()));
            if let crate::types::decl::ModuleType::MtySignature(sig) = &decl_mod_type {
                let should_substitute_sig_paths = !matches!(
                    &*arena.get_mod_expr(mb.pmb_expr).pmod_desc,
                    ParsedModuleExprDesc::Pmod_structure(_)
                );
                if should_substitute_sig_paths {
                    let sig = crate::types::typecore::copy_lookup_signature_for_subst(
                        sig,
                        tctx.type_ctx,
                    );
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
            let localized_decl_mod_type = match &decl_mod_type {
                crate::types::decl::ModuleType::MtySignature(sig) => {
                    if let ModuleExprDesc::Tmod_structure(structure) = &typed_mod.mod_desc {
                        if !structure_has_dotted_alias_child_modules(structure) {
                            decl_mod_type.clone()
                        } else {
                            let mut sig =
                                crate::types::typecore::copy_lookup_signature_for_subst(
                                    sig,
                                    tctx.type_ctx,
                                );
                            localize_alias_child_module_sig_paths_in_structure_sig(
                                &mut sig,
                                structure,
                                &Path::pident(mod_id.clone()),
                                tctx.type_ctx,
                            );
                            crate::types::decl::ModuleType::MtySignature(sig)
                        }
                    } else {
                        decl_mod_type.clone()
                    }
                }
                _ => decl_mod_type.clone(),
            };
            let item_sig_mod_type = localized_decl_mod_type.clone();
            new_env.add_module(
                mod_id.clone(),
                crate::types::decl::ModuleDeclaration {
                    md_type: localized_decl_mod_type,
                    md_attributes: vec![],
                    md_loc: crate::location::Location::none(),
                    md_path: None,
                },
            );
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
                let mod_id = tctx.type_ctx.create_ident(mod_name_str);
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
            let rec_env_ref = tctx.type_ctx.store_typed_env(&rec_env);
            let mut typed_bindings = Vec::new();
            let mut binding_mod_types = Vec::new();
            let mut new_env = env.clone();
            for (i, mb) in mbs.iter().enumerate() {
                let typed_mod = match &*arena.get_mod_expr(mb.pmb_expr).pmod_desc {
                    ParsedModuleExprDesc::Pmod_constraint(inner_expr, mty) => {
                        let typed_inner = type_module_expr(
                            tctx,
                            &rec_env,
                            arena,
                            arena.get_mod_expr(*inner_expr),
                        )?;
                        let typed_mty =
                            transl_modtype(tctx, &rec_env, arena, arena.get_mod_type(*mty))?;
                        let inner_loc = typed_inner.mod_loc;
                        // Compute coercion between implementation and constraint
                        let coercion = {
                            // Try mod_type first, then try extracting from the typed module expr
                            let impl_mty_opt = Some(typed_inner.mod_type.clone())
                                .or_else(|| {
                                    extract_module_type_from_mod_expr_with_resolver(
                                        &typed_inner,
                                        Some(&rec_env),
                                        Some(tctx.type_ctx),
                                        &mut |_, _| None,
                                    )
                                });
                            let sig_mty_opt = decl_module_type_from_typed(&typed_mty);
                            match (impl_mty_opt, sig_mty_opt) {
                                (Some(impl_mty), Some(sig_mty)) => {
                                    crate::types::includemod::modtypes(
                                        tctx.type_ctx,
                                        &rec_env,
                                        &impl_mty,
                                        &sig_mty,
                                    )
                                    .unwrap_or(ModuleCoercion::Tcoerce_none)
                                }
                                _ => ModuleCoercion::Tcoerce_none,
                            }
                        };
                        ModuleExpr {
                            mod_desc: ModuleExprDesc::Tmod_constraint(
                                Box::new(typed_inner),
                                typed_mty.mty_type.clone(),
                                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(
                                    Box::new(typed_mty.clone()),
                                ),
                                coercion,
                            ),
                            mod_loc: inner_loc,
                            mod_type: typed_mty.mty_type.clone(),
                            mod_env: rec_env_ref,
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
            let mtd_id = tctx.type_ctx.create_ident(mtd_name_str);

            let typed_mty = match &mtd.pmtd_type {
                Some(mt) => Some(transl_modtype(tctx, env, arena, arena.get_mod_type(*mt))?),
                None => None,
            };

            let decl_mtd_type = match mtd.pmtd_type {
                Some(mt) => Some(translate_module_type_to_decl_with_typed_hint(
                    tctx,
                    env,
                    arena,
                    arena.get_mod_type(mt),
                    typed_mty.as_ref(),
                )?),
                None => None,
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
                    mtd_id, decl_mtd,
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
            let typed_mod = type_module_expr(tctx, env, arena, arena.get_mod_expr(incl.pincl_mod))?;
            let final_include_sig = resolve_mod_type_to_sig(
                &typed_mod.mod_type,
                Some(env),
                &mut tctx.persistent_env,
                tctx.type_ctx,
            );
            let stored_include_sig = final_include_sig.as_ref().map(|sig_items| {
                let mut sig = crate::types::typecore::copy_lookup_signature_for_subst(
                    sig_items,
                    tctx.type_ctx,
                );
                crate::cmi::persistent_env::freshen_signature_bound_idents(&mut sig, tctx.type_ctx);
                sig
            });
            let localized_include_sig = stored_include_sig.as_ref().map(|sig_items| {
                let mut sig = sig_items.clone();
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
                sig
            });
            let mut new_env = env.clone();
            if let Some(sig_items) = &localized_include_sig {
                // OCaml's include adds all signature items directly to the environment
                // as if they were defined locally (Pident paths, not Pdot paths).
                // This matches OCaml's Env.add_signature behavior.
                for item in sig_items {
                    match item {
                        crate::types::decl::SignatureItem::SigValue(id, desc) => {
                            new_env.add_value(id.clone(), desc.clone());
                        }
                        crate::types::decl::SignatureItem::SigType(id, decl, _) => {
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
                                    .count()
                                    as i32;
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
                                        let tag = crate::types::decl::ConstructorTag::CstrConstant(
                                            const_idx,
                                        );
                                        const_idx += 1;
                                        tag
                                    } else {
                                        let tag = crate::types::decl::ConstructorTag::CstrBlock(
                                            nonconst_idx,
                                        );
                                        nonconst_idx += 1;
                                        tag
                                    };

                                    let (cstr_args, cstr_arity) = match &cd.cd_args {
                                        crate::types::decl::ConstructorArguments::CstrTuple(
                                            args,
                                        ) => (args.clone(), args.len() as i32),
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
                                        cstr_attributes:
                                            crate::types::decl::constructor_description_attrs_for_variant(
                                                constructors, cd,
                                            ),
                                        cstr_inlined: None,
                                    };
                                    new_env.add_constructor(cd.cd_id.clone(), cstr_desc);
                                }
                            }
                            if let crate::types::TypeKind::TypeRecord(labels, repres) =
                                &decl.type_kind
                            {
                                // Include should expose record labels from included types
                                // in the current scope, matching OCaml's Env.add_signature.
                                let ty_res = tctx.type_ctx.new_constr(
                                    crate::types::path::Path::Pident(id.clone()),
                                    decl.type_params.clone(),
                                );
                                // Include signatures can carry non-generic nodes in Rust.
                                // Promote the shared label scheme to generic-level so
                                // instance_label can instantiate fresh per-use copies.
                                crate::types::ctype::force_generalize_sig_type(
                                    tctx.type_ctx,
                                    ty_res,
                                );
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
                                    new_env.add_label(ld.ld_id.clone(), lbl_desc);
                                }
                            }
                        }
                        crate::types::decl::SignatureItem::SigModule(id, md, _) => {
                            new_env.add_module(id.clone(), md.clone());
                        }
                        crate::types::decl::SignatureItem::SigModtype(id, mtd) => {
                            new_env.add_modtype(id.clone(), mtd.clone());
                        }
                        _ => {}
                    }
                }
            }

            let item_sig = stored_include_sig.unwrap_or_default();
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
                env.clone_preserve_id(),
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
    transl_sig_type_declarations_with_ids(tctx, env, arena, decls, None)
}

fn transl_sig_type_declarations_with_ids<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    decls: &[crate::parser::ast::TypeDeclaration],
    predeclared_type_ids: Option<&[Ident]>,
) -> TypeModResult<Vec<TypedTypeDeclaration>> {
    let ctx = tctx.type_ctx;
    let mut typed_tree_decls = Vec::new();
    let mut internal_decls_for_generalize: Vec<crate::types::TypeDeclaration> = Vec::new();
    let declared_type_ids: Vec<Ident> = match predeclared_type_ids {
        Some(ids) => {
            debug_assert_eq!(ids.len(), decls.len());
            ids.to_vec()
        }
        None => {
            let mut ids = Vec::with_capacity(decls.len());
            for decl in decls {
                let type_name = decl.ptype_name.txt;
                let type_name_str = arena.get_string(type_name);
                ids.push(ctx.create_ident(type_name_str));
            }
            ids
        }
    };

    // Match OCaml Typedecl.transl_type_decl flow for signatures:
    // translate inside begin_def/end_def, then generalize declarations.
    ctx.begin_def();
    let loop_result: TypeModResult<()> = (|| {
        for (decl_idx, decl) in decls.iter().enumerate() {
            let type_name = decl.ptype_name.txt;
            let type_name_str = arena.get_string(type_name);
            let type_id = declared_type_ids[decl_idx].clone();

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
                    let (typed_manifest, manifest_ref) =
                        transl_type(tctx, env, arena.get_core_type(*manifest))?;
                    (Some(typed_manifest), Some(manifest_ref))
                }
                None => (None, None),
            };

            // Preserve signature type kind like OCaml transl_signature -> Typedecl.transl_type_decl.
            let (internal_type_kind, typed_tree_kind) = match &decl.ptype_kind {
                crate::parser::ast::TypeKind::Ptype_abstract => (
                    crate::types::TypeKind::TypeAbstract,
                    TypedTypeKind::Ttype_abstract,
                ),
                crate::parser::ast::TypeKind::Ptype_open => {
                    (crate::types::TypeKind::TypeOpen, TypedTypeKind::Ttype_open)
                }
                crate::parser::ast::TypeKind::Ptype_record(labels) => {
                    let mut internal_labels = Vec::with_capacity(labels.len());
                    let mut typed_tree_labels = Vec::with_capacity(labels.len());

                    for label in labels {
                        let lbl_name = arena.get_string(label.pld_name.txt);
                        let (typed_label_ty, mut lbl_type) =
                            transl_type(tctx, env, arena.get_core_type(label.pld_type))?;
                        if label.pld_optional {
                            let option_path = crate::types::predef::path_option();
                            lbl_type = tctx.type_ctx.new_constr(option_path, vec![lbl_type]);
                        }
                        let (poly_typed_core_type, poly_lbl_type) =
                            force_poly_typed_core_type(tctx.type_ctx, typed_label_ty, lbl_type);
                        let internal_lbl_type = match &*tctx.type_ctx.get_desc(poly_lbl_type) {
                            crate::types::type_expr::TypeDesc::Tpoly { body, vars }
                                if vars.is_empty() =>
                            {
                                *body
                            }
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
                        let label_id = ctx.create_ident(lbl_name);
                        internal_labels.push(crate::types::LabelDeclaration {
                            ld_id: label_id.clone(),
                            ld_mutable: mutable_flag,
                            ld_optional: label.pld_optional,
                            ld_type: internal_lbl_type,
                            ld_loc: arena.to_location(label.pld_loc),
                            ld_attributes: parser_attrs_to_decl_attrs(arena, &label.pld_attributes),
                        });

                        typed_tree_labels.push(TypedLabelDeclaration {
                            ld_id: label_id,
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
                                    let (typed_arg, arg_ref) =
                                        transl_type(tctx, env, arena.get_core_type(*arg))?;
                                    internal_tuple_args.push(arg_ref);
                                    typed_tuple_args.push(typed_arg);
                                }
                                (
                                    crate::types::ConstructorArguments::CstrTuple(
                                        internal_tuple_args,
                                    ),
                                    TypedConstructorArguments::Cstr_tuple(typed_tuple_args),
                                )
                            }
                            crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                                let mut internal_record_labels = Vec::with_capacity(labels.len());
                                let mut typed_record_labels = Vec::with_capacity(labels.len());
                                for label in labels {
                                    let lbl_name = arena.get_string(label.pld_name.txt);
                                    let (typed_label_ty, mut lbl_type) = transl_type(
                                        tctx,
                                        env,
                                        arena.get_core_type(label.pld_type),
                                    )?;
                                    if label.pld_optional {
                                        let option_path = crate::types::predef::path_option();
                                        lbl_type =
                                            tctx.type_ctx.new_constr(option_path, vec![lbl_type]);
                                    }
                                    let (poly_typed_core_type, poly_lbl_type) =
                                        force_poly_typed_core_type(
                                            tctx.type_ctx,
                                            typed_label_ty,
                                            lbl_type,
                                        );
                                    let internal_lbl_type =
                                        match &*tctx.type_ctx.get_desc(poly_lbl_type) {
                                            crate::types::type_expr::TypeDesc::Tpoly {
                                                body,
                                                vars,
                                            } if vars.is_empty() => *body,
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
                                    let label_id = ctx.create_ident(lbl_name);
                                    internal_record_labels.push(crate::types::LabelDeclaration {
                                        ld_id: label_id.clone(),
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
                                        ld_id: label_id,
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
                                let (typed, internal) =
                                    transl_type(tctx, env, arena.get_core_type(*res_type))?;
                                (Some(typed), Some(internal))
                            }
                            None => (None, None),
                        };

                        let cstr_id = ctx.create_ident(cstr_name);
                        internal_cstrs.push(crate::types::ConstructorDeclaration {
                            cd_id: cstr_id.clone(),
                            cd_args: internal_args,
                            cd_res: internal_res,
                            cd_loc: arena.to_location(cstr.pcd_loc),
                            cd_attributes: {
                                let mut attrs = tag_attrs.clone();
                                attrs.extend(cstr.pcd_attributes.iter().cloned());
                                parser_attrs_to_decl_attrs(arena, &Attributes::from_vec(attrs))
                            },
                        });
                        typed_tree_cstrs.push(TypedConstructorDeclaration {
                            cd_id: cstr_id,
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

    let mut variance_env = env.clone();
    for (type_id, decl) in declared_type_ids
        .iter()
        .zip(internal_decls_for_generalize.iter())
    {
        variance_env.add_type(type_id.clone(), decl.clone());
    }
    let resolved_variances = compute_type_variance_fixpoint(ctx, &variance_env, &declared_type_ids);
    if resolved_variances.len() == declared_type_ids.len() {
        for (idx, variance_row) in resolved_variances.iter().enumerate() {
            if let Some(typed_decl) = typed_tree_decls.get_mut(idx) {
                typed_decl.typ_type.type_variance = variance_row.clone();
            }
            if let Some(internal_decl) = internal_decls_for_generalize.get_mut(idx) {
                internal_decl.type_variance = variance_row.clone();
            }
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
    use crate::context::IdGenerator;
    use crate::parser::{Parser, module};
    use crate::types::{TypeCheckContext, TypeContext, initial_env};

    #[test]
    fn test_type_module_error_conversion() {
        let core_error = TypeCoreError::MultiplyBoundVariable("x".to_string());
        let mod_error: TypeModError = core_error.into();
        match mod_error {
            TypeModError::CoreError(_) => {}
            _ => panic!("Expected CoreError"),
        }
    }

    fn type_test_structure(source: &str) -> Structure {
        crate::ident::Ident::set_current_time(999);
        let id_gen = IdGenerator::with_start_stamp(999);
        let _ = id_gen.next_stamp();
        let type_ctx = TypeContext::new(&id_gen);
        let mut parser = Parser::new("test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "parse failed");
        let arena = parser.arena();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (typed, _) = type_structure(&mut tctx, &env, arena, &structure).expect("typecheck");
        typed
    }

    #[test]
    fn constrained_include_structure_keeps_original_alias_path() {
        let typed = type_test_structure(
            r#"
module M' = {
  module N = {
    let x = 1
  }
  module N' = N
}

module M3: {
  module N': {
    let x: int
  }
} = {
  include M'
}
"#,
        );

        let m_prime = typed
            .str_items
            .iter()
            .find_map(|item| match &item.str_desc {
                StructureItemDesc::Tstr_module(binding) if binding.mb_id.name() == "M'" => {
                    Some(binding.mb_id.clone())
                }
                _ => None,
            })
            .expect("M' binding");

        let inner_structure = typed
            .str_items
            .iter()
            .find_map(|item| match &item.str_desc {
                StructureItemDesc::Tstr_module(binding) if binding.mb_id.name() == "M3" => {
                    let ModuleExprDesc::Tmod_constraint(inner, _, _, _) = &binding.mb_expr.mod_desc
                    else {
                        panic!("expected constrained module");
                    };
                    let ModuleExprDesc::Tmod_structure(structure) = &inner.mod_desc else {
                        panic!("expected inner structure");
                    };
                    Some(structure)
                }
                _ => None,
            })
            .expect("M3 structure");

        let n_prime_decl = inner_structure
            .str_type
            .iter()
            .find_map(|item| match item {
                crate::types::decl::SignatureItem::SigModule(id, md, _) if id.name() == "N'" => {
                    Some(md)
                }
                _ => None,
            })
            .expect("N' signature item");

        assert!(matches!(
            &n_prime_decl.md_type,
            crate::types::decl::ModuleType::MtyAlias(
                _,
                Path::Pdot(prefix, name, _)
            ) if matches!(prefix.as_ref(), Path::Pident(id) if id.same(&m_prime))
                && name == "N"
        ));
    }
}

// ── Comptime Registration ──────────────────────────────────────────────────

// process_comptime_derives and compile_generated_source removed.
// The derive system will be reimplemented using the predefined typeInfo type
// and @comptime.inline evaluation. The optimizer handles switch elimination
// on literal typeInfo values automatically.

// Legacy function kept for reference — will be removed once predefined typeInfo works.
#[allow(dead_code)]
fn _process_comptime_derives_legacy<'a>(
    tctx: &mut crate::types::typecore::TypeCheckContext<'a>,
    env: &Env,
    arena: &'a crate::parse_arena::ParseArena,
    decl: &crate::parser::ast::TypeDeclaration,
) -> Result<Vec<(StructureItem, Vec<crate::types::decl::SignatureItem>, Env)>, TypeModError> {
    let mut results = Vec::new();
    let type_name = arena.get_string(decl.ptype_name.txt).to_string();

    // Check attributes for known derives
    for (attr_name_loc, _payload) in decl.ptype_attributes.iter() {
        let attr_name = arena.get_string(attr_name_loc.txt);

        // Find the type declaration in env to build TypeInfo
        let type_info = {
            let id_and_decl = env.find_type(&type_name);
            match id_and_decl {
                Ok(type_decl) => {
                    let mut visited = Vec::new();
                    // Build TypeInfo from the type declaration's kind
                    match &type_decl.type_kind {
                        crate::types::decl::TypeKind::TypeRecord(labels, _) => {
                            let fields = labels
                                .iter()
                                .map(|ld| crate::types::comptime::FieldInfo {
                                    name: ld.ld_id.name().to_string(),
                                    typ: crate::types::comptime::build_type_info(
                                        tctx.type_ctx,
                                        env,
                                        ld.ld_type,
                                        &mut visited,
                                    ),
                                    mutable: ld.ld_mutable
                                        == crate::types::asttypes::MutableFlag::Mutable,
                                    optional: ld.ld_optional,
                                    attributes: vec![],
                                })
                                .collect();
                            crate::types::comptime::TypeInfo::Record {
                                name: type_name.clone(),
                                fields,
                                unboxed: type_decl.type_unboxed.unboxed,
                            }
                        }
                        crate::types::decl::TypeKind::TypeVariant(ctors) => {
                            let constructors = ctors
                                .iter()
                                .map(|cd| {
                                    let args = match &cd.cd_args {
                                        crate::types::decl::ConstructorArguments::CstrTuple(
                                            tys,
                                        ) => tys
                                            .iter()
                                            .map(|t| {
                                                crate::types::comptime::build_type_info(
                                                    tctx.type_ctx,
                                                    env,
                                                    *t,
                                                    &mut visited,
                                                )
                                            })
                                            .collect(),
                                        crate::types::decl::ConstructorArguments::CstrRecord(
                                            labels,
                                        ) => labels
                                            .iter()
                                            .map(|ld| {
                                                crate::types::comptime::build_type_info(
                                                    tctx.type_ctx,
                                                    env,
                                                    ld.ld_type,
                                                    &mut visited,
                                                )
                                            })
                                            .collect(),
                                    };
                                    crate::types::comptime::ConstructorInfo {
                                        name: cd.cd_id.name().to_string(),
                                        args,
                                        attributes: vec![],
                                    }
                                })
                                .collect();
                            crate::types::comptime::TypeInfo::Variant {
                                name: type_name.clone(),
                                constructors,
                                unboxed: type_decl.type_unboxed.unboxed,
                            }
                        }
                        _ => continue,
                    }
                }
                Err(_) => continue,
            }
        };

        // TODO: @comptime.derive system — currently not implemented.
        // When implemented, this will look up the handler in
        // tctx.comptime_derive_handlers, partially evaluate its body
        // with @typeInfo(T) resolved, and splice the result.
        let _ = (attr_name, &type_info, &type_name);
    }

    Ok(results)
}

/// Compile a generated ReScript source string into typed structure items.
fn compile_generated_source<'a>(
    tctx: &mut crate::types::typecore::TypeCheckContext<'a>,
    env: &Env,
    source: &str,
) -> Result<Vec<(StructureItem, Vec<crate::types::decl::SignatureItem>, Env)>, TypeModError> {
    let mut parser = crate::parser::Parser::new("__comptime_derive__.res", source);
    let structure = crate::parser::module::parse_structure(&mut parser);

    if parser.has_errors() {
        return Err(TypeModError::CoreError(TypeCoreError::Other(format!(
            "Comptime derive generated invalid ReScript:\n{}\nErrors: {:?}",
            source,
            parser.diagnostics()
        ))));
    }

    let generated_arena = parser.into_arena();

    // Type-check each generated item in a sub-context
    let mut results = Vec::new();
    let mut current_env = env.clone();

    for item in &structure {
        let mut gen_tctx =
            crate::types::typecore::TypeCheckContext::new(tctx.type_ctx, &generated_arena);
        gen_tctx.persistent_env = tctx.persistent_env.clone();
        gen_tctx.comptime_functions = tctx.comptime_functions.clone();

        let ctx = gen_tctx.type_ctx;
        ctx.init_def(ctx.current_stamp());
        gen_tctx.set_unify_env(&current_env);

        match type_structure_item(&mut gen_tctx, &current_env, &generated_arena, item) {
            Ok((typed_item, item_sig, new_env)) => {
                current_env = new_env;
                results.push((typed_item, item_sig, current_env.clone()));
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    Ok(results)
}

// Comptime function registration is now done inline in the Pstr_value
// handler above, before type-checking the body.
