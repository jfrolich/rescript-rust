//! Module type checking for ReScript.
//!
//! This module handles type checking of:
//! - Module expressions (`ModuleExpr`)
//! - Structures (module bodies)
//! - Signatures (module types)
//! - Functor application and coercion

use crate::diagnostics::{Warning, WarningConfig};
use crate::fast_hash::{AHashMap as HashMap, AHashSet as HashSet};
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
use crate::types::Variance as TypesVariance;
use crate::types::env::Env;
use crate::types::path::PathView;
use crate::types::type_expr::{LOWEST_LEVEL, TypeExprRef};
use crate::types::typecore::{
    TypeCheckContext, TypeCoreError, resolve_type_constructor_path, transl_type, transl_type_fixed,
    type_binding, type_exp, type_expression,
};
use crate::types::typedtree::{
    EnvRef, Expression, IncludeDeclaration, IncludeDescription, ModuleBinding, ModuleCoercion,
    ModuleExpr, ModuleExprDesc, ModuleType, ModuleTypeDeclaration, OpenDeclaration, Structure,
    StructureItem, StructureItemDesc, TModTypeIdx, TypeExtension, TypedArena,
    TypedConstructorArguments, TypedConstructorDeclaration, TypedCoreType, TypedCoreTypeDesc,
    TypedLabelDeclaration, TypedTypeDeclaration, TypedTypeKind,
};
use crate::types::{Path, TypeDesc};

/// OCaml typedecl.ml:314-329 and 600-618: an optional record label is typed as
/// `{typ with ptyp_desc = Ptyp_constr ({txt = Lident "option"; loc =
/// typ.ptyp_loc}, [typ])}`, so `option` is looked up in the environment.
/// `Typetexp.transl_simple_type env closed` (typedecl.ml:225, 264-269):
/// record labels and non-GADT constructor arguments are translated `closed`.
fn transl_decl_arg_type(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    typ: &crate::parser::ast::CoreType,
    closed: bool,
) -> Result<(crate::types::typedtree::TypedCoreType, TypeExprRef), TypeCoreError> {
    if closed {
        crate::types::typecore::transl_type_fixed(tctx, env, typ)
    } else {
        transl_type(tctx, env, typ)
    }
}

fn transl_label_type(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    arena: &ParseArena,
    label: &crate::parser::ast::LabelDeclaration,
    closed: bool,
) -> Result<(crate::types::typedtree::TypedCoreType, TypeExprRef), TypeCoreError> {
    let typ = arena.get_core_type(label.pld_type);
    if !label.pld_optional {
        return transl_decl_arg_type(tctx, env, typ, closed);
    }
    let option_typ = crate::parser::ast::CoreType {
        ptyp_desc: crate::parser::ast::CoreTypeDesc::Ptyp_constr((
            crate::parse_arena::Located {
                txt: arena.option_lid(),
                loc: typ.ptyp_loc,
            },
            arena.push_shared_type_list(&[label.pld_type]),
        )),
        ptyp_loc: typ.ptyp_loc,
        ptyp_attributes: typ.ptyp_attributes.clone(),
    };
    transl_decl_arg_type(tctx, env, &option_typ, closed)
}

fn core_type_has_row_var(arena: &ParseArena, core_type: &crate::parser::ast::CoreType) -> bool {
    match &core_type.ptyp_desc {
        crate::parser::ast::CoreTypeDesc::Ptyp_alias(inner) => {
            let (inner, _) = &**inner;
            core_type_has_row_var(arena, arena.get_core_type(*inner))
        }
        crate::parser::ast::CoreTypeDesc::Ptyp_object(inner) => {
            let (_, closed) = &**inner;
            matches!(closed, crate::parser::ast::ClosedFlag::Open)
        }
        crate::parser::ast::CoreTypeDesc::Ptyp_variant(inner) => {
            let (_, closed, labels) = &**inner;
            matches!(closed, crate::parser::ast::ClosedFlag::Open)
                || (matches!(closed, crate::parser::ast::ClosedFlag::Closed) && labels.is_some())
        }
        _ => false,
    }
}

/// The usage checks `Env.store_type ~check:true` (env.ml:1592-1620)
/// registers for declarations added to the environment through
/// `List.fold_right`: the type, then its constructors.
fn register_type_declaration_usage_checks(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    decls: &[TypedTypeDeclaration],
) {
    for decl in decls.iter().rev() {
        let name = decl.typ_id.name();
        tctx.check_type_usage(name, tctx.resolve_loc(decl.typ_type.type_loc), decl.typ_loc);
        if let crate::types::TypeKind::TypeVariant(constructors, _) = &decl.typ_type.type_kind {
            let names: Vec<String> = constructors
                .iter()
                .map(|cd| cd.cd_id.name().to_string())
                .collect();
            tctx.check_constructor_usages(
                name,
                tctx.resolve_loc(decl.typ_type.type_loc),
                decl.typ_loc,
                &names,
                env.is_in_signature(),
            );
        }
    }
}

fn type_decl_is_fixed_type(
    arena: &ParseArena,
    decl: &crate::parser::ast::TypeDeclaration,
    manifest: &crate::parser::ast::CoreType,
) -> bool {
    type_decl_could_be_fixed_type(decl) && core_type_has_row_var(arena, manifest)
}

fn type_decl_could_be_fixed_type(decl: &crate::parser::ast::TypeDeclaration) -> bool {
    matches!(
        &decl.ptype_kind,
        crate::parser::ast::TypeKind::Ptype_abstract
    ) && matches!(decl.ptype_private, crate::parser::ast::PrivateFlag::Private)
}

/// The `fixed` argument OCaml passes to `transl_simple_type` for a manifest:
/// `no_row = not (is_fixed_type sdecl)` (typedecl.ml:703-704, 1975-1980).
fn type_decl_manifest_uses_fixed_type_variables(
    arena: &ParseArena,
    decl: &crate::parser::ast::TypeDeclaration,
    manifest: &crate::parser::ast::CoreType,
) -> bool {
    !type_decl_is_fixed_type(arena, decl, manifest)
}

fn parser_variance_to_types(variance: ParserVariance) -> TypesVariance {
    match variance {
        ParserVariance::Covariant => TypesVariance::covariant(),
        ParserVariance::Contravariant => TypesVariance::contravariant(),
        ParserVariance::Invariant => TypesVariance::null(),
    }
}

fn fixed_row_name(name: &str) -> String {
    format!("{name}#row")
}

#[derive(Clone)]
struct FixedRowTypeId {
    decl_idx: usize,
    id: Ident,
    name: String,
}

fn collect_fixed_row_type_ids(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    decls: &[crate::parser::ast::TypeDeclaration],
) -> Vec<FixedRowTypeId> {
    let mut row_ids = Vec::new();
    for (decl_idx, decl) in decls.iter().enumerate() {
        if !type_decl_could_be_fixed_type(decl) {
            continue;
        }
        let Some(manifest_idx) = decl.ptype_manifest else {
            continue;
        };
        let manifest = arena.get_core_type(manifest_idx);
        if core_type_has_row_var(arena, manifest) {
            let name = fixed_row_name(arena.get_string(decl.ptype_name.txt));
            row_ids.push(FixedRowTypeId {
                decl_idx,
                id: ctx.create_ident(&name),
                name,
            });
        }
    }
    row_ids
}

fn fixed_row_type_id_for_decl(
    row_ids: &[FixedRowTypeId],
    decl_idx: usize,
) -> Option<&FixedRowTypeId> {
    row_ids.iter().find(|row_id| row_id.decl_idx == decl_idx)
}

/// Translated declaration parameters with their variances, and their types.
type TranslatedParams = (Vec<(TypedCoreType, TypesVariance)>, Vec<TypeExprRef>);

fn translate_type_declaration_params<'a>(
    tctx: &mut TypeCheckContext<'a>,
    arena: &'a ParseArena,
    params: &[(crate::parse_arena::CoreTypeIdx, ParserVariance)],
) -> TypeModResult<TranslatedParams> {
    let ctx = tctx.type_ctx;
    let mut typed_params = Vec::with_capacity(params.len());
    let mut internal_params = Vec::with_capacity(params.len());

    // `make_params` (typedecl.ml:165-170) of `Typetexp.transl_type_param`
    // (typetexp.ml:233-270), each in `warning_scope styp.ptyp_attributes`.
    for (core_type_idx, parser_var) in params {
        let core_type = arena.get_core_type(*core_type_idx);
        let (typed_core_type, type_ref) =
            with_warning_scope(tctx, arena, &core_type.ptyp_attributes, true, |tctx| {
                let typed_param = |desc, type_ref| TypedCoreType {
                    ctyp_desc: desc,
                    ctyp_type: type_ref,
                    ctyp_env: EnvRef(0),
                    ctyp_loc: core_type.ptyp_loc,
                    ctyp_attributes: core_type.ptyp_attributes.clone(),
                };
                match &core_type.ptyp_desc {
                    // `Ttyp_any` with `new_global_var ~name:"_"`.
                    crate::parser::ast::CoreTypeDesc::Ptyp_any => {
                        let type_ref = ctx.new_global_var(Some("_".into()));
                        Ok((
                            typed_param(TypedCoreTypeDesc::Ttyp_var(None), type_ref),
                            type_ref,
                        ))
                    }
                    crate::parser::ast::CoreTypeDesc::Ptyp_var(name) => {
                        let name = arena.get_string(*name);
                        check_type_variable_name(core_type.ptyp_loc, name)?;
                        if tctx.type_variables.contains_key(name) {
                            return Err(TypeModError::RepeatedParameter {
                                loc: core_type.ptyp_loc,
                            });
                        }
                        let type_ref = ctx.new_global_var(Some(name.into()));
                        tctx.type_variables.insert(name.to_string(), type_ref);
                        Ok((
                            typed_param(
                                TypedCoreTypeDesc::Ttyp_var(Some(name.to_string())),
                                type_ref,
                            ),
                            type_ref,
                        ))
                    }
                    _ => unreachable!("Typetexp.transl_type_param: a parameter is a variable"),
                }
            })?;

        internal_params.push(type_ref);
        typed_params.push((typed_core_type, parser_variance_to_types(*parser_var)));
    }

    Ok((typed_params, internal_params))
}

fn fixed_row_placeholder_decl(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    decl: &crate::parser::ast::TypeDeclaration,
    row_id: &Ident,
) -> crate::types::TypeDeclaration {
    let arity = decl.ptype_params.len();
    crate::types::TypeDeclaration {
        type_params: (0..arity).map(|_| ctx.new_generic_var(None)).collect(),
        type_arity: arity as i32,
        type_kind: crate::types::TypeKind::TypeAbstract,
        type_private: crate::types::PrivateFlag::Private,
        type_manifest: None,
        type_variance: (0..arity).map(|_| TypesVariance::full()).collect(),
        type_newtype_level: None,
        type_loc: ctx.intern_ast_loc(arena, decl.ptype_loc),
        type_attributes: parser_attrs_to_decl_attrs(arena, ctx, &decl.ptype_attributes),
        type_immediate: false,
        type_representation: crate::types::TypeRepresentation::Boxed,
        type_shape: crate::types::ValueShape::Unstated,
        type_inlined_types: vec![],
        type_path: Some(Path::pident(*row_id)),
    }
}

fn translate_fixed_row_type_declaration<'a>(
    tctx: &mut TypeCheckContext<'a>,
    arena: &'a ParseArena,
    row_id: Ident,
    row_name: String,
    decl: &crate::parser::ast::TypeDeclaration,
    type_path: Option<Path>,
) -> TypeModResult<TypedTypeDeclaration> {
    let saved_type_variables = std::mem::take(&mut tctx.type_variables);
    let result = translate_type_declaration_params(tctx, arena, &decl.ptype_params);
    tctx.type_variables = saved_type_variables;
    let (typ_params, internal_type_params) = result?;

    let type_attributes = parser_attrs_to_decl_attrs(arena, tctx.type_ctx, &decl.ptype_attributes);
    let internal_decl = crate::types::TypeDeclaration {
        type_params: internal_type_params,
        type_arity: decl.ptype_params.len() as i32,
        type_kind: crate::types::TypeKind::TypeAbstract,
        type_private: crate::types::PrivateFlag::Private,
        type_manifest: None,
        type_variance: typ_params.iter().map(|(_, variance)| *variance).collect(),
        type_newtype_level: None,
        type_loc: tctx.intern_ast_loc(arena, decl.ptype_loc),
        type_attributes,
        type_immediate: false,
        type_representation: crate::types::TypeRepresentation::Boxed,
        type_shape: crate::types::ValueShape::Unstated,
        type_inlined_types: vec![],
        type_path,
    };

    Ok(TypedTypeDeclaration {
        typ_id: row_id,
        typ_name: crate::parse_arena::Located {
            txt: row_name,
            loc: decl.ptype_name.loc,
        },
        typ_params: typ_params
            .into_iter()
            .map(|(ct, v)| (tctx.typed.push_core_type(ct), v))
            .collect(),
        typ_type: internal_decl,
        typ_cstrs: Vec::new(),
        typ_kind: TypedTypeKind::Ttype_abstract,
        typ_private: decl.ptype_private,
        typ_manifest: None,
        typ_loc: decl.ptype_loc,
        typ_attributes: decl.ptype_attributes.clone(),
    })
}

fn check_type_variable_name(loc: LocIdx, name: &str) -> TypeModResult<()> {
    if name.starts_with('_') {
        Err(TypeModError::CoreError(
            TypeCoreError::InvalidVariableName {
                loc,
                name: format!("'{name}"),
            },
        ))
    } else {
        Ok(())
    }
}

pub(crate) fn report_inclusion_warnings(
    tctx: &mut TypeCheckContext<'_>,
    loc: LocIdx,
    warnings: Vec<Warning>,
) {
    for warning in warnings {
        tctx.report_warning(loc, warning);
    }
}

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

fn open_direct_persistent_module(
    env: &mut Env,
    lid: &Longident,
    arena: &ParseArena,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
    slot: Option<u32>,
) -> Option<Path> {
    let Longident::Lident(module_idx) = lid else {
        return None;
    };
    let module_name = arena.get_string(*module_idx);
    if env.find_module(module_name).is_ok() {
        return None;
    }
    let pers = pers_env.as_mut()?;
    // env.ml:1012: `Pident (Ident.create_persistent s)`.
    let root = Path::pident(ctx.create_ast_persistent_ident(arena, *module_idx));
    if pers.open_module(module_name, root, env, ctx, slot) {
        Some(root)
    } else {
        None
    }
}

/// Open a `-open M` module (command line or `@@config` flags) into the
/// initial environment `env`.
///
/// OCaml `Res_compmisc.open_implicit_module` (compiler/core/res_compmisc.ml:42-46)
/// runs `Typemod.type_open_ Override` on `Longident.parse m` located at
/// `Location.in_file "command line"`, so a module that is not found stops the
/// compile with the usual unbound-module error reported at "command line".
pub(crate) fn type_command_line_open(
    tctx: &mut TypeCheckContext<'_>,
    env: &mut Env,
    name: &str,
) -> TypeModResult<()> {
    let ctx = tctx.type_ctx;
    if !name.contains('.')
        && let Some(pers) = tctx.persistent_env.as_mut()
        && pers.open_module(
            name,
            Path::pident(Ident::create_persistent(name)),
            env,
            ctx,
            None,
        )
    {
        // Env.open_signature (env.ml:1874-1877) exposes the opened components
        // without a root module binding; keep the raw signature registered for
        // descriptor lookup.
        pers.register_opened_raw_sig(ctx, name);
        return Ok(());
    }
    // A dotted name, or one the environment binds (such as a module of the
    // implicitly opened Stdlib): look it up like a source `open`.
    let arena = tctx.arena;
    let lid = command_line_longident(arena, name);
    let lookup_env = env.clone();
    if lookup_module_path_by_lid(&lid, arena, &lookup_env, &mut tctx.persistent_env, ctx).is_none()
    {
        let loc = arena.push_typecheck_command_line_loc();
        return Err(TypeModError::CoreError(
            crate::types::typecore::unbound_module_lookup_error(tctx, &lookup_env, loc, &lid),
        ));
    }
    if crate::types::typecore::open_module_lid_components_into_env(
        &lid,
        arena,
        &lookup_env,
        env,
        &mut tctx.persistent_env,
        ctx,
        None,
    )
    .is_none()
    {
        let loc = arena.push_typecheck_command_line_loc();
        if let Some(err) = structure_expected_error_for_open(tctx, &lookup_env, arena, &lid, loc) {
            return Err(err);
        }
    }
    Ok(())
}

/// `Longident.parse` (compiler/ml/longident.ml): split a dotted module path.
fn command_line_longident(arena: &ParseArena, name: &str) -> Longident {
    let mut components = name.split('.');
    let head = components.next().unwrap_or_default();
    let mut lid = Longident::Lident(arena.push_shared_string(head.to_string()));
    for component in components {
        lid = Longident::Ldot(
            Box::new(lid),
            arena.push_shared_string(component.to_string()),
        );
    }
    lid
}

fn flattened_persistent_alias_path(
    path: &Path,
    pers_env: Option<&crate::cmi::persistent_env::PersistentEnv>,
) -> Option<Path> {
    let pers = pers_env?;
    let Ok((head, components)) = path.flatten() else {
        return None;
    };
    if components.is_empty() || !head.is_persistent() {
        return None;
    }

    // OCaml compiler/ml/env.ml:781-813 resolves dotted lookups through component
    // tables, while env.ml:1441-1444 and 1517 use the exact module reached by
    // `find_module`/`scrape_alias`. Only use flattened heads already registered
    // from that component-derived alias evidence; do not fabricate candidates
    // from `Stdlib.JSON` -> `Stdlib_JSON`/`Belt.Map.String` -> `Belt_MapString`
    // spellings here.
    pers.flattened_alias_heads_for_path(path)
        .into_iter()
        .next()
        .map(|flattened_head| Path::pident(Ident::create_persistent(&flattened_head)))
}

/// Wrap a translated label type in Ttyp_poly if not already poly.
/// Mirrors OCaml `Ast_helper.Typ.force_poly` + `transl_simple_type` flow in `transl_labels`:
/// if the parsed label type was already `Ptyp_poly`, `transl_type` already produced a
/// `Ttyp_poly` core type, so we don't double-wrap. If it wasn't poly, we wrap in
/// `Ttyp_poly([], inner)` to match OCaml's `force_poly` behavior.
fn force_poly_typed_core_type(
    ta: &mut TypedArena,
    ctx: &crate::types::context::TypeContext,
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
                ctyp_desc: TypedCoreTypeDesc::Ttyp_poly(
                    vec![],
                    ta.push_core_type(typed_core_type.clone()),
                ),
                ctyp_type: poly_ty,
                ctyp_env: typed_core_type.ctyp_env,
                ctyp_loc: typed_core_type.ctyp_loc,
                ctyp_attributes: Attributes::new(),
            };
            (poly_ctyp, poly_ty)
        }
    }
}

fn lookup_rebind_constructor<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    lid: &Located<LidentIdx>,
) -> TypeModResult<(Path, crate::types::decl::ConstructorDescription)> {
    let longident = tctx.resolve_lid(lid.txt).clone();
    let desc = match &longident {
        Longident::Lident(name_idx) => env
            .find_constructor(tctx.arena.get_string(*name_idx))
            .ok()
            .cloned(),
        Longident::Ldot(_, _) => crate::types::typecore::lookup_constructor_in_module(
            &longident,
            tctx.arena,
            env,
            &mut tctx.persistent_env,
            tctx.type_ctx,
            None,
        )
        .map(|(_, desc)| desc),
        Longident::Lapply(_, _) => None,
    };
    let desc = desc.ok_or_else(|| {
        TypeModError::CoreError(crate::types::typecore::unbound_constructor_lookup_error(
            tctx, env, lid.loc, &longident,
        ))
    })?;
    // The path the rebound constructor is read at is the one its description
    // carries (compiler/ml/typedecl.ml:1745-1749): for `M.E` the field `E`
    // of `M`, not a name of its own. A constructor that is no extension is
    // rejected by the caller, which unifies its type with the extended one.
    let path = match &desc.cstr_kind {
        crate::types::ConstructorKind::Extension(path) => *path,
        crate::types::ConstructorKind::Ordinary(_) => Path::pident(Ident::create_persistent(
            tctx.arena.get_string(longident.last_idx()),
        )),
    };
    Ok((path, desc))
}

/// The arguments of a rebound extension constructor (compiler/ml/
/// typedecl.ml:1701-1718): the instanced arguments, or for an inline record
/// the labels of an instance of its declaration whose parameters are unified
/// with the instanced record type's. The caller generalizes them.
fn rebind_constructor_arguments(
    tctx: &mut TypeCheckContext<'_>,
    desc: &crate::types::decl::ConstructorDescription,
    inst_args: &[TypeExprRef],
) -> crate::types::ConstructorArguments {
    let ctx = tctx.type_ctx;
    if let Some(inlined) = &desc.cstr_inlined {
        let tl = match inst_args {
            [arg] => match &*ctx.get_desc(ctx.repr(*arg)) {
                crate::types::TypeDesc::Tconstr { args, .. } => ctx.type_list(args).to_vec(),
                _ => Vec::new(),
            },
            _ => Vec::new(),
        };
        let decl = crate::types::ctype::instance_declaration(ctx, inlined);
        // typedecl.ml:1727-1728 asserts the arities agree and lets `Unify`
        // escape; neither can happen for a well-formed inline record.
        debug_assert_eq!(decl.type_params.len(), tl.len());
        for (param, ty) in decl.type_params.iter().zip(tl.iter()) {
            let unified = crate::types::ctype::unify(ctx, &mut tctx.unify_state, *param, *ty);
            debug_assert!(unified.is_ok(), "rebinding inline record parameters failed");
        }
        if let crate::types::TypeKind::TypeRecord(labels, _) = decl.type_kind {
            return crate::types::ConstructorArguments::CstrRecord(labels.to_vec());
        }
    }
    crate::types::ConstructorArguments::CstrTuple(inst_args.to_vec())
}

/// `Datarepr.constructor_args` (compiler/ml/datarepr.ml:64-92) for a
/// rebound constructor whose arguments are an inline record: the record type
/// at `path` and its declaration. `None` for tuple arguments.
fn rebound_constructor_args(
    ctx: &crate::types::context::TypeContext,
    path: &Path,
    ext_args: &crate::types::ConstructorArguments,
) -> (
    Option<Vec<TypeExprRef>>,
    Option<Box<crate::types::TypeDeclaration>>,
) {
    let crate::types::ConstructorArguments::CstrRecord(labels) = ext_args else {
        return (None, None);
    };
    let type_params = inline_record_type_params(ctx, labels);
    let inline_ty = ctx.new_generic_constr(*path, type_params.clone());
    let decl = crate::types::TypeDeclaration {
        type_arity: type_params.len() as i32,
        type_variance: type_params
            .iter()
            .map(|_| crate::types::Variance::FULL)
            .collect(),
        type_params,
        type_kind: crate::types::TypeKind::TypeRecord(
            labels.clone().into(),
            crate::types::RecordRepresentation::RecordExtension,
        ),
        type_private: crate::types::PrivateFlag::Public,
        type_manifest: None,
        type_newtype_level: None,
        type_loc: crate::types::DeclLoc::none(),
        type_attributes: vec![],
        type_immediate: false,
        type_representation: crate::types::TypeRepresentation::Boxed,
        type_shape: crate::types::ValueShape::Unstated,
        type_inlined_types: vec![],
        type_path: None,
    };
    (Some(vec![inline_ty]), Some(Box::new(decl)))
}

fn parser_private_to_type_private(
    private: crate::parser::ast::PrivateFlag,
) -> crate::types::PrivateFlag {
    match private {
        crate::parser::ast::PrivateFlag::Private => crate::types::PrivateFlag::Private,
        crate::parser::ast::PrivateFlag::Public => crate::types::PrivateFlag::Public,
    }
}

/// A payload expression that `Ast_payload.semantic_string_of_expression`
/// reads (compiler/ml/ast_payload.ml:39-51) other than a bare string
/// constant: braces around a string, or a backquoted string without
/// interpolation.
fn semantic_string_payload(
    arena: &ParseArena,
    ctx: &crate::types::context::TypeContext,
    expr: &crate::parser::ast::Expression,
) -> Option<crate::types::decl::SemanticStringPayload> {
    let mut braces = 0;
    let mut inner = expr;
    while let crate::parser::ast::ExpressionDesc::Pexp_braces(b) = &inner.pexp_desc {
        braces += 1;
        inner = arena.get_expanded_expr(b.expr);
    }
    let template = matches!(
        inner.pexp_desc,
        crate::parser::ast::ExpressionDesc::Pexp_template(_)
    );
    if braces == 0 && !template {
        return None;
    }
    // The parser rejects an invalid escape, but a PPX's template reaches
    // here undecoded; readers raise on it.
    let semantic = match crate::ast_payload::semantic_string_of_expression(arena, inner) {
        Ok(semantic) => Ok(semantic?),
        Err(error) => Err(ctx.intern_ast_loc(arena, error.loc)),
    };
    Some(crate::types::decl::SemanticStringPayload {
        semantic,
        braces,
        template,
    })
}

fn parser_attr_to_decl_attr(
    arena: &ParseArena,
    ctx: &crate::types::context::TypeContext,
    attr: &ParsedAttribute,
) -> crate::types::decl::Attribute {
    let (name, payload) = attr;
    let attr_name = arena.get_string(name.txt);
    let attr_payload = match payload {
        ParsedPayload::PStr(items) => {
            if attr_name == "deprecated"
                && let Some(payload) = parser_deprecated_payload_to_decl_payload(arena, ctx, items)
            {
                let loc = ctx.intern_ast_loc(arena, name.loc);
                return crate::types::decl::Attribute {
                    attr_name: crate::types::asttypes::Located {
                        txt: attr_name.to_string(),
                        loc,
                    },
                    attr_payload: payload,
                    attr_loc: loc,
                };
            }
            // OCaml's Lambda.find_name: extract string from @as("name") payloads.
            // PStr with a single Pstr_eval(Pexp_constant(String(value, _)), _) → Str(value)
            if let [item] = items.as_slice() {
                if let crate::parser::ast::StructureItemDesc::Pstr_eval(eval_box) = &item.pstr_desc
                {
                    let (expr_idx, _attrs) = eval_box.as_ref();
                    let expr = arena.get_expanded_expr(*expr_idx);
                    if let Some(payload) = semantic_string_payload(arena, ctx, expr) {
                        crate::types::decl::AttributePayload::SemanticString(Box::new(payload))
                    } else if let crate::parser::ast::ExpressionDesc::Pexp_constant(c) =
                        &expr.pexp_desc
                    {
                        match c {
                            crate::parser::ast::Constant::String(value) => {
                                crate::types::decl::AttributePayload::Str(
                                    value.semantic(arena).to_string(),
                                )
                            }
                            crate::parser::ast::Constant::Integer(value, suffix) => match suffix {
                                Some('n') => crate::types::decl::AttributePayload::BigInt(
                                    arena.get_string(*value).to_string(),
                                ),
                                Some(_) => crate::types::decl::AttributePayload::Structure(vec![]),
                                None => crate::types::decl::AttributePayload::IntLiteral(
                                    arena.get_string(*value).to_string(),
                                ),
                            },
                            crate::parser::ast::Constant::Float(value, _) => {
                                crate::types::decl::AttributePayload::Float(
                                    arena.get_string(*value).to_string(),
                                )
                            }
                            _ => crate::types::decl::AttributePayload::Structure(vec![]),
                        }
                    } else if let crate::parser::ast::ExpressionDesc::Pexp_ident(lid) =
                        &expr.pexp_desc
                    {
                        // @as(undefined), @as(null) — identifier payloads
                        let name = arena.lident_last(lid.txt);
                        match name {
                            "true" => crate::types::decl::AttributePayload::Bool(true),
                            "false" => crate::types::decl::AttributePayload::Bool(false),
                            _ => crate::types::decl::AttributePayload::Ident(name.to_string()),
                        }
                    } else if let crate::parser::ast::ExpressionDesc::Pexp_tuple(elements) =
                        &expr.pexp_desc
                        && let Some(strings) = arena
                            .expr_list(*elements)
                            .iter()
                            .map(|element| match &arena.get_expanded_expr(*element).pexp_desc {
                                crate::parser::ast::ExpressionDesc::Pexp_constant(
                                    crate::parser::ast::Constant::String(value),
                                ) => Some(value.semantic(arena).to_string()),
                                _ => None,
                            })
                            .collect::<Option<Vec<_>>>()
                    {
                        crate::types::decl::AttributePayload::StrTuple(strings)
                    } else if let crate::parser::ast::ExpressionDesc::Pexp_construct(lid, args) =
                        &expr.pexp_desc
                        && args.txt.is_empty()
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
    let loc = ctx.intern_ast_loc(arena, name.loc);
    crate::types::decl::Attribute {
        attr_name: crate::types::asttypes::Located {
            txt: arena.get_string(name.txt).to_string(),
            loc,
        },
        attr_payload,
        attr_loc: loc,
    }
}

/// `Env.store_module` (env.ml:1649) reads the entering declaration's
/// `Builtin_attributes.deprecated_of_attrs`, raising where
/// `string_of_opt_payload` raises.
fn store_module_deprecated(
    ctx: &crate::types::context::TypeContext,
    attrs: &[crate::types::decl::Attribute],
) -> TypeModResult<()> {
    crate::types::typecore::deprecated_of_decl_attrs(attrs)
        .map_err(|loc| crate::types::typecore::invalid_escape_at(ctx, loc))?;
    Ok(())
}

fn parser_attrs_to_decl_attrs(
    arena: &ParseArena,
    ctx: &crate::types::context::TypeContext,
    attrs: &Attributes,
) -> Vec<crate::types::decl::Attribute> {
    attrs
        .iter()
        .map(|attr| parser_attr_to_decl_attr(arena, ctx, attr))
        .collect()
}

/// The error `Ast_payload.semantic_string_of_expression` raises on a
/// template with an invalid escape (ast_payload.ml:39-51).
pub(crate) fn invalid_string_escape(
    error: crate::ast_payload::PayloadError,
) -> crate::types::typecore::TypeCoreError {
    crate::types::typecore::TypeCoreError::InvalidStringEscapeSequence { loc: error.loc }
}

fn parser_warning_attribute_payload<'a>(
    arena: &'a ParseArena,
    payload: &'a ParsedPayload,
) -> Result<Option<(String, LocIdx)>, crate::types::typecore::TypeCoreError> {
    let ParsedPayload::PStr(items) = payload else {
        return Ok(None);
    };
    let [item] = items.as_slice() else {
        return Ok(None);
    };
    let ParsedStructureItemDesc::Pstr_eval(eval_box) = &item.pstr_desc else {
        return Ok(None);
    };
    let (expr_idx, _attrs) = eval_box.as_ref();
    // builtin_attributes.ml `string_of_payload`: the payload's semantic
    // string, raising on an invalid template. `@ppwarning` is reported at
    // the payload item's `pstr_loc`.
    let spec = crate::ast_payload::semantic_string_of_expression(arena, arena.get_expanded_expr(*expr_idx))
        .map_err(invalid_string_escape)?;
    Ok(spec.map(|spec| (spec, item.pstr_loc)))
}

fn apply_warning_attribute(
    tctx: &mut TypeCheckContext<'_>,
    arena: &ParseArena,
    attr: &ParsedAttribute,
) -> Result<(), crate::types::typecore::TypeCoreError> {
    apply_warning_attribute_with_ppwarning(tctx, arena, attr, true)
}

/// `Builtin_attributes.warning_attribute` (builtin_attributes.ml:141-160),
/// raising where `string_of_payload` raises.
fn apply_warning_attribute_with_ppwarning(
    tctx: &mut TypeCheckContext<'_>,
    arena: &ParseArena,
    attr: &ParsedAttribute,
    ppwarning: bool,
) -> Result<(), crate::types::typecore::TypeCoreError> {
    let (name, payload) = attr;
    let attr_name = arena.get_string(name.txt);
    match attr_name {
        "warning" | "warnerror" => {
            let errflag = attr_name == "warnerror";
            let Some((spec, _loc)) = parser_warning_attribute_payload(arena, payload)? else {
                tctx.report_warning(
                    name.loc,
                    Warning::AttributePayload {
                        attr: attr_name.to_string(),
                        message: "A single string literal is expected".to_string(),
                    },
                );
                return Ok(());
            };

            let mut config = WarningConfig::new();
            let parsed = if errflag {
                config.parse_as_error(&spec)
            } else {
                config.parse(&spec)
            };
            if parsed.is_err() {
                tctx.report_warning(
                    name.loc,
                    Warning::AttributePayload {
                        attr: attr_name.to_string(),
                        message: "Ill-formed list of warnings".to_string(),
                    },
                );
                return Ok(());
            }

            if errflag {
                tctx.apply_warning_error_spec(&spec);
            } else {
                tctx.apply_warning_spec(&spec);
            }
        }
        "ppwarning" if ppwarning => {
            if let Some((message, loc)) = parser_warning_attribute_payload(arena, payload)? {
                tctx.report_warning(
                    loc,
                    Warning::Preprocessor {
                        message: message.to_string(),
                    },
                );
            }
        }
        _ => {}
    }
    Ok(())
}

pub(crate) fn with_warning_scope<'a, T, E, F>(
    tctx: &mut TypeCheckContext<'a>,
    arena: &ParseArena,
    attrs: &Attributes,
    ppwarning: bool,
    f: F,
) -> Result<T, E>
where
    E: From<crate::types::typecore::TypeCoreError>,
    F: FnOnce(&mut TypeCheckContext<'a>) -> Result<T, E>,
{
    if attrs.is_empty() {
        return f(tctx);
    }

    tctx.drain_open_slot_uses();
    let previous_config = tctx.warning_config.clone();
    // OCaml compiler/ml/builtin_attributes.ml:162-171 applies warning
    // attributes in reverse order inside a saved warning state, then restores
    // the previous state after the scoped typing operation, or when an
    // attribute or the operation raises.
    for attr in attrs.iter().rev() {
        if let Err(error) = apply_warning_attribute_with_ppwarning(tctx, arena, attr, ppwarning) {
            tctx.warning_config = previous_config;
            return Err(error.into());
        }
    }
    let result = f(tctx);
    tctx.drain_open_slot_uses();
    tctx.warning_config = previous_config;
    result
}

/// The entry half of `Builtin_attributes.warning_scope`, for loops whose body
/// cannot be a closure; pair with `exit_warning_scope`.
fn enter_warning_scope(
    tctx: &mut TypeCheckContext<'_>,
    arena: &ParseArena,
    attrs: &Attributes,
) -> Result<Option<WarningConfig>, crate::types::typecore::TypeCoreError> {
    if attrs.is_empty() {
        return Ok(None);
    }
    tctx.drain_open_slot_uses();
    let previous_config = tctx.warning_config.clone();
    for attr in attrs.iter().rev() {
        if let Err(error) = apply_warning_attribute_with_ppwarning(tctx, arena, attr, true) {
            tctx.warning_config = previous_config;
            return Err(error);
        }
    }
    Ok(Some(previous_config))
}

fn exit_warning_scope(tctx: &mut TypeCheckContext<'_>, previous: Option<WarningConfig>) {
    if let Some(previous_config) = previous {
        tctx.drain_open_slot_uses();
        tctx.warning_config = previous_config;
    }
}

/// `Builtin_attributes.deprecated_of_attrs` (builtin_attributes.ml:59-62) on
/// one parser attribute: `Some (string_of_opt_payload p)` for `deprecated`,
/// raising where `string_of_payload` raises.
fn parser_deprecated_of_attr(
    arena: &ParseArena,
    attr: &ParsedAttribute,
) -> Result<Option<String>, crate::ast_payload::PayloadError> {
    let (name, payload) = attr;
    if !matches!(arena.get_string(name.txt), "deprecated") {
        return Ok(None);
    }
    // `string_of_opt_payload` (builtin_attributes.ml:21-24).
    let string = crate::ast_payload::semantic_string_of_payload(arena, payload)?;
    Ok(Some(string.unwrap_or_default()))
}

/// `Builtin_attributes.deprecated_of_str` (builtin_attributes.ml:131-136):
/// the unit's leading floating attributes decide its `Deprecated` flag
/// (typemod.ml:1825).
pub(crate) fn deprecated_of_str(
    arena: &ParseArena,
    items: &[ParsedStructureItem],
) -> Result<Option<String>, crate::ast_payload::PayloadError> {
    for item in items {
        let ParsedStructureItemDesc::Pstr_attribute(attr) = &item.pstr_desc else {
            return Ok(None);
        };
        if let Some(txt) = parser_deprecated_of_attr(arena, attr)? {
            return Ok(Some(txt));
        }
    }
    Ok(None)
}

/// `Builtin_attributes.deprecated_of_sig` (builtin_attributes.ml:124-129),
/// used for interfaces (js_implementation.ml:59).
pub(crate) fn deprecated_of_sig(
    arena: &ParseArena,
    items: &[crate::parser::ast::SignatureItem],
) -> Result<Option<String>, crate::ast_payload::PayloadError> {
    for item in items {
        let crate::parser::ast::SignatureItemDesc::Psig_attribute(attr) = &item.psig_desc else {
            return Ok(None);
        };
        if let Some(txt) = parser_deprecated_of_attr(arena, attr)? {
            return Ok(Some(txt));
        }
    }
    Ok(None)
}

fn parser_deprecated_payload_to_decl_payload(
    arena: &ParseArena,
    ctx: &crate::types::context::TypeContext,
    items: &[ParsedStructureItem],
) -> Option<crate::types::decl::AttributePayload> {
    let [item] = items else {
        return None;
    };
    let ParsedStructureItemDesc::Pstr_eval(eval_box) = &item.pstr_desc else {
        return None;
    };
    let (expr_idx, _attrs) = eval_box.as_ref();
    // builtin_attributes.ml: `Ast_payload.unwrap_payload_expression payload`.
    let expr = crate::ast_payload::unwrap_braces(arena, arena.get_expanded_expr(*expr_idx));

    // The plain `string_of_payload` form (builtin_attributes.ml
    // `string_of_payload`); `Deprecated` is kept for the record form. A
    // template that does not decode is left to the general payload, a
    // `SemanticString` keeping the location its readers raise at.
    match crate::ast_payload::semantic_string_of_expression(arena, expr) {
        Ok(Some(reason)) => return Some(crate::types::decl::AttributePayload::Str(reason)),
        Ok(None) => {}
        Err(_) => return None,
    }
    match &expr.pexp_desc {
        crate::parser::ast::ExpressionDesc::Pexp_constant(_) => None,
        crate::parser::ast::ExpressionDesc::Pexp_record(record) => {
            let fields = arena.expr_field_list(record.0);
            let mut reason = Ok(None);
            let mut can_be_automigrated = false;
            let mut migrate = None;
            let mut migrate_in_pipe_chain = None;
            // builtin_attributes.ml:82-124 `deprecated_of_attrs_with_migrate`
            // keeps the template expressions for `Cmt_utils.deprecated_used`.
            let marshal_template = |expr_idx| {
                let mut writer = crate::binary_ast::MarshalWriter::new();
                writer.set_arena(arena);
                crate::binary_ast::Marshal::marshal(arena.get_expanded_expr(expr_idx), &mut writer);
                writer.fragment()
            };
            for field in fields {
                // builtin_attributes.ml:75-96 match `Lident` field names.
                let is_field = |name| arena.is_lident(field.lid.txt, name);
                if is_field("reason") && matches!(reason, Ok(None)) {
                    // builtin_attributes.ml:72-78: the first `reason` field
                    // that is a string; reading one raises on a template
                    // with an invalid escape.
                    let field_expr = arena.get_expanded_expr(field.expr);
                    reason = crate::ast_payload::semantic_string_of_expression(arena, field_expr)
                        .map_err(|error| ctx.intern_ast_loc(arena, error.loc));
                } else if is_field("migrate") {
                    can_be_automigrated = true;
                    if migrate.is_none() {
                        migrate = Some(marshal_template(field.expr));
                    }
                } else if is_field("migrateInPipeChain") {
                    can_be_automigrated = true;
                    if migrate_in_pipe_chain.is_none() {
                        migrate_in_pipe_chain = Some(marshal_template(field.expr));
                    }
                }
            }
            Some(crate::types::decl::AttributePayload::Deprecated {
                reason,
                can_be_automigrated,
                migrate,
                migrate_in_pipe_chain,
            })
        }
        _ => None,
    }
}

fn decl_attrs_mark_immediate(attrs: &[crate::types::decl::Attribute]) -> bool {
    attrs.iter().any(|attr| attr.attr_name.txt == "immediate")
}

fn type_expr_is_immediate(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    ty: TypeExprRef,
) -> bool {
    // This is the `not (Ctype.maybe_pointer_type env ty)` predicate used by
    // `compiler/ml/typedecl.ml:1331,1335`. The relevant OCaml pointer test is
    // `compiler/ml/ctype.ml:4492-4512`.
    match &*ctx.get_desc(ctx.repr(ty)) {
        crate::types::type_expr::TypeDesc::Tconstr { path, .. } => {
            find_type_decl_for_path(env, ctx, path).is_some_and(|decl| decl.type_immediate)
        }
        crate::types::type_expr::TypeDesc::Tvariant(row) => {
            let row = crate::types::btype::row_repr(ctx, &ctx.row_desc(row));
            row.row_closed
                && !row.row_fields.iter().any(|(_, field)| {
                    matches!(
                        crate::types::btype::row_field_repr(ctx, field),
                        crate::types::type_expr::RowField::Rpresent(Some(_))
                            | crate::types::type_expr::RowField::Reither {
                                constant: false,
                                ..
                            }
                    )
                })
        }
        crate::types::type_expr::TypeDesc::Tlink(next)
        | crate::types::type_expr::TypeDesc::Tsubst(next) => {
            type_expr_is_immediate(ctx, env, *next)
        }
        _ => false,
    }
}

fn compute_type_immediacy(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    type_kind: &crate::types::TypeKind,
    type_manifest: Option<TypeExprRef>,
    type_attributes: &[crate::types::decl::Attribute],
    type_representation: crate::types::TypeRepresentation,
) -> bool {
    // OCaml `compiler/ml/typedecl.ml:1324-1336` marks all-constant
    // variants immediate, marks abstract aliases immediate when their
    // manifest is immediate, and only trusts `[@immediate]` on opaque
    // abstracts. ReScript's comparison specialization depends on this via
    // `compiler/ml/translcore.ml:407-415`.
    match (type_kind, type_manifest) {
        (crate::types::TypeKind::TypeVariant(cstrs, _), _)
            if type_representation == crate::types::TypeRepresentation::Unboxed
                && cstrs.len() == 1 =>
        {
            match &cstrs[0].cd_args {
                crate::types::decl::ConstructorArguments::CstrTuple(args) if args.len() == 1 => {
                    type_expr_is_immediate(ctx, env, args[0])
                }
                crate::types::decl::ConstructorArguments::CstrRecord(labels)
                    if labels.len() == 1 =>
                {
                    type_expr_is_immediate(ctx, env, labels[0].ld_type)
                }
                _ => {
                    !cstrs.is_empty()
                        && cstrs.iter().all(|cstr| {
                            matches!(
                                &cstr.cd_args,
                                crate::types::decl::ConstructorArguments::CstrTuple(args)
                                    if args.is_empty()
                            )
                        })
                }
            }
        }
        (crate::types::TypeKind::TypeRecord(labels, _), _)
            if type_representation == crate::types::TypeRepresentation::Unboxed =>
        {
            labels
                .first()
                .filter(|_| labels.len() == 1)
                .is_some_and(|label| type_expr_is_immediate(ctx, env, label.ld_type))
        }
        (crate::types::TypeKind::TypeVariant(cstrs, _), _) => {
            !cstrs.is_empty()
                && cstrs.iter().all(|cstr| {
                    matches!(
                        &cstr.cd_args,
                        crate::types::decl::ConstructorArguments::CstrTuple(args)
                            if args.is_empty()
                    )
                })
        }
        (crate::types::TypeKind::TypeAbstract, Some(manifest)) => {
            type_expr_is_immediate(ctx, env, manifest)
        }
        (crate::types::TypeKind::TypeAbstract, None) => decl_attrs_mark_immediate(type_attributes),
        _ => false,
    }
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
        ParsedPayload::PStr(Box::default()),
    )
}

fn arity_from_arrow_core_type(arena: &ParseArena, core_type: &crate::parser::ast::CoreType) -> i32 {
    match &core_type.ptyp_desc {
        crate::parser::ast::CoreTypeDesc::Ptyp_arrow(inner) => {
            let (_, ret, _) = inner.as_ref();
            1 + arity_from_arrow_core_type(arena, arena.get_core_type(*ret))
        }
        _ => 0,
    }
}

pub(crate) fn get_primitive_arity_from_type(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    ty: TypeExprRef,
) -> Option<i32> {
    // OCaml compiler/ml/ctype.ml:4515-4518 implements get_arity as
    // expand_head followed by a Tarrow check. Keep expansion scoped to this
    // helper so primitive typing does not force unrelated aliases eagerly.
    get_primitive_arity_from_type_depth(ctx, env, ty, 0)
}

fn get_primitive_arity_from_type_depth(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    ty: TypeExprRef,
    depth: u32,
) -> Option<i32> {
    if depth > 100 {
        return None;
    }
    let repr = ctx.repr(ty);
    match &*ctx.get_desc(repr) {
        crate::types::TypeDesc::Tarrow { args, .. } => Some(args.len() as i32),
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
fn is_type_constructor(ctx: &crate::types::context::TypeContext, ty: TypeExprRef) -> bool {
    let repr = ctx.repr(ty);
    matches!(
        &*ctx.borrow_desc(repr),
        crate::types::TypeDesc::Tconstr { .. }
    )
}

fn primitive_description_from_value_decl(
    arena: &ParseArena,
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    val_prim: &crate::parser::ast::PrimitiveRepr,
    core_type_idx: crate::parse_arena::CoreTypeIdx,
    val_ty: TypeExprRef,
) -> crate::types::PrimitiveDescription {
    use crate::parser::ast::PrimitiveRepr;
    use crate::types::decl::PrimKind;
    // `Primitive.parse_declaration` (primitive.ml:55-70).
    let (prim_name, prim_kind) = match val_prim {
        PrimitiveRepr::PrimName(name) => {
            (arena.get_string(*name).to_string(), PrimKind::KindIntrinsic)
        }
        PrimitiveRepr::PrimFfi { name, spec } => {
            (name.clone(), PrimKind::KindExternal(std::sync::Arc::new((**spec).clone())))
        }
        PrimitiveRepr::PrimInlineConst(c) => (String::new(), PrimKind::KindInlineConst(c.clone())),
    };
    let arity_from_type = get_primitive_arity_from_type(ctx, env, val_ty);
    // OCaml: from_constructor = true when get_arity returns Some AND type is Tconstr
    let prim_from_constructor = arity_from_type.is_some() && is_type_constructor(ctx, val_ty);
    let prim_arity = arity_from_type
        .unwrap_or_else(|| arity_from_arrow_core_type(arena, arena.get_core_type(core_type_idx)));

    crate::types::PrimitiveDescription {
        prim_name,
        prim_arity,
        prim_kind,
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
    match &mod_expr.pmod_desc {
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
fn path_of_typed_module_expr(ta: &TypedArena, mod_expr: &ModuleExpr) -> Option<Path> {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(path, _) => Some(*path),
        ModuleExprDesc::Tmod_apply(functor, arg, _) => {
            let functor_path = path_of_typed_module_expr(ta, ta.module_expr(*functor))?;
            let arg_path = path_of_typed_module_expr(ta, ta.module_expr(*arg))?;
            Some(Path::papply(functor_path, arg_path))
        }
        ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
            path_of_typed_module_expr(ta, ta.module_expr(*inner))
        }
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
        match &mod_expr.pmod_desc {
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
    if let ParsedModuleExprDesc::Pmod_structure(items) = &arg_expr.pmod_desc {
        for item in items.iter() {
            if let ParsedStructureItemDesc::Pstr_module(mb) = &item.pstr_desc {
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
    ctx: &crate::types::context::TypeContext,
    labels: &[crate::types::LabelDeclaration],
) -> Vec<TypeExprRef> {
    // datarepr.ml:73-75: `free_vars ~param:true` of the fields' types, not
    // the parent declaration's parameters: a GADT constructor's fields
    // mention its own variables, existentials included.
    let field_types: Vec<TypeExprRef> = labels.iter().map(|label| label.ld_type).collect();
    crate::types::env::free_vars_param(ctx, &field_types)
}

/// The most recently interned arena location equal to `target`.
///
/// Searches from the end, unlike `make_typed_spread_label`'s first-match
/// lookup; the two are kept separate because the chosen `LocIdx` decides
/// location sharing in serialized output.
fn find_existing_loc_idx(arena: &ParseArena, target: &Location) -> Option<LocIdx> {
    for idx in (0..arena.locations().len()).rev() {
        let loc_idx = LocIdx(idx as u32);
        if arena.to_location(loc_idx) == *target {
            return Some(loc_idx);
        }
    }
    None
}

fn include_module_alias_heads(
    ta: &TypedArena,
    mod_expr: &ModuleExpr,
    pers_env: Option<&crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Vec<String> {
    let Some(root_path) = include_module_root_path(ta, mod_expr) else {
        return Vec::new();
    };
    // OCaml's include path localization follows the component paths produced by
    // env.ml:1454-1481 `prefix_idents` and then freshened by
    // subst.ml:327-364 `Subst.signature`; flattened ReScript heads are valid
    // here only when the component table has registered them as aliases.
    let mut heads = pers_env
        .map(|pers| pers.flattened_alias_heads_for_path(&root_path))
        .unwrap_or_default();
    for alias_source in ctx.alias_sources_for_component_path(&root_path) {
        let PathView::Pident(id) = alias_source.view() else {
            continue;
        };
        if !(id.is_persistent() || id.stamp() == 0) {
            continue;
        }
        if !heads.iter().any(|existing| existing == id.name()) {
            heads.push(id.name().to_string());
        }
    }
    heads
}

fn include_module_root_path(ta: &TypedArena, mod_expr: &ModuleExpr) -> Option<Path> {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(path, _) => Some(*path),
        ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
            include_module_root_path(ta, ta.module_expr(*inner))
        }
        _ => None,
    }
}

/// The members an `include` brings into scope, for rewriting paths that
/// reach them through the included module into local identifiers.
#[derive(Clone, Copy)]
struct IncludeLocalization<'a> {
    /// The included module's path, when the include names one.
    root_path: Option<&'a Path>,
    /// Single-identifier aliases of the included module.
    alias_heads: &'a [String],
    /// Included type names and their local identifiers.
    types: &'a HashMap<String, Ident>,
    /// Included module names and their local identifiers.
    modules: &'a HashMap<String, Ident>,
    /// Included module type names and their local identifiers.
    modtypes: &'a HashMap<String, Ident>,
}

fn rewrite_included_path_to_local(
    path: &Path,
    localization: &IncludeLocalization<'_>,
) -> Option<Path> {
    let IncludeLocalization {
        root_path: include_root_path,
        alias_heads: include_alias_heads,
        types: local_type_ids,
        modules: local_module_ids,
        modtypes: local_modtype_ids,
    } = *localization;
    let rewrite_direct_child = |name: &str| {
        local_type_ids
            .get(name)
            .or_else(|| local_module_ids.get(name))
            .or_else(|| local_modtype_ids.get(name))
            .map(|id| Path::pident(*id))
    };

    match path.view() {
        PathView::Pident(_) => None,
        PathView::Pdot(prefix, name, pos) => {
            if include_root_path.is_some_and(|root| prefix.same(root)) {
                if let Some(rewritten) = rewrite_direct_child(name) {
                    return Some(rewritten);
                }
            }

            if let PathView::Pident(prefix_id) = prefix.view() {
                if include_alias_heads
                    .iter()
                    .any(|flat| prefix_id.name() == flat)
                {
                    if let Some(rewritten) = rewrite_direct_child(name) {
                        return Some(rewritten);
                    }
                }
            }

            rewrite_included_path_to_local(prefix, localization)
                .map(|rewritten_prefix| Path::pdot_pos(rewritten_prefix, *name, *pos))
        }
        PathView::Papply(functor, arg) => {
            let rewritten_functor = rewrite_included_path_to_local(functor, localization);
            let rewritten_arg = rewrite_included_path_to_local(arg, localization);
            if rewritten_functor.is_none() && rewritten_arg.is_none() {
                None
            } else {
                Some(Path::papply(
                    rewritten_functor.unwrap_or(*functor),
                    rewritten_arg.unwrap_or(*arg),
                ))
            }
        }
    }
}

fn included_path_is_direct_child(
    path: &Path,
    include_root_path: Option<&Path>,
    include_alias_heads: &[String],
    child_name: &str,
) -> bool {
    match path.view() {
        PathView::Pdot(prefix, name, _) if name == child_name => {
            include_root_path.is_some_and(|root| prefix.same(root))
                || matches!(prefix.view(), crate::types::path::PathView::Pident(prefix_id)
                        if include_alias_heads.iter().any(|flat| prefix_id.name() == flat)
                )
        }
        _ => false,
    }
}

/// Which path-bearing type nodes `rewrite_type_paths_in_place` rewrites,
/// besides `Tconstr` paths (always rewritten).
#[derive(Clone, Copy)]
struct TypePathRewriteSites {
    /// Rewrite `Tpackage` paths.
    package_path: bool,
    /// Rewrite a `Tvariant` row's `row_name` path and visit its arguments
    /// (before `row_more`), as `Subst.typexp` does (compiler/ml/subst.ml:226-231).
    row_name: bool,
}

/// Rewrite type paths in place over the graph rooted at `ty_ref`.
///
/// `rewrite` returns `Some(new_path)` to replace a path. Each node is visited
/// once (tracked in `visited`); a node is rewritten before its children, and
/// children are visited in descriptor order.
fn rewrite_type_paths_in_place(
    ctx: &crate::types::context::TypeContext,
    ty_ref: TypeExprRef,
    sites: TypePathRewriteSites,
    visited: &mut HashSet<TypeExprRef>,
    rewrite: &mut impl FnMut(&Path) -> Option<Path>,
) {
    use crate::types::type_expr::{RowField, TypeDesc};

    let ty_ref = ctx.repr(ty_ref);
    if !visited.insert(ty_ref) {
        return;
    }

    let desc = ctx.get_desc(ty_ref).into_desc();
    match &desc {
        TypeDesc::Tconstr {
            path, args, abbrev, ..
        } => {
            if let Some(rewritten) = rewrite(path) {
                ctx.set_desc(
                    ty_ref,
                    TypeDesc::Tconstr {
                        path: rewritten,
                        args: *args,
                        abbrev: *abbrev,
                    },
                );
            }
            for arg in ctx.type_list(args).iter() {
                rewrite_type_paths_in_place(ctx, arg, sites, visited, rewrite);
            }
        }
        TypeDesc::Tarrow { args, ret } => {
            for arg in ctx.type_args(args).iter() {
                rewrite_type_paths_in_place(ctx, arg.typ, sites, visited, rewrite);
            }
            rewrite_type_paths_in_place(ctx, *ret, sites, visited, rewrite);
        }
        TypeDesc::Ttuple(types) => {
            for ty in ctx.type_list(types).iter() {
                rewrite_type_paths_in_place(ctx, ty, sites, visited, rewrite);
            }
        }
        TypeDesc::Tlink(ty) | TypeDesc::Tsubst(ty) => {
            rewrite_type_paths_in_place(ctx, *ty, sites, visited, rewrite);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_type_paths_in_place(ctx, *body, sites, visited, rewrite);
            for var in ctx.type_list(vars).iter() {
                rewrite_type_paths_in_place(ctx, var, sites, visited, rewrite);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_type_paths_in_place(ctx, *fields, sites, visited, rewrite);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_type_paths_in_place(ctx, *typ, sites, visited, rewrite);
            rewrite_type_paths_in_place(ctx, *rest, sites, visited, rewrite);
        }
        TypeDesc::Tvariant(row) => {
            let row = &ctx.row_desc(row);
            if sites.row_name
                && let Some((name_path, name_args)) = &row.row_name
            {
                if let Some(rewritten) = rewrite(name_path) {
                    let mut new_row = row.clone();
                    new_row.row_name = Some((rewritten, name_args.clone()));
                    ctx.set_desc(ty_ref, TypeDesc::Tvariant(ctx.new_row_desc(new_row)));
                }
                for arg in name_args {
                    rewrite_type_paths_in_place(ctx, *arg, sites, visited, rewrite);
                }
            }
            rewrite_type_paths_in_place(ctx, row.row_more, sites, visited, rewrite);
            for (_, field) in &row.row_fields {
                match field {
                    RowField::Rpresent(Some(ty)) => {
                        rewrite_type_paths_in_place(ctx, *ty, sites, visited, rewrite);
                    }
                    RowField::Reither { types, .. } => {
                        for ty in types {
                            rewrite_type_paths_in_place(ctx, *ty, sites, visited, rewrite);
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { path, args, lids } => {
            if sites.package_path
                && let Some(rewritten) = rewrite(path)
            {
                ctx.set_desc(
                    ty_ref,
                    TypeDesc::Tpackage {
                        path: rewritten,
                        lids: *lids,
                        args: *args,
                    },
                );
            }
            for arg in ctx.type_list(args).iter() {
                rewrite_type_paths_in_place(ctx, arg, sites, visited, rewrite);
            }
        }
        TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {}
    }
}

fn rewrite_included_type_paths_to_local(
    ctx: &crate::types::context::TypeContext,
    ty_ref: TypeExprRef,
    localization: &IncludeLocalization<'_>,
    visited: &mut HashSet<TypeExprRef>,
) {
    rewrite_type_paths_in_place(
        ctx,
        ty_ref,
        TypePathRewriteSites {
            package_path: false,
            row_name: true,
        },
        visited,
        &mut |path| rewrite_included_path_to_local(path, localization),
    );
}

fn rewrite_included_type_decl_paths_to_local(
    ctx: &crate::types::context::TypeContext,
    id: &Ident,
    decl: &mut crate::types::decl::TypeDeclaration,
    localization: &IncludeLocalization<'_>,
    visited: &mut HashSet<TypeExprRef>,
) {
    decl.type_path = Some(Path::pident(*id));
    for param in &decl.type_params {
        rewrite_included_type_paths_to_local(ctx, *param, localization, visited);
    }
    if let Some(manifest) = decl.type_manifest {
        // mtype.ml:28-40 `strengthen` gives the included declaration the
        // manifest `Root.t` of its own name; `Subst.signature` only renames
        // idents, so that path stays rooted at the included module.
        let manifest = ctx.repr(manifest);
        let self_strengthened_args = match &*ctx.get_desc(manifest) {
            crate::types::TypeDesc::Tconstr { path, args, .. }
                if rewrite_included_path_to_local(path, localization).is_some_and(
                    |local| matches!(local.view(), PathView::Pident(local_id) if local_id.same(id)),
                ) =>
            {
                Some(*args)
            }
            _ => None,
        };
        match self_strengthened_args {
            Some(args) => {
                visited.insert(manifest);
                for arg in ctx.type_list(args) {
                    rewrite_included_type_paths_to_local(ctx, arg, localization, visited);
                }
            }
            None => rewrite_included_type_paths_to_local(ctx, manifest, localization, visited),
        }
    }
    match &mut decl.type_kind {
        crate::types::TypeKind::TypeVariant(constructors, _) => {
            for cd in constructors {
                match &cd.cd_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for arg in args {
                            rewrite_included_type_paths_to_local(ctx, *arg, localization, visited);
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for label in labels {
                            rewrite_included_type_paths_to_local(
                                ctx,
                                label.ld_type,
                                localization,
                                visited,
                            );
                        }
                    }
                }
                if let Some(res_ty) = cd.cd_res {
                    rewrite_included_type_paths_to_local(ctx, res_ty, localization, visited);
                }
            }
        }
        crate::types::TypeKind::TypeRecord(labels, _) => {
            for label in labels {
                rewrite_included_type_paths_to_local(ctx, label.ld_type, localization, visited);
            }
        }
        crate::types::TypeKind::TypeAbstract | crate::types::TypeKind::TypeOpen => {}
    }
}

fn rewrite_included_module_type_paths_to_local(
    ctx: &crate::types::context::TypeContext,
    mty: &mut crate::types::decl::ModuleType,
    localization: &IncludeLocalization<'_>,
    visited: &mut HashSet<TypeExprRef>,
) {
    match mty {
        crate::types::decl::ModuleType::MtyIdent(path) => {
            if let Some(rewritten) = rewrite_included_path_to_local(path, localization) {
                *path = rewritten;
            }
        }
        crate::types::decl::ModuleType::MtyAlias(_, path) => {
            if let Some(rewritten) = rewrite_included_path_to_local(path, localization) {
                *path = std::sync::Arc::new(rewritten);
            }
        }
        crate::types::decl::ModuleType::MtySignature(sig) => {
            rewrite_included_signature_paths_to_local(
                ctx,
                crate::types::decl::signature_mut(sig),
                localization,
                visited,
            );
        }
        crate::types::decl::ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                rewrite_included_module_type_paths_to_local(ctx, param_type, localization, visited);
            }
            rewrite_included_module_type_paths_to_local(ctx, result, localization, visited);
        }
    }
}

fn rewrite_included_signature_paths_to_local(
    ctx: &crate::types::context::TypeContext,
    sig: &mut [crate::types::decl::SignatureItem],
    localization: &IncludeLocalization<'_>,
    visited: &mut HashSet<TypeExprRef>,
) {
    for item in sig {
        match item {
            crate::types::decl::SignatureItem::SigValue(_, desc) => {
                desc.val_path = None;
                rewrite_included_type_paths_to_local(ctx, desc.val_type, localization, visited);
            }
            crate::types::decl::SignatureItem::SigType(id, decl, _) => {
                rewrite_included_type_decl_paths_to_local(
                    ctx,
                    id,
                    std::sync::Arc::make_mut(decl),
                    localization,
                    visited,
                );
            }
            crate::types::decl::SignatureItem::SigTypext(_, ext, _) => {
                if let Some(rewritten) =
                    rewrite_included_path_to_local(&ext.ext_type_path, localization)
                {
                    ext.ext_type_path = rewritten;
                }
                for param in &ext.ext_type_params {
                    rewrite_included_type_paths_to_local(ctx, *param, localization, visited);
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for arg in args {
                            rewrite_included_type_paths_to_local(ctx, *arg, localization, visited);
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for label in labels {
                            rewrite_included_type_paths_to_local(
                                ctx,
                                label.ld_type,
                                localization,
                                visited,
                            );
                        }
                    }
                }
                if let Some(ret_ty) = ext.ext_ret_type {
                    rewrite_included_type_paths_to_local(ctx, ret_ty, localization, visited);
                }
            }
            crate::types::decl::SignatureItem::SigModule(id, md, _) => {
                if md.md_path.is_none() {
                    md.md_path = Some(Path::pident(*id));
                }
                let keep_strengthened_alias_target = match &md.md_type {
                    crate::types::decl::ModuleType::MtyAlias(..)
                    | crate::types::decl::ModuleType::MtyIdent(_) => {
                        let path = md.md_type.ident_or_alias_path().unwrap();
                        // OCaml keeps the strengthened alias target from the
                        // included module path: `type_module` strengthens child
                        // modules to `Mty_alias` (compiler/ml/mtype.ml:98-102),
                        // then include only freshens bound ids with
                        // `Subst.signature` (compiler/ml/typemod.ml:1569-1590).
                        // Rewriting `Included.Child` to the fresh local `Child`
                        // would create a self-alias that cannot be expanded.
                        included_path_is_direct_child(
                            path,
                            localization.root_path,
                            localization.alias_heads,
                            id.name(),
                        )
                    }
                    _ => false,
                };
                if !keep_strengthened_alias_target {
                    rewrite_included_module_type_paths_to_local(
                        ctx,
                        &mut md.md_type,
                        localization,
                        visited,
                    );
                }
            }
            crate::types::decl::SignatureItem::SigModtype(_, mtd) => {
                if let Some(mty) = mtd.mtd_type.as_mut() {
                    rewrite_included_module_type_paths_to_local(ctx, mty, localization, visited);
                }
            }
            crate::types::decl::SignatureItem::SigClass
            | crate::types::decl::SignatureItem::SigClassType => {}
        }
    }
}

fn module_type_is_self_alias(mty: &crate::types::decl::ModuleType, id: &Ident) -> bool {
    matches!(
        mty.ident_or_alias_path().map(|p| p.view()),
        Some(PathView::Pident(alias_id)) if alias_id.same(id)
    )
}

fn rewrite_module_path_prefix(path: &Path, old_param: &Ident, new_prefix: &Path) -> Path {
    match path.view() {
        PathView::Pident(id) if id.same(old_param) => *new_prefix,
        PathView::Pdot(prefix, name, pos) => Path::pdot_pos(
            rewrite_module_path_prefix(prefix, old_param, new_prefix),
            *name,
            *pos,
        ),
        PathView::Papply(functor, arg) => Path::papply(
            rewrite_module_path_prefix(functor, old_param, new_prefix),
            rewrite_module_path_prefix(arg, old_param, new_prefix),
        ),
        _ => *path,
    }
}

fn rewrite_module_prefix_in_type(
    ty_ref: TypeExprRef,
    old_param: &Ident,
    new_prefix: &Path,
    ctx: &crate::types::context::TypeContext,
    visited: &mut HashSet<TypeExprRef>,
) {
    rewrite_type_paths_in_place(
        ctx,
        ty_ref,
        TypePathRewriteSites {
            package_path: true,
            row_name: false,
        },
        visited,
        &mut |path| {
            let rewritten = rewrite_module_path_prefix(path, old_param, new_prefix);
            (rewritten != *path).then_some(rewritten)
        },
    );
}

fn copy_and_rewrite_module_prefix_type(
    ty_ref: TypeExprRef,
    old_param: &Ident,
    new_prefix: &Path,
    ctx: &crate::types::context::TypeContext,
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

/// Rebuild constructor arguments with every type mapped through `f`, in
/// argument / label order.
fn map_constructor_args_types(
    args: &crate::types::decl::ConstructorArguments,
    f: &mut impl FnMut(TypeExprRef) -> TypeExprRef,
) -> crate::types::decl::ConstructorArguments {
    match args {
        crate::types::decl::ConstructorArguments::CstrTuple(args) => {
            crate::types::decl::ConstructorArguments::CstrTuple(
                args.iter().map(|ty| f(*ty)).collect(),
            )
        }
        crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
            crate::types::decl::ConstructorArguments::CstrRecord(map_label_types(labels, f))
        }
    }
}

fn map_label_types<C: FromIterator<crate::types::decl::LabelDeclaration>>(
    labels: &[crate::types::decl::LabelDeclaration],
    f: &mut impl FnMut(TypeExprRef) -> TypeExprRef,
) -> C {
    labels
        .iter()
        .map(|label| {
            let mut copied = label.clone();
            copied.ld_type = f(label.ld_type);
            copied
        })
        .collect()
}

/// Rebuild a type kind with every type mapped through `f`: record labels in
/// order, or for each constructor its arguments and then its result type.
fn map_type_kind_types(
    type_kind: &crate::types::decl::TypeKind,
    f: &mut impl FnMut(TypeExprRef) -> TypeExprRef,
) -> crate::types::decl::TypeKind {
    match type_kind {
        crate::types::decl::TypeKind::TypeAbstract => crate::types::decl::TypeKind::TypeAbstract,
        crate::types::decl::TypeKind::TypeOpen => crate::types::decl::TypeKind::TypeOpen,
        crate::types::decl::TypeKind::TypeRecord(labels, repr) => {
            crate::types::decl::TypeKind::TypeRecord(map_label_types(labels, f), repr.clone())
        }
        crate::types::decl::TypeKind::TypeVariant(constructors, layout) => {
            crate::types::decl::TypeKind::TypeVariant(
                constructors
                    .iter()
                    .map(|constructor| {
                        let mut copied = constructor.clone();
                        copied.cd_args = map_constructor_args_types(&constructor.cd_args, f);
                        copied.cd_res = constructor.cd_res.map(&mut *f);
                        copied
                    })
                    .collect(),
                *layout,
            )
        }
    }
}

fn map_type_inlined_types(
    inlined: &crate::types::decl::TypeInlinedType,
    f: &mut impl FnMut(TypeExprRef) -> TypeExprRef,
) -> crate::types::decl::TypeInlinedType {
    match inlined {
        crate::types::decl::TypeInlinedType::Record { type_name, labels } => {
            crate::types::decl::TypeInlinedType::Record {
                type_name: type_name.clone(),
                labels: map_label_types(labels, f),
            }
        }
    }
}

fn copy_and_rewrite_constructor_args(
    args: &crate::types::decl::ConstructorArguments,
    old_param: &Ident,
    arg_path: &Path,
    ctx: &crate::types::context::TypeContext,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::ConstructorArguments {
    map_constructor_args_types(args, &mut |ty| {
        copy_and_rewrite_module_prefix_type(ty, old_param, arg_path, ctx, copy_cache)
    })
}

fn copy_and_rewrite_type_kind(
    type_kind: &crate::types::decl::TypeKind,
    old_param: &Ident,
    arg_path: &Path,
    ctx: &crate::types::context::TypeContext,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::TypeKind {
    map_type_kind_types(type_kind, &mut |ty| {
        copy_and_rewrite_module_prefix_type(ty, old_param, arg_path, ctx, copy_cache)
    })
}

fn copy_and_rewrite_type_inlined(
    inlined: &crate::types::decl::TypeInlinedType,
    old_param: &Ident,
    arg_path: &Path,
    ctx: &crate::types::context::TypeContext,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::TypeInlinedType {
    map_type_inlined_types(inlined, &mut |ty| {
        copy_and_rewrite_module_prefix_type(ty, old_param, arg_path, ctx, copy_cache)
    })
}

fn substitute_functor_param_in_signature(
    sig_items: &[crate::types::decl::SignatureItem],
    old_param: &Ident,
    arg_path: &Path,
    ctx: &crate::types::context::TypeContext,
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
                SignatureItem::SigValue(*id, copied_vd)
            }
            SignatureItem::SigType(id, decl, rec_status) => {
                let mut copied_decl = (**decl).clone();
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
                SignatureItem::SigType(*id, std::sync::Arc::new(copied_decl), *rec_status)
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
                SignatureItem::SigTypext(*id, copied_ext, *ext_status)
            }
            SignatureItem::SigModule(id, md, rec_status) => {
                let mut rewritten_md = md.clone();
                rewritten_md.md_type =
                    substitute_functor_param_in_module_type(&md.md_type, old_param, arg_path, ctx);
                rewritten_md.md_path = md
                    .md_path
                    .as_ref()
                    .map(|path| rewrite_module_path_prefix(path, old_param, arg_path));
                SignatureItem::SigModule(*id, rewritten_md, *rec_status)
            }
            SignatureItem::SigModtype(id, mtd) => {
                let mut rewritten_mtd = mtd.clone();
                rewritten_mtd.mtd_type = mtd.mtd_type.as_ref().map(|mty| {
                    substitute_functor_param_in_module_type(mty, old_param, arg_path, ctx)
                });
                SignatureItem::SigModtype(*id, rewritten_mtd)
            }
            _ => item.clone(),
        })
        .collect()
}

fn substitute_functor_param_in_module_type(
    mty: &crate::types::decl::ModuleType,
    old_param: &Ident,
    arg_path: &Path,
    ctx: &crate::types::context::TypeContext,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;

    match mty {
        DeclMty::MtySignature(sig_items) => DeclMty::MtySignature(std::sync::Arc::new(
            substitute_functor_param_in_signature(sig_items, old_param, arg_path, ctx),
        )),
        DeclMty::MtyIdent(path) => {
            DeclMty::MtyIdent(rewrite_module_path_prefix(path, old_param, arg_path))
        }
        DeclMty::MtyAlias(alias_presence, path) => DeclMty::MtyAlias(
            *alias_presence,
            // An unreplaced `Pident` target is the block itself (subst.ml:69-75).
            match &path.view() {
                PathView::Pident(id) if !id.same(old_param) => path.clone(),
                _ => std::sync::Arc::new(rewrite_module_path_prefix(path, old_param, arg_path)),
            },
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
                    param: *param,
                    param_type: rewritten_param_type,
                    result: result.clone(),
                }
            } else {
                DeclMty::MtyFunctor {
                    param: *param,
                    param_type: rewritten_param_type,
                    result: Box::new(substitute_functor_param_in_module_type(
                        result, old_param, arg_path, ctx,
                    )),
                }
            }
        }
    }
}

/// OCaml: Mtype.nondep_supertype
///
/// Eliminate dependencies on functor parameter `mid` from a module type.
/// The environment should already contain the argument module bound to `mid`.
/// Returns `None` if the dependency cannot be eliminated.
fn nondep_supertype(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    mid: &Ident,
    mty: &crate::types::decl::ModuleType,
) -> Option<crate::types::decl::ModuleType> {
    nondep_mty(ctx, env, mid, mty)
}

fn nondep_mty(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    mid: &Ident,
    mty: &crate::types::decl::ModuleType,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::ModuleType as DeclMty;

    match mty {
        DeclMty::MtyIdent(path) => {
            if path.is_free(mid) {
                // OCaml: nondep_mty env va (Env.find_modtype_expansion p env)
                // For simplicity, return None (cannot eliminate)
                None
            } else {
                Some(mty.clone())
            }
        }
        DeclMty::MtyAlias(_, path) => {
            if path.is_free(mid) {
                None
            } else {
                Some(mty.clone())
            }
        }
        DeclMty::MtySignature(sig_items) => {
            let new_items = nondep_sig(ctx, env, mid, sig_items)?;
            Some(DeclMty::MtySignature(std::sync::Arc::new(new_items)))
        }
        DeclMty::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            let new_param_type = match param_type {
                Some(pt) => Some(Box::new(nondep_mty(ctx, env, mid, pt)?)),
                None => None,
            };
            let inner_env = {
                let mut e = env.clone();
                let default_mty = param_type
                    .as_ref()
                    .map(|pt| (**pt).clone())
                    .unwrap_or_else(|| DeclMty::MtySignature(std::sync::Arc::new(vec![])));
                e.add_module(
                    *param,
                    crate::types::decl::ModuleDeclaration {
                        md_type: default_mty,
                        md_attributes: vec![],
                        md_loc: crate::types::DeclLoc::none(),
                        md_path: None,
                    },
                );
                e
            };
            let new_result = nondep_mty(ctx, &inner_env, mid, result)?;
            Some(DeclMty::MtyFunctor {
                param: *param,
                param_type: new_param_type,
                result: Box::new(new_result),
            })
        }
    }
}

fn nondep_sig(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    mid: &Ident,
    sig_items: &[crate::types::decl::SignatureItem],
) -> Option<Vec<crate::types::decl::SignatureItem>> {
    use crate::types::decl::SignatureItem;

    let mut result = Vec::new();
    for item in sig_items {
        match item {
            SignatureItem::SigValue(id, vd) => {
                let new_type = crate::types::ctype::nondep_type(ctx, env, mid, vd.val_type)?;
                let mut new_vd = vd.clone();
                new_vd.val_type = new_type;
                result.push(SignatureItem::SigValue(*id, new_vd));
            }
            SignatureItem::SigType(id, decl, rs) => {
                // OCaml: Ctype.nondep_type_decl env mid id (va = Co) d
                let new_decl =
                    crate::types::ctype::nondep_type_decl(ctx, env, mid, id, true, decl)?;
                result.push(SignatureItem::SigType(
                    *id,
                    std::sync::Arc::new(new_decl),
                    *rs,
                ));
            }
            SignatureItem::SigTypext(id, ext, es) => {
                // Simplified: try to remove dep from extension constructor
                let new_params: Option<Vec<_>> = ext
                    .ext_type_params
                    .iter()
                    .map(|ty| crate::types::ctype::nondep_type(ctx, env, mid, *ty))
                    .collect();
                let mut new_ext = ext.clone();
                new_ext.ext_type_params = new_params?;
                // TODO: handle ext_args and ext_ret_type nondep
                result.push(SignatureItem::SigTypext(*id, new_ext, *es));
            }
            SignatureItem::SigModule(id, md, rs) => {
                let new_md_type = nondep_mty(ctx, env, mid, &md.md_type)?;
                let mut new_md = md.clone();
                new_md.md_type = new_md_type;
                result.push(SignatureItem::SigModule(*id, new_md, *rs));
            }
            SignatureItem::SigModtype(id, mtd) => {
                let new_mtd_type = match &mtd.mtd_type {
                    Some(mty) => Some(nondep_mty(ctx, env, mid, mty)?),
                    None => None,
                };
                let mut new_mtd = mtd.clone();
                new_mtd.mtd_type = new_mtd_type;
                result.push(SignatureItem::SigModtype(*id, new_mtd));
            }
            _ => {
                result.push(item.clone());
            }
        }
    }
    Some(result)
}

fn rewrite_module_path_prefix_with_aliases(
    path: &Path,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
) -> Path {
    match path.view() {
        PathView::Pdot(prefix, name, pos) => {
            let rewritten_prefix =
                rewrite_module_path_prefix_with_aliases(prefix, old_param, arg_aliases);
            if let PathView::Pident(id) = rewritten_prefix.view() {
                if id.same(old_param) {
                    if let Some(alias_path) = arg_aliases.get(name.as_str()) {
                        return *alias_path;
                    }
                }
            }
            Path::pdot_pos(rewritten_prefix, *name, *pos)
        }
        PathView::Papply(functor, arg) => Path::papply(
            rewrite_module_path_prefix_with_aliases(functor, old_param, arg_aliases),
            rewrite_module_path_prefix_with_aliases(arg, old_param, arg_aliases),
        ),
        _ => *path,
    }
}

fn rewrite_module_aliases_in_type(
    ty_ref: TypeExprRef,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext,
    visited: &mut HashSet<TypeExprRef>,
) {
    rewrite_type_paths_in_place(
        ctx,
        ty_ref,
        TypePathRewriteSites {
            package_path: true,
            row_name: false,
        },
        visited,
        &mut |path| {
            let rewritten = rewrite_module_path_prefix_with_aliases(path, old_param, arg_aliases);
            (rewritten != *path).then_some(rewritten)
        },
    );
}

fn copy_and_rewrite_module_aliases_type(
    ty_ref: TypeExprRef,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext,
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
    ctx: &crate::types::context::TypeContext,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::ConstructorArguments {
    map_constructor_args_types(args, &mut |ty| {
        copy_and_rewrite_module_aliases_type(ty, old_param, arg_aliases, ctx, copy_cache)
    })
}

fn copy_and_rewrite_type_kind_with_aliases(
    kind: &crate::types::TypeKind,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::TypeKind {
    map_type_kind_types(kind, &mut |ty| {
        copy_and_rewrite_module_aliases_type(ty, old_param, arg_aliases, ctx, copy_cache)
    })
}

fn copy_and_rewrite_type_inlined_with_aliases(
    inlined: &crate::types::decl::TypeInlinedType,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::TypeInlinedType {
    map_type_inlined_types(inlined, &mut |ty| {
        copy_and_rewrite_module_aliases_type(ty, old_param, arg_aliases, ctx, copy_cache)
    })
}

fn substitute_functor_param_aliases_in_signature(
    sig_items: &[crate::types::decl::SignatureItem],
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext,
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
                SignatureItem::SigValue(*id, copied_vd)
            }
            SignatureItem::SigType(id, decl, rec_status) => {
                let mut copied_decl = (**decl).clone();
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
                SignatureItem::SigType(*id, std::sync::Arc::new(copied_decl), *rec_status)
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
                SignatureItem::SigTypext(*id, copied_ext, *ext_status)
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
                SignatureItem::SigModule(*id, rewritten_md, *rec_status)
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
                SignatureItem::SigModtype(*id, rewritten_mtd)
            }
            _ => item.clone(),
        })
        .collect()
}

fn substitute_functor_param_aliases_in_module_type(
    mty: &crate::types::decl::ModuleType,
    old_param: &Ident,
    arg_aliases: &HashMap<String, Path>,
    ctx: &crate::types::context::TypeContext,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;

    match mty {
        DeclMty::MtySignature(sig_items) => DeclMty::MtySignature(std::sync::Arc::new(
            substitute_functor_param_aliases_in_signature(sig_items, old_param, arg_aliases, ctx),
        )),
        DeclMty::MtyIdent(path) => DeclMty::MtyIdent(rewrite_module_path_prefix_with_aliases(
            path,
            old_param,
            arg_aliases,
        )),
        DeclMty::MtyAlias(alias_presence, path) => DeclMty::MtyAlias(
            *alias_presence,
            // Only dotted targets are rebuilt; a `Pident` target is the block
            // itself.
            match &path.view() {
                PathView::Pident(_) => path.clone(),
                _ => std::sync::Arc::new(rewrite_module_path_prefix_with_aliases(
                    path,
                    old_param,
                    arg_aliases,
                )),
            },
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
                    param: *param,
                    param_type: rewritten_param_type,
                    result: result.clone(),
                }
            } else {
                DeclMty::MtyFunctor {
                    param: *param,
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

fn unwrap_poly_type(ctx: &crate::types::context::TypeContext, ty: TypeExprRef) -> TypeExprRef {
    let repr = ctx.repr(ty);
    match &*ctx.get_desc(repr) {
        crate::types::TypeDesc::Tpoly { body, .. } => ctx.repr(*body),
        _ => repr,
    }
}

pub(crate) fn find_type_decl_for_path(
    env: &Env,
    ctx: &crate::types::context::TypeContext,
    path: &Path,
) -> Option<crate::types::TypeDeclaration> {
    // `Env.lookup_type` on qualified paths currently falls back to leaf-name
    // lookup, which can select an unrelated declaration with the same type
    // name. Keep direct env lookup for simple identifiers only.
    if let PathView::Pident(_) = path.view() {
        if let Ok(type_decl) = env.lookup_type(path) {
            return Some((*type_decl).clone());
        }
    }
    if let Some(type_decl) = crate::types::ctype::resolve_type_through_modules(ctx, path) {
        return Some(type_decl);
    }

    // Try resolving through module aliases visible in the local env.
    if let PathView::Pdot(parent, type_name, _) = path.view() {
        if let PathView::Pident(parent_id) = parent.view() {
            if let Ok(module_desc) = env
                .lookup_module(parent)
                .or_else(|_| env.find_module(parent_id.name_atom()))
            {
                use crate::types::decl::ModuleType;
                use crate::types::decl::SignatureItem;
                match &module_desc.md_type {
                    ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) => {
                        let alias_path = module_desc.md_type.ident_or_alias_path().unwrap();
                        let resolved_path = Path::pdot(*alias_path, type_name.as_str());
                        if let Some(type_decl) =
                            crate::types::ctype::resolve_type_through_modules(ctx, &resolved_path)
                        {
                            return Some(type_decl);
                        }
                    }
                    ModuleType::MtySignature(sig_items) => {
                        for item in sig_items.iter() {
                            if let SignatureItem::SigType(id, decl, _) = item {
                                if id.name() == type_name.as_str() {
                                    return Some((**decl).clone());
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    None
}

fn extract_concrete_type_decl_for_record_spread(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    ty: TypeExprRef,
) -> Option<(Path, Vec<TypeExprRef>, crate::types::TypeDeclaration)> {
    let mut current = unwrap_poly_type(ctx, ty);
    let mut seen = HashSet::new();

    loop {
        let current_repr = ctx.repr(current);
        let (path, args) = match &*ctx.get_desc(current_repr) {
            crate::types::TypeDesc::Tconstr { path, args, .. } => (*path, *args),
            _ => return None,
        };

        let decl = find_type_decl_for_path(env, ctx, &path)?;
        if !matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract) {
            return Some((path, ctx.type_list(args).to_vec(), decl));
        }

        if !seen.insert(path.name()) {
            return None;
        }

        // OCaml compiler/ml/record_type_spread.ml:121-125 delegates spreads to
        // Ctype.extract_concrete_typedecl, whose ctype.ml:1449-1460 first calls
        // Env.find_type and only expands when that declaration is abstract.
        // Avoid expanding concrete records up front, because expand_head's
        // normalize_path fallback forces persistent signatures earlier than OCaml.
        current = crate::types::ctype::expand_head_once(ctx, env, current_repr)?;
        current = unwrap_poly_type(ctx, current);
    }
}

fn expand_record_spread_label(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    label: &crate::types::LabelDeclaration,
    visited: &mut HashSet<String>,
) -> Option<Vec<crate::types::LabelDeclaration>> {
    fn with_original_level(
        ctx: &crate::types::context::TypeContext,
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
        ctx: &crate::types::context::TypeContext,
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
                let new_args: Vec<_> = ctx
                    .type_list(inner_args)
                    .iter()
                    .map(|arg| {
                        let new_arg = substitute_type_params(ctx, arg, params, args, cache);
                        if new_arg != arg {
                            changed = true;
                        }
                        new_arg
                    })
                    .collect();
                if changed {
                    with_original_level(ctx, ty, ctx.new_constr(*path, new_args))
                } else {
                    ty
                }
            }
            crate::types::TypeDesc::Tarrow {
                args: arrow_args,
                ret,
            } => {
                // Preserve substitution order; no-op arrows need no new labels.
                let new_types = ctx
                    .type_args(arrow_args)
                    .iter()
                    .map(|arg| substitute_type_params(ctx, arg.typ, params, args, cache))
                    .collect::<Vec<_>>();
                let new_ret = substitute_type_params(ctx, *ret, params, args, cache);
                if new_types
                    .iter()
                    .zip(ctx.type_args(arrow_args).iter())
                    .all(|(a, b)| *a == b.typ)
                    && new_ret == *ret
                {
                    ty
                } else {
                    let new_args = ctx.new_type_args_from(
                        ctx.type_args(*arrow_args)
                            .iter()
                            .zip(new_types)
                            .map(|(arg, typ)| arg.with_type(typ)),
                    );
                    with_original_level(
                        ctx,
                        ty,
                        ctx.new_type(TypeDesc::Tarrow {
                            args: new_args,
                            ret: new_ret,
                        }),
                    )
                }
            }
            crate::types::TypeDesc::Ttuple(items) => {
                let mut changed = false;
                let new_items: Vec<_> = ctx
                    .type_list(items)
                    .iter()
                    .map(|item| {
                        let new_item = substitute_type_params(ctx, item, params, args, cache);
                        if new_item != item {
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
            crate::types::TypeDesc::Tobject { fields } => {
                let new_fields = substitute_type_params(ctx, *fields, params, args, cache);
                if new_fields == *fields {
                    ty
                } else {
                    with_original_level(
                        ctx,
                        ty,
                        ctx.new_type(crate::types::TypeDesc::Tobject { fields: new_fields }),
                    )
                }
            }
            crate::types::TypeDesc::Tfield {
                name,
                mutability,
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
                            name: *name,
                            mutability: ctx.mutability_ref_repr(*mutability),
                            typ: new_typ,
                            rest: new_rest,
                        }),
                    )
                }
            }
            crate::types::TypeDesc::Tvariant(row) => {
                let row = &ctx.row_desc(row);
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
                        *path,
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
                            row_fields: new_fields.into(),
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
                    let new_vars: Vec<_> = ctx
                        .type_list(vars)
                        .iter()
                        .map(|var| {
                            let new_var = substitute_type_params(ctx, var, params, args, cache);
                            if new_var != var {
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
                let new_args: Vec<_> = ctx
                    .type_list(pkg_args)
                    .iter()
                    .map(|arg| {
                        let new_arg = substitute_type_params(ctx, arg, params, args, cache);
                        if new_arg != arg {
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
                            path: *path,
                            lids: *lids,
                            args: ctx.new_type_list(&new_args),
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

    // Match OCaml record_type_spread.ml:121-125 plus ctype.ml:1449-1460:
    // unwrap top-level Tpoly([], ..), then read the declaration before
    // expanding aliases, so concrete record spreads keep OCaml's lazy order.
    let spread_ty = unwrap_poly_type(ctx, label.ld_type);
    let (spread_path, spread_args, source_decl) =
        extract_concrete_type_decl_for_record_spread(ctx, env, spread_ty)?;
    let path_name = spread_path.name();
    if !visited.insert(path_name.clone()) {
        return None;
    }
    let source_params = source_decl.type_params.clone();
    let result = if let crate::types::TypeKind::TypeRecord(inner_fields, _) = &source_decl.type_kind
    {
        let mut expanded = Vec::new();
        // Share the substitution cache across all fields so that shared type
        // nodes (e.g., the same type parameter used in multiple fields) get
        // the same substituted result, matching OCaml's node sharing.
        let mut cache = HashMap::new();
        for inner_field in inner_fields {
            let resolved_inner = expand_record_spread_label(ctx, env, inner_field, visited)?;
            for mut field in resolved_inner {
                if source_params.len() == spread_args.len() && !source_params.is_empty() {
                    field.ld_type = substitute_type_params(
                        ctx,
                        field.ld_type,
                        &source_params,
                        &spread_args,
                        &mut cache,
                    );
                }
                expanded.push(field);
            }
        }
        Some(expanded)
    } else {
        None
    };
    visited.remove(&path_name);
    result
}

fn make_typed_spread_label(
    ta: &mut TypedArena,
    arena: &ParseArena,
    ctx: &crate::types::context::TypeContext,
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
    let template_ld_type = ta.core_type(template.ld_type).clone();
    let typed_ld_type = TypedCoreType {
        ctyp_type: actual_field_type,
        ..template_ld_type
    };
    let parser_mutable = match field.ld_mutable {
        crate::types::MutableFlag::Immutable => crate::parser::ast::MutableFlag::Immutable,
        crate::types::MutableFlag::Mutable => crate::parser::ast::MutableFlag::Mutable,
    };
    // OCaml record_type_spread.mk_lbl uses the expanded source field location
    // for both ld_name.loc and ld_loc (not the spread marker location).
    // `mk_lbl` (compiler/ml/record_type_spread.ml:110-121): `ld_loc = l.ld_loc`,
    // which for a label read from a `.cmi` may lie outside this file.
    let source_loc = find_loc_idx_by_location(arena, &ctx.resolve_loc(field.ld_loc))
        .unwrap_or_else(|| {
            arena.push_typecheck_location(&ctx.resolve_loc(field.ld_loc), &|idx| {
                ctx.resolve_cmi_longident_component(idx)
            })
        });
    TypedLabelDeclaration {
        ld_id: field.ld_id,
        ld_name: Located {
            txt: field.ld_id.name().to_string(),
            loc: source_loc,
        },
        ld_runtime_name: field.ld_runtime_name.clone(),
        ld_mutable: parser_mutable,
        ld_optional: field.ld_optional,
        ld_type: ta.push_core_type(typed_ld_type),
        ld_loc: source_loc,
        ld_attributes: decl_attrs_to_parser_attrs(arena, &field.ld_attributes),
        ld_types_attributes: Some(field.ld_attributes.clone().into_boxed_slice()),
    }
}

// ============================================================================
// Module Type Checking Results
// ============================================================================

/// Result type for module type checking operations.
pub type TypeModResult<T> = Result<T, TypeModError>;

// Keep the error of every module-typing `Result` small; box cold payloads.
const _: () = assert!(std::mem::size_of::<TypeModError>() <= 120);

/// `Includecore.type_mismatch` cases used by type-extension compatibility.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeExtensionMismatch {
    /// The extension and type declaration have different arities.
    Arity,
    /// The extension variance annotations are incompatible with the type declaration.
    Variance,
}

/// Context for `Typedecl.Unbound_type_var` detail lines.
#[derive(Debug, Clone)]
pub enum UnboundTypeVarDetail {
    /// The variable appears in a type expression.
    Type {
        /// Type expression that contains the variable.
        ty: TypeExprRef,
    },
    /// The variable appears in a variant case payload.
    Case {
        /// Constructor/tag name.
        name: String,
        /// Payload type that contains the variable.
        ty: TypeExprRef,
        /// Whether this is a polymorphic-variant tag.
        polymorphic: bool,
    },
    /// The variable appears in a variant constructor's arguments.
    Constructor {
        /// Constructor name.
        name: String,
        /// The constructor's arguments.
        args: crate::types::ConstructorArguments,
    },
    /// The variable appears in a record field.
    Field {
        /// Field name.
        name: String,
        /// Field type that contains the variable.
        ty: TypeExprRef,
    },
    /// The variable appears in an object method.
    Method {
        /// Method name.
        name: String,
        /// Method type that contains the variable.
        ty: TypeExprRef,
    },
}

/// Errors that can occur during module type checking.
#[derive(Debug, Clone)]
pub enum TypeModError {
    /// Core type checking error.
    CoreError(TypeCoreError),
    /// An obligation of a derived item's plan failed
    /// (`TypeCheckContext::derived_fallback`): no diagnostic, the unit is
    /// compiled again with plans off.
    DerivedFallback,
    /// Module type not found.
    UnboundModtype {
        /// Source location to report.
        loc: LocIdx,
        /// Missing module type path.
        lid: Longident,
        /// Visible module type names for spellchecking.
        alternatives: Vec<String>,
    },
    /// Signature mismatch.
    SignatureMismatch {
        /// Source location to report.
        loc: LocIdx,
        /// Why the module is not included in its signature.
        error: Box<crate::types::includemod::IncludeModError>,
    },
    /// `Typedecl.Type_clash` (typedecl.ml:2176-2180) from `update_type`.
    TypeDeclTypeClash {
        /// Source location to report.
        loc: LocIdx,
        /// The unification trace of the clash.
        trace: Vec<(TypeExprRef, TypeExprRef)>,
    },
    /// Type declaration constraints are inconsistent.
    InconsistentConstraint {
        /// Source location to report.
        loc: LocIdx,
        /// The unification trace of the failed constraint.
        trace: Vec<(TypeExprRef, TypeExprRef)>,
    },
    /// An ordinary external declaration has no function arguments.
    NullArityExternal {
        /// Source location to report.
        loc: LocIdx,
    },
    /// Raw fatal compiler exception message.
    FatalError {
        /// The exception message.
        message: String,
    },
    /// A recursive abbreviation expansion does not satisfy its constraints.
    ConstraintFailed {
        /// Source location to report.
        loc: LocIdx,
        /// The type the expansion produced.
        actual: TypeExprRef,
        /// The constrained type it should be an instance of.
        expected: TypeExprRef,
    },
    /// A manifest type and explicit record/variant representation do not agree.
    DefinitionMismatch {
        /// Source location to report.
        loc: LocIdx,
        /// The manifest type.
        ty: TypeExprRef,
        /// `Includecore.type_declarations`'s differences, possibly none.
        errs: Vec<crate::types::includecore::TypeMismatch>,
    },
    /// The type a manifest names has no declaration in the environment
    /// (typedecl.ml `Unavailable_type_constructor`).
    UnavailableTypeConstructor {
        /// Source location to report.
        loc: LocIdx,
        /// The type's path.
        path: Path,
    },
    /// A private fixed row type has an invalid manifest.
    BadFixedType {
        /// Source location to report.
        loc: LocIdx,
        /// Why the manifest is invalid.
        reason: String,
    },
    /// A type parameter variance annotation is not satisfied by the declaration.
    BadVariance {
        /// Source location to report.
        loc: LocIdx,
        /// The 1-based position of the parameter, or a negative code for a
        /// variable that is not a parameter (`Typedecl.Bad_variance`).
        param_index: i32,
        /// The variance the definition gives the parameter: (covariant,
        /// contravariant, injective).
        actual: (bool, bool, bool),
        /// The variance its annotation requires.
        expected: (bool, bool, bool),
    },
    /// A GADT result type constrains a parameter whose variance cannot be checked.
    VaryingAnonymous {
        /// Source location to report.
        loc: LocIdx,
    },
    /// Invalid untagged variant definition.
    InvalidUntaggedVariantDefinition {
        /// Source location to report.
        loc: Location,
        /// Why the definition is invalid.
        reason: String,
    },
    /// A variant type spread could not resolve its source type.
    VariantSpreadCouldNotFindType {
        /// Source location to report.
        loc: LocIdx,
    },
    /// A variant type spread source is not a concrete variant.
    VariantSpreadInvalidType {
        /// Source location to report.
        loc: LocIdx,
    },
    /// Type parameters are not supported in variant type spreads.
    VariantSpreadHasTypeParams {
        /// Source location to report.
        loc: LocIdx,
    },
    /// Variant type spread would duplicate a constructor already present in the target.
    VariantSpreadDuplicateConstructor {
        /// Source location to report.
        loc: LocIdx,
        /// The spread variant.
        variant_name: String,
        /// The constructor both variants define.
        constructor_name: String,
    },
    /// Variant type spread source and target have different unboxed configuration.
    VariantSpreadUnboxedMismatch {
        /// Source location to report.
        loc: LocIdx,
        /// Whether the spread variant is `@unboxed`.
        source_unboxed: bool,
    },
    /// Variant type spread source and target have different @tag configuration.
    VariantSpreadTagMismatch {
        /// Source location to report.
        loc: LocIdx,
    },
    /// A type declaration repeats the same type parameter.
    RepeatedParameter {
        /// Source location to report.
        loc: LocIdx,
    },
    /// Duplicate constructor in a variant type declaration.
    DuplicateConstructor {
        /// Source location to report.
        loc: LocIdx,
        /// Repeated constructor name.
        name: String,
    },
    /// Duplicate record field label in a type declaration.
    DuplicateLabel {
        /// Source location to report.
        loc: LocIdx,
        /// Repeated label name.
        label: String,
        /// Enclosing record name, when the label belongs to a named record type.
        record_name: Option<String>,
    },
    /// Duplicate structure/signature component name.
    RepeatedName {
        /// Current repeated name location.
        loc: LocIdx,
        /// Namespace class, e.g. "type" or "module".
        kind: &'static str,
        /// Repeated component name.
        name: String,
        /// Previous definition location.
        repeated_loc: LocIdx,
    },
    /// `Js_name_clash` (typemod.ml `check_js_names`): two runtime components
    /// of one module get the same JavaScript name.
    JsNameClash {
        /// The later component.
        loc: Box<Location>,
        /// The later component's kind, as printed (e.g. "value").
        kind: &'static str,
        /// The earlier component's kind, as printed.
        other_kind: &'static str,
        /// The JavaScript name both components get.
        js_name: String,
        /// The earlier component.
        other_loc: Box<Location>,
    },
    /// A record declaration mixes object-type spread syntax with record fields.
    ObjectSpreadWithRecordField {
        /// Source location to report.
        loc: LocIdx,
        /// First record field mixed with the object type spread.
        field_name: String,
    },
    /// A type abbreviation expands to itself.
    RecursiveAbbrev {
        /// Source location to report.
        loc: LocIdx,
        /// The abbreviation.
        name: String,
    },
    /// A type definition contains an abbreviation cycle.
    CycleInDef {
        /// Source location to report.
        loc: LocIdx,
        /// The type being defined.
        name: String,
        /// The abbreviation that leads back to it.
        ty: TypeExprRef,
    },
    /// A recursive type abbreviation is used with non-regular parameters.
    ParametersDiffer {
        /// Source location to report.
        loc: LocIdx,
        /// The recursive type.
        path: Path,
        /// The occurrence with different arguments.
        actual: TypeExprRef,
        /// The occurrence with the declared parameters.
        expected: TypeExprRef,
    },
    /// Invalid type declaration attribute usage.
    InvalidAttribute {
        /// Source location to report.
        loc: LocIdx,
        /// What is wrong with the attribute.
        message: String,
    },
    /// `Ast_payload.semantic_string_of_expression` on a template with an
    /// invalid escape: `Location.raise_errorf ~loc:pexp_loc "Invalid string
    /// escape sequence"` (compiler/ml/ast_payload.ml:39-51).
    InvalidStringEscape {
        /// The template's location.
        loc: Location,
    },
    /// `@unboxed` was used on a declaration shape that cannot be unboxed.
    BadUnboxedAttribute {
        /// Source location to report.
        loc: LocIdx,
        /// Why the declaration cannot be unboxed.
        message: String,
    },
    /// `@immediate` was used on a type that can contain pointer values.
    BadImmediateAttribute {
        /// Source location to report.
        loc: LocIdx,
    },
    /// A declaration constructor extends a private extensible type.
    CannotExtendPrivateType {
        /// Constructor declaration location.
        loc: LocIdx,
        /// Extended type path.
        path: Path,
    },
    /// A type extension targeted a type that is not extensible.
    NotExtensibleType {
        /// Type extension location.
        loc: LocIdx,
        /// Extended type path.
        path: Path,
    },
    /// A type extension does not match the extensible type declaration.
    ExtensionMismatch {
        /// Type extension location.
        loc: LocIdx,
        /// Extended type path.
        path: Path,
        /// Specific mismatch reported by `Includecore`.
        mismatch: TypeExtensionMismatch,
    },
    /// A rebound constructor has a result type incompatible with the extension.
    RebindWrongType {
        /// Rebound constructor path location.
        loc: LocIdx,
        /// Rebound constructor longident.
        lid: Longident,
        /// The failed unification's trace and env
        /// (`Rebind_wrong_type (lid, env, trace)`, typedecl.ml:1713-1715).
        trace: Vec<(TypeExprRef, TypeExprRef)>,
        /// The environment the unification ran in.
        env: EnvRef,
    },
    /// A private constructor was rebound as public.
    RebindPrivate {
        /// Rebound constructor path location.
        loc: LocIdx,
        /// Rebound constructor longident.
        lid: Longident,
    },
    /// A type declaration contains an unbound type variable.
    UnboundTypeVar {
        /// Unbound variable location.
        loc: LocIdx,
        /// Unbound variable name as printed by OCaml, including the leading quote.
        name: String,
        /// Extra detail matching `Typedecl.explain_unbound`.
        detail: Option<UnboundTypeVarDetail>,
        /// The unbound variable itself, printed by `explain_unbound`.
        var: Option<TypeExprRef>,
    },
    /// `Typedecl.Unbound_type_var_ext`: `Ctype.closed_extension_constructor`
    /// found the free variable `var` in the constructor arguments `args`.
    UnboundTypeVarInExtension {
        /// Extension constructor location.
        loc: LocIdx,
        /// The free type variable.
        var: TypeExprRef,
        /// The constructor arguments it occurs in.
        args: crate::types::ConstructorArguments,
    },
    /// An extension constructor contains an unbound type variable.
    UnboundTypeVarExt {
        /// Extension constructor location.
        loc: LocIdx,
        /// Unbound variable name as printed by OCaml, including the leading quote.
        name: String,
    },
    /// Invalid `@as` / `@tag` attributes on variant constructors or inline records.
    AstUntaggedVariantError {
        /// Source location to report.
        loc: Location,
        /// Specific attribute validation error.
        error: AstUntaggedVariantError,
    },
    /// OCaml Typedecl.Nonrec_gadt.
    NonrecursiveGadt {
        /// Constructor declaration location.
        loc: LocIdx,
    },
    /// An exported value has a weak type variable in its inferred scheme.
    NonGeneralizable {
        /// Value declaration location.
        loc: Location,
        /// Non-closed value type.
        typ: TypeExprRef,
    },
    /// An exported module has a weak type variable in its inferred module type.
    NonGeneralizableModule {
        /// Module declaration location.
        loc: Location,
        /// Non-closed module type.
        mty: crate::types::decl::ModuleType,
    },
    /// A module unpack payload is not a packaged module expression.
    NotAPackedModule {
        /// Module expression location to report.
        loc: LocIdx,
        /// Type of the unpack payload.
        ty: TypeExprRef,
    },
    /// A module expression was applied but its module type is not a functor.
    CannotApply {
        /// Functor expression location to report.
        loc: LocIdx,
        /// Actual module type.
        mty: crate::types::decl::ModuleType,
        /// The persistent unit `mty` was loaded from, if any. Rust stores
        /// persistent signatures with paths qualified by their unit; OCaml's
        /// `Env.find_module` returns the raw `ps_sig`, whose own items are
        /// local identifiers (env.ml:865-875).
        origin: Option<Path>,
    },
    /// A normalized internal module path points at a missing compiled interface.
    MissingModule {
        /// Source location to report.
        loc: LocIdx,
        /// Original internal path.
        path: Path,
        /// Normalized dangling path.
        expanded: Path,
    },
    /// A module type alias could not be scraped because its target is missing.
    CannotScrapeAlias {
        /// Source location to report.
        loc: LocIdx,
        /// Missing alias target path.
        path: Path,
    },
    /// A value identifier rejected by `Env.check_value_name`.
    IllegalValueName {
        /// Declaration location to report.
        loc: Location,
        /// Invalid value name.
        name: String,
    },
    /// A functor result still depends on an anonymous argument module.
    CannotEliminateDependency {
        /// Module application location to report.
        loc: LocIdx,
        /// Functor module type.
        mty: crate::types::decl::ModuleType,
    },
    /// Recursive modules require an explicit module type constraint.
    RecursiveModuleRequiresExplicitType {
        /// Module expression location to report.
        loc: LocIdx,
    },
    /// A generative functor was applied to an argument other than `()`.
    ApplyGenerative {
        /// Functor expression location to report.
        loc: LocIdx,
    },
    /// Fresh module-local types are not allowed in applicative functor bodies.
    NotAllowedInFunctorBody {
        /// Module expression location to report.
        loc: LocIdx,
    },
    /// A module unpack payload has package constraints with free type variables.
    IncompletePackedModule {
        /// Module expression location to report.
        loc: LocIdx,
        /// Type of the packed module expression.
        ty: TypeExprRef,
    },
    /// A packaged module constraint would export a local module dependency.
    ScopingPack {
        /// Packed module expression location to report.
        loc: LocIdx,
        /// Constrained type path inside the package.
        lid: Longident,
        /// Type that contains the local dependency.
        ty: TypeExprRef,
    },
    /// A module was opened where a structure signature was expected.
    StructureExpected {
        /// Module path location to report.
        loc: LocIdx,
        /// Actual module type.
        mty: crate::types::decl::ModuleType,
    },
    /// A `with` constraint targets a missing signature component.
    WithNoComponent {
        /// Whole constrained module type location.
        loc: LocIdx,
        /// Missing constrained component path.
        lid: Longident,
    },
    /// A `with` constraint replacement is not included in the original component.
    WithMismatch {
        /// Whole constrained module type location.
        loc: LocIdx,
        /// Constrained component path.
        lid: Longident,
        /// Inclusion error from checking the replacement against the original.
        error: Box<crate::types::includemod::IncludeModError>,
    },
    /// A destructive `with` constraint changes a module that is aliased in the signature.
    WithChangesModuleAlias {
        /// Whole constrained module type location.
        loc: LocIdx,
        /// Constrained component path.
        lid: Longident,
        /// Alias module identifier.
        id: Ident,
        /// Aliased module path changed by the destructive substitution.
        path: Path,
    },
    /// A destructive `with` constraint makes an applicative functor path ill typed.
    WithMakesApplicativeFunctorIllTyped {
        /// Whole constrained module type location.
        loc: LocIdx,
        /// Constrained component path.
        lid: Longident,
        /// Applicative functor path in the constrained signature.
        path: Path,
        /// Inclusion error from retyping the functor application argument.
        error: Box<crate::types::includemod::IncludeModError>,
    },
    /// A destructive type substitution would remove constrained type parameters.
    WithCannotRemoveConstrainedType {
        /// Whole constrained module type location.
        loc: LocIdx,
    },
}

impl From<TypeCoreError> for TypeModError {
    fn from(err: TypeCoreError) -> Self {
        TypeModError::CoreError(err)
    }
}

fn check_value_name_for_env(
    ctx: &crate::types::context::TypeContext,
    id: &Ident,
    desc: &crate::types::decl::ValueDescription,
) -> TypeModResult<()> {
    crate::types::env::check_value_name(id.name(), ctx.resolve_loc(desc.val_loc)).map_err(|err| {
        match err {
            crate::types::env::EnvError::IllegalValueName(loc, name) => {
                TypeModError::IllegalValueName { loc, name }
            }
            other => TypeModError::CoreError(TypeCoreError::Other(format!("{other:?}"))),
        }
    })
}

fn unify_type_declaration_constraints(
    tctx: &mut TypeCheckContext<'_>,
    constraints: &[(TypedCoreType, TypedCoreType, LocIdx)],
) -> TypeModResult<()> {
    let ctx = tctx.type_ctx;
    for (cty, cty_prime, loc) in constraints {
        crate::types::unify(
            ctx,
            &mut tctx.unify_state,
            cty.ctyp_type,
            cty_prime.ctyp_type,
        )
        .map_err(|err| match err {
            crate::types::TypeError::Unify(trace) => {
                TypeModError::InconsistentConstraint { loc: *loc, trace }
            }
            _ => TypeModError::InconsistentConstraint {
                loc: *loc,
                trace: vec![(cty.ctyp_type, cty_prime.ctyp_type)],
            },
        })?;
    }
    Ok(())
}

fn unify_with_constraint_original_params(
    tctx: &mut TypeCheckContext<'_>,
    loc: LocIdx,
    params: &[TypeExprRef],
    original_decl: &crate::types::decl::TypeDeclaration,
) -> TypeModResult<()> {
    if params.len() != original_decl.type_arity as usize {
        return Ok(());
    }

    // OCaml compiler/ml/typedecl.ml:1938-1941 instances the constrained
    // declaration, then unifies replacement params with the original params.
    // This makes constraints on the original parameters visible in the
    // replacement declaration before destructive-substitution checks run.
    let original_params =
        crate::types::ctype::instance_list(tctx.type_ctx, &original_decl.type_params);
    for (&param, original_param) in params.iter().zip(original_params) {
        crate::types::unify_var(tctx.type_ctx, &mut tctx.unify_state, param, original_param)
            .map_err(|err| match err {
                crate::types::TypeError::Unify(trace) => {
                    TypeModError::InconsistentConstraint { loc, trace }
                }
                _ => TypeModError::InconsistentConstraint {
                    loc,
                    trace: vec![(param, original_param)],
                },
            })?;
    }

    Ok(())
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

fn parser_variance_requirement(variance: ParserVariance) -> (bool, bool, bool) {
    let (co, cn, inj) = match variance {
        ParserVariance::Covariant => (true, false, false),
        ParserVariance::Contravariant => (false, true, false),
        ParserVariance::Invariant => (false, false, false),
    };
    (co, cn, inj)
}

fn normalized_parser_variance_requirement(variance: ParserVariance) -> (bool, bool, bool) {
    let (co, cn, inj) = parser_variance_requirement(variance);
    if co || cn {
        (co, cn, inj)
    } else {
        (true, true, inj)
    }
}

fn check_type_declaration_duplicate_definitions(
    tctx: &mut TypeCheckContext<'_>,
    arena: &ParseArena,
    decls: &[crate::parser::ast::TypeDeclaration],
) {
    let mut labels: HashMap<String, String> = HashMap::default();
    let mut constructors: HashMap<String, String> = HashMap::default();

    for decl in decls {
        let type_name = arena.get_string(decl.ptype_name.txt).to_string();
        match &decl.ptype_kind {
            crate::parser::ast::TypeKind::Ptype_variant(constructors_in_decl) => {
                for constructor in constructors_in_decl {
                    let constructor_name =
                        duplicate_definition_constructor_name_after_variant_spread(
                            arena,
                            constructor,
                        );
                    if let Some(previous_type_name) = constructors.get(&constructor_name) {
                        tctx.report_warning(
                            constructor.pcd_loc,
                            Warning::DuplicateDefinitions {
                                kind: "constructor".to_string(),
                                name: constructor_name.clone(),
                                type1: previous_type_name.clone(),
                                type2: type_name.clone(),
                            },
                        );
                    } else {
                        constructors.insert(constructor_name, type_name.clone());
                    }
                }
            }
            crate::parser::ast::TypeKind::Ptype_record(labels_in_decl) => {
                for label in labels_in_decl {
                    let label_name = arena.get_string(label.pld_name.txt);
                    if let Some(previous_type_name) = labels.get(label_name) {
                        if label_name != "..." {
                            tctx.report_warning(
                                label.pld_loc,
                                Warning::DuplicateDefinitions {
                                    kind: "label".to_string(),
                                    name: label_name.to_string(),
                                    type1: previous_type_name.clone(),
                                    type2: type_name.clone(),
                                },
                            );
                        }
                    } else {
                        labels.insert(label_name.to_string(), type_name.clone());
                    }
                }
            }
            crate::parser::ast::TypeKind::Ptype_abstract
            | crate::parser::ast::TypeKind::Ptype_open => {}
        }
    }
}

fn duplicate_definition_constructor_name_after_variant_spread(
    arena: &ParseArena,
    constructor: &crate::parser::ast::ConstructorDeclaration,
) -> String {
    let constructor_name = arena.get_string(constructor.pcd_name.txt);
    if constructor_name != "..." {
        return constructor_name.to_string();
    }

    let crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) = &constructor.pcd_args else {
        return constructor_name.to_string();
    };
    let Some(spread_type_idx) = args.first() else {
        return constructor_name.to_string();
    };
    let spread_type = arena.get_core_type(*spread_type_idx);
    let crate::parser::ast::CoreTypeDesc::Ptyp_constr(inner) = &spread_type.ptyp_desc else {
        return constructor_name.to_string();
    };
    let spread_lid = arena.get_longident(inner.0.txt);
    let variant_name = spread_lid
        .flatten_idx()
        .into_iter()
        .map(|idx| arena.get_string(idx))
        .collect::<Vec<_>>()
        .join(".");

    // OCaml compiler/ml/typedecl.ml:1463 expands variant spreads before
    // typedecl.ml:1399-1414 `check_duplicates`. The spread sentinel is renamed
    // by compiler/ml/variant_type_spread.ml:55-63 to `...<flattened type path>`,
    // so duplicate-definition warning 30 must not compare raw `...` markers.
    format!("...{variant_name}")
}

fn check_type_declaration_constraint_on_gadt(
    tctx: &mut TypeCheckContext<'_>,
    decl: &crate::parser::ast::TypeDeclaration,
) {
    let Some((_, _, loc)) = decl.ptype_cstrs.first() else {
        return;
    };
    let crate::parser::ast::TypeKind::Ptype_variant(constructors) = &decl.ptype_kind else {
        return;
    };
    if constructors
        .iter()
        .any(|constructor| constructor.pcd_res.is_some())
    {
        tctx.report_warning(*loc, Warning::ConstraintOnGadt);
    }
}

fn check_nonrecursive_gadt_enter_type(
    rec_flag: RecFlag,
    decl: &crate::parser::ast::TypeDeclaration,
) -> TypeModResult<()> {
    if !matches!(rec_flag, RecFlag::Nonrecursive) {
        return Ok(());
    }
    let crate::parser::ast::TypeKind::Ptype_variant(constructors) = &decl.ptype_kind else {
        return Ok(());
    };
    for constructor in constructors {
        if constructor.pcd_res.is_some() {
            return Err(TypeModError::NonrecursiveGadt {
                loc: constructor.pcd_loc,
            });
        }
    }
    Ok(())
}

fn type_is_tvar_without_repr(ctx: &crate::types::context::TypeContext, ty: TypeExprRef) -> bool {
    matches!(*ctx.borrow_desc(ty), TypeDesc::Tvar(..))
}

fn collect_free_type_variables(
    ctx: &crate::types::context::TypeContext,
    ty: TypeExprRef,
    result: &mut HashSet<TypeExprRef>,
    visited: &mut HashSet<TypeExprRef>,
) {
    // `Ctype.free_vars_rec` (compiler/ml/ctype.ml:370-395) without an env.
    let ty = ctx.repr(ty);
    if !visited.insert(ty) {
        return;
    }
    let desc = ctx.get_desc(ty).into_desc();
    match desc {
        TypeDesc::Tvar(..) => {
            result.insert(ty);
        }
        TypeDesc::Tobject { fields, .. } => {
            collect_free_type_variables(ctx, fields, result, visited);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            collect_free_type_variables(ctx, typ, result, visited);
            collect_free_type_variables(ctx, rest, result, visited);
        }
        TypeDesc::Tvariant(row) => {
            let row = crate::types::btype::row_repr(ctx, &ctx.row_desc(row));
            let mut children = Vec::new();
            crate::types::btype::iter_row(ctx, &row, |child| children.push(child));
            for child in children {
                collect_free_type_variables(ctx, child, result, visited);
            }
            if !crate::types::btype::static_row(ctx, &row) {
                collect_free_type_variables(ctx, row.row_more, result, visited);
            }
        }
        _ => {
            let mut children = Vec::new();
            crate::types::btype::iter_type_expr(ctx, ty, |child| children.push(child));
            for child in children {
                collect_free_type_variables(ctx, child, result, visited);
            }
        }
    }
}

fn type_decl_variance_fields(
    decl: &crate::types::decl::TypeDeclaration,
) -> Vec<(bool, TypeExprRef)> {
    let mut fields = Vec::new();
    if let Some(manifest) = decl.type_manifest {
        fields.push((false, manifest));
    }

    match &decl.type_kind {
        crate::types::decl::TypeKind::TypeRecord(labels, _) => {
            fields.extend(labels.iter().map(|label| {
                (
                    label.ld_mutable == crate::types::asttypes::MutableFlag::Mutable,
                    label.ld_type,
                )
            }));
        }
        crate::types::decl::TypeKind::TypeVariant(constructors, _) => {
            for constructor in constructors {
                match &constructor.cd_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        fields.extend(args.iter().copied().map(|arg| (false, arg)));
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        fields.extend(labels.iter().map(|label| {
                            (
                                label.ld_mutable == crate::types::asttypes::MutableFlag::Mutable,
                                label.ld_type,
                            )
                        }));
                    }
                }
                if let Some(result) = constructor.cd_res {
                    fields.push((false, result));
                }
            }
        }
        crate::types::decl::TypeKind::TypeAbstract | crate::types::decl::TypeKind::TypeOpen => {}
    }

    fields
}

fn constructor_arguments_variance_fields(
    args: &crate::types::ConstructorArguments,
) -> Vec<(bool, TypeExprRef)> {
    match args {
        crate::types::ConstructorArguments::CstrTuple(args) => {
            args.iter().copied().map(|arg| (false, arg)).collect()
        }
        crate::types::ConstructorArguments::CstrRecord(labels) => labels
            .iter()
            .map(|label| {
                (
                    label.ld_mutable == crate::types::asttypes::MutableFlag::Mutable,
                    label.ld_type,
                )
            })
            .collect(),
    }
}

fn extension_required_variance(variance: TypesVariance) -> (bool, bool, bool) {
    let (co, cn) = variance.get_upper();
    (!cn, !co, false)
}

fn check_extension_constructor_variance_requirements(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    loc: LocIdx,
    type_decl: &crate::types::decl::TypeDeclaration,
    ext: &crate::types::ExtensionConstructor,
) -> TypeModResult<()> {
    let params = match ext.ext_ret_type {
        Some(ret_type) => {
            let ret_repr = ctx.repr(ret_type);
            match &*ctx.get_desc(ret_repr) {
                // `let tyl = List.map Ctype.repr tyl` (typedecl.ml:1246).
                crate::types::type_expr::TypeDesc::Tconstr { args, .. } => ctx
                    .type_list(args)
                    .iter()
                    .map(|arg| ctx.repr(arg))
                    .collect(),
                _ => ext.ext_type_params.clone(),
            }
        }
        None => ext.ext_type_params.clone(),
    };
    if params.is_empty() {
        return Ok(());
    }

    let required: Vec<_> = type_decl
        .type_variance
        .iter()
        .copied()
        .map(extension_required_variance)
        .collect();
    if ext.ext_ret_type.is_some() {
        let free_vars_by_param: Vec<HashSet<TypeExprRef>> = params
            .iter()
            .map(|param| {
                let mut free_vars = HashSet::default();
                let mut visited = HashSet::default();
                collect_free_type_variables(ctx, *param, &mut free_vars, &mut visited);
                free_vars
            })
            .collect();
        for (idx, param) in params.iter().copied().enumerate() {
            let expected = required.get(idx).copied().unwrap_or((true, true, false));
            if !expected.0 && !expected.1 {
                continue;
            }
            let constrained = if type_is_tvar_without_repr(ctx, param) {
                free_vars_by_param
                    .iter()
                    .enumerate()
                    .any(|(other_idx, free_vars)| {
                        other_idx != idx && free_vars.contains(&ctx.repr(param))
                    })
            } else {
                true
            };
            if constrained {
                return Err(TypeModError::VaryingAnonymous { loc });
            }
        }
    }

    let fields = constructor_arguments_variance_fields(&ext.ext_args);
    let variance_map = crate::types::ctype::compute_variance_map_for_fields(ctx, env, &fields);
    for (idx, param) in params.iter().copied().enumerate() {
        if !type_is_tvar_without_repr(ctx, param) {
            continue;
        }
        let actual_variance = variance_map
            .get(&ctx.repr(param))
            .copied()
            .unwrap_or_else(TypesVariance::null);
        // `compute_variance_type` treats a requirement with neither
        // polarity as unrestricted (typedecl.ml:1123-1127).
        let expected = match required.get(idx).copied().unwrap_or((true, true, false)) {
            (false, false, i) => (true, true, i),
            requirement => requirement,
        };
        let (actual_co, actual_cn) = actual_variance.get_upper();
        let actual = (actual_co, actual_cn, actual_variance.is_injective());
        if (actual_co && !expected.0) || (actual_cn && !expected.1) || (!actual.2 && expected.2) {
            return Err(TypeModError::BadVariance {
                loc,
                param_index: (idx + 1) as i32,
                actual,
                expected,
            });
        }
    }

    Ok(())
}

fn variance_from_requirement(requirement: (bool, bool, bool)) -> TypesVariance {
    let (positive, negative, _) = requirement;
    if positive {
        if negative {
            TypesVariance::full()
        } else {
            TypesVariance::covariant()
        }
    } else {
        TypesVariance::covariant().conjugate()
    }
}

fn check_type_decl_variance_propagation(
    ta: &TypedArena,
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    parsed_decl: &crate::parser::ast::TypeDeclaration,
    typed_decl: &TypedTypeDeclaration,
) -> TypeModResult<()> {
    let params: Vec<TypeExprRef> = typed_decl
        .typ_params
        .iter()
        .map(|(param, _)| ta.core_type(*param).ctyp_type)
        .collect();
    if params.is_empty() {
        return Ok(());
    }
    let mut free_variables = HashSet::default();
    let mut free_visited = HashSet::default();
    let args = ctx.new_tuple(params.clone());
    collect_free_type_variables(ctx, args, &mut free_variables, &mut free_visited);
    for param in &params {
        free_variables.remove(param);
    }
    if free_variables.is_empty() {
        return Ok(());
    }

    let required: Vec<_> = parsed_decl
        .ptype_params
        .iter()
        .map(|(_, variance)| normalized_parser_variance_requirement(*variance))
        .collect();

    let mut constrained_param_fields = Vec::new();
    for (param, requirement) in params.iter().copied().zip(required.iter().copied()) {
        if !type_is_tvar_without_repr(ctx, param) {
            constrained_param_fields.push((variance_from_requirement(requirement), param));
        }
    }

    let tvl2 =
        crate::types::ctype::compute_variance_map_with_initial(ctx, env, &constrained_param_fields);

    let fields = type_decl_variance_fields(&typed_decl.typ_type);
    let tvl = crate::types::ctype::compute_variance_map_for_fields(ctx, env, &fields);
    let mut visited = HashSet::default();

    /// What every type node of the declaration is checked against.
    struct VarianceCheck<'a> {
        ctx: &'a crate::types::context::TypeContext,
        env: &'a Env,
        loc: LocIdx,
        /// Variances the fields give each node.
        tvl: &'a HashMap<TypeExprRef, TypesVariance>,
        /// Variances of the constrained parameters.
        tvl2: &'a HashMap<TypeExprRef, TypesVariance>,
        free_variables: &'a HashSet<TypeExprRef>,
    }

    fn check_type(
        check: &VarianceCheck<'_>,
        ty: TypeExprRef,
        visited: &mut HashSet<TypeExprRef>,
    ) -> TypeModResult<()> {
        let VarianceCheck {
            ctx,
            env,
            loc,
            tvl,
            tvl2,
            free_variables,
        } = *check;
        let ty = ctx.repr(ty);
        if !visited.insert(ty) {
            return Ok(());
        }

        let v1 = tvl.get(&ty).copied().unwrap_or_else(TypesVariance::null);
        let v2 = tvl2
            .iter()
            .filter_map(|(candidate, variance)| {
                crate::types::ctype::equal_type_exprs_without_renaming(ctx, env, ty, *candidate)
                    .then_some(*variance)
            })
            .fold(TypesVariance::null(), |acc, variance| acc.union(&variance));

        let (c1, n1) = v1.get_upper();
        let (c2, n2, _, i2) = v2.get_lower();
        if (c1 && !c2) || (n1 && !n2) {
            if free_variables.contains(&ty) {
                let code = if !i2 {
                    -2
                } else if c2 || n2 {
                    -1
                } else {
                    -3
                };
                return Err(TypeModError::BadVariance {
                    loc,
                    param_index: code,
                    actual: (c1, n1, false),
                    expected: (c2, n2, false),
                });
            }

            let mut children = Vec::new();
            crate::types::btype::iter_type_expr(ctx, ty, |child| children.push(child));
            for child in children {
                check_type(check, child, visited)?;
            }
        }

        Ok(())
    }

    let check = VarianceCheck {
        ctx,
        env,
        loc: parsed_decl.ptype_loc,
        tvl: &tvl,
        tvl2: &tvl2,
        free_variables: &free_variables,
    };
    for (_, ty) in fields {
        check_type(&check, ty, &mut visited)?;
    }

    Ok(())
}

fn check_type_decl_variance_requirements(
    ta: &TypedArena,
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    parsed_decl: &crate::parser::ast::TypeDeclaration,
    typed_decl: &TypedTypeDeclaration,
    variance_row: &[TypesVariance],
) -> TypeModResult<()> {
    // compiler/ml/typedecl.ml:1244-1270 checks each explicit GADT
    // result before computing ordinary declaration variance. An annotated
    // parameter cannot be checked when its result argument is constrained
    // (non-variable, or shared with another result argument).
    if let crate::types::decl::TypeKind::TypeVariant(constructors, _) =
        &typed_decl.typ_type.type_kind
    {
        for constructor in constructors {
            let Some(result) = constructor.cd_res else {
                continue;
            };
            let result = ctx.repr(result);
            let crate::types::type_expr::TypeDesc::Tconstr { args, .. } = &*ctx.get_desc(result)
            else {
                continue;
            };
            let free_vars_by_arg: Vec<HashSet<TypeExprRef>> = ctx
                .type_list(args)
                .iter()
                .map(|arg| {
                    let mut free_vars = HashSet::default();
                    let mut visited = HashSet::default();
                    collect_free_type_variables(ctx, arg, &mut free_vars, &mut visited);
                    free_vars
                })
                .collect();
            for (idx, arg) in ctx.type_list(args).iter().enumerate() {
                let Some((_, parser_variance)) = parsed_decl.ptype_params.get(idx) else {
                    continue;
                };
                let (co, contra, _) = parser_variance_requirement(*parser_variance);
                if !co && !contra {
                    continue;
                }
                let arg = ctx.repr(arg);
                let constrained = !matches!(&*ctx.borrow_desc(arg), TypeDesc::Tvar(..))
                    || free_vars_by_arg
                        .iter()
                        .enumerate()
                        .any(|(other_idx, vars)| other_idx != idx && vars.contains(&arg));
                if constrained {
                    return Err(TypeModError::VaryingAnonymous {
                        loc: parsed_decl.ptype_loc,
                    });
                }
            }
        }
    }

    for (idx, ((typed_param, _), (_, parser_variance))) in typed_decl
        .typ_params
        .iter()
        .zip(parsed_decl.ptype_params.iter())
        .enumerate()
    {
        if !type_is_tvar_without_repr(ctx, ta.core_type(*typed_param).ctyp_type) {
            continue;
        }
        let expected = normalized_parser_variance_requirement(*parser_variance);
        let actual_variance = variance_row
            .get(idx)
            .copied()
            .unwrap_or_else(TypesVariance::null);
        let (actual_co, actual_cn) = actual_variance.get_upper();
        let actual = (actual_co, actual_cn, actual_variance.is_injective());
        if (actual_co && !expected.0) || (actual_cn && !expected.1) || (!actual.2 && expected.2) {
            return Err(TypeModError::BadVariance {
                loc: parsed_decl.ptype_loc,
                param_index: (idx + 1) as i32,
                actual,
                expected,
            });
        }
    }
    check_type_decl_variance_propagation(ta, ctx, env, parsed_decl, typed_decl)
}

fn type_kind_needs_coherence_check(kind: &crate::types::decl::TypeKind) -> bool {
    matches!(
        kind,
        crate::types::decl::TypeKind::TypeVariant(_, _)
            | crate::types::decl::TypeKind::TypeRecord(_, _)
            | crate::types::decl::TypeKind::TypeOpen
    )
}

fn type_expr_lists_equal_without_renaming(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    left: crate::types::type_expr::TypeSlice<'_>,
    right: crate::types::type_expr::TypeSlice<'_>,
) -> bool {
    left.len() == right.len()
        && left.iter().zip(right.iter()).all(|(left_ty, right_ty)| {
            crate::types::ctype::equal_type_exprs_without_renaming(ctx, env, left_ty, right_ty)
        })
}

/// `Typedecl.check_coherence env loc id decl` (typedecl.ml): a variant,
/// record or open type with a manifest must be the declaration the manifest
/// names, compared by `Includecore.type_declarations ~equality:true`. The
/// comparison's `@deprecated` warnings go to `warnings`.
fn check_type_declaration_coherence(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    loc: LocIdx,
    id: &Ident,
    decl: &crate::types::decl::TypeDeclaration,
    warnings: &mut Vec<Warning>,
) -> TypeModResult<()> {
    if !type_kind_needs_coherence_check(&decl.type_kind) {
        return Ok(());
    }

    let Some(manifest) = decl.type_manifest else {
        return Ok(());
    };

    let manifest_repr = ctx.repr(manifest);
    let manifest_desc = ctx.get_desc(manifest_repr);
    let (manifest_path, manifest_args) = match &*manifest_desc {
        TypeDesc::Tconstr { path, args, .. } => (*path, *args),
        _ => {
            return Err(TypeModError::DefinitionMismatch {
                loc,
                ty: manifest,
                errs: Vec::new(),
            });
        }
    };

    // `Env.find_type path env`, whose `Not_found` is
    // `Unavailable_type_constructor path`.
    let Some(expected_decl) =
        crate::types::ctype::lookup_type_decl_for_path(ctx, env, &manifest_path)
    else {
        return Err(TypeModError::UnavailableTypeConstructor {
            loc,
            path: manifest_path,
        });
    };

    let errs = if manifest_args.len() != decl.type_params.len() {
        vec![crate::types::includecore::TypeMismatch::Arity]
    } else if !type_expr_lists_equal_without_renaming(
        ctx,
        env,
        ctx.type_list(manifest_args),
        crate::types::type_expr::PoolSlice::from(&decl.type_params),
    ) {
        vec![crate::types::includecore::TypeMismatch::Constraint]
    } else {
        // `Includecore.type_declarations ~loc ~equality:true env (Path.last
        // path) decl' id (Subst.type_declaration (Subst.add_type id path
        // Subst.identity) decl)`.
        let substituted_decl = crate::types::includemod::substitute_type_declaration_self_path(
            ctx,
            decl,
            &Path::pident(*id),
            &manifest_path,
        );
        let result = crate::types::includemod::includecore_type_declarations(
            ctx,
            env,
            manifest_path.last(),
            &expected_decl,
            *id,
            &substituted_decl,
            true,
            warnings,
        );
        crate::types::includemod::escaped(ctx, result)?
            .expect("a type declaration comparison raises only payload errors")
    };
    if errs.is_empty() {
        Ok(())
    } else {
        Err(TypeModError::DefinitionMismatch {
            loc,
            ty: manifest,
            errs,
        })
    }
}

fn object_field_rest(ctx: &crate::types::context::TypeContext, fields: TypeExprRef) -> TypeExprRef {
    let mut current = ctx.repr(fields);
    loop {
        let desc = ctx.get_desc(current);
        let next = match &*desc {
            TypeDesc::Tfield { rest, .. } => Some(ctx.repr(*rest)),
            _ => None,
        };
        let Some(next) = next else {
            return current;
        };
        current = next;
    }
}

fn link_fixed_row_variable(
    ctx: &crate::types::context::TypeContext,
    loc: LocIdx,
    path: &Path,
    params: &[TypeExprRef],
    row_var: TypeExprRef,
) -> TypeModResult<()> {
    if !crate::types::btype::is_tvar(ctx, row_var) {
        return Err(TypeModError::BadFixedType {
            loc,
            reason: "has no row variable".to_string(),
        });
    }

    let replacement = ctx.new_constr(*path, params.to_vec());
    let replacement_desc = ctx.get_desc(replacement).into_desc();
    ctx.set_desc(row_var, replacement_desc);
    Ok(())
}

fn set_fixed_row(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    loc: LocIdx,
    path: &Path,
    params: &[TypeExprRef],
    manifest: TypeExprRef,
) -> TypeModResult<()> {
    let expanded = crate::types::ctype::expand_head(ctx, env, manifest);
    let manifest_repr = ctx.repr(expanded);
    enum FixedRowTarget {
        Variant(crate::types::type_expr::RowDesc),
        Object(TypeExprRef),
        Other,
    }
    let target = {
        let desc = ctx.get_desc(manifest_repr);
        match &*desc {
            TypeDesc::Tvariant(row) => {
                FixedRowTarget::Variant(crate::types::btype::row_repr(ctx, &ctx.row_desc(row)))
            }
            TypeDesc::Tobject { fields, .. } => FixedRowTarget::Object(*fields),
            _ => FixedRowTarget::Other,
        }
    };

    let row_var = match target {
        FixedRowTarget::Variant(mut row) => {
            let row_var = if crate::types::btype::static_row(ctx, &row) {
                ctx.new_type(TypeDesc::Tnil)
            } else {
                crate::types::btype::row_more(ctx, &row)
            };
            row.row_fixed = true;
            ctx.set_desc(manifest_repr, TypeDesc::Tvariant(ctx.new_row_desc(row)));
            row_var
        }
        FixedRowTarget::Object(fields) => object_field_rest(ctx, fields),
        FixedRowTarget::Other => {
            return Err(TypeModError::BadFixedType {
                loc,
                reason: "is not an object or variant".to_string(),
            });
        }
    };

    link_fixed_row_variable(ctx, loc, path, params, row_var)
}

fn has_decl_attr(attrs: &[crate::types::decl::Attribute], name: &str) -> bool {
    attrs.iter().any(|attr| attr.attr_name.txt == name)
}

fn parser_attrs_have_name(arena: &ParseArena, attrs: &Attributes, name: &str) -> bool {
    attrs
        .as_slice()
        .iter()
        .any(|(attr_name, _)| arena.get_string(attr_name.txt) == name)
}

/// OCaml `Builtin_attributes.has_unboxed`.
fn parser_attrs_have_unboxed(arena: &ParseArena, attrs: &Attributes) -> bool {
    parser_attrs_have_name(arena, attrs, "unboxed")
}

/// typedecl.ml `transl_declaration`: `Ast_untagged_variants.
/// check_runtime_annotation ~loc:ptype_loc ~is_abstract_or_abbreviation:
/// (ptype_kind = Ptype_abstract) ptype_attributes`.
fn check_declaration_runtime_annotation(
    arena: &ParseArena,
    decl: &crate::parser::ast::TypeDeclaration,
) -> TypeModResult<()> {
    let attrs = decl.ptype_attributes.iter().map(|(name, payload)| {
        crate::types::variant_layout::AnnotationAttribute {
            name: arena.get_string(name.txt),
            semantic: crate::ast_payload::semantic_string_of_payload(arena, payload)
                .map_err(|error| arena.to_location(error.loc)),
            loc: arena.to_location(name.loc),
        }
    });
    crate::types::variant_layout::check_runtime_annotation(
        arena.to_location(decl.ptype_loc),
        matches!(decl.ptype_kind, crate::parser::ast::TypeKind::Ptype_abstract),
        attrs,
    )
}

fn check_unboxed_type_attributes(
    arena: &ParseArena,
    decl: &crate::parser::ast::TypeDeclaration,
) -> TypeModResult<()> {
    let has_unboxed = parser_attrs_have_unboxed(arena, &decl.ptype_attributes);

    if !has_unboxed {
        return Ok(());
    }

    // typedecl.ml: an untagged variant's constructors are checked when its
    // layout is computed.

    match &decl.ptype_kind {
        crate::parser::ast::TypeKind::Ptype_abstract => Err(TypeModError::BadUnboxedAttribute {
            loc: decl.ptype_loc,
            message: "it is abstract".to_string(),
        }),
        crate::parser::ast::TypeKind::Ptype_record(labels) => match labels.as_slice() {
            [label]
                if matches!(
                    label.pld_mutable,
                    crate::parser::ast::MutableFlag::Immutable
                ) =>
            {
                Ok(())
            }
            [label] if matches!(label.pld_mutable, crate::parser::ast::MutableFlag::Mutable) => {
                Err(TypeModError::BadUnboxedAttribute {
                    loc: decl.ptype_loc,
                    message: "it is mutable".to_string(),
                })
            }
            _ => Err(TypeModError::BadUnboxedAttribute {
                loc: decl.ptype_loc,
                message: "it has more than one field".to_string(),
            }),
        },
        crate::parser::ast::TypeKind::Ptype_open => Err(TypeModError::BadUnboxedAttribute {
            loc: decl.ptype_loc,
            message: "extensible variant types cannot be unboxed".to_string(),
        }),
        crate::parser::ast::TypeKind::Ptype_variant(_) => Ok(()),
    }
}

/// The representation of a declaration with `has_unboxed` (`@unboxed`), as
/// OCaml `compiler/ml/typedecl.ml:451-461` decides it. Only a record with one
/// immutable field, or a variant whose single constructor has a non-empty
/// tuple or a one-field immutable inline record, is unboxed: `@unboxed type t =
/// C({a: string, b: int})` is an untagged variant whose value is the record
/// object. A variant spread always counts as more than one constructor, since
/// OCaml keeps the `...t` marker next to the constructors it expands to
/// (variant_type_spread.ml:66).
fn unboxed_type_representation(
    arena: &ParseArena,
    decl: &crate::parser::ast::TypeDeclaration,
    has_unboxed: bool,
) -> crate::types::TypeRepresentation {
    use crate::parser::ast::{ConstructorArguments, LabelDeclaration, MutableFlag, TypeKind};
    let one_immutable_field = |labels: &[LabelDeclaration]| {
        matches!(labels, [label] if matches!(label.pld_mutable, MutableFlag::Immutable))
    };
    let unboxable = match &decl.ptype_kind {
        TypeKind::Ptype_variant(cstrs) => match cstrs.as_slice() {
            [cstr] if arena.get_string(cstr.pcd_name.txt) != "..." => match &cstr.pcd_args {
                ConstructorArguments::Pcstr_tuple(args) => !args.is_empty(),
                ConstructorArguments::Pcstr_record(labels) => one_immutable_field(labels),
            },
            _ => false,
        },
        TypeKind::Ptype_record(labels) => one_immutable_field(labels),
        TypeKind::Ptype_abstract | TypeKind::Ptype_open => false,
    };
    if has_unboxed && unboxable {
        crate::types::TypeRepresentation::Unboxed
    } else {
        crate::types::TypeRepresentation::Boxed
    }
}

/// OCaml `Variant_type_spread.expand_variant_spreads`
/// (variant_type_spread.ml:31-117): look up and validate each `...t` spread of
/// a variant declaration. Returns, per constructor, the spread source's
/// constructors (and whether the source path is qualified).
#[allow(clippy::type_complexity)]
fn resolve_variant_spread_sources(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    arena: &ParseArena,
    decl: &crate::parser::ast::TypeDeclaration,
    cstrs: &[crate::parser::ast::ConstructorDeclaration],
) -> TypeModResult<Vec<Option<(Vec<crate::types::ConstructorDeclaration>, bool)>>> {
    let mut sources = Vec::new();
    let target_type_attributes =
        parser_attrs_to_decl_attrs(arena, tctx.type_ctx, &decl.ptype_attributes);
    let target_unboxed = has_decl_attr(&target_type_attributes, "unboxed");
    let mut all_constructor_names = HashSet::new();
    for cstr in cstrs.iter() {
        let cstr_name = arena.get_string(cstr.pcd_name.txt);
        if cstr_name != "..." {
            all_constructor_names.insert(cstr_name.to_string());
        }
    }
    for cstr in cstrs.iter() {
        let cstr_name_str = arena.get_string(cstr.pcd_name.txt);
        if cstr_name_str != "..." {
            sources.push(None);
            continue;
        }
        // Type-check the spread source type to resolve qualified paths
        let found;
        let is_pdot;
        if let crate::parser::ast::ConstructorArguments::Pcstr_tuple(ref args) = cstr.pcd_args {
            if let Some(spread_type_ct) = args.first() {
                let spread_core_type = arena.get_core_type(*spread_type_ct);
                let spread_loc = match &spread_core_type.ptyp_desc {
                    crate::parser::ast::CoreTypeDesc::Ptyp_constr(inner) => inner.0.loc,
                    _ => spread_core_type.ptyp_loc,
                };
                let mut handle_source_decl = |source_decl: &crate::types::TypeDeclaration,
                                              variant_name: String|
                 -> TypeModResult<
                    Vec<crate::types::ConstructorDeclaration>,
                > {
                    // Variant_type_spread.map_constructors (variant_type_spread.ml:44-50):
                    // an empty or non-variant declaration is InvalidType before the
                    // type-parameter check.
                    let source_cstrs = match &source_decl.type_kind {
                        crate::types::TypeKind::TypeVariant(cstrs, _) if !cstrs.is_empty() => {
                            cstrs.clone()
                        }
                        _ => {
                            return Err(TypeModError::VariantSpreadInvalidType { loc: spread_loc });
                        }
                    };
                    if !source_decl.type_params.is_empty() {
                        return Err(TypeModError::VariantSpreadHasTypeParams { loc: spread_loc });
                    }
                    let source_unboxed = has_decl_attr(&source_decl.type_attributes, "unboxed");
                    if source_unboxed != target_unboxed {
                        return Err(TypeModError::VariantSpreadUnboxedMismatch {
                            loc: spread_loc,
                            source_unboxed,
                        });
                    }
                    // Variant_coercion.variant_configuration_can_be_coerced_raises
                    // (variant_coercion.ml:237-240) reads the tag
                    // names only for a spread; the tuple is
                    // evaluated right to left (target first).
                    let target_tag_name =
                        process_variant_tag_name(tctx.type_ctx, &target_type_attributes)?;
                    let source_tag_name =
                        process_variant_tag_name(tctx.type_ctx, &source_decl.type_attributes)?;
                    if source_tag_name != target_tag_name {
                        return Err(TypeModError::VariantSpreadTagMismatch { loc: spread_loc });
                    }
                    for source_cstr in &source_cstrs {
                        let source_name = source_cstr.cd_id.name().to_string();
                        if all_constructor_names.contains(&source_name) {
                            return Err(TypeModError::VariantSpreadDuplicateConstructor {
                                loc: spread_loc,
                                variant_name,
                                constructor_name: source_name,
                            });
                        }
                    }
                    for source_cstr in &source_cstrs {
                        all_constructor_names.insert(source_cstr.cd_id.name().to_string());
                    }
                    Ok(source_cstrs.to_vec())
                };
                if let crate::parser::ast::CoreTypeDesc::Ptyp_constr(inner) =
                    &spread_core_type.ptyp_desc
                {
                    let spread_lid = tctx.resolve_lid(inner.0.txt).clone();
                    let (path, source_decl) =
                        resolve_type_constructor_path(tctx, env, &spread_lid, None);
                    if let Some(source_decl) = source_decl {
                        // variant_type_spread.ml:47-50: `bool` and `unit` would
                        // build `true`, `false` and `undefined`, but be matched
                        // and coerced as the strings of their names.
                        if matches!(
                            source_decl.type_kind,
                            crate::types::TypeKind::TypeVariant(..)
                        ) && crate::types::ctype::is_bool_or_unit(&path)
                        {
                            return Err(TypeModError::VariantSpreadInvalidType {
                                loc: spread_loc,
                            });
                        }
                        is_pdot = matches!(path.view(), PathView::Pdot(..));
                        found = Some(handle_source_decl(
                            &source_decl,
                            tctx.longident_to_string(&spread_lid),
                        )?);
                    } else {
                        return Err(TypeModError::VariantSpreadCouldNotFindType {
                            loc: spread_loc,
                        });
                    }
                } else {
                    // variant_type_spread.ml:98-100: only `Pcstr_tuple
                    // [Ptyp_constr _]` is a spread; any other `...`
                    // constructor is kept and typed as written.
                    sources.push(None);
                    continue;
                }
            } else {
                sources.push(None);
                continue;
            }
        } else {
            sources.push(None);
            continue;
        }
        sources.push(found.map(|cstrs| (cstrs, is_pdot)));
    }
    Ok(sources)
}

/// A constructor copied from a variant spread source (OCaml typedecl.ml:498-560).
struct SpreadConstructor {
    id: Ident,
    name: String,
    args: Vec<TypeExprRef>,
    inlined_labels: Option<Vec<crate::types::LabelDeclaration>>,
    internal: crate::types::ConstructorDeclaration,
    typed: TypedConstructorDeclaration,
}

/// Build the declaration of one constructor copied from a variant spread
/// source: the Types declaration reuses the source's arguments (fresh copies
/// for a qualified source, like `Subst.type_declaration`), and the typed tree
/// gets `Ttyp_any`-style placeholders carrying the real types.
fn build_spread_constructor(
    ta: &mut TypedArena,
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    cstr: &crate::parser::ast::ConstructorDeclaration,
    source_cstr: &crate::types::ConstructorDeclaration,
    is_pdot_source: bool,
    tag_attrs: &[crate::parser::ast::Attribute],
) -> SpreadConstructor {
    let sc_name = source_cstr.cd_id.name().to_string();
    let sc_id = ctx.create_ident(&sc_name);
    let spread_constructor_attr = (
        Located::mknoloc(arena.constructor_from_spread_attr_str()),
        crate::parser::ast::Payload::PStr(Box::default()),
    );
    let source_cd_loc =
        find_existing_loc_idx(arena, &ctx.resolve_loc(source_cstr.cd_loc)).unwrap_or(cstr.pcd_loc);
    // Use actual types from the source constructor (like OCaml's typedecl.ml lines 523-530)
    // ctyp_desc = Ttyp_var(None) acts as Ttyp_any placeholder, ctyp_type = real type from source
    let (sc_args, sc_internal_cd_args, sc_typed_tree_cd_args, sc_inlined_labels) =
        match &source_cstr.cd_args {
            crate::types::ConstructorArguments::CstrTuple(args) => {
                // Use the actual types from the source, not fresh vars
                // For Pdot sources (sub-module types), create fresh shallow copies
                // to match OCaml's Subst.type_declaration behavior
                let copied_args: Vec<TypeExprRef> = if is_pdot_source {
                    args.iter()
                        .map(|&texpr| {
                            ctx.new_type(ctx.get_desc(texpr).into_desc())
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
                    crate::types::ConstructorArguments::CstrTuple(copied_args.clone())
                } else {
                    source_cstr.cd_args.clone()
                };
                (
                    copied_args,
                    internal_cd_args,
                    TypedConstructorArguments::Cstr_tuple(ta.push_core_types(typed_tree_args)),
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
                        let unwrapped = unwrap_poly_type(ctx, l.ld_type);
                        normalized.ld_type = if is_pdot_source {
                            ctx.new_type(ctx.get_desc(unwrapped).into_desc())
                        } else {
                            unwrapped
                        };
                        normalized
                    })
                    .collect::<Vec<_>>();
                let typed_lbls: Vec<TypedLabelDeclaration> = normalized_lbls
                    .iter()
                    .map(|l| {
                        let label_loc = find_existing_loc_idx(arena, &ctx.resolve_loc(l.ld_loc))
                            .unwrap_or(source_cd_loc);
                        TypedLabelDeclaration {
                            ld_id: l.ld_id,
                            ld_name: crate::parse_arena::Located {
                                txt: l.ld_id.name().to_string(),
                                loc: label_loc,
                            },
                            ld_runtime_name: l.ld_runtime_name.clone(),
                            ld_mutable: match l.ld_mutable {
                                crate::types::asttypes::MutableFlag::Mutable => {
                                    crate::parser::ast::MutableFlag::Mutable
                                }
                                crate::types::asttypes::MutableFlag::Immutable => {
                                    crate::parser::ast::MutableFlag::Immutable
                                }
                            },
                            ld_optional: l.ld_optional,
                            ld_type: ta.push_core_type(TypedCoreType {
                                ctyp_desc: TypedCoreTypeDesc::Ttyp_var(None),
                                ctyp_type: l.ld_type,
                                ctyp_env: EnvRef(0),
                                ctyp_loc: label_loc,
                                ctyp_attributes: Attributes::new(),
                            }),
                            ld_loc: label_loc,
                            ld_attributes: decl_attrs_to_parser_attrs(arena, &l.ld_attributes),
                            ld_types_attributes: Some(l.ld_attributes.clone().into_boxed_slice()),
                        }
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
                    TypedConstructorArguments::Cstr_record(typed_lbls),
                    Some(normalized_lbls),
                )
            }
        };

    // Variant_type_spread.map_constructors carries the source constructor's
    // tag over as `pcd_runtime_tag`, which typedecl decodes back.
    let internal = crate::types::ConstructorDeclaration {
        cd_id: sc_id,
        cd_runtime_tag: source_cstr.cd_runtime_tag.clone(),
        cd_args: sc_internal_cd_args,
        cd_res: source_cstr.cd_res,
        cd_loc: source_cstr.cd_loc,
        cd_attributes: source_cstr.cd_attributes.clone(),
    };
    let spread_cd_res = source_cstr.cd_res.map(|ty| TypedCoreType {
        ctyp_desc: TypedCoreTypeDesc::Ttyp_var(None),
        ctyp_type: ty,
        ctyp_env: EnvRef(0),
        ctyp_loc: source_cd_loc,
        ctyp_attributes: Attributes::new(),
    });
    let typed = TypedConstructorDeclaration {
        cd_id: sc_id,
        cd_name: crate::parse_arena::Located {
            txt: sc_name.clone(),
            loc: source_cd_loc,
        },
        cd_runtime_tag: source_cstr.cd_runtime_tag.clone(),
        cd_args: sc_typed_tree_cd_args,
        cd_res: spread_cd_res.map(|ct| ta.push_core_type(ct)),
        cd_loc: source_cd_loc,
        cd_attributes: {
            let mut attrs = tag_attrs.to_vec();
            attrs.push(spread_constructor_attr.clone());
            attrs.extend(
                decl_attrs_to_parser_attrs(arena, &source_cstr.cd_attributes)
                    .iter()
                    .cloned(),
            );
            Attributes::from_vec(attrs)
        },
    };
    SpreadConstructor {
        id: sc_id,
        name: sc_name,
        args: sc_args,
        inlined_labels: sc_inlined_labels,
        internal,
        typed,
    }
}

fn check_duplicate_constructor_declarations(
    arena: &ParseArena,
    loc: LocIdx,
    constructors: &[crate::parser::ast::ConstructorDeclaration],
) -> TypeModResult<()> {
    let mut seen: HashSet<&str> = HashSet::default();
    for constructor in constructors {
        let name = arena.get_string(constructor.pcd_name.txt);
        if name == "..." {
            continue;
        }
        if !seen.insert(name) {
            return Err(TypeModError::DuplicateConstructor {
                loc,
                name: name.to_string(),
            });
        }
    }
    Ok(())
}

/// typedecl.ml `transl_declaration`: `@unboxed` applies to the whole
/// variant, so a constructor cannot have its own.
fn check_unboxed_on_constructors(
    arena: &ParseArena,
    constructors: &[crate::parser::ast::ConstructorDeclaration],
) -> TypeModResult<()> {
    for constructor in constructors {
        let Some((attr_name, _)) = constructor
            .pcd_attributes
            .iter()
            .find(|(name, _)| arena.get_string(name.txt) == "unboxed")
        else {
            continue;
        };
        return Err(ast_untagged_variant_error(
            arena.to_location(attr_name.loc),
            AstUntaggedVariantError::UnboxedOnConstructor {
                constructor: arena.get_string(constructor.pcd_name.txt).to_string(),
                single_field_record: matches!(
                    &constructor.pcd_args,
                    crate::parser::ast::ConstructorArguments::Pcstr_record(labels)
                        if labels.len() == 1
                ),
            },
        ));
    }
    Ok(())
}

/// `Record_runtime.check_duplicated_labels` (record_runtime.ml), run by
/// `Typedecl.transl_labels` (typedecl.ml:209-213). A runtime name clashes
/// with any earlier declared or runtime name.
fn check_duplicate_label_declarations(
    arena: &ParseArena,
    labels: &[crate::parser::ast::LabelDeclaration],
    record_name: Option<&str>,
) -> TypeModResult<()> {
    match crate::types::record_runtime::check_duplicated_labels(arena, labels) {
        None => Ok(()),
        Some((label, loc)) => Err(TypeModError::DuplicateLabel {
            loc,
            label,
            record_name: record_name.map(str::to_string),
        }),
    }
}

/// `Record_runtime.extra_as_attribute` raised as
/// `Ast_untagged_variants.Error (loc, Duplicated_bs_as)` (typedecl.ml
/// `transl_labels`).
fn check_extra_as_attribute(
    arena: &ParseArena,
    label: &crate::parser::ast::LabelDeclaration,
) -> TypeModResult<()> {
    match crate::types::record_runtime::extra_as_attribute(arena, label) {
        Ok(None) => Ok(()),
        Ok(Some(loc)) => Err(ast_untagged_variant_error(
            arena.to_location(loc),
            AstUntaggedVariantError::DuplicatedBsAs,
        )),
        // `Location.raise_errorf` from `Ast_payload.string_literal_of_payload`.
        Err(error) => Err(TypeModError::InvalidAttribute {
            loc: error.loc,
            message: error.message.to_string(),
        }),
    }
}

fn check_duplicate_typed_label_declarations(
    loc: LocIdx,
    labels: &[TypedLabelDeclaration],
    record_name: Option<&str>,
) -> TypeModResult<()> {
    let mut seen: HashSet<&str> = HashSet::default();
    for label in labels {
        let name = label.ld_id.name();
        if !seen.insert(name) {
            return Err(TypeModError::DuplicateLabel {
                loc,
                label: name.to_string(),
                record_name: record_name.map(str::to_string),
            });
        }
    }
    Ok(())
}

/// typemod.ml `check_js_names`: two runtime components of a module must not
/// get the same JavaScript name. The module's fields, and the exports of a
/// compilation unit, are named by `Ext_ident.convert`, which maps both
/// `delete` and `$$delete` to `$$delete` and `\"a-b"` like `a$b`. The exports
/// of a compilation unit keep `default` as written. Values are checked after
/// `simplify_signature`, so a value that is shadowed by one of the same name
/// is not a field.
pub(crate) fn check_js_names(
    ctx: &crate::types::context::TypeContext,
    toplevel: bool,
    sg: &[crate::types::decl::SignatureItem],
) -> TypeModResult<()> {
    use crate::types::decl::{SignatureItem as S, ValueKind};
    let mut seen: HashMap<String, (&'static str, crate::types::DeclLoc)> = HashMap::default();
    for item in sg {
        let (kind, id, loc) = match item {
            S::SigValue(_, desc) if matches!(desc.val_kind, ValueKind::ValPrim(_)) => continue,
            S::SigType(..) | S::SigModtype(..) | S::SigClass | S::SigClassType => continue,
            S::SigValue(id, desc) => ("value", id, desc.val_loc),
            S::SigTypext(id, ext, _) => ("extension constructor", id, ext.ext_loc),
            S::SigModule(id, md, _) => ("module", id, md.md_loc),
        };
        let name = id.name();
        let js_name = if toplevel && name == "default" {
            name.to_string()
        } else {
            crate::js_ir::printer::convert_ident_name(name)
        };
        match seen.get(&js_name) {
            Some((other_kind, other_loc)) => {
                return Err(TypeModError::JsNameClash {
                    loc: Box::new(ctx.resolve_loc(loc)),
                    kind,
                    other_kind,
                    js_name,
                    other_loc: Box::new(ctx.resolve_loc(*other_loc)),
                });
            }
            None => {
                seen.insert(js_name, (kind, loc));
            }
        }
    }
    Ok(())
}

#[derive(Default)]
struct Names {
    types: HashMap<String, LocIdx>,
    modules: HashMap<String, LocIdx>,
    modtypes: HashMap<String, LocIdx>,
    typexts: HashMap<String, LocIdx>,
}

fn check_name(
    table: &mut HashMap<String, LocIdx>,
    kind: &'static str,
    loc: LocIdx,
    name: &str,
) -> TypeModResult<()> {
    match table.entry(name.to_string()) {
        std::collections::hash_map::Entry::Occupied(entry) => Err(TypeModError::RepeatedName {
            loc,
            kind,
            name: entry.key().clone(),
            repeated_loc: *entry.get(),
        }),
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(loc);
            Ok(())
        }
    }
}

/// OCaml `check_sig_item` (compiler/ml/typemod.ml:637-642): names bound by an
/// included signature must not repeat names already in the structure/signature.
fn check_included_signature_names(
    names: &mut Names,
    loc: LocIdx,
    sig: &[crate::types::decl::SignatureItem],
) -> TypeModResult<()> {
    use crate::types::decl::SignatureItem as S;
    for item in sig {
        match item {
            S::SigType(id, _, _) => check_name(&mut names.types, "type", loc, id.name())?,
            S::SigModule(id, _, _) => check_name(&mut names.modules, "module", loc, id.name())?,
            S::SigModtype(id, _) => check_name(&mut names.modtypes, "module type", loc, id.name())?,
            S::SigTypext(id, _, _) => {
                check_name(&mut names.typexts, "extension constructor", loc, id.name())?
            }
            _ => {}
        }
    }
    Ok(())
}

fn check_structure_item_names(
    names: &mut Names,
    arena: &ParseArena,
    item: &ParsedStructureItem,
) -> TypeModResult<()> {
    match &item.pstr_desc {
        ParsedStructureItemDesc::Pstr_type(inner) => {
            let (_, decls) = &**inner;
            for decl in decls {
                check_name(
                    &mut names.types,
                    "type",
                    decl.ptype_name.loc,
                    arena.get_string(decl.ptype_name.txt),
                )?;
            }
        }
        ParsedStructureItemDesc::Pstr_typext(ext) => {
            for constructor in &ext.ptyext_constructors {
                check_name(
                    &mut names.typexts,
                    "extension constructor",
                    constructor.pext_name.loc,
                    arena.get_string(constructor.pext_name.txt),
                )?;
            }
        }
        ParsedStructureItemDesc::Pstr_exception(constructor) => {
            check_name(
                &mut names.typexts,
                "extension constructor",
                constructor.pext_name.loc,
                arena.get_string(constructor.pext_name.txt),
            )?;
        }
        ParsedStructureItemDesc::Pstr_module(mb) => {
            check_name(
                &mut names.modules,
                "module",
                mb.pmb_name.loc,
                arena.get_string(mb.pmb_name.txt),
            )?;
        }
        ParsedStructureItemDesc::Pstr_recmodule(mbs) => {
            for mb in mbs.iter() {
                check_name(
                    &mut names.modules,
                    "module",
                    mb.pmb_name.loc,
                    arena.get_string(mb.pmb_name.txt),
                )?;
            }
        }
        ParsedStructureItemDesc::Pstr_modtype(mtd) => {
            check_name(
                &mut names.modtypes,
                "module type",
                mtd.pmtd_name.loc,
                arena.get_string(mtd.pmtd_name.txt),
            )?;
        }
        _ => {}
    }
    Ok(())
}

fn check_signature_item_names(
    names: &mut Names,
    arena: &ParseArena,
    item: &crate::parser::ast::SignatureItem,
) -> TypeModResult<()> {
    use crate::parser::ast::SignatureItemDesc as PSigDesc;

    match &item.psig_desc {
        PSigDesc::Psig_type(inner) => {
            let (_, decls) = &**inner;
            for decl in decls {
                check_name(
                    &mut names.types,
                    "type",
                    decl.ptype_name.loc,
                    arena.get_string(decl.ptype_name.txt),
                )?;
            }
        }
        PSigDesc::Psig_typext(ext) => {
            for constructor in &ext.ptyext_constructors {
                check_name(
                    &mut names.typexts,
                    "extension constructor",
                    constructor.pext_name.loc,
                    arena.get_string(constructor.pext_name.txt),
                )?;
            }
        }
        PSigDesc::Psig_exception(constructor) => {
            check_name(
                &mut names.typexts,
                "extension constructor",
                constructor.pext_name.loc,
                arena.get_string(constructor.pext_name.txt),
            )?;
        }
        PSigDesc::Psig_module(md) => {
            check_name(
                &mut names.modules,
                "module",
                md.pmd_name.loc,
                arena.get_string(md.pmd_name.txt),
            )?;
        }
        PSigDesc::Psig_recmodule(mds) => {
            for md in mds.iter() {
                check_name(
                    &mut names.modules,
                    "module",
                    md.pmd_name.loc,
                    arena.get_string(md.pmd_name.txt),
                )?;
            }
        }
        PSigDesc::Psig_modtype(mtd) => {
            check_name(
                &mut names.modtypes,
                "module type",
                mtd.pmtd_name.loc,
                arena.get_string(mtd.pmtd_name.txt),
            )?;
        }
        _ => {}
    }
    Ok(())
}

fn first_non_spread_label<'a>(
    arena: &ParseArena,
    labels: &'a [crate::parser::ast::LabelDeclaration],
) -> Option<&'a crate::parser::ast::LabelDeclaration> {
    labels
        .iter()
        .find(|label| arena.get_string(label.pld_name.txt) != "...")
}

fn reject_object_spread_with_record_field(
    arena: &ParseArena,
    labels: &[crate::parser::ast::LabelDeclaration],
) -> TypeModResult<()> {
    if let Some(label) = first_non_spread_label(arena, labels) {
        let field_name = arena.get_string(label.pld_name.txt).to_string();
        Err(TypeModError::ObjectSpreadWithRecordField {
            loc: label.pld_loc,
            field_name,
        })
    } else {
        Ok(())
    }
}

/// Error raised by the ReScript variant runtime-representation checks.
#[derive(Debug, Clone)]
pub enum AstUntaggedVariantError {
    /// A variant `@as(...)` payload has an unsupported shape.
    InvalidVariantAsAnnotation,
    /// The integer of a variant case's `@as` is out of range.
    VariantAsIntegerOutOfRange(String),
    /// More than one `@as` attribute was found.
    DuplicatedBsAs,
    /// A variant `@tag(...)` payload is not a string.
    InvalidVariantTagAnnotation,
    /// An inline record field runtime name conflicts with the constructor tag.
    TagFieldNameConflict {
        /// Constructor source name.
        constructor_name: String,
        /// Inline record field source name.
        field_name: String,
        /// Runtime value shared by the constructor tag and inline field.
        runtime_value: String,
    },
    /// `@unboxed` on a constructor rather than on its type.
    UnboxedOnConstructor {
        /// Constructor source name.
        constructor: String,
        /// Whether the constructor's payload is an inline record with one field.
        single_field_record: bool,
    },
    /// An `@instanceOf` payload that is not the name of a global class.
    InvalidInstanceOf,
    /// An `@instanceOf` class, by name, that cannot be used, and why.
    UnsupportedInstanceOf(String, crate::types::variant_layout::UnsupportedClass),
    /// An `@typeOf` payload that is not a `typeof` result, if it is a string.
    InvalidTypeOf(String),
    /// More than one of `@notUndefined`, `@instanceOf` and `@typeOf` on one
    /// type.
    ConflictingRuntimeAnnotations,
    /// The same runtime annotation, by name, twice on one type.
    DuplicateRuntimeAnnotation(String),
    /// A runtime annotation, by name, on a functor parameter, a recursive
    /// module's type or a locally abstract type.
    RuntimeAnnotationOnTypeParameter(String),
    /// A runtime annotation, by name, on a type that has its own
    /// representation (neither abstract nor an abbreviation).
    RuntimeAnnotationOnRepresentedType(String),
    /// A runtime annotation, by name, on an abbreviation of a type that is
    /// neither abstract nor annotated the same way.
    RuntimeAnnotationOnUnrelatedType(String),
    /// An annotation that contradicts the one of the abbreviated type, both
    /// as printed.
    RuntimeAnnotationContradictsManifest(String, String),
    /// An `@instanceOf` class, by name, on an abbreviation of an array type.
    SubclassOfArray(String),
    /// A class, by name, declared as a public abbreviation of its
    /// superclass, by name.
    SubclassOfPublicAbbreviation(String, String),
    /// A class, by name, declared on a public abbreviation.
    ClassOnPublicAbbreviation(String),
    /// A class, by name, that appears twice in its chain of abbreviations.
    ClassTwiceInChain(String),
}

impl AstUntaggedVariantError {
    /// Return the message text used by OCaml's `Ast_untagged_variants.report_error`.
    pub fn message_text(&self) -> String {
        match self {
            AstUntaggedVariantError::InvalidVariantAsAnnotation => {
                "A variant case annotation @as(...) must be a string, integer, float, bigint, boolean, null, or undefined.".to_string()
            }
            AstUntaggedVariantError::VariantAsIntegerOutOfRange(value) => format!(
                "The integer {value} in this variant case's @as annotation is out of range."
            ),
            AstUntaggedVariantError::DuplicatedBsAs => {
                "Duplicate @as annotation; only one @as is allowed here.".to_string()
            }
            AstUntaggedVariantError::InvalidVariantTagAnnotation => {
                "A variant tag annotation @tag(...) must be a string".to_string()
            }
            AstUntaggedVariantError::TagFieldNameConflict {
                constructor_name,
                field_name,
                runtime_value,
            } => format!(
                "Constructor \"{constructor_name}\": the @tag name \"{runtime_value}\" conflicts with the runtime value of inline record field \"{field_name}\". Use a different @tag name or rename the field."
            ),
            AstUntaggedVariantError::UnboxedOnConstructor {
                constructor,
                single_field_record,
            } => {
                let mut message = format!(
                    "@unboxed applies to a whole variant: write it on the type, as in `@unboxed type t = ...`, instead of on constructor {constructor}."
                );
                if *single_field_record {
                    message.push_str(&format!(
                        " For a constructor whose payload is an inline record with one field, `@unboxed type t = {constructor}({{...}})` makes the value that field. To keep the record object, give the record type a name: `@unboxed type t = {constructor}(r)`."
                    ));
                }
                message
            }
            AstUntaggedVariantError::InvalidInstanceOf => {
                "@instanceOf expects the name of a global class, such as @instanceOf(\"Date\") or @instanceOf(\"Intl.Locale\").".to_string()
            }
            AstUntaggedVariantError::UnsupportedInstanceOf(name, reason) => {
                use crate::types::variant_layout::UnsupportedClass;
                match reason {
                    UnsupportedClass::ThroughGlobalThis => {
                        let rest = name.split('.').skip(1).collect::<Vec<_>>().join(".");
                        format!(
                            "Write @instanceOf(\"{rest}\") without \"globalThis.\": the compiler reads the class through globalThis itself where a local binding shadows it."
                        )
                    }
                    UnsupportedClass::EveryValueOf(type_of) => format!(
                        "Every {type_of} is an instance of {name}, so @instanceOf(\"{name}\") cannot tell cases apart. Use @typeOf(\"{type_of}\") instead."
                    ),
                    UnsupportedClass::WrapperOf(type_of) => format!(
                        "Values of type {type_of} are primitives, not instances of {name}. Use @typeOf(\"{type_of}\") instead."
                    ),
                    UnsupportedClass::ArrayClass => {
                        "Arrays are recognized by Array.isArray. Use array<_> as the payload type instead of @instanceOf(\"Array\").".to_string()
                    }
                    UnsupportedClass::NotAClass => {
                        format!("{name} is not a class, so it cannot be used with @instanceOf.")
                    }
                }
            }
            AstUntaggedVariantError::InvalidTypeOf(name) => format!(
                "@typeOf expects one of \"string\", \"number\", \"bigint\", \"boolean\", \"symbol\", \"function\" or \"object\"{}.",
                if name.is_empty() {
                    String::new()
                } else {
                    format!(", not \"{name}\"")
                }
            ),
            AstUntaggedVariantError::DuplicateRuntimeAnnotation(attribute) => {
                format!("Duplicate @{attribute} annotation; a type can have only one.")
            }
            AstUntaggedVariantError::RuntimeAnnotationOnTypeParameter(attribute) => format!(
                "@{attribute} cannot describe the type of a functor parameter, of a recursive module being defined, or a locally abstract type: such a type stands for another one, whose values can be anything."
            ),
            AstUntaggedVariantError::ConflictingRuntimeAnnotations => {
                "A type can have only one of @notUndefined, @instanceOf and @typeOf. @instanceOf and @typeOf already imply @notUndefined.".to_string()
            }
            AstUntaggedVariantError::RuntimeAnnotationOnRepresentedType(attribute) => format!(
                "@{attribute} can only be used on abstract types and type abbreviations, whose runtime representation it describes."
            ),
            AstUntaggedVariantError::RuntimeAnnotationOnUnrelatedType(attribute) => format!(
                "@{attribute} on a type abbreviation must describe an abstract type, or a type with the same annotation. The abbreviated type already has a runtime representation the compiler knows, or can be undefined."
            ),
            AstUntaggedVariantError::RuntimeAnnotationContradictsManifest(outer, inner) => format!(
                "This annotation, {outer}, contradicts the abbreviated type, whose values are recognized by {inner}."
            ),
            AstUntaggedVariantError::SubclassOfArray(name) => format!(
                "@instanceOf(\"{name}\") cannot describe the values of an array type: they are recognized by Array.isArray, and subclasses of Array are not supported."
            ),
            AstUntaggedVariantError::ClassOnPublicAbbreviation(name) => format!(
                "A class must be declared on an abstract type or a private abbreviation: write `= private ...`, so that values of the abbreviated type are not instances of {name} without a coercion, and another abbreviation cannot declare them instances of another class."
            ),
            AstUntaggedVariantError::SubclassOfPublicAbbreviation(name, ancestor) => format!(
                "A subclass must be a private abbreviation: write `= private ...` so that instances of {ancestor} cannot be used as instances of {name} without a coercion."
            ),
            AstUntaggedVariantError::ClassTwiceInChain(name) => format!(
                "{name} appears twice in this chain of abbreviations, so it would be its own superclass."
            ),
        }
    }
}

fn ast_untagged_variant_error(loc: Location, error: AstUntaggedVariantError) -> TypeModError {
    TypeModError::AstUntaggedVariantError { loc, error }
}

/// OCaml `Ast_untagged_variants.runtime_tag_of_parsetree`.
pub(crate) fn runtime_tag_of_parsetree(
    tag: &crate::parser::ast::ConstructorTag,
    arena: &ParseArena,
) -> Result<crate::types::VariantLiteralTag, AstUntaggedVariantError> {
    use crate::parser::ast::ConstructorTag as P;
    use crate::types::VariantLiteralTag as T;
    Ok(match *tag {
        P::Pct_string(s) => T::String(s.semantic(arena).to_string()),
        P::Pct_int(source) => {
            let source = arena.get_string(source);
            match crate::types::decl::parse_ocaml_int_literal(source) {
                Some(i) => T::Int(i),
                None => {
                    return Err(AstUntaggedVariantError::VariantAsIntegerOutOfRange(
                        source.to_string(),
                    ));
                }
            }
        }
        P::Pct_float(f) => T::Float(arena.get_string(f).to_string()),
        P::Pct_bigint(i) => T::BigInt(arena.get_string(i).to_string()),
        P::Pct_bool(b) => T::Bool(b),
        P::Pct_null => T::Null,
        P::Pct_undefined => T::Undefined,
    })
}

/// OCaml `Ast_untagged_variants.process_constructor_tag`: an `@as` left in
/// the attributes is invalid (no valid tag was taken out) or a duplicate.
pub(crate) fn process_constructor_tag(
    arena: &ParseArena,
    cstr: &crate::parser::ast::ConstructorDeclaration,
) -> Result<Option<crate::types::VariantLiteralTag>, (LocIdx, AstUntaggedVariantError)> {
    let leftover_as = cstr
        .pcd_attributes
        .iter()
        .find(|attr| arena.get_string(attr.0.txt) == "as")
        .map(|attr| attr.0.loc);
    match &cstr.pcd_runtime_tag {
        None => match leftover_as {
            Some(loc) => Err((loc, AstUntaggedVariantError::InvalidVariantAsAnnotation)),
            None => Ok(None),
        },
        Some(tag) => {
            if let Some(loc) = leftover_as {
                return Err((loc, AstUntaggedVariantError::DuplicatedBsAs));
            }
            runtime_tag_of_parsetree(&tag.txt, arena)
                .map(Some)
                .map_err(|error| (tag.loc, error))
        }
    }
}

/// `Ast_untagged_variants.process_tag_name`: the name a `@tag` annotation
/// gives the tag field.
pub(crate) fn process_variant_tag_name(
    ctx: &crate::types::context::TypeContext,
    attrs: &[crate::types::decl::Attribute],
) -> TypeModResult<Option<String>> {
    let mut tag_name = None;
    for attr in attrs {
        if attr.attr_name.txt != "tag" {
            continue;
        }
        if tag_name.is_some() {
            return Err(ast_untagged_variant_error(
                ctx.resolve_loc(attr.attr_name.loc),
                AstUntaggedVariantError::DuplicatedBsAs,
            ));
        }
        // `Ast_payload.semantic_string_of_payload`.
        match attr.attr_payload.semantic_string() {
            Ok(Some(value)) => tag_name = Some(value.to_string()),
            Ok(None) => {}
            Err(loc) => {
                return Err(TypeModError::InvalidStringEscape {
                    loc: ctx.resolve_loc(loc),
                });
            }
        }
        if tag_name.is_none() {
            return Err(ast_untagged_variant_error(
                ctx.resolve_loc(attr.attr_name.loc),
                AstUntaggedVariantError::InvalidVariantTagAnnotation,
            ));
        }
    }
    Ok(tag_name)
}

fn check_variant_tag_field_conflicts(
    ctx: &crate::types::context::TypeContext,
    constructors: &[crate::types::decl::ConstructorDeclaration],
) -> TypeModResult<()> {
    for constructor in constructors {
        let constructor_name = constructor.cd_id.name().to_string();
        let effective_tag_name = process_variant_tag_name(ctx, &constructor.cd_attributes)?
            .unwrap_or_else(|| constructor_name.clone());
        let crate::types::decl::ConstructorArguments::CstrRecord(fields) = &constructor.cd_args
        else {
            continue;
        };
        for field in fields {
            let field_name = field.ld_id.name().to_string();
            // `Record_runtime.declaration_name field`.
            let effective_field_name = field.declaration_name().to_string();
            if effective_field_name == effective_tag_name {
                return Err(ast_untagged_variant_error(
                    ctx.resolve_loc(constructor.cd_loc),
                    AstUntaggedVariantError::TagFieldNameConflict {
                        constructor_name,
                        field_name,
                        runtime_value: effective_field_name,
                    },
                ));
            }
        }
    }
    Ok(())
}

/// typedecl.ml `transl_type_decl`: compute the canonical runtime layout of a
/// variant declaration (`check_tag_field_conflicts`, then
/// `Variant_layout.layout_from_type_variant`), which also validates the
/// untagged invariants with the whole recursive group in the environment.
fn check_variant_declaration_well_formed(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    decl: &crate::types::decl::TypeDeclaration,
) -> TypeModResult<()> {
    let crate::types::decl::TypeKind::TypeVariant(constructors, _) = &decl.type_kind else {
        return Ok(());
    };
    check_variant_tag_field_conflicts(ctx, constructors)?;
    let configuration = crate::types::VariantConfiguration {
        unboxed: has_decl_attr(&decl.type_attributes, "unboxed"),
        tag_name: process_variant_tag_name(ctx, &decl.type_attributes)?,
    };
    let layout = crate::types::variant_layout::layout_from_type_variant(
        ctx,
        env,
        configuration,
        constructors,
        |cstr| process_variant_tag_name(ctx, &cstr.cd_attributes),
    )?;
    if let Some(layout_ref) = decl.variant_layout_ref() {
        ctx.complete_variant_layout(layout_ref, layout);
    }
    Ok(())
}

/// typedecl.ml `transl_type_decl`: `Variant_layout.resolve_shapes ~env
/// decls` before the final environment is built, so every copy of a
/// declaration of the group carries what it states about its values at run
/// time, resolved in the environment it is declared in.
fn resolve_declaration_group_shapes(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    ids: &[Ident],
    decls: &[crate::types::decl::TypeDeclaration],
) -> TypeModResult<Vec<(Ident, crate::types::ValueShape)>> {
    let shapes = crate::types::variant_layout::resolve_shapes(ctx, env, ids, decls)?;
    Ok(ids.iter().copied().zip(shapes).collect())
}

fn shape_for(
    shapes: &[(Ident, crate::types::ValueShape)],
    id: &Ident,
) -> Option<crate::types::ValueShape> {
    shapes
        .iter()
        .find(|(shape_id, _)| shape_id.same(id))
        .map(|(_, shape)| shape.clone())
}

fn touch_manifest_cyclic_abbrev_check(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    manifest: TypeExprRef,
) {
    // OCaml compiler/ml/typedecl.ml:734-739 calls `Ctype.cyclic_abbrev`
    // after translating a manifest. That check is observational: ctype.ml
    // 4155-4170 calls `expand_abbrev_opt`, whose normalize_path fallback can
    // force a persistent module's `ps_sig` before the next local type is named.
    // Keep the same force point even when the abbreviation is not cyclic.
    let mut seen = Vec::new();
    let mut current = manifest;
    for _ in 0..20 {
        let current_repr = ctx.repr(current);
        if seen.contains(&current_repr) {
            break;
        }
        seen.push(current_repr);
        let Some(expanded) = crate::types::ctype::expand_abbrev_opt_once(ctx, env, current_repr)
        else {
            if let crate::types::type_expr::TypeDesc::Tconstr { path, .. } =
                &*ctx.get_desc(current_repr)
            {
                // OCaml compiler/ml/ctype.ml:1367-1372 still calls
                // Env.normalize_path when Env.find_type_expansion cannot
                // expand the abbreviation. In the cyclic-abbrev path from
                // compiler/ml/ctype.ml:4155-4170 this can force persistent
                // module signature lazies through env.ml:903-914 even though
                // the type path normalizes to itself.
                crate::types::ctype::force_normalize_path_full_side_effects(ctx, env, path);
            }
            break;
        };
        current = expanded;
    }
}

fn find_type_decl_for_abbrev_cycle(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    path: &Path,
) -> Option<crate::types::TypeDeclaration> {
    crate::types::ctype::lookup_type_decl_for_path_pub(ctx, env, path)
}

fn type_abbrev_path_to_check(path: &Path, ids: &[Ident]) -> bool {
    match path.view() {
        PathView::Pident(id) => ids.iter().any(|candidate| candidate.same(id)),
        _ => false,
    }
}

fn type_exprs_equal_for_abbrev_recursion(
    ctx: &crate::types::context::TypeContext,
    left: TypeExprRef,
    right: TypeExprRef,
    seen: &mut HashSet<(TypeExprRef, TypeExprRef)>,
) -> bool {
    let left = ctx.repr(left);
    let right = ctx.repr(right);
    if left == right {
        return true;
    }
    if !seen.insert((left, right)) {
        return true;
    }

    let left_desc = *ctx.get_desc(left);
    let right_desc = *ctx.get_desc(right);
    match (left_desc, right_desc) {
        (
            TypeDesc::Tarrow {
                args: left_args,
                ret: left_ret,
            },
            TypeDesc::Tarrow {
                args: right_args,
                ret: right_ret,
            },
        ) => {
            left_args.len() == right_args.len()
                && ctx
                    .type_args(left_args)
                    .iter()
                    .zip(ctx.type_args(right_args).iter())
                    .all(|(left, right)| {
                        arg_labels_equal_for_abbrev_recursion(left.label(), right.label())
                            && type_exprs_equal_for_abbrev_recursion(ctx, left.typ, right.typ, seen)
                    })
                && type_exprs_equal_for_abbrev_recursion(ctx, left_ret, right_ret, seen)
        }
        (TypeDesc::Ttuple(left_items), TypeDesc::Ttuple(right_items)) => {
            type_expr_lists_equal_for_abbrev_recursion(
                ctx,
                ctx.type_list(left_items),
                ctx.type_list(right_items),
            )
        }
        (
            TypeDesc::Tconstr {
                path: left_path,
                args: left_args,
                ..
            },
            TypeDesc::Tconstr {
                path: right_path,
                args: right_args,
                ..
            },
        ) => {
            left_path.same(&right_path)
                && type_expr_lists_equal_for_abbrev_recursion(
                    ctx,
                    ctx.type_list(left_args),
                    ctx.type_list(right_args),
                )
        }
        (TypeDesc::Tlink(left_next), _) | (TypeDesc::Tsubst(left_next), _) => {
            type_exprs_equal_for_abbrev_recursion(ctx, left_next, right, seen)
        }
        (_, TypeDesc::Tlink(right_next)) | (_, TypeDesc::Tsubst(right_next)) => {
            type_exprs_equal_for_abbrev_recursion(ctx, left, right_next, seen)
        }
        (
            TypeDesc::Tpoly {
                body: left_body,
                vars: left_vars,
            },
            TypeDesc::Tpoly {
                body: right_body,
                vars: right_vars,
            },
        ) => {
            left_vars.len() == right_vars.len()
                && ctx
                    .type_list(left_vars)
                    .iter()
                    .zip(ctx.type_list(right_vars).iter())
                    .all(|(left_var, right_var)| {
                        type_exprs_equal_for_abbrev_recursion(ctx, left_var, right_var, seen)
                    })
                && type_exprs_equal_for_abbrev_recursion(ctx, left_body, right_body, seen)
        }
        (
            TypeDesc::Tpackage {
                path: left_path,
                lids: left_lids,
                args: left_args,
            },
            TypeDesc::Tpackage {
                path: right_path,
                lids: right_lids,
                args: right_args,
            },
        ) => {
            left_path.same(&right_path)
                && ctx.package_lids(left_lids) == ctx.package_lids(right_lids)
                && type_expr_lists_equal_for_abbrev_recursion(
                    ctx,
                    ctx.type_list(left_args),
                    ctx.type_list(right_args),
                )
        }
        (TypeDesc::Tnil, TypeDesc::Tnil) => true,
        _ => false,
    }
}

fn arg_labels_equal_for_abbrev_recursion(
    left: crate::types::type_expr::TypeArgLabel,
    right: crate::types::type_expr::TypeArgLabel,
) -> bool {
    left.same_label(right)
}

fn type_var_name_for_abbrev_recursion(
    ctx: &crate::types::context::TypeContext,
    ty: TypeExprRef,
) -> Option<crate::name::Name> {
    match &*ctx.get_desc(ctx.repr(ty)) {
        TypeDesc::Tvar(name) | TypeDesc::Tunivar(name) => *name,
        _ => None,
    }
}

fn instance_parameterized_type_keep_names_for_abbrev_recursion(
    ctx: &crate::types::context::TypeContext,
    params: &[TypeExprRef],
    body: TypeExprRef,
) -> (Vec<TypeExprRef>, TypeExprRef) {
    let (fresh_params, fresh_body) =
        crate::types::ctype::instance_parameterized_type(ctx, params, body);
    for (param, fresh_param) in params.iter().zip(fresh_params.iter()) {
        let Some(name) = type_var_name_for_abbrev_recursion(ctx, *param) else {
            continue;
        };
        let fresh_param = ctx.repr(*fresh_param);
        let replacement = match &*ctx.get_desc(fresh_param) {
            TypeDesc::Tvar(..) => Some(TypeDesc::Tvar(
                Some(name))),
            TypeDesc::Tunivar(..) => Some(TypeDesc::Tunivar(
                Some(name))),
            _ => None,
        };
        if let Some(replacement) = replacement {
            ctx.set_desc(fresh_param, replacement);
        }
    }
    (fresh_params, fresh_body)
}

fn type_expr_lists_equal_for_abbrev_recursion(
    ctx: &crate::types::context::TypeContext,
    left: crate::types::type_expr::TypeSlice<'_>,
    right: crate::types::type_expr::TypeSlice<'_>,
) -> bool {
    left.len() == right.len()
        && left.iter().zip(right.iter()).all(|(left, right)| {
            type_exprs_equal_for_abbrev_recursion(ctx, left, right, &mut HashSet::new())
        })
}

/// The declaration whose abbreviation recursion is checked for regularity.
struct AbbrevRecursionCheck<'a> {
    ctx: &'a crate::types::context::TypeContext,
    env: &'a Env,
    loc: LocIdx,
    /// The declared type's path.
    target_path: &'a Path,
    /// Its parameters, which every recursive occurrence must repeat.
    expected_args: &'a [TypeExprRef],
    should_check_path: &'a dyn Fn(&Path) -> bool,
    find_decl: &'a dyn Fn(&Path) -> Option<crate::types::TypeDeclaration>,
}

fn check_type_abbrev_recursion_regular(
    check: &AbbrevRecursionCheck<'_>,
    current_path: &Path,
    prev_expansions: &[Path],
    ty: TypeExprRef,
    visited: &mut HashSet<TypeExprRef>,
) -> TypeModResult<()> {
    let AbbrevRecursionCheck {
        ctx,
        env,
        loc,
        target_path,
        expected_args,
        should_check_path,
        find_decl,
    } = *check;
    let ty = ctx.repr(ty);
    if !visited.insert(ty) {
        return Ok(());
    }

    match *ctx.get_desc(ty) {
        TypeDesc::Tconstr { path, args, .. } => {
            if path.same(target_path) {
                if !type_expr_lists_equal_for_abbrev_recursion(
                    ctx,
                    expected_args.into(),
                    ctx.type_list(args),
                ) {
                    return Err(TypeModError::ParametersDiffer {
                        loc,
                        path: *current_path,
                        actual: ty,
                        expected: ctx.new_constr(*target_path, expected_args.to_vec()),
                    });
                }
            } else if should_check_path(&path)
                && !prev_expansions
                    .iter()
                    .any(|expanded_path| expanded_path.same(&path))
                && let Some(decl) = find_decl(&path)
                && let Some(body0) = decl.type_manifest
                // `Env.find_type_expansion` (env.ml:944-956) does not expand
                // a private abstract type without a constructor row.
                && (decl.type_private == crate::types::PrivateFlag::Public
                    || !matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract)
                    || crate::types::btype::has_constr_row(ctx, body0))
            {
                let (params, body) =
                    crate::types::ctype::instance_parameterized_type(ctx, &decl.type_params, body0);
                let mut unify_state = crate::types::ctype::UnifyState::new();
                unify_state.set_env(env);
                let same_arity = params.len() == args.len();
                let params_unify = same_arity
                    && params
                        .iter()
                        .zip(ctx.type_list(args).iter())
                        .all(|(param, arg)| {
                            crate::types::ctype::unify(ctx, &mut unify_state, *param, arg).is_ok()
                        });
                if !params_unify {
                    return Err(TypeModError::ConstraintFailed {
                        loc,
                        actual: ty,
                        expected: ctx.new_constr(path, decl.type_params.clone()),
                    });
                }
                let mut next_expansions = prev_expansions.to_vec();
                next_expansions.push(path);
                check_type_abbrev_recursion_regular(check, &path, &next_expansions, body, visited)?;
            }

            for arg in ctx.type_list(args) {
                check_type_abbrev_recursion_regular(
                    check,
                    current_path,
                    prev_expansions,
                    arg,
                    visited,
                )?;
            }
            Ok(())
        }
        TypeDesc::Tpoly { body, vars } => {
            let (_, body) =
                crate::types::ctype::instance_poly(ctx, true, false, ctx.type_list(vars), body);
            check_type_abbrev_recursion_regular(check, current_path, prev_expansions, body, visited)
        }
        _ => {
            let mut children = Vec::new();
            crate::types::btype::iter_type_expr(ctx, ty, |child| children.push(child));
            for child in children {
                check_type_abbrev_recursion_regular(
                    check,
                    current_path,
                    prev_expansions,
                    child,
                    visited,
                )?;
            }
            Ok(())
        }
    }
}

fn check_type_declaration_abbrev_recursion(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    loc: LocIdx,
    target_path: &Path,
    internal_decl: &crate::types::TypeDeclaration,
    should_check_path: &dyn Fn(&Path) -> bool,
    find_decl: &dyn Fn(&Path) -> Option<crate::types::TypeDeclaration>,
) -> TypeModResult<()> {
    if internal_decl.type_params.is_empty() {
        return Ok(());
    }
    let Some(manifest) = internal_decl.type_manifest else {
        return Ok(());
    };

    let (args, body) = instance_parameterized_type_keep_names_for_abbrev_recursion(
        ctx,
        &internal_decl.type_params,
        manifest,
    );
    let check = AbbrevRecursionCheck {
        ctx,
        env,
        loc,
        target_path,
        expected_args: &args,
        should_check_path,
        find_decl,
    };
    check_type_abbrev_recursion_regular(&check, target_path, &[], body, &mut HashSet::new())
}

type WellFoundedParents = im_rc::HashSet<TypeExprRef>;

/// OCaml `Typedecl.check_well_founded` (typedecl.ml:885-941).
fn check_well_founded(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    loc: LocIdx,
    path: &Path,
    to_check: &dyn Fn(&Path) -> bool,
    ty: TypeExprRef,
) -> TypeModResult<()> {
    struct WellFounded<'c> {
        ctx: &'c crate::types::context::TypeContext,
        env: &'c Env,
        loc: LocIdx,
        path: &'c Path,
        to_check: &'c dyn Fn(&Path) -> bool,
        visited: im_rc::HashMap<TypeExprRef, WellFoundedParents>,
    }

    impl WellFounded<'_> {
        fn check(
            &mut self,
            ty0: TypeExprRef,
            parents: &WellFoundedParents,
            ty: TypeExprRef,
        ) -> TypeModResult<()> {
            let ctx = self.ctx;
            let ty = ctx.repr(ty);
            if parents.contains(&ty) {
                let is_path = matches!(
                    &*ctx.get_desc(ctx.repr(ty0)),
                    TypeDesc::Tconstr { path: p, .. } if p.same(self.path)
                );
                return Err(if is_path {
                    TypeModError::RecursiveAbbrev {
                        loc: self.loc,
                        name: self.path.name(),
                    }
                } else {
                    TypeModError::CycleInDef {
                        loc: self.loc,
                        name: self.path.name(),
                        ty: ty0,
                    }
                });
            }
            let (fini, parents) = match self.visited.get(&ty) {
                Some(prev) if parents.is_subset(prev) => (true, parents.clone()),
                Some(prev) => (false, parents.clone().union(prev.clone())),
                None => (false, parents.clone()),
            };
            if fini {
                return Ok(());
            }
            let desc = *ctx.get_desc(ty);
            let rec_ok = matches!(desc, TypeDesc::Tobject { .. } | TypeDesc::Tvariant(_));
            let visited_after = self.visited.update(ty, parents.clone());
            self.visited = visited_after.clone();
            let child_parents = if rec_ok {
                WellFoundedParents::new()
            } else {
                parents.update(ty)
            };
            let mut children = Vec::new();
            crate::types::btype::iter_type_expr(ctx, ty, |child| children.push(child));
            let mut arg_exn = Ok(());
            for child in &children {
                if let Err(e) = self.check(ty0, &child_parents, *child) {
                    self.visited = visited_after.clone();
                    arg_exn = Err(e);
                    break;
                }
            }
            match &desc {
                TypeDesc::Tconstr { path: p, .. } if arg_exn.is_err() || (self.to_check)(p) => {
                    // `if to_check p then may raise arg_exn else iter (check ty0 empty) ty`;
                    // the pending `arg_exn` is re-raised when expansion fails.
                    let arg_exn = if (self.to_check)(p) {
                        arg_exn?;
                        Ok(())
                    } else {
                        let empty = WellFoundedParents::new();
                        for child in &children {
                            self.check(ty0, &empty, *child)?;
                        }
                        arg_exn
                    };
                    match crate::types::ctype::expand_abbrev_opt_once(ctx, self.env, ty) {
                        Some(expanded) => {
                            let ty0 = if parents.is_empty() { ty } else { ty0 };
                            self.check(ty0, &parents.update(ty), expanded)
                        }
                        None => arg_exn,
                    }
                }
                _ => arg_exn,
            }
        }
    }

    /// `check` only fails on reaching a node already on its path or through
    /// expanding a constructor (it expands only `to_check` paths before a
    /// failure). A graph walk that sees neither proves the check passes.
    fn surely_well_founded(
        ctx: &crate::types::context::TypeContext,
        to_check: &dyn Fn(&Path) -> bool,
        ty: TypeExprRef,
        seen: &mut crate::types::type_expr::TypeExprRefSet,
        on_path: &mut Vec<TypeExprRef>,
    ) -> bool {
        let ty = ctx.repr(ty);
        if !seen.insert(ty) {
            return !on_path.contains(&ty);
        }
        if let TypeDesc::Tconstr { path, .. } = &*ctx.borrow_desc(ty)
            && to_check(path)
        {
            return false;
        }
        on_path.push(ty);
        let mut children: smallvec::SmallVec<[TypeExprRef; 8]> = smallvec::SmallVec::new();
        crate::types::btype::iter_type_expr(ctx, ty, |child| children.push(child));
        for child in children {
            if !surely_well_founded(ctx, to_check, child, seen, on_path) {
                return false;
            }
        }
        on_path.pop();
        true
    }
    if surely_well_founded(
        ctx,
        to_check,
        ty,
        &mut crate::types::type_expr::TypeExprRefSet::new(),
        &mut Vec::new(),
    ) {
        return Ok(());
    }

    let mut checker = WellFounded {
        ctx,
        env,
        loc,
        path,
        to_check,
        visited: im_rc::HashMap::new(),
    };
    checker.check(ty, &WellFoundedParents::new(), ty)
}

/// OCaml `Typedecl.check_well_founded_manifest` (typedecl.ml:943-947).
fn check_well_founded_manifest(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    loc: LocIdx,
    path: &Path,
    decl: &crate::types::TypeDeclaration,
) -> TypeModResult<()> {
    if decl.type_manifest.is_none() {
        return Ok(());
    }
    let args = decl.type_params.iter().map(|_| ctx.new_var(None)).collect();
    let to_check = |p: &Path| p.same(path);
    check_well_founded(
        ctx,
        env,
        loc,
        path,
        &to_check,
        ctx.new_constr(*path, args),
    )
}

/// OCaml `Typedecl.check_well_founded_decl` (typedecl.ml:949-956): every
/// type expression of the instantiated declaration, in `it_type_declaration`
/// order (params, manifest, kind).
fn check_well_founded_decl(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    loc: LocIdx,
    path: &Path,
    decl: &crate::types::TypeDeclaration,
    to_check: &dyn Fn(&Path) -> bool,
) -> TypeModResult<()> {
    let decl = crate::types::ctype::instance_declaration(ctx, decl);
    let mut tys: Vec<TypeExprRef> = decl.type_params.clone();
    tys.extend(decl.type_manifest);
    crate::types::btype::iter_type_expr_kind(&decl.type_kind, |ty| tys.push(ty));
    for ty in tys {
        check_well_founded(ctx, env, loc, path, to_check, ty)?;
    }
    Ok(())
}

/// The ill-formed abbreviation checks of `Typedecl.transl_type_decl`
/// (typedecl.ml:1550-1570): all manifests, then all declarations, then
/// `check_abbrev_recursion`.
fn check_type_declaration_abbrev_cycles(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    ids: &[Ident],
    parser_decls: &[crate::parser::ast::TypeDeclaration],
    internal_decls: &[crate::types::TypeDeclaration],
) -> TypeModResult<()> {
    let should_check_path = |path: &Path| type_abbrev_path_to_check(path, ids);
    let find_decl = |path: &Path| find_type_decl_for_abbrev_cycle(ctx, env, path);
    for ((id, parser_decl), internal_decl) in ids.iter().zip(parser_decls).zip(internal_decls) {
        check_well_founded_manifest(
            ctx,
            env,
            parser_decl.ptype_loc,
            &Path::pident(*id),
            internal_decl,
        )?;
    }
    for ((id, parser_decl), internal_decl) in ids.iter().zip(parser_decls).zip(internal_decls) {
        check_well_founded_decl(
            ctx,
            env,
            parser_decl.ptype_loc,
            &Path::pident(*id),
            internal_decl,
            &should_check_path,
        )?;
    }
    for ((id, parser_decl), internal_decl) in ids.iter().zip(parser_decls).zip(internal_decls) {
        check_type_declaration_abbrev_recursion(
            ctx,
            env,
            parser_decl.ptype_loc,
            &Path::pident(*id),
            internal_decl,
            &should_check_path,
            &find_decl,
        )?;
    }
    Ok(())
}

/// `Mtype.scrape` (mtype.ml:22-26).
fn mtype_scrape(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    mty: &crate::types::decl::ModuleType,
) -> crate::types::decl::ModuleType {
    match mty {
        crate::types::decl::ModuleType::MtyIdent(p) => {
            match find_modtype_expansion(p, env, pers_env, ctx) {
                Some(expansion) => mtype_scrape(ctx, env, pers_env, &expansion),
                None => mty.clone(),
            }
        }
        _ => mty.clone(),
    }
}

/// `Translmod.flat_make_paths` (translmod.ml): the nested `make` values of a
/// compilation unit's final signature, which are also exported under a flat
/// name such as `A$B$make`. React Server Components can only pass a client
/// module's top-level exports to the client, so `Lib.A.B.make` must not be
/// reached through the module object. Producer and consumer derive these
/// paths from the signature alone. Each step carries the field's runtime
/// position, counted as in `Env`.
///
/// OCaml adds every level's signature to the environment
/// (`Env.add_signature`) before scraping its submodules; only `Mty_ident`
/// reads that environment, so Rust materializes it when one is scraped.
pub(crate) fn flat_make_paths(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    sg: &[crate::types::decl::SignatureItem],
) -> Vec<crate::lambda::FlatMakePath> {
    use crate::lambda::FlatMakeStep;
    use crate::types::decl::{ModuleType as Mty, SignatureItem as S, ValueKind};

    struct Scope<'a> {
        base: &'a Env,
        /// The compilation unit's signature.
        top: &'a [S],
        /// The scraped signatures of the enclosing submodules, outermost
        /// first.
        nested: Vec<std::sync::Arc<crate::types::decl::Signature>>,
        /// `envs[i]` is `base` with the first `i + 1` levels added.
        envs: Vec<Env>,
    }

    impl Scope<'_> {
        fn depth(&self) -> usize {
            1 + self.nested.len()
        }

        fn level(&self, index: usize) -> &[S] {
            if index == 0 {
                self.top
            } else {
                &self.nested[index - 1]
            }
        }

        fn env(&mut self, ctx: &crate::types::context::TypeContext) -> Env {
            while self.envs.len() < self.depth() {
                let mut env = self.envs.last().unwrap_or(self.base).clone();
                for item in self.level(self.envs.len()) {
                    crate::types::includemod::add_sig_item_to_env(ctx, item, &mut env);
                }
                self.envs.push(env);
            }
            self.envs.last().unwrap_or(self.base).clone()
        }
    }

    fn of_signature(
        ctx: &crate::types::context::TypeContext,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        scope: &mut Scope<'_>,
        rev_path: &mut Vec<FlatMakeStep>,
        acc: &mut Vec<crate::lambda::FlatMakePath>,
    ) {
        let depth = scope.depth();
        let mut pos = 0;
        let mut index = 0;
        while index < scope.level(depth - 1).len() {
            let item = &scope.level(depth - 1)[index];
            index += 1;
            match item {
                S::SigValue(_, desc) if matches!(desc.val_kind, ValueKind::ValPrim(_)) => {}
                S::SigValue(id, _) => {
                    if !rev_path.is_empty() && id.name() == "make" {
                        let mut path = rev_path.clone();
                        path.push(FlatMakeStep {
                            pos,
                            name: "make".to_string(),
                        });
                        acc.push(path);
                    }
                    pos += 1;
                }
                S::SigTypext(..) => pos += 1,
                S::SigModule(id, md, _) => {
                    let name = id.name().to_string();
                    let scraped = match &md.md_type {
                        Mty::MtySignature(sg) => Some(sg.clone()),
                        Mty::MtyIdent(_) => {
                            let md_type = md.md_type.clone();
                            let env = scope.env(ctx);
                            match mtype_scrape(ctx, &env, pers_env, &md_type) {
                                Mty::MtySignature(sg) => Some(sg),
                                _ => None,
                            }
                        }
                        Mty::MtyAlias(..) | Mty::MtyFunctor { .. } => None,
                    };
                    if let Some(sub) = scraped {
                        rev_path.push(FlatMakeStep { pos, name });
                        scope.nested.push(sub);
                        of_signature(ctx, pers_env, scope, rev_path, acc);
                        scope.nested.pop();
                        scope.envs.truncate(scope.depth());
                        rev_path.pop();
                    }
                    pos += 1;
                }
                S::SigType(..) | S::SigModtype(..) | S::SigClass | S::SigClassType => {}
            }
        }
    }

    let mut acc = Vec::new();
    let mut scope = Scope {
        base: env,
        top: sg,
        nested: Vec::new(),
        envs: Vec::new(),
    };
    of_signature(ctx, pers_env, &mut scope, &mut Vec::new(), &mut acc);
    acc
}

/// `Mtype.type_paths` (mtype.ml:200-225).
fn mtype_type_paths(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    p: &Path,
    mty: &crate::types::decl::ModuleType,
) -> Vec<Path> {
    match mtype_scrape(ctx, env, pers_env, mty) {
        crate::types::decl::ModuleType::MtySignature(sg) => {
            mtype_type_paths_sig(ctx, env, pers_env, p, 0, &sg)
        }
        _ => Vec::new(),
    }
}

fn mtype_type_paths_sig(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    p: &Path,
    pos: i32,
    sg: &[crate::types::decl::SignatureItem],
) -> Vec<Path> {
    use crate::types::decl::SignatureItem;
    let Some((item, rem)) = sg.split_first() else {
        return Vec::new();
    };
    match item {
        SignatureItem::SigValue(_, decl) => {
            let pos = match decl.val_kind {
                crate::types::decl::ValueKind::ValPrim(_) => pos,
                crate::types::decl::ValueKind::ValReg => pos + 1,
            };
            mtype_type_paths_sig(ctx, env, pers_env, p, pos, rem)
        }
        SignatureItem::SigType(id, _, _) => {
            let mut paths = vec![Path::pdot(*p, id.name())];
            paths.extend(mtype_type_paths_sig(ctx, env, pers_env, p, pos, rem));
            paths
        }
        SignatureItem::SigModule(id, md, _) => {
            let mut paths = mtype_type_paths(
                ctx,
                env,
                pers_env,
                &Path::pdot_pos(*p, id.name(), pos),
                &md.md_type,
            );
            let mut env = env.clone();
            env.add_module(*id, md.clone());
            paths.extend(mtype_type_paths_sig(ctx, &env, pers_env, p, pos + 1, rem));
            paths
        }
        SignatureItem::SigModtype(id, decl) => {
            let mut env = env.clone();
            env.add_modtype(*id, decl.clone());
            mtype_type_paths_sig(ctx, &env, pers_env, p, pos, rem)
        }
        SignatureItem::SigTypext(..) => mtype_type_paths_sig(ctx, env, pers_env, p, pos + 1, rem),
        SignatureItem::SigClass | SignatureItem::SigClassType => {
            mtype_type_paths_sig(ctx, env, pers_env, p, pos, rem)
        }
    }
}

/// The persistent unit a typed module identifier's signature comes from: the
/// normalized alias target for an alias, otherwise the identifier itself.
fn persistent_module_origin(me: &crate::types::typedtree::ModuleExpr) -> Option<Path> {
    use crate::types::typedtree::{ModuleCoercion, ModuleExprDesc};
    let path = match &me.mod_desc {
        ModuleExprDesc::Tmod_constraint(_, _, _, ModuleCoercion::Tcoerce_alias(_, target, _)) => {
            *target
        }
        ModuleExprDesc::Tmod_ident(path, _) => *path,
        _ => return None,
    };
    match path.view() {
        PathView::Pident(id) if id.is_persistent() => Some(path),
        _ => None,
    }
}

/// `pmd_name`, its loc, `pmd_type`, `pmd_attributes` and `pmd_loc`.
type RecModuleTypeDecl = (
    String,
    LocIdx,
    crate::parse_arena::ModTypeIdx,
    Attributes,
    LocIdx,
);
/// The second transition's declarations and `env2`.
type RecModuleTypes = (Vec<crate::types::typedtree::TypedModuleDeclaration>, Env);

/// OCaml `Typemod.transl_recmodule_modtypes` (typemod.ml:914-981), shared by
/// `module rec` structures and signatures. Returns the second transition's
/// declarations and their environment (`env2`).
fn transl_recmodule_modtypes<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    decls: &[RecModuleTypeDecl],
) -> TypeModResult<RecModuleTypes> {
    let ctx = tctx.type_ctx;
    // OCaml transl_recmodule_modtypes creates all recursive module ids
    // before initializing the definition level or translating any
    // module-type constraint.
    let mod_ids = decls
        .iter()
        .map(|(name, _, _, _, _)| ctx.create_ident(name))
        .collect::<Vec<_>>();

    let mut approx_env = env.clone();
    for id in &mod_ids {
        let dummy =
            crate::types::decl::ModuleType::MtyIdent(Path::pident(ctx.create_ident("#recmod#")));
        approx_env.add_module(*id, empty_module_decl(dummy));
    }

    ctx.init_def(ctx.current_stamp());

    let mut init_decls = Vec::with_capacity(decls.len());
    for ((_, _, mty_idx, _, _), id) in decls.iter().zip(mod_ids.iter()) {
        let approx = approx_modtype(tctx, &approx_env, arena, arena.get_mod_type(*mty_idx))?;
        init_decls.push((*id, approx));
    }

    let mut env0 = env.clone();
    for (id, mty) in &init_decls {
        env0.add_module(*id, empty_module_decl(mty.clone()));
    }

    // typemod.ml:957: `Warnings.without_warnings (fun () -> transition env0 init)`.
    let mut dcl1 = Vec::with_capacity(decls.len());
    for ((name, name_loc, mty_idx, attrs, mb_loc), id) in decls.iter().zip(mod_ids.iter()) {
        let typed_mty = without_warnings(tctx, |tctx| {
            transl_modtype(tctx, &env0, arena, arena.get_mod_type(*mty_idx))
        })?;
        dcl1.push(crate::types::typedtree::TypedModuleDeclaration {
            md_id: *id,
            md_name: Located {
                txt: name.clone(),
                loc: *name_loc,
            },
            md_type: tctx.typed.push_module_type(typed_mty),
            md_attributes: attrs.clone(),
            md_loc: *mb_loc,
        });
    }

    let mut env1 = env.clone();
    for decl in &dcl1 {
        env1.add_module(
            decl.md_id,
            empty_module_decl(tctx.typed.module_type(decl.md_type).mty_type.clone()),
        );
    }
    // OCaml transl_recmodule_modtypes checks recursive-module type
    // declarations after the first transition environment is built.
    for ((_, _, mty_idx, _, _), decl) in decls.iter().zip(dcl1.iter()) {
        check_recmod_type_declarations(
            ctx,
            &env1,
            &mut tctx.persistent_env,
            arena.get_mod_type(*mty_idx).pmty_loc,
            &mod_ids,
            &decl.md_id,
            &tctx.typed.module_type(decl.md_type).mty_type,
        )?;
    }

    let mut dcl2 = Vec::with_capacity(decls.len());
    for ((name, name_loc, mty_idx, attrs, mb_loc), id) in decls.iter().zip(mod_ids.iter()) {
        let typed_mty = transl_modtype(tctx, &env1, arena, arena.get_mod_type(*mty_idx))?;
        dcl2.push(crate::types::typedtree::TypedModuleDeclaration {
            md_id: *id,
            md_name: Located {
                txt: name.clone(),
                loc: *name_loc,
            },
            md_type: tctx.typed.push_module_type(typed_mty),
            md_attributes: attrs.clone(),
            md_loc: *mb_loc,
        });
    }

    let mut rec_env = env.clone();
    for decl in &dcl2 {
        rec_env.add_module(
            decl.md_id,
            empty_module_decl(tctx.typed.module_type(decl.md_type).mty_type.clone()),
        );
    }
    // And again after the second transition environment, before body
    // typing and recursive module inclusion.
    for ((_, _, mty_idx, _, _), decl) in decls.iter().zip(dcl2.iter()) {
        check_recmod_type_declarations(
            ctx,
            &rec_env,
            &mut tctx.persistent_env,
            arena.get_mod_type(*mty_idx).pmty_loc,
            &mod_ids,
            &decl.md_id,
            &tctx.typed.module_type(decl.md_type).mty_type,
        )?;
    }
    Ok((dcl2, rec_env))
}

/// OCaml `Typemod.check_recmod_typedecls` for one module (typemod.ml:591-601)
/// with `Typedecl.check_recmod_typedecl` (typedecl.ml:2069-2074).
fn check_recmod_type_declarations(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    loc: LocIdx,
    recmod_ids: &[Ident],
    module_id: &Ident,
    mty: &crate::types::decl::ModuleType,
) -> TypeModResult<()> {
    let to_check = |path: &Path| recmod_ids.iter().any(|id| path.is_free(id));
    let find_decl = |path: &Path| find_type_decl_for_abbrev_cycle(ctx, env, path);
    for path in mtype_type_paths(ctx, env, pers_env, &Path::pident(*module_id), mty) {
        let Some(decl) = find_type_decl_for_abbrev_cycle(ctx, env, &path) else {
            continue;
        };
        check_well_founded_decl(ctx, env, loc, &path, &decl, &to_check)?;
        check_type_declaration_abbrev_recursion(
            ctx, env, loc, &path, &decl, &to_check, &find_decl,
        )?;
    }
    Ok(())
}

/// OCaml `Typedecl.check_constraints_rec` (typedecl.ml:758-779).
fn check_constraints_rec(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    loc: LocIdx,
    visited: &mut HashSet<TypeExprRef>,
    ty: TypeExprRef,
) -> TypeModResult<()> {
    let ty = ctx.repr(ty);
    if !visited.insert(ty) {
        return Ok(());
    }
    let desc = ctx.get_desc(ty).into_desc();
    match desc {
        crate::types::type_expr::TypeDesc::Tconstr { path, args, .. } => {
            let fresh_args = ctx
                .type_list(args)
                .iter()
                .map(|_| ctx.new_var(None))
                .collect();
            let expected = ctx.new_constr(path, fresh_args);
            let decl = match path.view() {
                PathView::Pident(id) => env.find_type_by_ident(id).ok().cloned(),
                PathView::Pdot(parent, type_name, _) => {
                    crate::types::typecore::lookup_type_in_resolved_path(
                        parent,
                        type_name.as_str(),
                        env,
                        pers_env,
                        ctx,
                    )
                    .map(|(_, _, decl)| (*decl).clone())
                }
                PathView::Papply(..) => None,
            };
            if let Some(decl) = decl {
                crate::types::ctype::enforce_constraints(ctx, env, expected, &decl);
            }
            if !crate::types::ctype::matches(ctx, env, ty, expected) {
                return Err(TypeModError::ConstraintFailed {
                    loc,
                    actual: ty,
                    expected,
                });
            }
            for arg in ctx.type_list(args) {
                check_constraints_rec(ctx, env, pers_env, loc, visited, arg)?;
            }
        }
        crate::types::type_expr::TypeDesc::Tpoly { body, vars } => {
            let (_, body) =
                crate::types::ctype::instance_poly(ctx, false, false, ctx.type_list(vars), body);
            check_constraints_rec(ctx, env, pers_env, loc, visited, body)?;
        }
        _ => {
            let mut children = Vec::new();
            crate::types::btype::iter_type_expr(ctx, ty, |child| children.push(child));
            for child in children {
                check_constraints_rec(ctx, env, pers_env, loc, visited, child)?;
            }
        }
    }
    Ok(())
}

/// OCaml `Typedecl.check_constraints` (typedecl.ml:791-845): check every type
/// written in the declaration at its source location.
fn check_constraints(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    type_record_as_object: bool,
    sdecl: &crate::parser::ast::TypeDeclaration,
    decl: &crate::types::decl::TypeDeclaration,
) -> TypeModResult<()> {
    use crate::parser::ast::ConstructorArguments as PArgs;
    use crate::types::decl::ConstructorArguments as Args;
    let mut visited = HashSet::default();
    let check_labels = |visited: &mut HashSet<TypeExprRef>,
                        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
                        labels: &[crate::types::decl::LabelDeclaration],
                        slabels: &[crate::parser::ast::LabelDeclaration]|
     -> TypeModResult<()> {
        for label in labels {
            let loc = slabels
                .iter()
                .find(|sl| arena.get_string(sl.pld_name.txt) == label.ld_id.name())
                .map(|sl| arena.get_core_type(sl.pld_type).ptyp_loc)
                .unwrap_or_else(|| arena.none_loc());
            check_constraints_rec(ctx, env, pers_env, loc, visited, label.ld_type)?;
        }
        Ok(())
    };
    match (&decl.type_kind, &sdecl.ptype_kind) {
        (
            crate::types::TypeKind::TypeVariant(constructors, _),
            crate::parser::ast::TypeKind::Ptype_variant(scstrs),
        ) => {
            for cd in constructors {
                let Some(scd) = scstrs
                    .iter()
                    .find(|scd| arena.get_string(scd.pcd_name.txt) == cd.cd_id.name())
                else {
                    continue;
                };
                match (&cd.cd_args, &scd.pcd_args) {
                    (Args::CstrTuple(tys), PArgs::Pcstr_tuple(stys)) => {
                        for (sty, ty) in stys.iter().zip(tys) {
                            let loc = arena.get_core_type(*sty).ptyp_loc;
                            check_constraints_rec(ctx, env, pers_env, loc, &mut visited, *ty)?;
                        }
                    }
                    (Args::CstrRecord(labels), PArgs::Pcstr_record(slabels)) => {
                        check_labels(&mut visited, pers_env, labels, slabels)?;
                    }
                    // A single-spread record reinterpreted as an object argument.
                    (Args::CstrTuple(tys), PArgs::Pcstr_record(slabels))
                        if tys.len() == 1 && slabels.len() == 1 =>
                    {
                        let loc = arena.get_core_type(slabels[0].pld_type).ptyp_loc;
                        check_constraints_rec(ctx, env, pers_env, loc, &mut visited, tys[0])?;
                    }
                    _ => {}
                }
                if let (Some(sres), Some(res)) = (scd.pcd_res, cd.cd_res) {
                    let loc = arena.get_core_type(sres).ptyp_loc;
                    check_constraints_rec(ctx, env, pers_env, loc, &mut visited, res)?;
                }
            }
        }
        (
            crate::types::TypeKind::TypeRecord(labels, _),
            crate::parser::ast::TypeKind::Ptype_record(slabels),
        ) => {
            check_labels(&mut visited, pers_env, labels, slabels)?;
        }
        _ => {}
    }
    if let Some(manifest) = decl.type_manifest
        && !type_record_as_object
        && let Some(smanifest) = sdecl.ptype_manifest
    {
        let loc = arena.get_core_type(smanifest).ptyp_loc;
        check_constraints_rec(ctx, env, pers_env, loc, &mut visited, manifest)?;
    }
    Ok(())
}

fn compute_type_variance_fixpoint(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    type_ids: &[Ident],
    required: &[Vec<(bool, bool, bool)>],
) -> Vec<Vec<TypesVariance>> {
    let paths: Vec<Path> = type_ids.iter().map(|id| Path::pident(*id)).collect();

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

    // OCaml iterates until the variances stop changing; this port caps the
    // fixpoint at 32 rounds. Union only grows the rows, so the cap is only
    // reached for very large recursive groups.
    for _ in 0..32 {
        let mut iter_env = env.clone();
        for ((type_id, template), variance) in
            type_ids.iter().zip(templates.iter()).zip(variances.iter())
        {
            let mut decl = template.clone();
            decl.type_variance = variance.clone();
            iter_env.store_type(ctx, *type_id, decl);
        }

        let computed: Vec<Vec<TypesVariance>> = paths
            .iter()
            .enumerate()
            .filter_map(|(idx, path)| iter_env.lookup_type(path).ok().map(|decl| (idx, decl)))
            .map(|(idx, decl)| {
                crate::types::ctype::compute_variance_decl(
                    ctx,
                    &iter_env,
                    decl,
                    required.get(idx).map(Vec::as_slice).unwrap_or(&[]),
                )
            })
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
fn iter_bound_pattern_idents<'a, F>(
    ta: &'a TypedArena,
    pat: &'a crate::types::typedtree::Pattern,
    f: &mut F,
) where
    F: FnMut(&'a Ident),
{
    use crate::types::typedtree::PatternDesc;

    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => f(id),
        PatternDesc::Tpat_alias(inner, id, _) => {
            iter_bound_pattern_idents(ta, ta.pattern(*inner), f);
            f(id);
        }
        PatternDesc::Tpat_tuple(pats)
        | PatternDesc::Tpat_construct(_, _, pats)
        | PatternDesc::Tpat_array(pats) => {
            for p in ta.patterns(*pats) {
                iter_bound_pattern_idents(ta, p, f);
            }
        }
        PatternDesc::Tpat_record(fields, _, _) => {
            for (_, _, p, _) in fields {
                iter_bound_pattern_idents(ta, ta.pattern(*p), f);
            }
        }
        PatternDesc::Tpat_dict(entries) => {
            for entry in entries {
                iter_bound_pattern_idents(ta, ta.pattern(entry.tdp_pattern), f);
            }
        }
        PatternDesc::Tpat_variant(_, Some(inner), _) => {
            iter_bound_pattern_idents(ta, ta.pattern(*inner), f)
        }
        PatternDesc::Tpat_or(left, _right, _) => {
            iter_bound_pattern_idents(ta, ta.pattern(*left), f)
        }
        PatternDesc::Tpat_any
        | PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_interval(..)
        | PatternDesc::Tpat_variant(_, None, _) => {}
    }
}

fn push_sig_values_from_env_pattern(
    ta: &TypedArena,
    env: &Env,
    pat: &crate::types::typedtree::Pattern,
    sig_items: &mut Vec<crate::types::decl::SignatureItem>,
) {
    use crate::types::typedtree::PatternDesc;

    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => {
            let value_desc = env
                .lookup_value(&Path::pident(*id))
                .expect("let-bound value missing from structure environment")
                .clone();
            sig_items.push(crate::types::decl::SignatureItem::SigValue(*id, value_desc));
        }
        PatternDesc::Tpat_alias(inner, id, _) => {
            push_sig_values_from_env_pattern(ta, env, ta.pattern(*inner), sig_items);
            let value_desc = env
                .lookup_value(&Path::pident(*id))
                .expect("let-bound alias missing from structure environment")
                .clone();
            sig_items.push(crate::types::decl::SignatureItem::SigValue(*id, value_desc));
        }
        PatternDesc::Tpat_tuple(pats) => {
            for p in ta.patterns(*pats) {
                push_sig_values_from_env_pattern(ta, env, p, sig_items);
            }
        }
        PatternDesc::Tpat_record(fields, _, rest) => {
            // `Typedtree.bound_idents` binds the record rest before the fields
            // (typedtree.ml:464-469).
            if let Some(rest) = rest {
                let value_desc = env
                    .lookup_value(&Path::pident(rest.rest_ident))
                    .expect("let-bound record rest missing from structure environment")
                    .clone();
                sig_items.push(crate::types::decl::SignatureItem::SigValue(
                    rest.rest_ident,
                    value_desc,
                ));
            }
            for (_, _, p, _) in fields {
                push_sig_values_from_env_pattern(ta, env, ta.pattern(*p), sig_items);
            }
        }
        PatternDesc::Tpat_construct(_, _, pats) | PatternDesc::Tpat_array(pats) => {
            for p in ta.patterns(*pats) {
                push_sig_values_from_env_pattern(ta, env, p, sig_items);
            }
        }
        PatternDesc::Tpat_variant(_, Some(inner), _) => {
            push_sig_values_from_env_pattern(ta, env, ta.pattern(*inner), sig_items);
        }
        PatternDesc::Tpat_or(left, _, _) => {
            push_sig_values_from_env_pattern(ta, env, ta.pattern(*left), sig_items);
        }
        _ => {}
    }
}

fn extract_sig_values_from_pattern(
    ta: &TypedArena,
    pat: &crate::types::typedtree::Pattern,
    ty: TypeExprRef,
    sig_items: &mut Vec<crate::types::decl::SignatureItem>,
) {
    use crate::types::decl::{SignatureItem as SigItem, ValueDescription};
    iter_bound_pattern_idents(ta, pat, &mut |id| {
        sig_items.push(SigItem::SigValue(
            *id,
            ValueDescription {
                val_type: ty,
                val_kind: crate::types::decl::ValueKind::ValReg,
                val_loc: crate::types::DeclLoc::none(),
                val_attributes: Default::default(),
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
    ta: &TypedArena,
    mod_expr: &ModuleExpr,
) -> Option<crate::types::decl::ModuleType> {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_structure(structure) => {
            Some(crate::types::decl::ModuleType::MtySignature(
                std::sync::Arc::new(structure.str_type.clone()),
            ))
        }
        ModuleExprDesc::Tmod_constraint(
            inner,
            _,
            crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
            _,
        ) => match &ta.module_expr(*inner).mod_desc {
            ModuleExprDesc::Tmod_structure(structure) => Some(
                crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(
                    crate::types::includemod::simplify_signature(&structure.str_type),
                )),
            ),
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
            Some(DeclMty::MtyAlias(
                AliasPresence::MtaAbsent,
                std::sync::Arc::new(*path),
            ))
        }
        ModuleExprDesc::Tmod_structure(structure) => Some(DeclMty::MtySignature(
            std::sync::Arc::new(structure.str_type.clone()),
        )),
        ModuleExprDesc::Tmod_constraint(
            _inner,
            _,
            crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
            _,
        ) => {
            // Match compiler/ml/typemod.ml:1205-1217 and 1349-1355:
            // `wrap_constraint` checks inclusion against `arg.mod_type`.
            // An implicit duplicate-removal constraint has already replaced
            // that type with the simplified signature at typemod.ml:1277-1282.
            Some(mod_expr.mod_type.clone())
        }
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
///
/// The result is the path `Env.lookup_module` builds (compiler/ml/env.ml:
/// 1036-1074): a fresh `Pident (Ident.create_persistent s)` for a unit and
/// a fresh `Pdot (p, s, pos)` per step, named by the longident's strings.
pub fn lookup_module_path_by_lid(
    lid: &crate::parser::longident::Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Option<Path> {
    lookup_module_paths_by_lid(lid, arena, env, pers_env, ctx).map(|(_, lookup)| lookup)
}

/// The access path whose components each step of [`lookup_module_path_by_lid`]
/// reads, and the path that lookup returns.
fn lookup_module_paths_by_lid(
    lid: &crate::parser::longident::Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Option<(Path, Path)> {
    use crate::parser::longident::Longident;

    match lid {
        Longident::Lident(mod_idx) => {
            let mod_name = arena.get_string(*mod_idx);
            if let Ok((id, md)) = env.find_module_with_id(mod_name) {
                let access = md.md_path.unwrap_or_else(|| Path::pident(*id));
                // `IdTbl.find_name` (env.ml:284-301): `Pident id`, or
                // `Pdot (root, s, pos)` around the root of an open.
                let (lookup, _) = env
                    .find_module_with_path(mod_name)
                    .expect("a module find_module_with_id finds has a path");
                return Some((access, lookup));
            }
            if let Some(pers) = pers_env.as_mut() {
                if pers.find_pers_struct(mod_name, ctx).is_some() {
                    // env.ml:1012: `Pident (Ident.create_persistent s)`.
                    return Some((
                        Path::pident(Ident::create_persistent(mod_name)),
                        Path::pident(ctx.create_ast_persistent_ident(arena, *mod_idx)),
                    ));
                }
            }
            None
        }
        Longident::Ldot(prefix, submod_idx) => {
            let submod_name = arena.get_string(*submod_idx);
            // Match OCaml Pmod_ident path lookup: type_module calls
            // Typetexp.lookup_module (compiler/ml/typemod.ml:1227-1230),
            // and Env.lookup_module for Ldot only looks up the child in the
            // parent components (compiler/ml/env.ml:1064-1073). It does not
            // force the final child module's signature while merely building
            // the path.
            let (parent_access, parent_lookup) =
                lookup_module_paths_by_lid(prefix, arena, env, pers_env, ctx)?;
            let (access, pos) = crate::types::typecore::with_resolved_module_components_for_path(
                &parent_access,
                env,
                pers_env,
                ctx,
                |components| {
                    components
                        .lookup_module(submod_name, ctx)
                        .map(|(runtime_pos, _, _md)| {
                            (
                                Path::pdot_pos(
                                    *components.access_path(),
                                    submod_name.to_string(),
                                    runtime_pos as i32,
                                ),
                                runtime_pos as i32,
                            )
                        })
                },
            )
            .flatten()?;
            let lookup = ctx.create_ast_dotted(arena, parent_lookup, *submod_idx, pos);
            Some((access, lookup))
        }
        Longident::Lapply(functor, arg) => {
            let (functor_access, functor_lookup) =
                lookup_module_paths_by_lid(functor, arena, env, pers_env, ctx)?;
            let (arg_access, arg_lookup) =
                lookup_module_paths_by_lid(arg, arena, env, pers_env, ctx)?;
            Some((
                Path::papply(functor_access, arg_access),
                Path::papply(functor_lookup, arg_lookup),
            ))
        }
    }
}

fn lookup_module_path_for_module_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    lid: &Longident,
    load: bool,
    loc: LocIdx,
) -> TypeModResult<Path> {
    // OCaml `Env.lookup_module` (compiler/ml/env.ml:1022-1036) raises
    // `Recmodule` for a recursive module still bound to its `#recmod#`
    // placeholder; `Typetexp.find_component` (typetexp.ml:86-96) reports it,
    // also when a dotted path's prefix is the placeholder.
    let illegal_recursive_reference =
        || TypeModError::CoreError(TypeCoreError::IllegalReferenceToRecursiveModule { loc });
    if let Longident::Lident(mod_idx) = lid
        && let Ok((_, md)) = env.find_module_with_id(arena.get_string(*mod_idx))
        && is_recursive_module_placeholder_type(&md.md_type)
    {
        return Err(illegal_recursive_reference());
    }
    if tctx.transparent_modules
        && !load
        && let Longident::Lident(mod_idx) = lid
    {
        let mod_name = arena.get_string(*mod_idx);
        if let Ok((id, md)) = env.find_module_with_id(mod_name) {
            return Ok(md.md_path.unwrap_or_else(|| Path::pident(*id)));
        }

        if tctx
            .persistent_env
            .as_ref()
            .is_some_and(|pers| pers.is_compiling_module(mod_name))
        {
            let error = crate::types::typecore::unbound_module_lookup_error(tctx, env, loc, lid);
            return Err(TypeModError::CoreError(error));
        }

        // env.ml:1044-1045: `check_pers_struct` records the weak import.
        if let Some(pers) = tctx.persistent_env.as_ref() {
            pers.check_pers_struct(mod_name);
        }
        let has_cmi = tctx
            .persistent_env
            .as_ref()
            .is_some_and(|pers| pers.has_known_module_without_loading(mod_name));
        if !has_cmi {
            tctx.report_warning(
                arena.none_loc(),
                Warning::NoCmiFile {
                    name: mod_name.to_string(),
                    reason: None,
                },
            );
        }
        return Ok(Path::pident(Ident::create_persistent(mod_name)));
    }

    let path = lookup_module_path_by_lid(lid, arena, env, &mut tctx.persistent_env, tctx.type_ctx)
        .ok_or_else(|| {
            if module_lid_references_recursive_placeholder(lid, arena, env) {
                return illegal_recursive_reference();
            }
            TypeModError::CoreError(crate::types::typecore::unbound_module_lookup_error(
                tctx, env, loc, lid,
            ))
        })?;
    // env.ml:1035-1037: looking up a module bound to an alias of a
    // persistent unit loads that unit (and records it as an import), unless
    // `-no-alias-deps`.
    if !tctx.transparent_modules
        && let Longident::Lident(mod_idx) = lid
        && let Ok((_, md)) = env.find_module_with_id(arena.get_string(*mod_idx))
        && let crate::types::decl::ModuleType::MtyAlias(_, target) = &md.md_type
        && let PathView::Pident(target) = target.view()
        && target.is_persistent()
        && let Some(pers) = tctx.persistent_env.as_mut()
    {
        pers.find_pers_struct(target.name(), tctx.type_ctx);
    }
    Ok(path)
}

/// Look up a module-type path by longident in the module-type namespace.
/// This mirrors OCaml `Typetexp.find_modtype` / `transl_modtype_longident`.
pub fn lookup_modtype_path_by_lid(
    lid: &crate::parser::longident::Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Option<Path> {
    use crate::parser::longident::Longident;

    match lid {
        Longident::Lident(modtype_idx) => {
            let modtype_name = arena.get_string(*modtype_idx);
            // OCaml `Env.lookup_modtype` uses `IdTbl.find_name`: a local binding
            // is `Pident id`, an opened one `Pdot (root, name, pos)`.
            env.find_modtype_with_path(modtype_name)
                .ok()
                .map(|(path, _)| path)
        }
        Longident::Ldot(prefix, submodtype_idx) => {
            let submodtype_name = arena.get_string(*submodtype_idx);
            // env.ml:1091-1099: `Pdot (p, s, pos)` around the path
            // `lookup_module_descr` returns for the prefix.
            if let Some(path) = crate::types::typecore::with_module_descr_for_lid(
                prefix,
                arena,
                env,
                pers_env,
                ctx,
                |lookup_path, components| {
                    components
                        .lookup_qualified_modtype(submodtype_name, ctx)
                        .map(|_| {
                            ctx.create_ast_dotted(
                                arena,
                                *lookup_path,
                                *submodtype_idx,
                                crate::types::path::NOPOS,
                            )
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

fn lookup_modtype_path_or_error(
    tctx: &mut TypeCheckContext<'_>,
    lid: &crate::parser::longident::Longident,
    loc: LocIdx,
    arena: &ParseArena,
    env: &Env,
) -> TypeModResult<Path> {
    // `Env.lookup_modtype` (env.ml:1022-1036) only goes through
    // `lookup_module_descr` for the module prefix of a dotted path; a bare
    // name is looked up among module types.
    if let crate::parser::longident::Longident::Ldot(prefix, _) = lid
        && module_lid_references_recursive_placeholder(prefix, arena, env)
    {
        return Err(TypeModError::CoreError(
            TypeCoreError::IllegalReferenceToRecursiveModule { loc },
        ));
    }
    if let Some(path) =
        lookup_modtype_path_by_lid(lid, arena, env, &mut tctx.persistent_env, tctx.type_ctx)
    {
        return Ok(path);
    }
    // `Typetexp.find_modtype` narrows the error to an unbound module prefix
    // (typetexp.ml `find_component` / `narrow_unbound_lid_error`).
    if let Some(error) = crate::types::typecore::unbound_module_prefix_error(tctx, env, loc, lid) {
        return Err(TypeModError::CoreError(error));
    }
    let alternatives =
        unbound_modtype_alternatives(lid, arena, env, &mut tctx.persistent_env, tctx.type_ctx);
    Err(TypeModError::UnboundModtype {
        loc,
        lid: lid.clone(),
        alternatives,
    })
}

pub(crate) fn unbound_modtype_alternatives(
    lid: &crate::parser::longident::Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Vec<String> {
    match lid {
        crate::parser::longident::Longident::Lident(_) => env.fold_modtype_names(),
        crate::parser::longident::Longident::Ldot(prefix, _) => {
            let mut names: Vec<String> =
                lookup_module_type_by_lid(prefix, arena, env, pers_env, ctx)
                    .and_then(|mty| match mty {
                        crate::types::decl::ModuleType::MtySignature(sig) => Some(
                            sig.iter()
                                .filter_map(|item| match item {
                                    crate::types::decl::SignatureItem::SigModtype(id, _) => {
                                        Some(id.name().to_string())
                                    }
                                    _ => None,
                                })
                                .collect(),
                        ),
                        _ => None,
                    })
                    .unwrap_or_default();
            // `Tbl.fold` visits the components in ascending name order and
            // conses them (compiler/ml/env.ml:1938-1945).
            names.sort_unstable_by(|a, b| b.as_bytes().cmp(a.as_bytes()));
            names.dedup();
            names
        }
        crate::parser::longident::Longident::Lapply(_, _) => Vec::new(),
    }
}

fn alias_of_module_type(
    mty: &crate::types::decl::ModuleType,
) -> Option<(crate::types::decl::AliasPresence, std::sync::Arc<Path>)> {
    match mty {
        crate::types::decl::ModuleType::MtyAlias(alias_presence, alias_path) => {
            // The declaration's own target block.
            Some((*alias_presence, alias_path.clone()))
        }
        _ => None,
    }
}

fn check_recursive_module_reference_lid(
    lid: &Located<LidentIdx>,
    arena: &ParseArena,
    env: &Env,
) -> TypeModResult<()> {
    let longident = arena.get_longident(lid.txt);
    if module_lid_references_recursive_placeholder(longident, arena, env) {
        Err(TypeModError::CoreError(
            TypeCoreError::IllegalReferenceToRecursiveModule { loc: lid.loc },
        ))
    } else {
        Ok(())
    }
}

pub(crate) fn is_recursive_module_placeholder_type(mty: &crate::types::decl::ModuleType) -> bool {
    matches!(
        mty,
        crate::types::decl::ModuleType::MtyIdent(path)
            if path.as_pident().is_some_and(|id| id.name() == "#recmod#")
    )
}

fn module_lid_references_recursive_placeholder(
    lid: &crate::parser::longident::Longident,
    arena: &ParseArena,
    env: &Env,
) -> bool {
    use crate::parser::longident::Longident;

    match lid {
        Longident::Lident(mod_idx) => {
            let mod_name = arena.get_string(*mod_idx);
            env.find_module_with_id(mod_name)
                .map(|(_, md)| is_recursive_module_placeholder_type(&md.md_type))
                .unwrap_or(false)
        }
        Longident::Ldot(prefix, _) => {
            module_lid_references_recursive_placeholder(prefix, arena, env)
        }
        Longident::Lapply(functor_lid, arg_lid) => {
            module_lid_references_recursive_placeholder(functor_lid, arena, env)
                || module_lid_references_recursive_placeholder(arg_lid, arena, env)
        }
    }
}

fn lookup_module_alias_by_lid(
    lid: &crate::parser::longident::Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Option<(crate::types::decl::AliasPresence, std::sync::Arc<Path>)> {
    use crate::parser::longident::Longident;

    match lid {
        Longident::Lident(mod_idx) => {
            let mod_name = arena.get_string(*mod_idx);
            env.find_module(mod_name)
                .ok()
                .and_then(|md| alias_of_module_type(&md.md_type))
        }
        Longident::Ldot(prefix, submod_idx) => {
            let submod_name = arena.get_string(*submod_idx);
            if let Some((alias_presence, alias_path)) =
                lookup_module_alias_by_lid(prefix, arena, env, pers_env, ctx)
            {
                return Some((
                    alias_presence,
                    std::sync::Arc::new(Path::pdot_pos(
                        *alias_path,
                        submod_name,
                        crate::types::path::NOPOS,
                    )),
                ));
            }
            crate::types::typecore::with_resolved_module_components_for_lid(
                prefix,
                arena,
                env,
                pers_env,
                ctx,
                |components| {
                    components
                        .lookup_module(submod_name, ctx)
                        .and_then(|(_, _, md)| alias_of_module_type(&md.md_type))
                },
            )
            .flatten()
        }
        Longident::Lapply(_, _) => None,
    }
}

/// Look up the semantic module type for a longident by searching env and persistent env.
/// Returns a `decl::ModuleType` (the semantic type), not the `typedtree::ModuleType` (the syntactic type tree).
pub fn lookup_module_type_by_lid(
    lid: &crate::parser::longident::Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Option<crate::types::decl::ModuleType> {
    use crate::parser::longident::Longident;
    use crate::types::decl::ModuleType as DeclMty;
    fn local_parent_alias_by_lid(
        lid: &crate::parser::longident::Longident,
        arena: &ParseArena,
        env: &Env,
    ) -> Option<(crate::types::decl::AliasPresence, std::sync::Arc<Path>)> {
        match lid {
            Longident::Lident(mod_idx) => {
                let mod_name = arena.get_string(*mod_idx);
                env.find_module(mod_name)
                    .ok()
                    .and_then(|md| alias_of_module_type(&md.md_type))
            }
            _ => None,
        }
    }
    fn parent_alias_by_lid(
        lid: &crate::parser::longident::Longident,
        arena: &ParseArena,
        env: &Env,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &crate::types::context::TypeContext,
    ) -> Option<(crate::types::decl::AliasPresence, std::sync::Arc<Path>)> {
        if let Longident::Lident(mod_idx) = lid {
            let mod_name = arena.get_string(*mod_idx);
            if env.find_module(mod_name).is_err() {
                return None;
            }
        }
        local_parent_alias_by_lid(lid, arena, env).or_else(|| {
            // OCaml `type_module` wraps identifiers whose `Env.find_module`
            // result is `Mty_alias` (compiler/ml/typemod.ml:1242-1252).
            // Nested paths such as Belt.Id.MakeComparable must preserve the
            // alias for the Belt.Id prefix so the final lookup still sees an
            // alias module type instead of the resolved target signature.
            lookup_module_type_by_lid(lid, arena, env, pers_env, ctx)
                .and_then(|mty| alias_of_module_type(&mty))
        })
    }
    match lid {
        Longident::Lident(mod_idx) => {
            let mod_name = arena.get_string(*mod_idx);
            // Try local env first
            if let Ok((id, md)) = env.find_module_with_id(mod_name) {
                if id.is_persistent() {
                    // OCaml compiler/ml/typemod.ml:1227-1229 resolves
                    // `Pmod_ident` with `Typetexp.lookup_module`, whose
                    // Lident path uses compiler/ml/env.ml:1000-1007 and reads
                    // persistent components without forcing `ps_sig`. The
                    // following `Env.find_module` at typemod.ml:1244 reaches
                    // env.ml:872-874 for persistent roots and forces
                    // `Lazy.force ps.ps_sig` before include processing later
                    // freshens the extracted signature at typemod.ml:1575-1578.
                    if let Some(pers) = pers_env.as_mut() {
                        pers.force_lazy_signature_rename(mod_name, ctx);
                    }
                }
                return Some(md.md_type.clone());
            }
            if let Some(pers) = pers_env.as_mut() {
                if let Some(sig) = pers.get_renamed_sig(mod_name, ctx) {
                    // env.ml:865-875: `find_module` of a persistent unit is
                    // its forced `ps_sig`, with local item paths.
                    let root = Path::pident(Ident::create_persistent(mod_name));
                    return Some(DeclMty::MtySignature(std::sync::Arc::new(
                        localize_scraped_signature_vec(ctx, Some(&*pers), &sig, &root),
                    )));
                }
            }
            None
        }
        Longident::Ldot(prefix, submod_idx) => {
            let submod_name = arena.get_string(*submod_idx);
            if let Some(found) = crate::types::typecore::with_resolved_module_components_for_lid(
                prefix,
                arena,
                env,
                pers_env,
                ctx,
                |components| {
                    if let Some((_, _, sub_md)) =
                        components.lookup_qualified_module_shared(submod_name, ctx)
                    {
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
                if matches!(found, DeclMty::MtyAlias(..)) {
                    return Some(found);
                }
                // OCaml compiler/ml/typemod.ml:1653-1659 obtains
                // `module type of M.N` through Typetexp.find_module. That uses
                // compiler/ml/typetexp.ml:150-152 and compiler/ml/env.ml:1000-1007,
                // 865-880: dotted parents come from component tables (`ps_comps`)
                // before any full persistent `ps_sig` force. Only fall back to a
                // parent alias after the child component did not carry one itself.
                if let Some((alias_presence, alias_path)) =
                    parent_alias_by_lid(prefix, arena, env, pers_env, ctx)
                {
                    return Some(DeclMty::MtyAlias(
                        alias_presence,
                        std::sync::Arc::new(Path::pdot_pos(
                            *alias_path,
                            submod_name,
                            crate::types::path::NOPOS,
                        )),
                    ));
                }
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
                        components.lookup_qualified_module_shared(submod_name, ctx)
                    {
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
            .map(|found| {
                if matches!(found, DeclMty::MtyAlias(..)) {
                    found
                } else if let Some((alias_presence, alias_path)) =
                    parent_alias_by_lid(prefix, arena, env, pers_env, ctx)
                {
                    DeclMty::MtyAlias(
                        alias_presence,
                        std::sync::Arc::new(Path::pdot_pos(
                            *alias_path,
                            submod_name,
                            crate::types::path::NOPOS,
                        )),
                    )
                } else {
                    found
                }
            })
        }
        _ => None,
    }
}

/// Resolve a decl::ModuleType to a signature, following aliases via local and
/// persistent environments. This mirrors OCaml's Env.scrape_alias behavior.
pub fn resolve_mod_type_to_sig(
    mty: &crate::types::decl::ModuleType,
    env: Option<&Env>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Option<crate::types::decl::Signature> {
    let mut visiting = HashSet::new();
    resolve_mod_type_to_sig_impl(mty, env, pers_env, ctx, &mut visiting)
}

fn freshened_signature_from_module_type<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    mty: &crate::types::decl::ModuleType,
    loc: LocIdx,
) -> TypeModResult<crate::types::decl::Signature> {
    use crate::types::decl::ModuleType as DeclMty;

    let sig = if let Some(sig) =
        resolve_mod_type_to_sig(mty, Some(env), &mut tctx.persistent_env, tctx.type_ctx)
    {
        sig
    } else {
        match scrape_alias_module_type(mty, env, &mut tctx.persistent_env, tctx.type_ctx) {
            Some(DeclMty::MtySignature(sig)) => std::sync::Arc::unwrap_or_clone(sig),
            Some(DeclMty::MtyAlias(_, path)) => {
                return Err(TypeModError::CannotScrapeAlias { loc, path: *path });
            }
            Some(_) => {
                return Err(TypeModError::CoreError(TypeCoreError::SignatureExpected {
                    loc,
                }));
            }
            None => {
                if let Some(path) = cannot_scrape_alias_path_for_module_type(tctx, env, mty) {
                    return Err(TypeModError::CannotScrapeAlias { loc, path });
                }
                return Err(TypeModError::CoreError(TypeCoreError::SignatureExpected {
                    loc,
                }));
            }
        }
    };

    Ok(
        crate::cmi::persistent_env::freshened_signature_bound_idents_from_kind(
            "typemod_freshened_module_type",
            &sig,
            tctx.type_ctx,
        ),
    )
}

fn add_signature_items_to_env(
    ctx: &crate::types::context::TypeContext,
    sig_items: &[crate::types::decl::SignatureItem],
    env: &mut Env,
) -> TypeModResult<()> {
    use crate::types::decl::SignatureItem;

    for item in sig_items {
        match item {
            SignatureItem::SigValue(id, desc) => {
                check_value_name_for_env(ctx, id, desc)?;
                env.add_value(*id, desc.clone());
            }
            SignatureItem::SigType(id, decl, _) => env.store_type(ctx, *id, decl.clone()),
            SignatureItem::SigModule(id, md, _) => env.add_module(*id, md.clone()),
            SignatureItem::SigModtype(id, mtd) => env.add_modtype(*id, mtd.clone()),
            SignatureItem::SigTypext(_, _, _)
            | SignatureItem::SigClass
            | SignatureItem::SigClassType => {}
        }
    }
    Ok(())
}

fn resolve_mod_type_to_sig_impl(
    mty: &crate::types::decl::ModuleType,
    env: Option<&Env>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
    visiting: &mut HashSet<Path>,
) -> Option<crate::types::decl::Signature> {
    use crate::types::decl::ModuleType as DeclMty;
    match mty {
        DeclMty::MtySignature(sig) => Some((**sig).clone()),
        DeclMty::MtyAlias(_, path) => resolve_path_to_sig_impl(path, env, pers_env, ctx, visiting),
        DeclMty::MtyIdent(path) => {
            resolve_modtype_path_to_sig_impl(path, env, pers_env, ctx, visiting)
                .or_else(|| resolve_path_to_sig_impl(path, env, pers_env, ctx, visiting))
        }
        _ => None,
    }
}

fn resolve_modtype_path_to_sig_impl(
    path: &Path,
    env: Option<&Env>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
    visiting: &mut HashSet<Path>,
) -> Option<crate::types::decl::Signature> {
    if !visiting.insert(*path) {
        return None;
    }

    let result = match path.view() {
        PathView::Pident(id) => env.and_then(|local_env| {
            let mtd = local_env.lookup_modtype(&Path::pident(*id)).ok()?;
            let mty = mtd.mtd_type.as_ref()?;
            resolve_mod_type_to_sig_impl(mty, env, pers_env, ctx, visiting)
        }),
        PathView::Pdot(parent, name, _) => env.and_then(|local_env| {
            let (_, mtd) = crate::types::typecore::lookup_modtype_in_resolved_path(
                parent,
                name.as_str(),
                local_env,
                pers_env,
                ctx,
            )?;
            let mty = mtd.mtd_type.as_ref()?;
            resolve_mod_type_to_sig_impl(mty, env, pers_env, ctx, visiting)
        }),
        PathView::Papply(_, _) => None,
    };

    visiting.remove(path);
    result
}

/// Resolve a module/modtype path to a signature by following through local and
/// persistent environments.
fn resolve_path_to_sig_impl(
    path: &Path,
    env: Option<&Env>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
    visiting: &mut HashSet<Path>,
) -> Option<crate::types::decl::Signature> {
    use crate::types::decl::SignatureItem as SigItem;

    if !visiting.insert(*path) {
        return None;
    }

    let result = match path.view() {
        PathView::Pident(id) => {
            let name = id.name();
            if let Some(local_env) = env {
                if let Ok(md) = local_env.lookup_module(&Path::pident(*id)) {
                    if let Some(sig) =
                        resolve_mod_type_to_sig_impl(&md.md_type, env, pers_env, ctx, visiting)
                    {
                        visiting.remove(path);
                        return Some(sig);
                    }
                }

                if let Ok(mtd) = local_env.lookup_modtype(&Path::pident(*id)) {
                    if let Some(mty) = &mtd.mtd_type {
                        if let Some(sig) =
                            resolve_mod_type_to_sig_impl(mty, env, pers_env, ctx, visiting)
                        {
                            visiting.remove(path);
                            return Some(sig);
                        }
                    }
                }

                if (id.is_persistent() || id.stamp() == 0)
                    && let Some(pers) = pers_env.as_mut()
                    && let Some(sig) = pers.get_renamed_sig(name, ctx)
                {
                    visiting.remove(path);
                    return Some(sig);
                }
            }

            if let Some(pers) = pers_env.as_mut() {
                pers.get_renamed_sig(name, ctx)
            } else {
                None
            }
        }
        PathView::Pdot(parent, name, _) => {
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
                    parent, local_env, pers_env, ctx,
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
    ctx: &crate::types::context::TypeContext,
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

fn with_type_subst_replacement_is_same_arg_alias(
    arena: &ParseArena,
    decl: &crate::parser::ast::TypeDeclaration,
) -> bool {
    use crate::parser::ast::CoreTypeDesc;

    let Some(manifest_idx) = decl.ptype_manifest else {
        return false;
    };
    let manifest = arena.get_core_type(manifest_idx);
    let CoreTypeDesc::Ptyp_constr(inner) = &manifest.ptyp_desc else {
        return false;
    };
    let (_, args) = inner;
    if args.len() != decl.ptype_params.len() {
        return false;
    }

    arena
        .type_list(*args)
        .iter()
        .zip(decl.ptype_params.iter())
        .all(|(arg_idx, (param_idx, _))| {
            let arg = arena.get_core_type(*arg_idx);
            let param = arena.get_core_type(*param_idx);
            match (&arg.ptyp_desc, &param.ptyp_desc) {
                (CoreTypeDesc::Ptyp_var(arg), CoreTypeDesc::Ptyp_var(param)) => arg == param,
                _ => false,
            }
        })
}

fn typed_params_are_constrained(
    ctx: &crate::types::context::TypeContext,
    params: &[TypeExprRef],
) -> bool {
    params.iter().enumerate().any(|(index, param)| {
        let param = ctx.repr(*param);
        match &*ctx.get_desc(param) {
            TypeDesc::Tvar(..) => params[index + 1..]
                .iter()
                .any(|other| ctx.repr(*other) == param),
            _ => true,
        }
    })
}

fn apply_package_constraints_to_module_type(
    env: &Env,
    mty: &crate::types::decl::ModuleType,
    constraints: &[PackageConstraint],
    _package_parent_path: Option<&Path>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
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
                    rewritten_sig.push(SignatureItem::SigValue(*id, vd.clone()))
                }
                SignatureItem::SigType(id, td, rec_status) => {
                    let mut td = (**td).clone();
                    if td.type_params.is_empty() {
                        if let Some((_, manifest_ty)) = constraints
                            .iter()
                            .find(|(path, _)| path.len() == 1 && path[0] == id.name())
                        {
                            td.type_manifest = Some(*manifest_ty);
                        }
                    }
                    rewritten_sig.push(SignatureItem::SigType(
                        *id,
                        std::sync::Arc::new(td),
                        *rec_status,
                    ));
                }
                SignatureItem::SigModule(id, md, rec_status) => {
                    let nested = nested_package_constraints(id.name(), constraints);
                    if !nested.is_empty() {
                        nested_modules.push((rewritten_sig.len(), nested));
                    }
                    rewritten_sig.push(SignatureItem::SigModule(*id, md.clone(), *rec_status));
                }
                other => rewritten_sig.push(other.clone()),
            }
        }

        (rewritten_sig, nested_modules)
    }

    fn finish_rewritten_package_sig(
        env: &Env,
        mut rewritten_sig: crate::types::decl::Signature,
        nested_modules: Vec<(usize, Vec<PackageConstraint>)>,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &crate::types::context::TypeContext,
    ) -> Option<crate::types::decl::ModuleType> {
        for (idx, nested) in nested_modules {
            let Some(SignatureItem::SigModule(_, md, _)) = rewritten_sig.get_mut(idx) else {
                continue;
            };
            md.md_type = apply_package_constraints_to_module_type(
                env,
                &md.md_type,
                &nested,
                None,
                pers_env,
                ctx,
            )?;
        }

        Some(crate::types::decl::ModuleType::MtySignature(
            std::sync::Arc::new(rewritten_sig),
        ))
    }

    fn resolve_path_package_constraints(
        env: &Env,
        path: &Path,
        constraints: &[PackageConstraint],
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &crate::types::context::TypeContext,
        visiting: &mut HashSet<Path>,
    ) -> Option<crate::types::decl::ModuleType> {
        if !visiting.insert(*path) {
            return None;
        }

        let result = match path.view() {
            PathView::Pident(id) => {
                let ident_path = Path::pident(*id);
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
                        |components| {
                            rewrite_package_constraints_over_sig(
                                components.signature(),
                                constraints,
                            )
                        },
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
            PathView::Pdot(parent, name, _) => {
                if let Some((rewritten_sig, nested_modules)) =
                    crate::types::typecore::with_resolved_module_components_for_path(
                        path,
                        env,
                        pers_env,
                        ctx,
                        |components| {
                            rewrite_package_constraints_over_sig(
                                components.signature(),
                                constraints,
                            )
                        },
                    )
                {
                    finish_rewritten_package_sig(env, rewritten_sig, nested_modules, pers_env, ctx)
                } else if let Some((_, mtd)) =
                    crate::types::typecore::lookup_modtype_in_resolved_path(
                        parent,
                        name.as_str(),
                        env,
                        pers_env,
                        ctx,
                    )
                {
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
                    finish_rewritten_package_sig(env, rewritten_sig, nested_modules, pers_env, ctx)
                }
            }
            PathView::Papply(_, _) => None,
        };

        visiting.remove(path);
        result
    }

    fn apply_package_constraints_impl(
        env: &Env,
        mty: &crate::types::decl::ModuleType,
        constraints: &[PackageConstraint],
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &crate::types::context::TypeContext,
        visiting: &mut HashSet<Path>,
    ) -> Option<crate::types::decl::ModuleType> {
        use crate::types::decl::ModuleType as DeclMty;

        match mty {
            DeclMty::MtySignature(sig) => {
                let (rewritten_sig, nested_modules) =
                    rewrite_package_constraints_over_sig(sig, constraints);
                finish_rewritten_package_sig(env, rewritten_sig, nested_modules, pers_env, ctx)
            }
            DeclMty::MtyAlias(..) | DeclMty::MtyIdent(_) => {
                let path = mty.ident_or_alias_path().unwrap();
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
pub fn modtype_of_package(
    env: &Env,
    package_path: &Path,
    package_lids: &[Longident],
    package_args: &[TypeExprRef],
    arena: &ParseArena,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::ModuleType as DeclMty;

    if package_lids.len() != package_args.len() {
        return None;
    }

    let constraints: Vec<PackageConstraint> = package_lids
        .iter()
        .zip(package_args.iter())
        .map(|(lid, ty)| (flatten_package_constraint_path(lid, arena, ctx), *ty))
        .collect();

    let base_mty = match package_path.view() {
        PathView::Pident(_) => env.lookup_modtype(package_path).ok()?.mtd_type.clone()?,
        PathView::Pdot(parent, modtype_name, _) => {
            crate::types::typecore::lookup_modtype_in_resolved_path(
                parent,
                modtype_name,
                env,
                pers_env,
                ctx,
            )
            .and_then(|(_, mtd)| mtd.mtd_type)
            .or_else(|| env.lookup_modtype(package_path).ok()?.mtd_type.clone())?
        }
        PathView::Papply(_, _) => return None,
    };
    if package_lids.is_empty() {
        // OCaml compiler/ml/typemod.ml:1176-1183 calls Env.find_modtype
        // before returning `Mty_ident p` for unconstrained packages. Preserve
        // that force point so package unpacking observes local module-type
        // signatures before `Env.enter_module`, not later through member lookup.
        return Some(DeclMty::MtyIdent(*package_path));
    }
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
    match mty.ident_or_alias_path().map(|p| p.view()) {
        Some(PathView::Pdot(parent, _, _)) => Some(*parent),
        _ => None,
    }
}

fn cannot_scrape_alias_path_for_module_type<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    mty: &crate::types::decl::ModuleType,
) -> Option<Path> {
    use crate::types::decl::ModuleType as DeclMty;

    let DeclMty::MtyAlias(_, path) = mty else {
        return None;
    };
    crate::types::typecore::alias_target_for_module_path(
        path,
        env,
        &mut tctx.persistent_env,
        tctx.type_ctx,
    )
    .or(Some(**path))
}

/// `transl_modtype` of the module type `Typetexp.create_package_mty true`
/// builds for a package type (typetexp.ml:160-188, 572-576): the package's
/// module type with one nested `Pmty_with` per sorted field, each a
/// `Pwith_type` of an abstract declaration without manifest, translated
/// between `narrow ()` and `widen` (typetexp.ml:218-222).
pub(crate) fn transl_fake_package_modtype<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    package_path: &Path,
    fields: &[Located<LidentIdx>],
    loc: LocIdx,
) -> TypeModResult<()> {
    let ctx = tctx.type_ctx;
    let global_level = ctx.increase_global_level();
    let type_variables = tctx.type_variables.clone();
    let mut result = Ok(());
    let mut mty = crate::types::decl::ModuleType::MtyIdent(*package_path);
    for field in fields {
        let lid = tctx.resolve_lid(field.txt).clone();
        let sdecl = crate::parser::ast::TypeDeclaration {
            ptype_name: Located {
                txt: lid.last_idx(),
                loc: field.loc,
            },
            ptype_params: vec![],
            ptype_cstrs: vec![],
            ptype_kind: crate::parser::ast::TypeKind::Ptype_abstract,
            ptype_private: crate::parser::ast::PrivateFlag::Public,
            ptype_manifest: None,
            ptype_origin: crate::parser::ast::TypeDeclarationOrigin::Declared,
            ptype_attributes: crate::parser::ast::Attributes(None),
            ptype_loc: loc,
        };
        let constr = crate::parser::ast::WithConstraint::Pwith_type(*field, sdecl);
        let merged = extract_sig(tctx, env, loc, &mty)
            .and_then(|sg| merge_constraint(tctx, env, arena, loc, &sg, &constr));
        match merged {
            Ok((_, sg)) => {
                mty = crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(sg));
                crate::cmi::persistent_env::freshen_module_type_bound_idents(&mut mty, ctx);
            }
            Err(error) => {
                result = Err(error);
                break;
            }
        }
    }
    ctx.restore_global_level(global_level);
    tctx.type_variables = type_variables;
    result
}

/// `Mtype.get_arg_paths` (mtype.ml:273-279) with `get_prefixes`
/// (mtype.ml:269-271): the arguments of the functor applications in `path`
/// and their prefixes.
fn mtype_get_arg_paths(path: &Path, out: &mut Vec<Path>) {
    fn get_prefixes(path: &Path, out: &mut Vec<Path>) {
        match &path.view() {
            PathView::Pident(_) => {}
            PathView::Pdot(prefix, _, _) | PathView::Papply(prefix, _) => {
                push_same_path(out, prefix);
                get_prefixes(prefix, out);
            }
        }
    }
    match &path.view() {
        PathView::Pident(_) => {}
        PathView::Pdot(prefix, _, _) => mtype_get_arg_paths(prefix, out),
        PathView::Papply(functor, argument) => {
            push_same_path(out, argument);
            get_prefixes(argument, out);
            mtype_get_arg_paths(functor, out);
            mtype_get_arg_paths(argument, out);
        }
    }
}

/// Add `path` to a `Path_set` kept as a list.
fn push_same_path(out: &mut Vec<Path>, path: &Path) {
    if !out.iter().any(|known| known.same(path)) {
        out.push(*path);
    }
}

/// `Btype.type_iterators` with `it_path` and `it_signature_item` overridden
/// as `Mtype.collect_arg_paths` does (mtype.ml:300-328). The marks of
/// `it_type_expr` only stop the walk at visited nodes, and
/// `unmark_iterators` removes them again; a visited set does both.
struct CollectArgPaths<'c> {
    ctx: &'c crate::types::context::TypeContext,
    visited: HashSet<TypeExprRef>,
    paths: Vec<Path>,
    subst: Vec<(Path, Ident)>,
    bindings: Vec<(Ident, Path)>,
}

impl CollectArgPaths<'_> {
    fn it_path(&mut self, path: &Path) {
        mtype_get_arg_paths(path, &mut self.paths);
    }

    fn it_type_expr(&mut self, ty: TypeExprRef) {
        use crate::types::type_expr::TypeDesc;
        let ty = self.ctx.repr(ty);
        if !self.visited.insert(ty) {
            return;
        }
        let mut children = Vec::new();
        crate::types::iter_type_expr(self.ctx, ty, |child| children.push(child));
        for child in children {
            self.it_type_expr(child);
        }
        let path = match &*self.ctx.get_desc(ty) {
            TypeDesc::Tconstr { path, .. } | TypeDesc::Tpackage { path, .. } => Some(*path),
            TypeDesc::Tvariant(row) => crate::types::btype::row_repr(self.ctx, &self.ctx.row_desc(*row))
                .row_name
                .map(|(path, _)| path),
            _ => None,
        };
        if let Some(path) = path {
            self.it_path(&path);
        }
    }

    fn it_type_declaration(&mut self, td: &crate::types::decl::TypeDeclaration) {
        use crate::types::TypeKind;
        for &param in &td.type_params {
            self.it_type_expr(param);
        }
        if let Some(manifest) = td.type_manifest {
            self.it_type_expr(manifest);
        }
        match &td.type_kind {
            TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
            TypeKind::TypeVariant(constructors, _) => {
                for cd in constructors.iter() {
                    let mut args = Vec::new();
                    crate::types::btype::iter_type_expr_cstr_args(&cd.cd_args, |ty| args.push(ty));
                    for arg in args {
                        self.it_type_expr(arg);
                    }
                    if let Some(res) = cd.cd_res {
                        self.it_type_expr(res);
                    }
                }
            }
            TypeKind::TypeRecord(labels, _) => {
                for label in labels.iter() {
                    self.it_type_expr(label.ld_type);
                }
            }
        }
    }

    fn it_signature_item(&mut self, item: &crate::types::decl::SignatureItem) {
        use crate::types::decl::{ModuleType as DeclMty, SignatureItem};
        match item {
            SignatureItem::SigValue(_, vd) => self.it_type_expr(vd.val_type),
            SignatureItem::SigType(_, td, _) => self.it_type_declaration(td),
            SignatureItem::SigTypext(_, ext, _) => {
                self.it_path(&ext.ext_type_path);
                for &param in &ext.ext_type_params {
                    self.it_type_expr(param);
                }
                let mut args = Vec::new();
                crate::types::btype::iter_type_expr_cstr_args(&ext.ext_args, |ty| args.push(ty));
                for arg in args {
                    self.it_type_expr(arg);
                }
                if let Some(ret) = ext.ext_ret_type {
                    self.it_type_expr(ret);
                }
            }
            SignatureItem::SigModule(_, md, _) => self.it_module_type(&md.md_type),
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(mty) = &mtd.mtd_type {
                    self.it_module_type(mty);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
        if let SignatureItem::SigModule(id, md, _) = item {
            match &md.md_type {
                DeclMty::MtyAlias(_, path) => self.bindings.push((*id, **path)),
                DeclMty::MtySignature(sg) => {
                    for inner in sg.iter() {
                        if let SignatureItem::SigModule(inner_id, _, _) = inner {
                            self.subst.push((
                                Path::pdot_pos(Path::pident(*id), inner_id.name(), -1),
                                *inner_id,
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn it_module_type(&mut self, mty: &crate::types::decl::ModuleType) {
        use crate::types::decl::ModuleType as DeclMty;
        match mty {
            DeclMty::MtyIdent(path) => self.it_path(path),
            DeclMty::MtyAlias(_, path) => self.it_path(path),
            DeclMty::MtySignature(sg) => {
                for item in sg.iter() {
                    self.it_signature_item(item);
                }
            }
            DeclMty::MtyFunctor {
                param_type, result, ..
            } => {
                if let Some(param_type) = param_type {
                    self.it_module_type(param_type);
                }
                self.it_module_type(result);
            }
        }
    }

    /// `rollback_path subst p` (mtype.ml:281-288).
    fn rollback_path(&self, path: &Path) -> Path {
        if let Some((_, id)) = self.subst.iter().rev().find(|(key, _)| key.same(path)) {
            return Path::pident(*id);
        }
        match &path.view() {
            PathView::Pident(_) | PathView::Papply(..) => *path,
            PathView::Pdot(prefix, name, pos) => {
                let rolled = self.rollback_path(prefix);
                if prefix.same(&rolled) {
                    *path
                } else {
                    self.rollback_path(&Path::pdot_pos(rolled, *name, *pos))
                }
            }
        }
    }

    /// `collect_ids subst bindings p` (mtype.ml:290-298).
    fn collect_ids(&self, path: &Path, out: &mut Vec<Ident>) {
        if let PathView::Pident(id) = self.rollback_path(path).view() {
            if let Some((_, bound)) = self.bindings.iter().rev().find(|(bid, _)| bid.same(id)) {
                self.collect_ids(bound, out);
            }
            if !out.iter().any(|known| known.same(id)) {
                out.push(*id);
            }
        }
    }
}

/// `Mtype.collect_arg_paths mty` (mtype.ml:300-328): the module identifiers
/// that functor applications in `mty` take as arguments, which
/// `remove_aliases` must keep as aliases.
fn mtype_collect_arg_paths(
    ctx: &crate::types::context::TypeContext,
    mty: &crate::types::decl::ModuleType,
) -> Vec<Ident> {
    let mut it = CollectArgPaths {
        ctx,
        visited: HashSet::default(),
        paths: Vec::new(),
        subst: Vec::new(),
        bindings: Vec::new(),
    };
    it.it_module_type(mty);
    let mut ids = Vec::new();
    for path in &it.paths {
        it.collect_ids(path, &mut ids);
    }
    ids
}

/// `Mtype.remove_aliases env mty` (mtype.ml:330-358).
fn mtype_remove_aliases(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    mty: &crate::types::decl::ModuleType,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::{ModuleType as DeclMty, SignatureItem};

    fn remove_aliases(
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        excl: &[Ident],
        mty: &DeclMty,
    ) -> DeclMty {
        match mty {
            DeclMty::MtySignature(sg) => {
                DeclMty::MtySignature(std::sync::Arc::new(remove_aliases_sig(tctx, env, excl, sg)))
            }
            DeclMty::MtyAlias(..) => {
                // `Env.scrape_alias env mty`, then again until it stays.
                match scrape_alias_module_type(mty, env, &mut tctx.persistent_env, tctx.type_ctx) {
                    Some(scraped) if scraped != *mty => remove_aliases(tctx, env, excl, &scraped),
                    _ => mty.clone(),
                }
            }
            other => other.clone(),
        }
    }

    fn remove_aliases_sig(
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        excl: &[Ident],
        sg: &[SignatureItem],
    ) -> crate::types::decl::Signature {
        let mut env = env.clone();
        let mut out = Vec::with_capacity(sg.len());
        for item in sg {
            match item {
                SignatureItem::SigModule(id, md, rs) => {
                    let md_type = match &md.md_type {
                        DeclMty::MtyAlias(..) if excl.iter().any(|ex| ex.same(id)) => {
                            md.md_type.clone()
                        }
                        mty => remove_aliases(tctx, &env, excl, mty),
                    };
                    let item = SignatureItem::SigModule(
                        *id,
                        crate::types::decl::ModuleDeclaration {
                            md_type,
                            ..md.clone()
                        },
                        *rs,
                    );
                    // `Env.add_module id mty env`.
                    crate::types::includemod::add_sig_item_to_env(tctx.type_ctx, &item, &mut env);
                    out.push(item);
                }
                SignatureItem::SigModtype(..) => {
                    crate::types::includemod::add_sig_item_to_env(tctx.type_ctx, item, &mut env);
                    out.push(item.clone());
                }
                _ => out.push(item.clone()),
            }
        }
        out
    }

    let excl = mtype_collect_arg_paths(tctx.type_ctx, mty);
    remove_aliases(tctx, env, &excl, mty)
}

/// `Typetexp.find_module env loc lid`: the module's path and declaration,
/// whose module type is the declaration's own (env.ml:865-882).
fn find_module_declaration_for_lid<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    loc: LocIdx,
    lid: &Longident,
) -> TypeModResult<(Path, crate::types::decl::ModuleDeclaration)> {
    let unbound = |tctx: &mut TypeCheckContext<'a>| {
        TypeModError::CoreError(crate::types::typecore::unbound_module_lookup_error(
            tctx, env, loc, lid,
        ))
    };
    let Some(path) =
        lookup_module_path_by_lid(lid, arena, env, &mut tctx.persistent_env, tctx.type_ctx)
    else {
        return Err(unbound(tctx));
    };
    let decl = match &path.view() {
        PathView::Pident(id) => match env.lookup_module(&path) {
            Ok(md) => Some(md.clone()),
            Err(_) => tctx
                .persistent_env
                .as_mut()
                .and_then(|pers| pers.get_renamed_sig(id.name(), tctx.type_ctx))
                .map(|sig| {
                    empty_module_decl(crate::types::decl::ModuleType::MtySignature(
                        std::sync::Arc::new(sig),
                    ))
                }),
        },
        PathView::Pdot(parent, name, _) => crate::types::typecore::lookup_module_in_resolved_path(
            parent,
            name,
            env,
            &mut tctx.persistent_env,
            tctx.type_ctx,
        )
        .map(|(_, _, md)| md),
        PathView::Papply(..) => None,
    };
    match decl {
        Some(decl) => Ok((path, decl)),
        None => Err(unbound(tctx)),
    }
}

/// `Mtype.strengthen_decl ~aliasable:false env md p` (mtype.ml:93-97).
fn strengthen_decl_non_aliasable(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    md: crate::types::decl::ModuleDeclaration,
    path: &Path,
) -> crate::types::decl::ModuleDeclaration {
    match &md.md_type {
        crate::types::decl::ModuleType::MtyAlias(..) => md,
        mty => crate::types::decl::ModuleDeclaration {
            md_type: crate::types::ctype::strengthen_module_type_for_non_aliasable_path(
                ctx, env, path, mty,
            ),
            ..md
        },
    }
}

/// `update_rec_next rs rem` (typemod.ml:139-146).
fn update_rec_next(
    rs: crate::types::decl::RecStatus,
    rem: &mut [crate::types::decl::SignatureItem],
) {
    use crate::types::decl::{RecStatus, SignatureItem};
    if rs == RecStatus::TrecNext {
        return;
    }
    match rem.first_mut() {
        Some(SignatureItem::SigType(_, _, next @ RecStatus::TrecNext))
        | Some(SignatureItem::SigModule(_, _, next @ RecStatus::TrecNext)) => *next = rs,
        _ => {}
    }
}

/// The `Pwith_module` and `Pwith_modsubst` cases of OCaml
/// `Typemod.merge_constraint initial_env loc sg constr` (typemod.ml:287-470):
/// walk the signature along the constrained path, adding each item passed
/// to the environment (`Env.add_item`), and replace the module it names by
/// the strengthened replacement checked with `Includemod.modtypes`, or drop
/// it for a destructive substitution, which `Subst.signature` then applies.
#[allow(clippy::too_many_arguments)]
/// `extract_sig` (typemod.ml:75-79): the signature `Env.scrape_alias` gives.
fn extract_sig<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    loc: LocIdx,
    mty: &crate::types::decl::ModuleType,
) -> TypeModResult<crate::types::decl::Signature> {
    use crate::types::decl::ModuleType as DeclMty;

    if !matches!(mty, DeclMty::MtyAlias(..))
        && let Some(sg) =
            resolve_mod_type_to_sig(mty, Some(env), &mut tctx.persistent_env, tctx.type_ctx)
    {
        return Ok(sg);
    }
    match scrape_alias_module_type(mty, env, &mut tctx.persistent_env, tctx.type_ctx) {
        Some(DeclMty::MtySignature(sg)) => Ok(std::sync::Arc::unwrap_or_clone(sg)),
        Some(DeclMty::MtyAlias(_, path)) => {
            Err(TypeModError::CannotScrapeAlias { loc, path: *path })
        }
        Some(_) => Err(TypeModError::CoreError(TypeCoreError::SignatureExpected {
            loc,
        })),
        None => match cannot_scrape_alias_path_for_module_type(tctx, env, mty) {
            Some(path) => Err(TypeModError::CannotScrapeAlias { loc, path }),
            None => Err(TypeModError::CoreError(TypeCoreError::SignatureExpected {
                loc,
            })),
        },
    }
}

/// `path_concat` (typemod.ml:68-72).
fn path_concat(head: &Ident, path: &Path) -> Path {
    match &path.view() {
        PathView::Pident(tail) => Path::pdot(Path::pident(*head), tail.name()),
        PathView::Pdot(prefix, name, pos) => {
            Path::pdot_pos(path_concat(head, prefix), *name, *pos)
        }
        PathView::Papply(..) => unreachable!("path_concat of a functor application"),
    }
}

/// `Typedecl.is_fixed_type` (typedecl.ml:122-135).
fn sdecl_is_fixed_type(arena: &ParseArena, sdecl: &crate::parser::ast::TypeDeclaration) -> bool {
    sdecl.ptype_manifest.is_some_and(|manifest| {
        type_decl_is_fixed_type(arena, sdecl, arena.get_core_type(manifest))
    })
}

/// `Typedecl.transl_with_constraint` (typedecl.ml:1991-2086): the
/// declaration `sdecl` gives the signature's type `id`, whose declaration is
/// `orig_decl`; `row_path` is the `#row` type of a fixed private row.
#[allow(clippy::too_many_arguments)]
fn transl_with_constraint<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    id: Ident,
    row_path: Option<Path>,
    orig_decl: &crate::types::decl::TypeDeclaration,
    sdecl: &crate::parser::ast::TypeDeclaration,
) -> TypeModResult<TypedTypeDeclaration> {
    use crate::types::type_expr::TypeDesc;

    let ctx = tctx.type_ctx;
    crate::types::typecore::mark_type_used(
        ctx,
        env,
        id.name(),
        ctx.resolve_loc(orig_decl.type_loc),
    );
    tctx.reset_type_variables();
    ctx.begin_def();
    let (tparams, params) = translate_type_declaration_params(tctx, arena, &sdecl.ptype_params)?;
    let orig_decl = crate::types::ctype::instance_declaration(ctx, orig_decl);
    let arity_ok = params.len() == orig_decl.type_arity as usize;
    if arity_ok {
        for (&param, &orig_param) in params.iter().zip(orig_decl.type_params.iter()) {
            crate::types::unify_var(ctx, &mut tctx.unify_state, param, orig_param).map_err(
                |err| TypeModError::InconsistentConstraint {
                    loc: sdecl.ptype_loc,
                    trace: match err {
                        crate::types::TypeError::Unify(trace) => trace,
                        _ => vec![(param, orig_param)],
                    },
                },
            )?;
        }
    }
    let mut constraints = Vec::with_capacity(sdecl.ptype_cstrs.len());
    for (sty, sty2, cstr_loc) in &sdecl.ptype_cstrs {
        let (cty, ty) = transl_type(tctx, env, arena.get_core_type(*sty))?;
        let (cty2, ty2) = transl_type(tctx, env, arena.get_core_type(*sty2))?;
        crate::types::unify(ctx, &mut tctx.unify_state, ty, ty2).map_err(|err| {
            TypeModError::InconsistentConstraint {
                loc: *cstr_loc,
                trace: match err {
                    crate::types::TypeError::Unify(trace) => trace,
                    _ => vec![(ty, ty2)],
                },
            }
        })?;
        constraints.push((cty, cty2, *cstr_loc));
    }
    let is_fixed = sdecl_is_fixed_type(arena, sdecl);
    let (tman, man) = match sdecl.ptype_manifest {
        None => (None, None),
        Some(sty) => {
            let sty = arena.get_core_type(sty);
            // `transl_simple_type env no_row sty`, `no_row = not is_fixed`.
            let (cty, ty) = if is_fixed {
                transl_type(tctx, env, sty)?
            } else {
                crate::types::typecore::transl_type_fixed(tctx, env, sty)?
            };
            (Some(cty), Some(ty))
        }
    };
    let sdecl_private = parser_private_to_type_private(sdecl.ptype_private);
    let orig_abstract = matches!(orig_decl.type_kind, crate::types::TypeKind::TypeAbstract);
    let priv_ = if sdecl_private == crate::types::PrivateFlag::Private {
        crate::types::PrivateFlag::Private
    } else if arity_ok && !orig_abstract {
        orig_decl.type_private
    } else {
        sdecl_private
    };
    if arity_ok && !orig_abstract && sdecl_private == crate::types::PrivateFlag::Private {
        tctx.report_warning_at(
            tctx.warnings.len(),
            sdecl.ptype_loc,
            Warning::Deprecated {
                message: "spurious use of private".to_string(),
                def_loc: Location::none(),
                use_loc: Location::none(),
                can_be_automigrated: false,
            },
        );
    }
    let (type_kind, type_representation) = if arity_ok && man.is_some() {
        (orig_decl.type_kind.clone(), orig_decl.type_representation)
    } else {
        (
            crate::types::TypeKind::TypeAbstract,
            crate::types::TypeRepresentation::Boxed,
        )
    };
    let type_attributes = parser_attrs_to_decl_attrs(arena, ctx, &sdecl.ptype_attributes);
    let mut decl = crate::types::TypeDeclaration {
        type_arity: params.len() as i32,
        type_params: params,
        type_kind,
        type_private: priv_,
        type_manifest: man,
        type_variance: vec![],
        type_newtype_level: None,
        type_loc: tctx.intern_ast_loc(arena, sdecl.ptype_loc),
        type_attributes,
        type_immediate: false,
        type_representation,
        type_shape: crate::types::ValueShape::Unstated,
        type_inlined_types: vec![],
        type_path: Some(Path::pident(id)),
    };
    if let Some(row_path) = &row_path
        && let Some(manifest) = decl.type_manifest
    {
        set_fixed_row(
            ctx,
            env,
            sdecl.ptype_loc,
            row_path,
            &decl.type_params,
            manifest,
        )?;
    }
    // `Ctype.closed_type_decl` (typedecl.ml:2058-2060).
    if let Some(unbound) = find_unbound_type_var_in_type_decl(ctx, &decl) {
        return Err(TypeModError::UnboundTypeVar {
            loc: sdecl.ptype_loc,
            name: type_var_report_name_from_type_expr(ctx, unbound),
            detail: find_unbound_type_var_detail_in_type_decl(ctx, &decl, unbound),
            var: Some(unbound),
        });
    }
    decl.type_shape = crate::types::variant_layout::declaration_shape(ctx, env, &decl)?;
    crate::types::variant_layout::check_manifest_annotation(
        ctx,
        arena.to_location(sdecl.ptype_loc),
        env,
        &decl,
    )?;
    // `name_recursion` (typedecl.ml:1474-1484).
    if is_fixed
        && orig_abstract_kind(&decl.type_kind)
        && decl.type_private == crate::types::PrivateFlag::Private
        && let Some(ty) = decl.type_manifest
    {
        let ty = ctx.repr(ty);
        let level = ctx.get_level(ty);
        // `newty2 ty.level ty.desc` shares `ty`'s descriptor.
        let ty2 = ctx.alloc_type_at_level(ctx.get_desc(ty).into_desc(), level);
        if crate::types::ctype::deep_occur(ctx, ty, ty2) {
            let td = TypeDesc::Tconstr {
                path: Path::pident(id),
                args: ctx.new_type_list(&decl.type_params),
                abbrev: ctx.alloc_abbrev_nil(),
            };
            crate::types::ctype::link_type(ctx, ty, ctx.alloc_type_at_level(td, level));
            decl.type_manifest = Some(ty2);
        }
    }
    let typed_kind = TypedTypeKind::Ttype_abstract;
    let mut typed = TypedTypeDeclaration {
        typ_id: id,
        typ_name: crate::parse_arena::Located {
            txt: arena.get_string(sdecl.ptype_name.txt).to_string(),
            loc: sdecl.ptype_name.loc,
        },
        typ_params: tparams.into_iter().map(|(ct, v)| (tctx.typed.push_core_type(ct), v)).collect(),
        typ_type: decl,
        typ_cstrs: constraints.into_iter().map(|(a, b, loc)| (tctx.typed.push_core_type(a), tctx.typed.push_core_type(b), loc)).collect(),
        typ_kind: typed_kind,
        typ_private: sdecl.ptype_private,
        typ_manifest: tman.map(|ct| tctx.typed.push_core_type(ct)),
        typ_loc: sdecl.ptype_loc,
        typ_attributes: sdecl.ptype_attributes.clone(),
    };
    // `compute_variance_decl env true decl (add_injectivity ..., loc)`.
    let required: Vec<(bool, bool, bool)> = sdecl
        .ptype_params
        .iter()
        .map(|(_, variance)| parser_variance_requirement(*variance))
        .collect();
    let type_variance =
        crate::types::ctype::compute_variance_decl(ctx, env, &typed.typ_type, &required);
    check_type_decl_variance_requirements(&tctx.typed, ctx, env, sdecl, &typed, &type_variance)?;
    let type_immediate = compute_type_immediacy(
        ctx,
        env,
        &typed.typ_type.type_kind,
        typed.typ_type.type_manifest,
        &typed.typ_type.type_attributes,
        typed.typ_type.type_representation,
    );
    typed.typ_type.type_variance = type_variance;
    typed.typ_type.type_immediate = type_immediate;
    ctx.end_def();
    // `generalize_decl` (typedecl.ml:792-797).
    for &param in &typed.typ_type.type_params {
        crate::types::ctype::generalize(ctx, param);
    }
    crate::types::btype::iter_type_expr_kind(&typed.typ_type.type_kind, |ty| {
        crate::types::ctype::generalize(ctx, ty);
    });
    if let Some(manifest) = typed.typ_type.type_manifest {
        crate::types::ctype::generalize(ctx, manifest);
    }
    Ok(typed)
}

fn orig_abstract_kind(kind: &crate::types::TypeKind) -> bool {
    matches!(kind, crate::types::TypeKind::TypeAbstract)
}

/// `check_type_decl` (typemod.ml:128-137).
#[allow(clippy::too_many_arguments)]
fn check_type_decl(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    merge_loc: LocIdx,
    lid: &Longident,
    id: Ident,
    row_id: Option<Ident>,
    newdecl: &crate::types::decl::TypeDeclaration,
    decl: &crate::types::decl::TypeDeclaration,
    rs: crate::types::decl::RecStatus,
    rem: &[crate::types::decl::SignatureItem],
) -> TypeModResult<()> {
    let ctx = tctx.type_ctx;
    // `Env.add_type ~check:true` (env.ml:1561-1566).
    let mut env = env.clone();
    tctx.check_type_usage(id.name(), ctx.resolve_loc(newdecl.type_loc), loc);
    env.store_type(ctx, id, newdecl.clone());
    if let Some(row_id) = row_id {
        env.store_type(ctx, row_id, newdecl.clone());
    }
    // `add_rec_types` (typemod.ml:273-276).
    if rs != crate::types::decl::RecStatus::TrecNot {
        for item in rem {
            let crate::types::decl::SignatureItem::SigType(
                rec_id,
                rec_decl,
                crate::types::decl::RecStatus::TrecNext,
            ) = item
            else {
                break;
            };
            tctx.check_type_usage(rec_id.name(), ctx.resolve_loc(rec_decl.type_loc), loc);
            env.store_type(ctx, *rec_id, rec_decl.clone());
        }
    }
    let mut inclusion_warnings = Vec::new();
    let inclusion = crate::types::includemod::type_declarations(
        ctx,
        &env,
        id,
        newdecl,
        decl,
        &mut inclusion_warnings,
    );
    report_inclusion_warnings(tctx, loc, inclusion_warnings);
    crate::types::includemod::escaped(ctx, inclusion)?.map_err(|error| {
        // `merge_constraint` reports the inclusion error at its own location
        // (typemod.ml:470-471).
        TypeModError::WithMismatch {
            loc: merge_loc,
            lid: lid.clone(),
            error: Box::new(error),
        }
    })?;
    let mut coherence_warnings = Vec::new();
    let coherence =
        check_type_declaration_coherence(ctx, &env, loc, &id, newdecl, &mut coherence_warnings);
    report_inclusion_warnings(tctx, loc, coherence_warnings);
    coherence
}

/// A `with` constraint as `merge_constraint` returns it: the constrained
/// item's path, its longident, and the typed constraint.
type MergedConstraint = (
    Path,
    Located<LidentIdx>,
    crate::types::typedtree::WithConstraint,
);

/// `merge_constraint` (typemod.ml:288-473): merges one `with` constraint into
/// the signature `sg`, returning the typed constraint and the new signature.
fn merge_constraint<'a>(
    tctx: &mut TypeCheckContext<'a>,
    initial_env: &Env,
    arena: &'a ParseArena,
    loc: LocIdx,
    sg: &[crate::types::decl::SignatureItem],
    constr: &crate::parser::ast::WithConstraint,
) -> TypeModResult<(MergedConstraint, crate::types::decl::Signature)> {
    use crate::parser::ast::WithConstraint as PWith;
    use crate::types::decl::{ModuleType as DeclMty, SignatureItem};
    use crate::types::typedtree::WithConstraint as TWith;

    let (lid_loc, destructive) = match constr {
        PWith::Pwith_type(lid, _) | PWith::Pwith_module(lid, _) => (*lid, false),
        PWith::Pwith_typesubst(lid, _) | PWith::Pwith_modsubst(lid, _) => (*lid, true),
    };
    let lid = tctx.resolve_lid(lid_loc.txt).clone();

    struct Merge<'c> {
        initial_env: &'c Env,
        loc: LocIdx,
        lid: &'c Longident,
        constr: &'c PWith,
        real_ids: Vec<Path>,
    }

    fn merge<'a>(
        tctx: &mut TypeCheckContext<'a>,
        arena: &'a ParseArena,
        m: &mut Merge<'_>,
        env: &Env,
        sg: &[SignatureItem],
        names: &[String],
        mut row_id: Option<Ident>,
    ) -> TypeModResult<((Path, TWith), Vec<SignatureItem>)> {
        let loc = m.loc;
        let mut env = env.clone();
        for (index, item) in sg.iter().enumerate() {
            let rem = &sg[index + 1..];
            let prefix = || {
                sg[..index]
                    .iter()
                    .filter(|it| !is_row_item_of(it, row_id))
                    .cloned()
            };
            let single = (names.len() == 1).then(|| names[0].as_str());
            match (item, single, m.constr) {
                (SignatureItem::SigType(id, decl, rs), Some(s), PWith::Pwith_type(_, sdecl))
                    if id.name() == s
                        && matches!(
                            sdecl.ptype_kind,
                            crate::parser::ast::TypeKind::Ptype_abstract
                        )
                        && sdecl_is_fixed_type(arena, sdecl) =>
                {
                    let ctx = tctx.type_ctx;
                    let decl_row = crate::types::TypeDeclaration {
                        type_params: sdecl
                            .ptype_params
                            .iter()
                            .map(|_| ctx.new_generic_var(None))
                            .collect(),
                        type_arity: sdecl.ptype_params.len() as i32,
                        type_kind: crate::types::TypeKind::TypeAbstract,
                        type_private: crate::types::PrivateFlag::Private,
                        type_manifest: None,
                        type_variance: sdecl
                            .ptype_params
                            .iter()
                            .map(|(_, v)| {
                                let (c, n, _) = parser_variance_requirement(*v);
                                TypesVariance::null()
                                    .set(crate::types::VarianceFlag::MayPos, !n)
                                    .set(crate::types::VarianceFlag::MayNeg, !c)
                                    .set(crate::types::VarianceFlag::MayWeak, !c)
                                    .set(crate::types::VarianceFlag::Inj, false)
                            })
                            .collect(),
                        type_newtype_level: None,
                        type_loc: tctx.intern_ast_loc(arena, sdecl.ptype_loc),
                        type_attributes: vec![],
                        type_immediate: false,
                        type_representation: crate::types::TypeRepresentation::Boxed,
                        type_shape: crate::types::ValueShape::Unstated,
                        type_inlined_types: vec![],
                        type_path: None,
                    };
                    let id_row = ctx.create_ident(format!("{s}#row"));
                    let mut row_env = m.initial_env.clone();
                    let mut decl_row_with_path = decl_row.clone();
                    decl_row_with_path.type_path = Some(Path::pident(id_row));
                    row_env.store_type(tctx.type_ctx, id_row, decl_row_with_path);
                    let tdecl = transl_with_constraint(
                        tctx,
                        &row_env,
                        arena,
                        *id,
                        Some(Path::pident(id_row)),
                        decl,
                        sdecl,
                    )?;
                    let newdecl = tdecl.typ_type.clone();
                    check_type_decl(
                        tctx,
                        &env,
                        sdecl.ptype_loc,
                        loc,
                        m.lid,
                        *id,
                        row_id,
                        &newdecl,
                        decl,
                        *rs,
                        rem,
                    )?;
                    let mut decl_row = decl_row;
                    decl_row.type_params = newdecl.type_params.clone();
                    decl_row.type_path = Some(Path::pident(id_row));
                    let rs2 = if *rs == crate::types::decl::RecStatus::TrecFirst {
                        crate::types::decl::RecStatus::TrecNot
                    } else {
                        *rs
                    };
                    let mut out: Vec<SignatureItem> = prefix().collect();
                    out.push(SignatureItem::SigType(
                        id_row,
                        std::sync::Arc::new(decl_row),
                        rs2,
                    ));
                    out.push(SignatureItem::SigType(
                        *id,
                        std::sync::Arc::new(newdecl),
                        *rs,
                    ));
                    out.extend(rem.iter().cloned());
                    return Ok(((Path::pident(*id), TWith::Twith_type(tdecl)), out));
                }
                (SignatureItem::SigType(id, decl, rs), Some(s), PWith::Pwith_type(_, sdecl))
                    if id.name() == s =>
                {
                    let tdecl =
                        transl_with_constraint(tctx, m.initial_env, arena, *id, None, decl, sdecl)?;
                    let newdecl = tdecl.typ_type.clone();
                    check_type_decl(
                        tctx,
                        &env,
                        sdecl.ptype_loc,
                        loc,
                        m.lid,
                        *id,
                        row_id,
                        &newdecl,
                        decl,
                        *rs,
                        rem,
                    )?;
                    let mut out: Vec<SignatureItem> = prefix().collect();
                    out.push(SignatureItem::SigType(
                        *id,
                        std::sync::Arc::new(newdecl),
                        *rs,
                    ));
                    out.extend(rem.iter().cloned());
                    return Ok(((Path::pident(*id), TWith::Twith_type(tdecl)), out));
                }
                (
                    SignatureItem::SigType(id, _, _),
                    Some(s),
                    PWith::Pwith_type(..) | PWith::Pwith_typesubst(..),
                ) if id.name() == format!("{s}#row") => {
                    // The `#row` item is dropped; the declaration after it is
                    // merged with it as `row_id`.
                    row_id = Some(*id);
                    continue;
                }
                (
                    SignatureItem::SigType(id, decl, rs),
                    Some(s),
                    PWith::Pwith_typesubst(_, sdecl),
                ) if id.name() == s => {
                    let tdecl =
                        transl_with_constraint(tctx, m.initial_env, arena, *id, None, decl, sdecl)?;
                    let newdecl = tdecl.typ_type.clone();
                    check_type_decl(
                        tctx,
                        &env,
                        sdecl.ptype_loc,
                        loc,
                        m.lid,
                        *id,
                        row_id,
                        &newdecl,
                        decl,
                        *rs,
                        rem,
                    )?;
                    m.real_ids = vec![Path::pident(*id)];
                    let mut rem = rem.to_vec();
                    update_rec_next(*rs, &mut rem);
                    let mut out: Vec<SignatureItem> = prefix().collect();
                    out.extend(rem);
                    return Ok(((Path::pident(*id), TWith::Twith_typesubst(tdecl)), out));
                }
                (
                    SignatureItem::SigModule(id, md, rs),
                    Some(s),
                    PWith::Pwith_module(_, rhs) | PWith::Pwith_modsubst(_, rhs),
                ) if id.name() == s => {
                    let modsubst = matches!(m.constr, PWith::Pwith_modsubst(..));
                    let rhs_lid = tctx.resolve_lid(rhs.txt).clone();
                    let (path, rhs_md) =
                        find_module_declaration_for_lid(tctx, m.initial_env, arena, loc, &rhs_lid)?;
                    let rhs_md = if modsubst {
                        rhs_md
                    } else {
                        let md_type = mtype_remove_aliases(tctx, &env, &rhs_md.md_type);
                        crate::types::decl::ModuleDeclaration { md_type, ..rhs_md }
                    };
                    let newmd = strengthen_decl_non_aliasable(tctx.type_ctx, &env, rhs_md, &path);
                    let inclusion = crate::types::includemod::modtypes(
                        tctx.type_ctx,
                        &env,
                        &newmd.md_type,
                        &md.md_type,
                    );
                    crate::types::includemod::escaped(tctx.type_ctx, inclusion)
                        .map_err(TypeModError::CoreError)?
                        .map_err(|error| TypeModError::WithMismatch {
                            loc,
                            lid: m.lid.clone(),
                            error: Box::new(error),
                        })?;
                    let mut out: Vec<SignatureItem> = prefix().collect();
                    let tcstr = if modsubst {
                        m.real_ids = vec![Path::pident(*id)];
                        let mut rem = rem.to_vec();
                        update_rec_next(*rs, &mut rem);
                        out.extend(rem);
                        TWith::Twith_modsubst(path, *rhs)
                    } else {
                        out.push(SignatureItem::SigModule(*id, newmd, *rs));
                        out.extend(rem.iter().cloned());
                        TWith::Twith_module(path, *rhs)
                    };
                    return Ok(((Path::pident(*id), tcstr), out));
                }
                (SignatureItem::SigModule(id, md, rs), _, _)
                    if names.first().is_some_and(|s| id.name() == s.as_str()) =>
                {
                    let inner = extract_sig(tctx, &env, loc, &md.md_type)?;
                    let ((path, tcstr), newsg) =
                        merge(tctx, arena, m, &env, &inner, &names[1..], None)?;
                    let path = path_concat(id, &path);
                    m.real_ids.push(path);
                    let mut out: Vec<SignatureItem> = prefix().collect();
                    out.push(SignatureItem::SigModule(
                        *id,
                        crate::types::decl::ModuleDeclaration {
                            md_type: DeclMty::MtySignature(std::sync::Arc::new(newsg)),
                            ..md.clone()
                        },
                        *rs,
                    ));
                    out.extend(rem.iter().cloned());
                    return Ok(((path, tcstr), out));
                }
                _ => {}
            }
            crate::types::includemod::add_sig_item_to_env(tctx.type_ctx, item, &mut env);
        }
        Err(TypeModError::WithNoComponent {
            loc,
            lid: m.lid.clone(),
        })
    }

    /// Whether `item` is the `#row` item `merge` dropped as `row_id`.
    fn is_row_item_of(item: &SignatureItem, row_id: Option<Ident>) -> bool {
        matches!((item, row_id), (SignatureItem::SigType(id, _, _), Some(row)) if *id == row)
    }

    let names = flatten_package_constraint_path(&lid, arena, tctx.type_ctx);
    let mut m = Merge {
        initial_env,
        loc,
        lid: &lid,
        constr,
        real_ids: Vec::new(),
    };
    let ((path, tcstr), sg) = merge(tctx, arena, &mut m, initial_env, sg, &names, None)?;
    let real_ids = std::mem::take(&mut m.real_ids);
    // `real_ids` holds the removed item's identifier first, then the paths
    // `path_concat` made of it on the way out (`List.rev !real_ids`).
    if destructive {
        debug_assert!(matches!(
            real_ids.first().map(|p| p.view()),
            Some(PathView::Pident(_))
        ));
        if real_ids.len() > 1 {
            check_usage_of_path_of_substituted_item(
                tctx,
                initial_env,
                &real_ids[1..],
                &sg,
                loc,
                &lid,
            )?;
        }
    }
    let sg = match (&tcstr, constr) {
        (TWith::Twith_typesubst(tdecl), PWith::Pwith_typesubst(_, sdecl)) => {
            let replacement = match type_decl_is_alias(arena, sdecl) {
                Some(alias_lid) => {
                    let alias_lid = tctx.resolve_lid(alias_lid.txt).clone();
                    let (replacement, _) = crate::types::typecore::find_type_for_lid(
                        tctx,
                        initial_env,
                        alias_lid_loc(arena, sdecl),
                        &alias_lid,
                    )?;
                    crate::cmi::persistent_env::TypeReplacement::Path(replacement)
                }
                None => {
                    let body = tdecl
                        .typ_type
                        .type_manifest
                        .expect("a type substitution has a manifest");
                    let params = tdecl.typ_type.type_params.clone();
                    if typed_params_are_constrained(tctx.type_ctx, &params) {
                        return Err(TypeModError::WithCannotRemoveConstrainedType { loc });
                    }
                    crate::cmi::persistent_env::TypeReplacement::Function { params, body }
                }
            };
            let types: Vec<_> = real_ids
                .iter()
                .map(|path| {
                    (
                        *path,
                        match &replacement {
                            crate::cmi::persistent_env::TypeReplacement::Path(p) => {
                                crate::cmi::persistent_env::TypeReplacement::Path(*p)
                            }
                            crate::cmi::persistent_env::TypeReplacement::Function {
                                params,
                                body,
                            } => crate::cmi::persistent_env::TypeReplacement::Function {
                                params: params.clone(),
                                body: *body,
                            },
                        },
                    )
                })
                .collect();
            crate::cmi::persistent_env::substitute_signature_with_path_subst(
                &sg,
                &types,
                &[],
                tctx.type_ctx,
            )
        }
        (TWith::Twith_modsubst(real_path, _), _) => {
            let modules: Vec<_> = real_ids.iter().map(|path| (*path, *real_path)).collect();
            crate::cmi::persistent_env::substitute_signature_with_path_subst(
                &sg,
                &[],
                &modules,
                tctx.type_ctx,
            )
        }
        _ => sg,
    };
    Ok(((path, lid_loc, tcstr), sg))
}

/// `type_decl_is_alias` (typemod.ml:260-276): the constructor a type
/// substitution's manifest applies to its own parameters, in order.
fn type_decl_is_alias(
    arena: &ParseArena,
    sdecl: &crate::parser::ast::TypeDeclaration,
) -> Option<Located<LidentIdx>> {
    if !with_type_subst_replacement_is_same_arg_alias(arena, sdecl) {
        return None;
    }
    let manifest = arena.get_core_type(sdecl.ptype_manifest?);
    match &manifest.ptyp_desc {
        crate::parser::ast::CoreTypeDesc::Ptyp_constr(inner) => Some(inner.0),
        _ => None,
    }
}

fn alias_lid_loc(arena: &ParseArena, sdecl: &crate::parser::ast::TypeDeclaration) -> LocIdx {
    sdecl.ptype_manifest.map_or(sdecl.ptype_loc, |manifest| {
        arena.get_core_type(manifest).ptyp_loc
    })
}

pub(crate) fn path_is_strict_prefix(path: &Path, prefix: &Path) -> bool {
    let (Ok((path_head, path_components)), Ok((prefix_head, prefix_components))) =
        (path.flatten(), prefix.flatten())
    else {
        return false;
    };

    path_head.same(prefix_head)
        && prefix_components.len() < path_components.len()
        && path_components
            .iter()
            .zip(prefix_components.iter())
            .all(|(path_component, prefix_component)| path_component == prefix_component)
}

fn check_usage_of_path_of_substituted_item(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    paths: &[Path],
    signature: &[crate::types::decl::SignatureItem],
    loc: LocIdx,
    lid: &Longident,
) -> TypeModResult<()> {
    use crate::types::decl::{
        ConstructorArguments, ModuleType as DeclMty, SignatureItem, TypeDeclaration, TypeKind,
    };
    use crate::types::type_expr::TypeDesc;

    if paths.is_empty() {
        return Ok(());
    }

    fn iter_path_apply(path: &Path, mut f: impl FnMut(&Path, &Path)) {
        fn loop_(path: &Path, f: &mut impl FnMut(&Path, &Path)) {
            match path.view() {
                PathView::Papply(funct, arg) => {
                    f(funct, arg);
                    loop_(funct, f);
                    loop_(arg, f);
                }
                PathView::Pdot(prefix, _, _) => loop_(prefix, f),
                PathView::Pident(_) => {}
            }
        }

        loop_(path, &mut f);
    }

    fn retype_applicative_functor_type(
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        funct: &Path,
        arg: &Path,
    ) -> Result<(), crate::types::includemod::IncludeModError> {
        let Ok(functor_md) = env.lookup_module(funct) else {
            return Ok(());
        };
        let Ok(arg_md) = env.lookup_module(arg) else {
            return Ok(());
        };
        let Some(DeclMty::MtyFunctor {
            param_type: Some(mty_param),
            ..
        }) = scrape_alias_module_type(
            &functor_md.md_type,
            env,
            &mut tctx.persistent_env,
            tctx.type_ctx,
        )
        else {
            return Ok(());
        };
        let aliasable = !env.is_functor_arg_path(arg);
        let mty_arg = if aliasable {
            crate::types::ctype::strengthen_module_type_for_inclusion_path(
                tctx.type_ctx,
                env,
                arg,
                &arg_md.md_type,
            )
        } else {
            crate::types::ctype::strengthen_module_type_for_non_aliasable_path(
                tctx.type_ctx,
                env,
                arg,
                &arg_md.md_type,
            )
        };

        crate::types::includemod::modtypes(tctx.type_ctx, env, &mty_arg, &mty_param).map(|_| ())
    }

    fn check_path(
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        paths: &[Path],
        referenced_path: &Path,
        loc: LocIdx,
        lid: &Longident,
    ) -> TypeModResult<()> {
        let mut result = Ok(());
        iter_path_apply(referenced_path, |funct, arg| {
            if result.is_err() {
                return;
            }
            if paths.iter().any(|path| path_is_strict_prefix(path, arg)) {
                let retyped = retype_applicative_functor_type(tctx, env, funct, arg);
                match crate::types::includemod::escaped(tctx.type_ctx, retyped) {
                    Ok(Ok(())) => {}
                    Ok(Err(error)) => {
                        result = Err(TypeModError::WithMakesApplicativeFunctorIllTyped {
                            loc,
                            lid: lid.clone(),
                            path: *referenced_path,
                            error: Box::new(error),
                        });
                    }
                    Err(error) => result = Err(error.into()),
                }
            }
        });
        result
    }

    fn check_type_expr(
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        paths: &[Path],
        ty: TypeExprRef,
        loc: LocIdx,
        lid: &Longident,
        visited: &mut HashSet<TypeExprRef>,
    ) -> TypeModResult<()> {
        let ty = tctx.type_ctx.repr(ty);
        if !visited.insert(ty) {
            return Ok(());
        }

        enum TypeAction {
            Path(Path, Vec<TypeExprRef>),
            Object(TypeExprRef),
            Variant(crate::types::type_expr::RowDesc),
            Children(Vec<TypeExprRef>),
        }

        let action = {
            let desc = tctx.type_ctx.borrow_desc(ty);
            match &*desc {
                TypeDesc::Tconstr { path, args, .. } => {
                    TypeAction::Path(*path, tctx.type_ctx.type_list(args).to_vec())
                }
                TypeDesc::Tpackage { path, args, .. } => {
                    TypeAction::Path(*path, tctx.type_ctx.type_list(args).to_vec())
                }
                TypeDesc::Tobject { fields } => TypeAction::Object(*fields),
                TypeDesc::Tvariant(row) => TypeAction::Variant(tctx.type_ctx.row_desc(row)),
                _ => {
                    let mut children = Vec::new();
                    crate::types::btype::iter_type_expr(tctx.type_ctx, ty, |child| {
                        children.push(child);
                    });
                    TypeAction::Children(children)
                }
            }
        };

        match action {
            TypeAction::Path(path, args) => {
                check_path(tctx, env, paths, &path, loc, lid)?;
                for arg in args {
                    check_type_expr(tctx, env, paths, arg, loc, lid, visited)?;
                }
            }
            TypeAction::Object(fields) => {
                check_type_expr(tctx, env, paths, fields, loc, lid, visited)?;
            }
            TypeAction::Variant(row) => {
                if let Some((path, args)) = &row.row_name {
                    check_path(tctx, env, paths, path, loc, lid)?;
                    for arg in args {
                        check_type_expr(tctx, env, paths, *arg, loc, lid, visited)?;
                    }
                }
                let mut children = Vec::new();
                crate::types::btype::iter_row(tctx.type_ctx, &row, |child| {
                    children.push(child);
                });
                children.push(crate::types::btype::row_more(tctx.type_ctx, &row));
                for child in children {
                    check_type_expr(tctx, env, paths, child, loc, lid, visited)?;
                }
            }
            TypeAction::Children(children) => {
                for child in children {
                    check_type_expr(tctx, env, paths, child, loc, lid, visited)?;
                }
            }
        }

        Ok(())
    }

    fn check_constructor_arguments(
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        paths: &[Path],
        args: &ConstructorArguments,
        loc: LocIdx,
        lid: &Longident,
    ) -> TypeModResult<()> {
        let mut visited = HashSet::new();
        match args {
            ConstructorArguments::CstrTuple(args) => {
                for ty in args {
                    check_type_expr(tctx, env, paths, *ty, loc, lid, &mut visited)?;
                }
            }
            ConstructorArguments::CstrRecord(labels) => {
                for label in labels {
                    check_type_expr(tctx, env, paths, label.ld_type, loc, lid, &mut visited)?;
                }
            }
        }
        Ok(())
    }

    fn check_type_declaration(
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        paths: &[Path],
        decl: &TypeDeclaration,
        loc: LocIdx,
        lid: &Longident,
    ) -> TypeModResult<()> {
        let mut visited = HashSet::new();
        for param in &decl.type_params {
            check_type_expr(tctx, env, paths, *param, loc, lid, &mut visited)?;
        }
        if let Some(manifest) = decl.type_manifest {
            check_type_expr(tctx, env, paths, manifest, loc, lid, &mut visited)?;
        }
        match &decl.type_kind {
            TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
            TypeKind::TypeRecord(labels, _) => {
                for label in labels {
                    check_type_expr(tctx, env, paths, label.ld_type, loc, lid, &mut visited)?;
                }
            }
            TypeKind::TypeVariant(constructors, _) => {
                for cstr in constructors {
                    check_constructor_arguments(tctx, env, paths, &cstr.cd_args, loc, lid)?;
                    if let Some(res) = cstr.cd_res {
                        check_type_expr(tctx, env, paths, res, loc, lid, &mut visited)?;
                    }
                }
            }
        }
        for inlined in &decl.type_inlined_types {
            match inlined {
                crate::types::decl::TypeInlinedType::Record { labels, .. } => {
                    for label in labels {
                        check_type_expr(tctx, env, paths, label.ld_type, loc, lid, &mut visited)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn check_extension_constructor(
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        paths: &[Path],
        ext: &crate::types::decl::ExtensionConstructor,
        loc: LocIdx,
        lid: &Longident,
    ) -> TypeModResult<()> {
        check_path(tctx, env, paths, &ext.ext_type_path, loc, lid)?;
        let mut visited = HashSet::new();
        for param in &ext.ext_type_params {
            check_type_expr(tctx, env, paths, *param, loc, lid, &mut visited)?;
        }
        check_constructor_arguments(tctx, env, paths, &ext.ext_args, loc, lid)?;
        if let Some(ret) = ext.ext_ret_type {
            check_type_expr(tctx, env, paths, ret, loc, lid, &mut visited)?;
        }
        Ok(())
    }

    fn check_module_type(
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        paths: &[Path],
        mty: &DeclMty,
        loc: LocIdx,
        lid: &Longident,
    ) -> TypeModResult<()> {
        match mty {
            DeclMty::MtySignature(signature) => {
                check_usage_of_path_of_substituted_item(tctx, env, paths, signature, loc, lid)
            }
            DeclMty::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                if let Some(param_type) = param_type {
                    check_module_type(tctx, env, paths, param_type, loc, lid)?;
                }
                let mut result_env = env.clone();
                result_env.add_module_arg(
                    *param,
                    empty_module_decl(default_module_type(param_type.as_deref().cloned())),
                );
                check_module_type(tctx, &result_env, paths, result, loc, lid)
            }
            DeclMty::MtyIdent(_) | DeclMty::MtyAlias(..) => {
                let path = mty.ident_or_alias_path().unwrap();
                check_path(tctx, env, paths, path, loc, lid)
            }
        }
    }

    let mut iter_env = env.clone();
    for item in signature {
        crate::types::includemod::add_sig_item_to_env(tctx.type_ctx, item, &mut iter_env);
    }

    for item in signature {
        match item {
            SignatureItem::SigModule(id, md, _) => {
                if let DeclMty::MtyAlias(_, aliased_path) = &md.md_type {
                    if paths
                        .iter()
                        .any(|path| path_is_strict_prefix(path, aliased_path))
                    {
                        return Err(TypeModError::WithChangesModuleAlias {
                            loc,
                            lid: lid.clone(),
                            id: *id,
                            path: **aliased_path,
                        });
                    }
                }
                check_module_type(tctx, &iter_env, paths, &md.md_type, loc, lid)?;
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(mty) = &mtd.mtd_type {
                    check_module_type(tctx, &iter_env, paths, mty, loc, lid)?;
                }
            }
            SignatureItem::SigValue(_, desc) => {
                let mut visited = HashSet::new();
                check_type_expr(
                    tctx,
                    &iter_env,
                    paths,
                    desc.val_type,
                    loc,
                    lid,
                    &mut visited,
                )?;
            }
            SignatureItem::SigType(_, decl, _) => {
                check_type_declaration(tctx, &iter_env, paths, decl, loc, lid)?;
            }
            SignatureItem::SigTypext(_, ext, _) => {
                check_extension_constructor(tctx, &iter_env, paths, ext, loc, lid)?;
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }

    Ok(())
}

fn collect_manifest_type_aliases_for_functor_arg(
    arg_mty: &crate::types::decl::ModuleType,
) -> HashMap<String, TypeExprRef> {
    use crate::types::decl::SignatureItem;

    let mut manifests = HashMap::new();

    if let crate::types::decl::ModuleType::MtySignature(sig_items) = arg_mty {
        for item in sig_items.iter() {
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
    ctx: &crate::types::context::TypeContext,
    visited: &mut HashSet<TypeExprRef>,
    manifest_subst_cache: &mut HashMap<crate::name::Name, TypeExprRef>,
) {
    use crate::types::type_expr::{RowField, TypeDesc};

    let ty = ctx.repr(ty);
    if !visited.insert(ty) {
        return;
    }

    let desc = ctx.get_desc(ty).into_desc();
    match desc {
        TypeDesc::Tconstr { path, args, .. } => {
            let has_args = !args.is_empty();
            for arg in ctx.type_list(args) {
                rewrite_functor_param_type_paths_in_type(
                    arg,
                    param_name,
                    manifests,
                    ctx,
                    visited,
                    manifest_subst_cache,
                );
            }

            if let PathView::Pdot(prefix, type_name, _) = path.view() {
                if let PathView::Pident(id) = prefix.view() {
                    if id.name() == param_name && !has_args {
                        if let Some(manifest_ty) = manifests.get(type_name.as_str()) {
                            // Cache manifest substitution results so all occurrences of
                            // the same functor parameter type (e.g. S.elt) map to the
                            // SAME substituted node, matching OCaml's Subst.typexp sharing.
                            let manifest_copy =
                                if let Some(&cached) = manifest_subst_cache.get(type_name) {
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
                                    manifest_subst_cache.insert(*type_name, copy);
                                    copy
                                };
                            ctx.set_desc(ty, TypeDesc::Tlink(manifest_copy));
                        }
                    }
                }
            }
        }
        TypeDesc::Tarrow { args, ret } => {
            for arg in ctx.type_args(args) {
                rewrite_functor_param_type_paths_in_type(
                    arg.typ,
                    param_name,
                    manifests,
                    ctx,
                    visited,
                    manifest_subst_cache,
                );
            }
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
            for inner in ctx.type_list(types) {
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
            let row = ctx.row_desc(row);
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
            for var in ctx.type_list(vars) {
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
            for arg in ctx.type_list(args) {
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
        TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {}
    }
}

fn copy_and_specialize_functor_arg_type(
    ty: TypeExprRef,
    param_name: &str,
    manifests: &HashMap<String, TypeExprRef>,
    ctx: &crate::types::context::TypeContext,
    copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
    manifest_subst_cache: &mut HashMap<crate::name::Name, TypeExprRef>,
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
    ctx: &crate::types::context::TypeContext,
) -> crate::types::decl::ModuleType {
    fn specialize_label_decl(
        label: &crate::types::decl::LabelDeclaration,
        param_name: &str,
        manifests: &HashMap<String, TypeExprRef>,
        ctx: &crate::types::context::TypeContext,
        copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
        manifest_subst_cache: &mut HashMap<crate::name::Name, TypeExprRef>,
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
        ctx: &crate::types::context::TypeContext,
        copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
        manifest_subst_cache: &mut HashMap<crate::name::Name, TypeExprRef>,
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
        ctx: &crate::types::context::TypeContext,
        copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
        manifest_subst_cache: &mut HashMap<crate::name::Name, TypeExprRef>,
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
            crate::types::decl::TypeKind::TypeVariant(constructors, layout) => {
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
                    *layout,
                )
            }
        }
    }

    fn specialize_type_inlined(
        inlined: &crate::types::decl::TypeInlinedType,
        param_name: &str,
        manifests: &HashMap<String, TypeExprRef>,
        ctx: &crate::types::context::TypeContext,
        copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
        manifest_subst_cache: &mut HashMap<crate::name::Name, TypeExprRef>,
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
        ctx: &crate::types::context::TypeContext,
        copy_cache: &mut HashMap<TypeExprRef, TypeExprRef>,
        manifest_subst_cache: &mut HashMap<crate::name::Name, TypeExprRef>,
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
                            SignatureItem::SigValue(*id, specialized_vd)
                        }
                        SignatureItem::SigType(id, decl, rec_status) => {
                            let mut local_copy_cache = HashMap::new();
                            let mut specialized_decl = (**decl).clone();
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
                            SignatureItem::SigType(
                                *id,
                                std::sync::Arc::new(specialized_decl),
                                *rec_status,
                            )
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
                            SignatureItem::SigTypext(*id, specialized_ext, *ext_status)
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
                            SignatureItem::SigModule(*id, specialized_md, *rec_status)
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
                            SignatureItem::SigModtype(*id, specialized_mtd)
                        }
                        _ => item.clone(),
                    })
                    .collect();
                DeclMty::MtySignature(std::sync::Arc::new(specialized_sig))
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
                        param: *param,
                        param_type: specialized_param_type,
                        result: result.clone(),
                    }
                } else {
                    DeclMty::MtyFunctor {
                        param: *param,
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

/// Resolve a module path to its (anchored) module type, following module
/// aliases; the helper behind `scrape_alias_module_type` for `Mty_alias`.
fn scrape_resolve_module_path(
    path: &Path,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
    visiting: &mut HashSet<Path>,
    force_component_subst: bool,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::ModuleType as DeclMty;
    if !visiting.insert(*path) {
        return None;
    }

    let resolved = match path.view() {
        PathView::Pident(id) => {
            let name = id.name();
            if let Ok(md) = env.lookup_module(&Path::pident(*id)) {
                match &md.md_type {
                    DeclMty::MtyAlias(_, alias_path) => scrape_resolve_module_path(
                        alias_path,
                        env,
                        pers_env,
                        ctx,
                        visiting,
                        force_component_subst,
                    ),
                    // `Env.scrape_alias` expands a module type path with
                    // `find_modtype_expansion` (env.ml:1396-1400).
                    DeclMty::MtyIdent(mty_path) => {
                        match find_modtype_expansion(mty_path, env, pers_env, ctx) {
                            Some(expansion) => {
                                scrape_alias_module_type(&expansion, env, pers_env, ctx)
                            }
                            None => Some(md.md_type.clone()),
                        }
                    }
                    other => Some(anchored_module_type(&Path::pident(*id), other)),
                }
            } else {
                let persistent_path = Path::pident(Ident::create_persistent(name));
                pers_env
                    .as_mut()
                    .and_then(|pers| pers.get_renamed_sig(name, ctx))
                    .map(|sig| {
                        anchored_module_type(
                            &persistent_path,
                            &DeclMty::MtySignature(std::sync::Arc::new(sig)),
                        )
                    })
            }
        }
        PathView::Pdot(parent, submod, _) => {
            let resolved_component = if force_component_subst {
                crate::types::typecore::with_resolved_module_components_for_path(
                    parent,
                    env,
                    pers_env,
                    ctx,
                    |components| {
                        // OCaml compiler/ml/env.ml:91-99 caches
                        // EnvLazy.force, env.ml:1568-1569 stores component
                        // modules as EnvLazy declarations, and
                        // env.ml:876-880 forces them through that cache.
                        // Force through lookup_qualified_module so alias
                        // scraping shares the same cached Subst.modtype
                        // result as later component lookups instead of
                        // freshening the child signature twice.
                        let (runtime_pos, _, md) =
                            components.lookup_qualified_module_shared(submod.as_str(), ctx)?;
                        let parent_access_path = *components.access_path();
                        let owner_path =
                            Path::pdot_pos(parent_access_path, *submod, runtime_pos as i32);
                        Some((owner_path, md))
                    },
                )
                .flatten()
            } else {
                crate::types::typecore::lookup_module_in_resolved_path(
                    parent, submod, env, pers_env, ctx,
                )
                .map(|(_, owner_path, md)| (owner_path, std::sync::Arc::new(md)))
            };

            if let Some((owner_path, md)) = resolved_component {
                match &md.md_type {
                    DeclMty::MtyAlias(_, alias_path) => scrape_resolve_module_path(
                        alias_path,
                        env,
                        pers_env,
                        ctx,
                        visiting,
                        force_component_subst,
                    ),
                    // env.ml:1396-1400.
                    DeclMty::MtyIdent(mty_path) => {
                        match find_modtype_expansion(mty_path, env, pers_env, ctx) {
                            Some(expansion) => {
                                scrape_alias_module_type(&expansion, env, pers_env, ctx)
                            }
                            None => Some(md.md_type.clone()),
                        }
                    }
                    other => Some(anchored_module_type(&owner_path, other)),
                }
            } else {
                None
            }
        }
        PathView::Papply(_, _) => None,
    };

    visiting.remove(path);
    resolved
}

/// The module type of the module at `path`, resolved through module aliases
/// without strengthening.
pub(crate) fn resolve_module_path_module_type(
    path: &Path,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Option<crate::types::decl::ModuleType> {
    let mut visiting = HashSet::new();
    // `Env.find_module path env` (env.ml:865-882, via
    // includemod.ml `expand_module_alias`): the declaration's own module
    // type, whose items refer to each other locally.
    match scrape_resolve_module_path(path, env, pers_env, ctx, &mut visiting, false)? {
        crate::types::decl::ModuleType::MtySignature(sig) => {
            Some(crate::types::decl::ModuleType::MtySignature(
                localize_scraped_signature(ctx, pers_env.as_ref(), &sig, path),
            ))
        }
        other => Some(other),
    }
}

/// Mirror OCaml `Env.scrape_alias` enough for functor-application typing:
/// follow `Mty_alias`/`Mty_ident` module-type paths until reaching a
/// concrete module type (for example `Mty_functor`).
pub(crate) fn scrape_alias_module_type(
    mty: &crate::types::decl::ModuleType,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Option<crate::types::decl::ModuleType> {
    use crate::types::decl::ModuleType as DeclMty;

    match mty {
        DeclMty::MtyAlias(_, path) => {
            let mut visiting = HashSet::new();
            let resolved =
                scrape_resolve_module_path(path, env, pers_env, ctx, &mut visiting, true)?;
            // `find_module path env` (env.ml:865-882) is the declaration's own
            // module type, whose items refer to each other locally.
            let resolved =
                match resolved {
                    DeclMty::MtySignature(sig) => DeclMty::MtySignature(
                        localize_scraped_signature(ctx, pers_env.as_ref(), &sig, path),
                    ),
                    other => other,
                };
            // OCaml compiler/ml/env.ml:1435-1449 strengthens the concrete
            // module type found through an alias using the alias path, and
            // compiler/ml/mtype.ml:365-385 then removes aliases recursively.
            // Strengthening here turns child signatures into aliases such as
            // `VariantSpreads.S`, so later scraping forces the same EnvLazy
            // component thunks as OCaml.
            let mut strengthened = crate::types::ctype::strengthen_module_type_for_inclusion_path(
                ctx, env, path, &resolved,
            );
            anchor_local_module_aliases_to_owner(&mut strengthened, path);
            Some(strengthened)
        }
        // `Env.scrape_alias` (env.ml:1396-1400): `Mty_ident p` scrapes the
        // module type's expansion, or stays as is when `p` is abstract.
        DeclMty::MtyIdent(path) => match find_modtype_expansion(path, env, pers_env, ctx) {
            Some(expansion) => scrape_alias_module_type(&expansion, env, pers_env, ctx),
            None => Some(mty.clone()),
        },
        other => Some(other.clone()),
    }
}

/// `Env.find_modtype_expansion` (env.ml): the manifest of a module type path,
/// or `None` for an abstract or unknown module type.
fn find_modtype_expansion(
    path: &Path,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> Option<crate::types::decl::ModuleType> {
    match path.view() {
        PathView::Pident(_) => env.lookup_modtype(path).ok()?.mtd_type.clone(),
        PathView::Pdot(parent, name, _) => {
            let (_, mtd) = crate::types::typecore::lookup_modtype_in_resolved_path(
                parent,
                name.as_str(),
                env,
                pers_env,
                ctx,
            )?;
            mtd.mtd_type
        }
        PathView::Papply(_, _) => None,
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
            let arg_path = if let ParsedModuleExprDesc::Pmod_ident(lid) = &arg_expr.pmod_desc {
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
                                &tctx.typed,
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
                Some((*path, *lids, *args))
            }
            _ => None,
        }
    }?;

    let (package_path, package_lids, package_args) = package_info;
    modtype_of_package(
        env,
        &package_path,
        &tctx.type_ctx.package_lids(package_lids),
        &tctx.type_ctx.type_list(package_args).to_smallvec::<4>(),
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

fn remove_module_type_aliases_for_typeof(
    mty: &crate::types::decl::ModuleType,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;
    use crate::types::decl::SignatureItem as SigItem;

    match mty {
        DeclMty::MtySignature(sig) => {
            let mut env = env.clone();
            let mut out = Vec::with_capacity(sig.len());
            for item in sig.iter() {
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
                        env.add_module(*id, md.clone());
                        out.push(SigItem::SigModule(*id, md, *rs));
                    }
                    SigItem::SigModtype(id, mtd) => {
                        env.add_modtype(*id, mtd.clone());
                        out.push(item.clone());
                    }
                    _ => out.push(item.clone()),
                }
            }
            DeclMty::MtySignature(std::sync::Arc::new(out))
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

/// `Env.scrape_alias` (env.ml:865-882, mtype.ml:356-364) returns the module
/// declaration's own signature, whose items refer to each other by their
/// local idents; for a persistent unit that is the saved `ps_sig`
/// (env.ml:677). Rust's loaded signatures name those items through the
/// module's path (`Root.t`), so turn references rooted at the alias target
/// back into the local idents of the signature, on a copy.
fn localize_scraped_signature(
    ctx: &crate::types::context::TypeContext,
    pers_env: Option<&crate::cmi::persistent_env::PersistentEnv>,
    sig: &[crate::types::decl::SignatureItem],
    root: &Path,
) -> std::sync::Arc<Vec<crate::types::decl::SignatureItem>> {
    std::sync::Arc::new(localize_scraped_signature_vec(ctx, pers_env, sig, root))
}

fn localize_scraped_signature_vec(
    ctx: &crate::types::context::TypeContext,
    pers_env: Option<&crate::cmi::persistent_env::PersistentEnv>,
    sig: &[crate::types::decl::SignatureItem],
    root: &Path,
) -> Vec<crate::types::decl::SignatureItem> {
    use crate::types::decl::SignatureItem as SigItem;
    // The flattened unit names registered as aliases of `root` (as for
    // `include`, include_module_alias_heads).
    let mut heads = pers_env
        .map(|pers| pers.flattened_alias_heads_for_path(root))
        .unwrap_or_default();
    for alias_source in ctx.alias_sources_for_component_path(root) {
        if let PathView::Pident(id) = alias_source.view()
            && (id.is_persistent() || id.stamp() == 0)
            && !heads.iter().any(|existing| existing == id.name())
        {
            heads.push(id.name().to_string());
        }
    }
    let mut sig = crate::types::typecore::copy_lookup_signature_for_subst(sig, ctx);
    let mut types = HashMap::new();
    let mut modules = HashMap::new();
    let mut modtypes = HashMap::new();
    for item in &sig {
        match item {
            SigItem::SigType(id, _, _) => {
                types.insert(id.name().to_string(), *id);
            }
            SigItem::SigModule(id, _, _) => {
                modules.insert(id.name().to_string(), *id);
            }
            SigItem::SigModtype(id, _) => {
                modtypes.insert(id.name().to_string(), *id);
            }
            _ => {}
        }
    }
    let mut visited = HashSet::new();
    rewrite_included_signature_paths_to_local(
        ctx,
        &mut sig,
        &IncludeLocalization {
            root_path: Some(root),
            alias_heads: &heads,
            types: &types,
            modules: &modules,
            modtypes: &modtypes,
        },
        &mut visited,
    );
    // The raw `ps_sig` (env.ml:719-721, 872-875) names members locally at
    // every level: a nested module's items refer to each other by their own
    // identifiers, not through the module (`chunk`, not `M.chunk`).
    for item in sig.iter_mut() {
        if let SigItem::SigModule(id, md, _) = item
            && let crate::types::decl::ModuleType::MtySignature(nested) = &md.md_type
        {
            let localized = localize_scraped_signature(ctx, None, nested, &Path::pident(*id));
            md.md_type = crate::types::decl::ModuleType::MtySignature(localized);
        }
    }
    sig
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

    let result = match &mod_expr.pmod_desc {
        ParsedModuleExprDesc::Pmod_ident(lid) => {
            semantic_module_type_for_ident_expr(tctx, env, arena, lid)
        }
        ParsedModuleExprDesc::Pmod_apply(functor_idx, arg_idx) => {
            let functor_expr = arena.get_mod_expr(*functor_idx);
            let arg_expr = arena.get_mod_expr(*arg_idx);
            extract_functor_result_type(tctx, &functor_expr.pmod_desc, arg_expr, arena, env)
        }
        ParsedModuleExprDesc::Pmod_constraint(inner_idx, mty_idx) => {
            let inner = arena.get_mod_expr(*inner_idx);
            let mty = arena.get_mod_type(*mty_idx);
            translate_module_type_to_decl(tctx, env, arena, mty)
                .ok()
                .or_else(|| lookup_module_type_from_parsed_module_expr(tctx, env, arena, inner))
        }
        ParsedModuleExprDesc::Pmod_unpack(expr_idx) => {
            let expr = arena.get_expanded_expr(*expr_idx);
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

fn strengthen_semantic_ident_module_type(
    env: &Env,
    path: &Path,
    semantic_mty: crate::types::decl::ModuleType,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;

    let mut semantic_mty = semantic_mty;
    let strengthen_path = match semantic_mty.clone() {
        DeclMty::MtyAlias(_, alias_path) => {
            semantic_mty =
                scrape_alias_module_type(&semantic_mty, env, pers_env, ctx).unwrap_or(semantic_mty);
            normalize_module_alias_path(env, pers_env, ctx, &alias_path)
        }
        _ => *path,
    };
    crate::types::ctype::strengthen_module_type_for_inclusion_path(
        ctx,
        env,
        &strengthen_path,
        &semantic_mty,
    )
}

fn normalize_module_alias_path(
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
    path: &Path,
) -> Path {
    match normalize_module_alias_path_inner(env, pers_env, ctx, path, path, false) {
        Ok(path) => path,
        Err(_) => unreachable!("unchecked module alias normalization cannot fail"),
    }
}

fn normalize_module_alias_path_checked(
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
    path: &Path,
) -> Result<Path, (Path, Path)> {
    normalize_module_alias_path_inner(env, pers_env, ctx, path, path, true)
}

/// Shared recursion for [`normalize_module_alias_path`] and
/// [`normalize_module_alias_path_checked`]. When `check_missing` is set, a
/// persistent root that cannot be found reports `Err((original, root))`;
/// otherwise that probe is skipped entirely.
fn normalize_module_alias_path_inner(
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
    original: &Path,
    path: &Path,
    check_missing: bool,
) -> Result<Path, (Path, Path)> {
    // OCaml compiler/ml/env.ml:903-914 normalizes dotted prefixes before
    // asking `find_module ~alias:true` whether the complete path is itself
    // an alias. This matters for namespace-backed aliases such as
    // `Webapi.Fetch.Request`: `Webapi.Fetch` must normalize to
    // `Webapi__Fetch` before the child component is selected.
    let path = match path.view() {
        PathView::Pdot(prefix, name, pos) => {
            let normalized_prefix = normalize_module_alias_path_inner(
                env,
                pers_env,
                ctx,
                original,
                prefix,
                check_missing,
            )?;
            if normalized_prefix.same(prefix) {
                *path
            } else {
                Path::pdot_pos(normalized_prefix, *name, *pos)
            }
        }
        PathView::Papply(functor, arg) => Path::papply(
            normalize_module_alias_path_inner(
                env,
                pers_env,
                ctx,
                original,
                functor,
                check_missing,
            )?,
            normalize_module_alias_path_inner(env, pers_env, ctx, original, arg, check_missing)?,
        ),
        PathView::Pident(id)
            if check_missing && id.is_persistent() && !env.has_module_ident(id) =>
        {
            if let Some(pers) = pers_env.as_mut()
                && pers.find_pers_struct(id.name(), ctx).is_none()
                && pers.last_error().is_none()
            {
                return Err((*original, *path));
            }
            *path
        }
        PathView::Pident(_) => *path,
    };

    force_persistent_sigs_for_normalize_path(env, pers_env, ctx, &path);
    if let Some(alias_target) =
        crate::types::typecore::alias_target_for_module_path(&path, env, pers_env, ctx)
        && !alias_target.same(&path)
    {
        return normalize_module_alias_path_inner(
            env,
            pers_env,
            ctx,
            original,
            &alias_target,
            check_missing,
        );
    }

    let env_normalized = env.normalize_path(ctx, &path);
    if !env_normalized.same(&path) {
        normalize_module_alias_path_inner(
            env,
            pers_env,
            ctx,
            original,
            &env_normalized,
            check_missing,
        )
    } else {
        Ok(path)
    }
}

fn force_persistent_sigs_for_normalize_path(
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &crate::types::context::TypeContext,
    path: &Path,
) {
    match path.view() {
        PathView::Pdot(parent, _, _) => {
            force_persistent_sigs_for_normalize_path(env, pers_env, ctx, parent);
        }
        PathView::Papply(functor, arg) => {
            force_persistent_sigs_for_normalize_path(env, pers_env, ctx, functor);
            force_persistent_sigs_for_normalize_path(env, pers_env, ctx, arg);
        }
        PathView::Pident(id) if id.is_persistent() && !env.has_module_ident(id) => {
            // OCaml compiler/ml/typemod.ml:1244-1247 calls
            // `Env.normalize_path` for alias targets. env.ml:903-914
            // normalizes a `Pdot` prefix first, and env.ml:865-875 forces
            // `Lazy.force ps.ps_sig` for a persistent `Pident` that is not in
            // the local module table. That lazy is created at env.ml:676-678
            // as `Subst.signature Subst.identity`, whose binder-renaming order
            // is implemented in compiler/ml/subst.ml:378-400.
            if let Some(pers) = pers_env.as_mut() {
                let _ = pers.force_lazy_signature_rename(id.name(), ctx);
            } else {
                ctx.trigger_module_sig_rename(id.name());
            }
        }
        _ => {}
    }
}

/// Translate a parsed module type (signature) into a decl::ModuleType.
/// Used for recursive module constraint signatures to populate the environment.
/// The typed module type already built for a parsed one: the node
/// `transl_modtype` is finishing, or a child it stored in the typed arena.
#[derive(Clone, Copy)]
enum MtyHint<'h> {
    Node(&'h crate::types::typedtree::ModuleType),
    Stored(TModTypeIdx),
}

impl<'h> MtyHint<'h> {
    fn get<'x>(self, ta: &'x TypedArena) -> &'x crate::types::typedtree::ModuleType
    where
        'h: 'x,
    {
        match self {
            MtyHint::Node(node) => node,
            MtyHint::Stored(idx) => ta.module_type(idx),
        }
    }
}

fn translate_module_type_to_decl_with_typed_hint<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mty: &crate::parser::ast::ModuleType,
    typed_hint: Option<MtyHint<'_>>,
) -> TypeModResult<crate::types::decl::ModuleType> {
    use crate::parser::ast::ModuleTypeDesc as PMtyDesc;
    use crate::types::decl::{
        AliasPresence, ModuleType as DeclMty, SignatureItem as SigItem, ValueDescription,
    };
    use crate::types::typedtree::ModuleTypeDesc as TypedMtyDesc;
    use crate::types::typedtree::TypedSignatureItemDesc as TypedSigDesc;

    match &mty.pmty_desc {
        PMtyDesc::Pmty_signature(sig_items) => {
            let mut items = Vec::new();
            let mut sig_env = env.clone();
            if let Some(TypedMtyDesc::Tmty_signature(sig)) =
                typed_hint.map(|hint| &hint.get(&tctx.typed).mty_desc)
            {
                // OCaml typemod.ml:709-712 builds `Mty_signature sg.sig_type`
                // from the already translated signature, and typemod.ml:879-883
                // computes `sg.sig_type` once. Reusing the typed signature here
                // avoids rewalking the parsed signature and recreating constructor
                // identifiers after `transl_modtype`.
                return Ok(DeclMty::MtySignature(std::sync::Arc::new(
                    decl_signature_from_typed_signature(&tctx.typed, sig, arena, tctx.type_ctx),
                )));
            }
            for sig_item in sig_items.iter() {
                // A typed signature hint returns above, so the items are
                // translated without one.
                let typed_sig_item: Option<&crate::types::typedtree::TypedSignatureItem> = None;
                match &sig_item.psig_desc {
                    crate::parser::ast::SignatureItemDesc::Psig_value(vd) => {
                        let val_name = arena.get_string(vd.pval_name.txt);
                        let val_id = match typed_sig_item.map(|item| &item.sig_desc) {
                            Some(TypedSigDesc::Tsig_value(typed_vd)) => {
                                tctx.typed.value_description(*typed_vd).val_id
                            }
                            _ => tctx.type_ctx.create_ident(val_name),
                        };
                        // Use transl_type_scheme pattern: begin_def/end_def/generalize
                        // OCaml: reset_type_variables() for each val declaration
                        tctx.reset_type_variables();
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
                                val_kind: match &vd.pval_prim {
                                    None => crate::types::decl::ValueKind::ValReg,
                                    Some(prim) => crate::types::decl::ValueKind::ValPrim(
                                        std::sync::Arc::new(primitive_description_from_value_decl(
                                            arena,
                                            ctx,
                                            &sig_env,
                                            prim,
                                            vd.pval_type,
                                            val_type,
                                        )),
                                    ),
                                },
                                val_loc: tctx.intern_ast_loc(arena, sig_item.psig_loc),
                                val_attributes: Default::default(),
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
                                .map(|typed_decl| typed_decl.typ_id)
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
                                type_loc: crate::types::DeclLoc::none(),
                                type_attributes: vec![],
                                type_immediate: false,
                                type_representation: crate::types::TypeRepresentation::Boxed,
                                type_shape: crate::types::ValueShape::Unstated,
                                type_inlined_types: vec![],
                                type_path: Some(Path::pident(type_id)),
                            };
                            sig_env.add_type(type_id, placeholder_decl);
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
                            let type_id = declared_type_ids[decl_idx];
                            let saved_type_variables = std::mem::take(&mut tctx.type_variables);
                            // Match OCaml transl_type_decl: begin_def so params/manifest
                            // are created at elevated level, then end_def + generalize
                            // marks them as generic (needed for instance_parameterized_type).
                            tctx.type_ctx.begin_def();
                            let mut type_params = Vec::with_capacity(decl.ptype_params.len());
                            let mut type_variance = Vec::with_capacity(decl.ptype_params.len());
                            for (param_ty_idx, variance) in &decl.ptype_params {
                                let param_ty = arena.get_core_type(*param_ty_idx);
                                let param_ref = match &param_ty.ptyp_desc {
                                    crate::parser::ast::CoreTypeDesc::Ptyp_any => {
                                        tctx.type_ctx.new_var(Some(crate::name::Name::new("_")))
                                    }
                                    crate::parser::ast::CoreTypeDesc::Ptyp_var(name) => {
                                        let name = arena.get_string(*name);
                                        check_type_variable_name(param_ty.ptyp_loc, name)?;
                                        if tctx.type_variables.contains_key(name) {
                                            return Err(TypeModError::RepeatedParameter {
                                                loc: param_ty.ptyp_loc,
                                            });
                                        }
                                        tctx.type_ctx.new_var(Some(crate::name::Name::new(name)))
                                    }
                                    _ => {
                                        let (_typed_param, param_ref) =
                                            transl_type(tctx, &sig_env, param_ty)?;
                                        param_ref
                                    }
                                };
                                type_params.push(param_ref);
                                if let crate::parser::ast::CoreTypeDesc::Ptyp_var(name) =
                                    &param_ty.ptyp_desc
                                {
                                    tctx.type_variables
                                        .insert(arena.get_string(*name).to_string(), param_ref);
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
                                    touch_manifest_cyclic_abbrev_check(
                                        tctx.type_ctx,
                                        &sig_env,
                                        manifest_ref,
                                    );
                                    Some(manifest_ref)
                                }
                                None => None,
                            };

                            let type_variant_layout = matches!(
                                &decl.ptype_kind,
                                crate::parser::ast::TypeKind::Ptype_variant(_)
                            )
                            .then(|| tctx.type_ctx.pending_variant_layout());
                            let type_kind = match &decl.ptype_kind {
                                crate::parser::ast::TypeKind::Ptype_abstract => {
                                    crate::types::TypeKind::TypeAbstract
                                }
                                crate::parser::ast::TypeKind::Ptype_open => {
                                    crate::types::TypeKind::TypeOpen
                                }
                                crate::parser::ast::TypeKind::Ptype_variant(cstrs) => {
                                    check_duplicate_constructor_declarations(
                                        arena,
                                        decl.ptype_loc,
                                        cstrs,
                                    )?;
                                    check_unboxed_on_constructors(arena, cstrs)?;
                                    let mut constructors = Vec::with_capacity(cstrs.len());
                                    for cstr in cstrs {
                                        let cstr_name = arena.get_string(cstr.pcd_name.txt);
                                        // OCaml compiler/ml/typedecl.ml:481-484
                                        // creates the constructor id before
                                        // make_constructor translates inline
                                        // record labels.
                                        let cstr_id = tctx.type_ctx.create_ident(cstr_name);
                                        let runtime_tag = process_constructor_tag(arena, cstr)
                                            .map_err(|(loc, error)| {
                                                ast_untagged_variant_error(
                                                    arena.to_location(loc),
                                                    error,
                                                )
                                            })?;
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
                                                check_duplicate_label_declarations(
                                                    arena, labels, None,
                                                )?;
                                                let mut record_labels =
                                                    Vec::with_capacity(labels.len());
                                                for label in labels {
                                                    check_extra_as_attribute(arena, label)?;
                                                    let (_typed_label_ty, lbl_type) =
                                                        transl_label_type(tctx, &sig_env, arena, label, false)?;
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
                                                    let label_id = tctx.type_ctx.create_ast_ident(arena, label.pld_name.txt);
                                                    record_labels.push(crate::types::LabelDeclaration {
                                                        ld_id: label_id,
                                                        ld_runtime_name: crate::types::record_runtime::parsetree_runtime_name(label, arena),
                                                        ld_mutable: mutable_flag,
                                                        ld_optional: label.pld_optional,
                                                        ld_type: lbl_type,
                                                        ld_loc: tctx.intern_ast_loc(arena, label.pld_loc),
                                                        ld_attributes: vec![],
                                                    });
                                                }
                                                crate::types::ConstructorArguments::CstrRecord(
                                                    record_labels,
                                                )
                                            }
                                        };
                                        constructors.push(crate::types::ConstructorDeclaration {
                                            cd_id: cstr_id,
                                            cd_runtime_tag: runtime_tag,
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
                                            cd_loc: tctx
                                                .intern_ast_loc(arena, cstr.pcd_loc),
                                            cd_attributes: vec![],
                                        });
                                    }
                                    crate::types::TypeKind::TypeVariant(
                                        crate::types::decl::SharedVec::from(constructors),
                                        type_variant_layout.expect("variant declaration layout"),
                                    )
                                }
                                crate::parser::ast::TypeKind::Ptype_record(labels) => {
                                    check_duplicate_label_declarations(
                                        arena,
                                        labels,
                                        Some(arena.get_string(decl.ptype_name.txt)),
                                    )?;
                                    let mut record_labels = Vec::with_capacity(labels.len());
                                    for label in labels {
                                        check_extra_as_attribute(arena, label)?;
                                        let (_typed_label_ty, lbl_type) =
                                            transl_label_type(tctx, &sig_env, arena, label, false)?;
                                        let lbl_type = tctx.type_ctx.new_poly(lbl_type, vec![]);
                                        let mutable_flag = match label.pld_mutable {
                                            crate::parser::ast::MutableFlag::Immutable => {
                                                crate::types::MutableFlag::Immutable
                                            }
                                            crate::parser::ast::MutableFlag::Mutable => {
                                                crate::types::MutableFlag::Mutable
                                            }
                                        };
                                        let label_id = tctx.type_ctx.create_ast_ident(arena, label.pld_name.txt);
                                        record_labels.push(crate::types::LabelDeclaration {
                                            ld_id: label_id,
                                            ld_runtime_name: crate::types::record_runtime::parsetree_runtime_name(label, arena),
                                            ld_mutable: mutable_flag,
                                            ld_optional: label.pld_optional,
                                            ld_type: lbl_type,
                                            ld_loc: tctx.intern_ast_loc(arena, label.pld_loc),
                                            ld_attributes: vec![],
                                        });
                                    }
                                    let repres = crate::types::record_runtime::boxed_representation(&record_labels);
                                    crate::types::TypeKind::TypeRecord(
                                        crate::types::decl::SharedVec::from(record_labels),
                                        repres,
                                    )
                                }
                            };
                            let type_attributes = parser_attrs_to_decl_attrs(
                                arena,
                                tctx.type_ctx,
                                &decl.ptype_attributes,
                            );
                            let decl_has_unboxed_attr =
                                parser_attrs_have_unboxed(arena, &decl.ptype_attributes);
                            let typed_type_decl_hint =
                                typed_type_decls.and_then(|typed_decls| typed_decls.get(decl_idx));
                            let type_representation = typed_type_decl_hint
                                .map(|typed_decl| typed_decl.typ_type.type_representation)
                                .unwrap_or_else(|| {
                                    unboxed_type_representation(arena, decl, decl_has_unboxed_attr)
                                });
                            // Keep module-type declaration conversion aligned with
                            // OCaml `compiler/ml/typedecl.ml:2005`; this path
                            // feeds constrained module environments.
                            let type_immediate = typed_type_decl_hint
                                .map(|typed_decl| typed_decl.typ_type.type_immediate)
                                .unwrap_or_else(|| {
                                    compute_type_immediacy(
                                        tctx.type_ctx,
                                        &sig_env,
                                        &type_kind,
                                        type_manifest,
                                        &type_attributes,
                                        type_representation,
                                    )
                                });

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
                                type_loc: tctx.intern_ast_loc(arena, decl.ptype_loc),
                                type_attributes,
                                type_immediate,
                                type_representation,
                                type_shape: typed_type_decls
                                    .and_then(|typed_decls| typed_decls.get(decl_idx))
                                    .map(|typed_decl| typed_decl.typ_type.type_shape.clone())
                                    .unwrap_or_default(),
                                type_inlined_types: vec![],
                                type_path: Some(Path::pident(type_id)),
                            };
                            check_variant_declaration_well_formed(
                                tctx.type_ctx,
                                &sig_env,
                                &type_decl,
                            )?;
                            sig_env.store_type(tctx.type_ctx, type_id, type_decl.clone());
                            items.push(SigItem::SigType(
                                type_id,
                                std::sync::Arc::new(type_decl),
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
                                    (typed_md.md_id, Some(MtyHint::Stored(typed_md.md_type)))
                                }
                                _ => (tctx.type_ctx.create_ident(mod_name), None),
                            };
                        let inner_mty = match typed_inner_mty
                            .and_then(|hint| decl_module_type_from_typed(hint.get(&tctx.typed)))
                        {
                            Some(mty) => {
                                // OCaml compiler/ml/typemod.ml:806-834 stores
                                // `tmty.mty_type` directly in the `Sig_module`
                                // after `transl_modtype`; it does not translate
                                // the parsed module type a second time.
                                mty
                            }
                            None => translate_module_type_to_decl_with_typed_hint(
                                tctx,
                                &sig_env,
                                arena,
                                arena.get_mod_type(md.pmd_type),
                                typed_inner_mty,
                            )?,
                        };
                        sig_env.add_module(
                            mod_id,
                            crate::types::decl::ModuleDeclaration {
                                md_type: inner_mty.clone(),
                                md_attributes: vec![],
                                md_loc: crate::types::DeclLoc::none(),
                                md_path: None,
                            },
                        );
                        items.push(SigItem::SigModule(
                            mod_id,
                            crate::types::decl::ModuleDeclaration {
                                md_type: inner_mty,
                                md_attributes: vec![],
                                md_loc: crate::types::DeclLoc::none(),
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
                                    (typed_mtd.mtd_id, typed_mtd.mtd_type.map(MtyHint::Stored))
                                }
                                _ => (tctx.type_ctx.create_ident(modtype_name), None),
                            };
                        let mtd_type = match typed_inner_mty
                            .and_then(|hint| decl_module_type_from_typed(hint.get(&tctx.typed)))
                        {
                            Some(mty) => Some(mty),
                            None => pmtd
                                .pmtd_type
                                .as_ref()
                                .map(|inner_idx| {
                                    // OCaml compiler/ml/typemod.ml:898-923
                                    // builds `mtd_type` from `tmty.mty_type`.
                                    // Re-translate only when no typed hint is
                                    // available.
                                    translate_module_type_to_decl_with_typed_hint(
                                        tctx,
                                        &sig_env,
                                        arena,
                                        arena.get_mod_type(*inner_idx),
                                        typed_inner_mty,
                                    )
                                })
                                .transpose()?,
                        };
                        let mtd = crate::types::decl::ModtypeDeclaration {
                            mtd_type,
                            mtd_attributes: vec![],
                            mtd_loc: crate::types::DeclLoc::none(),
                        };
                        sig_env.add_modtype(modtype_id, mtd.clone());
                        items.push(SigItem::SigModtype(modtype_id, mtd));
                    }
                    crate::parser::ast::SignatureItemDesc::Psig_open(od) => {
                        // Process open declarations to extend sig_env with
                        // opened module's types, matching transl_signature behavior.
                        let open_lid = arena.get_longident(od.popen_lid.txt);
                        if open_direct_persistent_module(
                            &mut sig_env,
                            open_lid,
                            arena,
                            &mut tctx.persistent_env,
                            tctx.type_ctx,
                            None,
                        )
                        .is_none()
                        {
                            let lookup_env = sig_env.clone();
                            let _ = crate::types::typecore::open_module_lid_components_into_env(
                                open_lid,
                                arena,
                                &lookup_env,
                                &mut sig_env,
                                &mut tctx.persistent_env,
                                tctx.type_ctx,
                                None,
                            );
                        }
                    }
                    crate::parser::ast::SignatureItemDesc::Psig_include(incl) => {
                        let include_sig = match typed_sig_item.map(|item| &item.sig_desc) {
                            Some(TypedSigDesc::Tsig_include(typed_incl)) => {
                                typed_incl.incl_type.clone()
                            }
                            _ => {
                                let include_mty = translate_module_type_to_decl_with_typed_hint(
                                    tctx,
                                    &sig_env,
                                    arena,
                                    arena.get_mod_type(incl.pincl_mod),
                                    None,
                                )?;
                                freshened_signature_from_module_type(
                                    tctx,
                                    &sig_env,
                                    &include_mty,
                                    arena.get_mod_type(incl.pincl_mod).pmty_loc,
                                )?
                            }
                        };
                        add_signature_items_to_env(tctx.type_ctx, &include_sig, &mut sig_env)?;
                        items.extend(include_sig);
                    }
                    _ => {}
                }
            }
            Ok(DeclMty::MtySignature(std::sync::Arc::new(
                crate::types::includemod::simplify_signature(&items),
            )))
        }
        PMtyDesc::Pmty_ident(lid) => {
            let longident = tctx.resolve_lid(lid.txt).clone();
            crate::types::typecore::mark_open_lid_use(
                tctx.type_ctx,
                env,
                arena,
                &longident,
                crate::types::env::OpenLookupKind::Modtype,
                None,
            );
            let path = lookup_modtype_path_or_error(tctx, &longident, mty.pmty_loc, arena, env)?;
            Ok(DeclMty::MtyIdent(path))
        }
        PMtyDesc::Pmty_functor(args) => {
            let (name, param_type, result_type_idx) = &**args;
            let (param_id, typed_param_mty, typed_result_mty) =
                match typed_hint.map(|hint| &hint.get(&tctx.typed).mty_desc) {
                    Some(TypedMtyDesc::Tmty_functor(param, _name, param_mty, result_mty)) => (
                        *param,
                        param_mty.map(MtyHint::Stored),
                        Some(MtyHint::Stored(*result_mty)),
                    ),
                    _ => (
                        tctx.type_ctx.create_ident(arena.get_string(name.txt)),
                        None,
                        None,
                    ),
                };
            let param_decl = match param_type {
                Some(pt_idx) => {
                    let decl = match typed_param_mty
                        .and_then(|hint| decl_module_type_from_typed(hint.get(&tctx.typed)))
                    {
                        Some(mty) => {
                            // OCaml compiler/ml/typemod.ml:713-724 reuses
                            // `arg.mty_type` as `ty_arg` when building
                            // `Mty_functor`; it does not translate the
                            // parameter module type again.
                            mty
                        }
                        None => translate_module_type_to_decl_with_typed_hint(
                            tctx,
                            env,
                            arena,
                            arena.get_mod_type(*pt_idx),
                            typed_param_mty,
                        )?,
                    };
                    Some(Box::new(decl))
                }
                None => None,
            };
            let mut result_env = env.clone();
            result_env.add_module_arg(
                param_id,
                crate::types::decl::ModuleDeclaration {
                    md_type: param_decl.as_deref().cloned().unwrap_or(
                        crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(vec![])),
                    ),
                    md_attributes: vec![],
                    md_loc: crate::types::DeclLoc::none(),
                    md_path: None,
                },
            );
            let result_decl = match typed_result_mty
                .and_then(|hint| decl_module_type_from_typed(hint.get(&tctx.typed)))
            {
                Some(mty) => {
                    // OCaml compiler/ml/typemod.ml:721-724 stores
                    // `res.mty_type` in the functor result. Reusing it keeps
                    // nested `Pmty_with` freshening single-pass.
                    mty
                }
                None => translate_module_type_to_decl_with_typed_hint(
                    tctx,
                    &result_env,
                    arena,
                    arena.get_mod_type(*result_type_idx),
                    typed_result_mty,
                )?,
            };
            Ok(DeclMty::MtyFunctor {
                param: param_id,
                param_type: param_decl,
                result: Box::new(result_decl),
            })
        }
        PMtyDesc::Pmty_with(_) => match typed_hint {
            // `transl_modtype` merges the constraints (typemod.ml:759-772);
            // its `mty_type` is the result.
            Some(hint) if matches!(hint.get(&tctx.typed).mty_desc, TypedMtyDesc::Tmty_with(..)) => {
                Ok(hint.get(&tctx.typed).mty_type.clone())
            }
            _ => Ok(transl_modtype(tctx, env, arena, mty)?.mty_type),
        },
        PMtyDesc::Pmty_typeof(me_idx) => {
            let me = arena.get_mod_expr(*me_idx);
            let typed_me = match typed_hint.map(|hint| &hint.get(&tctx.typed).mty_desc) {
                Some(TypedMtyDesc::Tmty_typeof(typed_me)) => Some(*typed_me),
                _ => None,
            };
            match typed_me {
                Some(typed_me) => {
                    let typed_mod_type = tctx.typed.module_expr(typed_me).mod_type.clone();
                    module_type_of_typed_module_expr(tctx, env, arena, me, &typed_mod_type)
                }
                _ => {
                    let (_typed_me, module_type) = type_module_type_of(tctx, env, arena, me)?;
                    Ok(module_type)
                }
            }
        }
        PMtyDesc::Pmty_alias(lid) => {
            check_recursive_module_reference_lid(lid, arena, env)?;
            let longident = tctx.resolve_lid(lid.txt).clone();
            crate::types::typecore::mark_open_lid_use(
                tctx.type_ctx,
                env,
                arena,
                &longident,
                crate::types::env::OpenLookupKind::Module,
                None,
            );
            // typemod.ml:670 `transl_module_alias` uses `Typetexp.lookup_module`,
            // whose default `~load:false` (typetexp.ml:126) leaves the unit
            // unloaded under `-no-alias-deps` (env.ml:1044-1045).
            let path = lookup_module_path_for_module_expr(
                tctx,
                env,
                arena,
                &longident,
                false,
                mty.pmty_loc,
            )?;
            Ok(DeclMty::MtyAlias(
                AliasPresence::MtaAbsent,
                std::sync::Arc::new(path),
            ))
        }
        // OCaml `compiler/ml/typemod.ml:519-520` (approx_modtype) and
        // `compiler/ml/typemod.ml:743-744` (transl_modtype_aux).
        PMtyDesc::Pmty_extension(ext) => Err(TypeModError::CoreError(
            crate::types::typecore::builtin_extension_error(arena, ext),
        )),
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

fn empty_module_decl(
    md_type: crate::types::decl::ModuleType,
) -> crate::types::decl::ModuleDeclaration {
    crate::types::decl::ModuleDeclaration {
        md_type,
        md_attributes: vec![],
        md_loc: crate::types::DeclLoc::none(),
        md_path: None,
    }
}

fn default_module_type(
    mty: Option<crate::types::decl::ModuleType>,
) -> crate::types::decl::ModuleType {
    mty.unwrap_or_else(|| crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(vec![])))
}

fn approx_abstract_type_decl(
    ctx: &crate::types::context::TypeContext,
    arity: usize,
) -> crate::types::decl::TypeDeclaration {
    ctx.begin_def();
    let params = (0..arity).map(|_| ctx.new_var(None)).collect::<Vec<_>>();
    ctx.end_def();
    for &param in &params {
        crate::types::ctype::generalize(ctx, param);
    }
    crate::types::decl::TypeDeclaration {
        type_params: params,
        type_arity: arity as i32,
        type_kind: crate::types::decl::TypeKind::TypeAbstract,
        type_private: crate::types::PrivateFlag::Public,
        type_manifest: None,
        type_variance: (0..arity).map(|_| TypesVariance::full()).collect(),
        type_newtype_level: None,
        type_loc: crate::types::DeclLoc::none(),
        type_attributes: vec![],
        type_immediate: false,
        type_representation: crate::types::TypeRepresentation::Boxed,
        type_shape: crate::types::ValueShape::Unstated,
        type_inlined_types: vec![],
        type_path: None,
    }
}

fn approx_type_decls(
    tctx: &mut TypeCheckContext<'_>,
    arena: &ParseArena,
    decls: &[crate::parser::ast::TypeDeclaration],
) -> Vec<(Ident, crate::types::decl::TypeDeclaration)> {
    decls
        .iter()
        .map(|decl| {
            let id = tctx
                .type_ctx
                .create_ident(arena.get_string(decl.ptype_name.txt));
            let mut approx = approx_abstract_type_decl(tctx.type_ctx, decl.ptype_params.len());
            approx.type_path = Some(Path::pident(id));
            (id, approx)
        })
        .collect()
}

/// OCaml `approx_modtype env smty = Warnings.without_warnings (fun () ->
/// approx_modtype env smty)` (typemod.ml:585-586).
fn approx_modtype<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mty: &crate::parser::ast::ModuleType,
) -> TypeModResult<crate::types::decl::ModuleType> {
    without_warnings(tctx, |tctx| approx_modtype_rec(tctx, env, arena, mty))
}

/// `Warnings.without_warnings f` (warnings.ml): run `f` with every warning
/// disabled.
fn without_warnings<'a, T>(
    tctx: &mut TypeCheckContext<'a>,
    f: impl FnOnce(&mut TypeCheckContext<'a>) -> T,
) -> T {
    tctx.drain_open_slot_uses();
    let mut disabled = tctx.warning_config.clone();
    disabled.disable_all();
    let saved = std::mem::replace(&mut tctx.warning_config, disabled);
    let result = f(tctx);
    tctx.drain_open_slot_uses();
    tctx.warning_config = saved;
    result
}

fn approx_modtype_rec<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mty: &crate::parser::ast::ModuleType,
) -> TypeModResult<crate::types::decl::ModuleType> {
    use crate::parser::ast::ModuleTypeDesc as PMtyDesc;
    use crate::types::decl::{AliasPresence, ModuleType as DeclMty};

    fn approx_signature<'a>(
        tctx: &mut TypeCheckContext<'a>,
        env: &Env,
        arena: &'a ParseArena,
        sig_items: &[crate::parser::ast::SignatureItem],
    ) -> TypeModResult<crate::types::decl::Signature> {
        use crate::parser::ast::SignatureItemDesc as PSigDesc;
        use crate::types::decl::{ModtypeDeclaration, RecStatus, SignatureItem as SigItem};

        let mut items = Vec::new();
        let mut sig_env = env.clone();
        for sig_item in sig_items {
            match &sig_item.psig_desc {
                PSigDesc::Psig_type(args) => {
                    let (rec_flag, decls) = &**args;
                    for (idx, (id, decl)) in approx_type_decls(tctx, arena, decls)
                        .into_iter()
                        .enumerate()
                    {
                        items.push(SigItem::SigType(
                            id,
                            std::sync::Arc::new(decl),
                            sig_rec_status(*rec_flag, idx),
                        ));
                    }
                }
                PSigDesc::Psig_module(pmd) => {
                    let id = tctx
                        .type_ctx
                        .create_ident(arena.get_string(pmd.pmd_name.txt));
                    let md_type =
                        approx_modtype(tctx, &sig_env, arena, arena.get_mod_type(pmd.pmd_type))?;
                    let md = empty_module_decl(md_type);
                    sig_env.add_module(id, md.clone());
                    items.push(SigItem::SigModule(id, md, RecStatus::TrecNot));
                }
                PSigDesc::Psig_recmodule(sdecls) => {
                    let mut decls = Vec::with_capacity(sdecls.len());
                    for pmd in sdecls.iter() {
                        let id = tctx
                            .type_ctx
                            .create_ident(arena.get_string(pmd.pmd_name.txt));
                        let md_type =
                            approx_modtype(tctx, env, arena, arena.get_mod_type(pmd.pmd_type))?;
                        decls.push((id, empty_module_decl(md_type)));
                    }
                    for (id, md) in &decls {
                        sig_env.add_module(*id, md.clone());
                    }
                    for (idx, (id, md)) in decls.into_iter().enumerate() {
                        items.push(SigItem::SigModule(
                            id,
                            md,
                            if idx == 0 {
                                RecStatus::TrecFirst
                            } else {
                                RecStatus::TrecNext
                            },
                        ));
                    }
                }
                PSigDesc::Psig_modtype(pmtd) => {
                    let mtd_type = pmtd
                        .pmtd_type
                        .map(|idx| approx_modtype(tctx, &sig_env, arena, arena.get_mod_type(idx)))
                        .transpose()?;
                    let id = tctx
                        .type_ctx
                        .create_ident(arena.get_string(pmtd.pmtd_name.txt));
                    let mtd = ModtypeDeclaration {
                        mtd_type,
                        mtd_attributes: vec![],
                        mtd_loc: crate::types::DeclLoc::none(),
                    };
                    sig_env.add_modtype(id, mtd.clone());
                    items.push(SigItem::SigModtype(id, mtd));
                }
                PSigDesc::Psig_open(od) => {
                    let open_lid = arena.get_longident(od.popen_lid.txt);
                    crate::types::typecore::mark_open_lid_use(
                        tctx.type_ctx,
                        &sig_env,
                        arena,
                        open_lid,
                        crate::types::env::OpenLookupKind::Module,
                        Some(od.popen_lid.loc),
                    );
                    let lookup_env = sig_env.clone();
                    let _ = crate::types::typecore::open_module_lid_components_into_env(
                        open_lid,
                        arena,
                        &lookup_env,
                        &mut sig_env,
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                        None,
                    );
                }
                PSigDesc::Psig_include(incl) => {
                    let mty =
                        approx_modtype(tctx, &sig_env, arena, arena.get_mod_type(incl.pincl_mod))?;
                    if let Some(sig) = resolve_mod_type_to_sig(
                        &mty,
                        Some(&sig_env),
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    ) {
                        for item in &sig {
                            crate::types::includemod::add_sig_item_to_env(tctx.type_ctx, item, &mut sig_env);
                        }
                        items.extend(sig);
                    }
                }
                _ => {}
            }
        }

        Ok(crate::types::includemod::simplify_signature(&items))
    }

    match &mty.pmty_desc {
        PMtyDesc::Pmty_ident(lid) => {
            let longident = tctx.resolve_lid(lid.txt).clone();
            crate::types::typecore::mark_open_lid_use(
                tctx.type_ctx,
                env,
                arena,
                &longident,
                crate::types::env::OpenLookupKind::Modtype,
                Some(mty.pmty_loc),
            );
            let path = lookup_modtype_path_or_error(tctx, &longident, mty.pmty_loc, arena, env)?;
            Ok(DeclMty::MtyIdent(path))
        }
        PMtyDesc::Pmty_alias(lid) => {
            check_recursive_module_reference_lid(lid, arena, env)?;
            let longident = tctx.resolve_lid(lid.txt).clone();
            crate::types::typecore::mark_open_lid_use(
                tctx.type_ctx,
                env,
                arena,
                &longident,
                crate::types::env::OpenLookupKind::Module,
                Some(mty.pmty_loc),
            );
            // typemod.ml:670 `transl_module_alias` uses `Typetexp.lookup_module`,
            // whose default `~load:false` (typetexp.ml:126) leaves the unit
            // unloaded under `-no-alias-deps` (env.ml:1044-1045).
            let path = lookup_module_path_for_module_expr(
                tctx,
                env,
                arena,
                &longident,
                false,
                mty.pmty_loc,
            )?;
            Ok(DeclMty::MtyAlias(
                AliasPresence::MtaAbsent,
                std::sync::Arc::new(path),
            ))
        }
        PMtyDesc::Pmty_signature(sig_items) => Ok(DeclMty::MtySignature(std::sync::Arc::new(
            approx_signature(tctx, env, arena, sig_items)?,
        ))),
        PMtyDesc::Pmty_functor(args) => {
            let (name, param_type, result_type_idx) = &**args;
            let param_decl = param_type
                .map(|idx| approx_modtype(tctx, env, arena, arena.get_mod_type(idx)))
                .transpose()?;
            let param_id = tctx.type_ctx.create_ident(arena.get_string(name.txt));
            let mut result_env = env.clone();
            result_env.add_module_arg(
                param_id,
                empty_module_decl(default_module_type(param_decl.clone())),
            );
            let result = approx_modtype(
                tctx,
                &result_env,
                arena,
                arena.get_mod_type(*result_type_idx),
            )?;
            Ok(DeclMty::MtyFunctor {
                param: param_id,
                param_type: param_decl.map(Box::new),
                result: Box::new(result),
            })
        }
        PMtyDesc::Pmty_with(args) => {
            let (body_idx, _constraints) = &**args;
            approx_modtype(tctx, env, arena, arena.get_mod_type(*body_idx))
        }
        PMtyDesc::Pmty_typeof(me_idx) => {
            let me = arena.get_mod_expr(*me_idx);
            let (_typed_me, module_type) = type_module_type_of(tctx, env, arena, me)?;
            Ok(module_type)
        }
        // OCaml `compiler/ml/typemod.ml:519-520` (approx_modtype) and
        // `compiler/ml/typemod.ml:743-744` (transl_modtype_aux).
        PMtyDesc::Pmty_extension(ext) => Err(TypeModError::CoreError(
            crate::types::typecore::builtin_extension_error(arena, ext),
        )),
    }
}

/// Clone `mty` and anchor its local module aliases to `owner_path`.
fn anchored_module_type(
    owner_path: &Path,
    mty: &crate::types::decl::ModuleType,
) -> crate::types::decl::ModuleType {
    let mut mty = mty.clone();
    anchor_local_module_aliases_to_owner(&mut mty, owner_path);
    mty
}

/// Clone `mty`, substitute child type paths through `parent_sig`, then anchor
/// its local module aliases to `owner_path`.
fn substituted_and_anchored_module_type(
    parent_sig: &[crate::types::decl::SignatureItem],
    parent_path: &Path,
    owner_path: &Path,
    mty: &crate::types::decl::ModuleType,
    ctx: &crate::types::context::TypeContext,
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

fn anchor_local_module_aliases_to_owner(
    mty: &mut crate::types::decl::ModuleType,
    owner_path: &Path,
) {
    use crate::types::decl::ModuleType as DeclMty;
    use crate::types::decl::SignatureItem as SigItem;

    fn path_contains_apply(path: &Path) -> bool {
        match path.view() {
            PathView::Pident(_) => false,
            PathView::Pdot(prefix, _, _) => path_contains_apply(prefix),
            PathView::Papply(_, _) => true,
        }
    }

    fn qualify_local_module_type_paths(mty: &mut crate::types::decl::ModuleType) {
        match mty {
            DeclMty::MtySignature(sig) => {
                for item in crate::types::decl::signature_mut(sig) {
                    match item {
                        SigItem::SigModule(_, md, _) => {
                            qualify_local_module_type_paths(&mut md.md_type);
                        }
                        SigItem::SigModtype(_, mtd) => {
                            if let Some(mty) = mtd.mtd_type.as_mut() {
                                qualify_local_module_type_paths(mty);
                            }
                        }
                        _ => {}
                    }
                }
            }
            // OCaml compiler/ml/mtype.ml:98-101 leaves `Mty_alias` module
            // declarations unchanged during strengthening, and
            // compiler/ml/mtype.ml:187-203 `enrich_modtype` only descends into
            // signatures instead of qualifying `Mty_ident`/`Mty_alias` paths.
            // Keep local sibling aliases like `module N' = N` as `Pident N`
            // here; rewriting them to `Owner.N` changes Includemod's
            // Subst.add_module path comparison at compiler/ml/includemod.ml:209-215.
            DeclMty::MtyIdent(_) | DeclMty::MtyAlias(_, _) => {}
            DeclMty::MtyFunctor {
                param_type, result, ..
            } => {
                if let Some(param_type) = param_type.as_mut() {
                    qualify_local_module_type_paths(param_type);
                }
                qualify_local_module_type_paths(result);
            }
        }
    }

    match mty {
        DeclMty::MtySignature(sig) => {
            let qualify_local_paths = !path_contains_apply(owner_path);

            for item in crate::types::decl::signature_mut(sig) {
                if let SigItem::SigModule(id, md, _) = item {
                    let child_owner_path = Path::pdot(*owner_path, id.name());
                    md.md_path = Some(child_owner_path);
                    if qualify_local_paths {
                        qualify_local_module_type_paths(&mut md.md_type);
                    }
                    anchor_local_module_aliases_to_owner(&mut md.md_type, &child_owner_path);
                } else if let SigItem::SigModtype(id, mtd) = item {
                    if let Some(mty) = mtd.mtd_type.as_mut() {
                        if qualify_local_paths {
                            qualify_local_module_type_paths(mty);
                        }
                        let modtype_owner_path = Path::pdot(*owner_path, id.name());
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
                Path::papply(*owner_path, Path::pident(*param))
            } else {
                *owner_path
            };
            anchor_local_module_aliases_to_owner(result, &result_owner_path);
        }
        DeclMty::MtyIdent(_) | DeclMty::MtyAlias(_, _) => {}
    }
}

/// Convert a typed signature to a decl signature.
/// Used both in extract_module_type_from_mod_expr_with_ctx and in transl_signature
/// to add modules to sig_env for subsequent items.
pub(crate) fn decl_signature_from_typed_signature(
    ta: &TypedArena,
    sig: &crate::types::typedtree::TypedSignature,
    arena: &ParseArena,
    ctx: &crate::types::context::TypeContext,
) -> crate::types::decl::Signature {
    use crate::types::decl::{
        ModtypeDeclaration, ModuleDeclaration, SignatureItem as SigItem, ValueDescription,
    };
    use crate::types::typedtree::TypedSignatureItemDesc;

    let mut out = Vec::new();
    for item in ta.signature_items(sig.sig_items) {
        match &item.sig_desc {
            TypedSignatureItemDesc::Tsig_value(vd) => {
                let vd = ta.value_description(*vd);
                // typedecl.ml:1878-1915: the value's kind as typed.
                let val_kind = vd.val_kind.clone();
                out.push(SigItem::SigValue(
                    vd.val_id,
                    ValueDescription {
                        val_type: ta.core_type(vd.val_desc).ctyp_type,
                        val_kind,
                        // typedecl.ml:1883-1889: `Types.val_loc` is the
                        // signature item loc (typemod.ml:755-757).
                        val_loc: ctx.intern_ast_loc(arena, item.sig_loc),
                        val_attributes: parser_attrs_to_decl_attrs(arena, ctx, &vd.val_attributes).into(),
                        val_path: None,
                    },
                ));
            }
            TypedSignatureItemDesc::Tsig_type(rec_flag, decls) => {
                let statuses = sig_type_rec_statuses(*rec_flag, decls);
                for (decl, status) in decls.iter().zip(statuses) {
                    out.push(SigItem::SigType(
                        decl.typ_id,
                        std::sync::Arc::new(decl.typ_type.clone()),
                        status,
                    ));
                }
            }
            TypedSignatureItemDesc::Tsig_typext(ext) => {
                for (i, ext_cstr) in ext.tyext_constructors.iter().enumerate() {
                    out.push(SigItem::SigTypext(
                        ext_cstr.ext_id,
                        ext_cstr.ext_type.clone(),
                        sig_ext_status(i),
                    ));
                }
            }
            TypedSignatureItemDesc::Tsig_exception(ext) => {
                out.push(SigItem::SigTypext(
                    ta.extension_constructor(*ext).ext_id,
                    ta.extension_constructor(*ext).ext_type.clone(),
                    crate::types::decl::ExtStatus::TextException,
                ));
            }
            TypedSignatureItemDesc::Tsig_module(md) => {
                out.push(SigItem::SigModule(
                    md.md_id,
                    ModuleDeclaration {
                        md_type: decl_module_type_from_typed(ta.module_type(md.md_type)).unwrap_or(
                            crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(
                                vec![],
                            )),
                        ),
                        md_attributes: parser_attrs_to_decl_attrs(arena, ctx, &md.md_attributes),
                        md_loc: ctx.intern_ast_loc(arena, md.md_loc),
                        md_path: None,
                    },
                    crate::types::decl::RecStatus::TrecNot,
                ));
            }
            TypedSignatureItemDesc::Tsig_recmodule(decls) => {
                for (i, md) in decls.iter().enumerate() {
                    out.push(SigItem::SigModule(
                        md.md_id,
                        ModuleDeclaration {
                            md_type: decl_module_type_from_typed(ta.module_type(md.md_type))
                                .unwrap_or(crate::types::decl::ModuleType::MtySignature(
                                    std::sync::Arc::new(vec![]),
                                )),
                            md_attributes: parser_attrs_to_decl_attrs(
                                arena,
                                ctx,
                                &md.md_attributes,
                            ),
                            md_loc: ctx.intern_ast_loc(arena, md.md_loc),
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
                    mtd.mtd_id,
                    ModtypeDeclaration {
                        mtd_type: mtd
                            .mtd_type
                            .and_then(|mty| decl_module_type_from_typed(ta.module_type(mty))),
                        mtd_attributes: parser_attrs_to_decl_attrs(arena, ctx, &mtd.mtd_attributes),
                        mtd_loc: ctx.intern_ast_loc(arena, mtd.mtd_loc),
                    },
                ));
            }
            TypedSignatureItemDesc::Tsig_include(incl) => {
                out.extend(incl.incl_type.clone());
            }
            TypedSignatureItemDesc::Tsig_open(_) | TypedSignatureItemDesc::Tsig_attribute(_) => {}
        }
    }
    crate::types::includemod::simplify_signature(&out)
}

pub(crate) fn decl_module_type_from_typed(
    mty: &ModuleType,
) -> Option<crate::types::decl::ModuleType> {
    Some(mty.mty_type.clone())
}

pub(crate) fn extract_module_type_from_mod_expr_with_ctx(
    ta: &TypedArena,
    mod_expr: &ModuleExpr,
    env: Option<&Env>,
    type_ctx: &crate::types::context::TypeContext,
) -> Option<crate::types::decl::ModuleType> {
    extract_module_type_from_mod_expr_inner(ta, mod_expr, env, Some(type_ctx))
}

fn strip_self_module_prefix_in_sig(
    sig: &[crate::types::decl::SignatureItem],
    module_id: &Ident,
    type_ctx: &crate::types::context::TypeContext,
) {
    use crate::types::decl::SignatureItem;
    use crate::types::type_expr::{RowField, TypeDesc};

    let direct_items = sig
        .iter()
        .filter_map(|item| match item {
            SignatureItem::SigType(id, _, _)
            | SignatureItem::SigModule(id, _, _)
            | SignatureItem::SigModtype(id, _) => Some((id.name().to_string(), *id)),
            _ => None,
        })
        .collect::<HashMap<_, _>>();

    fn rewrite_self_path(
        path: &Path,
        module_id: &Ident,
        direct_items: &HashMap<String, Ident>,
    ) -> Option<Path> {
        match path.view() {
            PathView::Pdot(prefix, name, pos) => {
                if let PathView::Pident(prefix_id) = prefix.view() {
                    if prefix_id.name() == module_id.name() {
                        if let Some(local_id) = direct_items.get(name.as_str()) {
                            return Some(Path::pident(*local_id));
                        }
                    }
                }
                rewrite_self_path(prefix, module_id, direct_items)
                    .map(|rewritten_prefix| Path::pdot_pos(rewritten_prefix, *name, *pos))
            }
            _ => None,
        }
    }

    fn rewrite_type(
        ty_ref: crate::types::TypeExprRef,
        module_id: &Ident,
        direct_items: &HashMap<String, Ident>,
        type_ctx: &crate::types::context::TypeContext,
        visited: &mut HashSet<crate::types::TypeExprRef>,
    ) {
        let ty_ref = type_ctx.repr(ty_ref);
        if !visited.insert(ty_ref) {
            return;
        }

        let desc = type_ctx.get_desc(ty_ref);
        match &*desc {
            TypeDesc::Tconstr {
                path, args, abbrev, ..
            } => {
                for arg in type_ctx.type_list(*args).iter() {
                    rewrite_type(arg, module_id, direct_items, type_ctx, visited);
                }
                if let Some(rewritten) = rewrite_self_path(path, module_id, direct_items) {
                    type_ctx.set_desc(
                        ty_ref,
                        TypeDesc::Tconstr {
                            path: rewritten,
                            args: *args,
                            abbrev: *abbrev,
                        },
                    );
                }
            }
            TypeDesc::Tarrow { args, ret } => {
                for arg in type_ctx.type_args(args).iter() {
                    rewrite_type(arg.typ, module_id, direct_items, type_ctx, visited);
                }
                rewrite_type(*ret, module_id, direct_items, type_ctx, visited);
            }
            TypeDesc::Ttuple(items) => {
                for item in type_ctx.type_list(items).iter() {
                    rewrite_type(item, module_id, direct_items, type_ctx, visited);
                }
            }
            TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                rewrite_type(*target, module_id, direct_items, type_ctx, visited);
            }
            TypeDesc::Tpoly { body, vars } => {
                rewrite_type(*body, module_id, direct_items, type_ctx, visited);
                for var in type_ctx.type_list(vars).iter() {
                    rewrite_type(var, module_id, direct_items, type_ctx, visited);
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
                let row = crate::types::btype::row_repr(type_ctx, &type_ctx.row_desc(row0));
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
                for arg in type_ctx.type_list(args).iter() {
                    rewrite_type(arg, module_id, direct_items, type_ctx, visited);
                }
                if let Some(rewritten) = rewrite_self_path(path, module_id, direct_items) {
                    type_ctx.set_desc(
                        ty_ref,
                        TypeDesc::Tpackage {
                            path: rewritten,
                            args: *args,
                            lids: *lids,
                        },
                    );
                }
            }
            TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {}
        }
    }

    fn rewrite_sig(
        sig: &[crate::types::decl::SignatureItem],
        module_id: &Ident,
        direct_items: &HashMap<String, Ident>,
        type_ctx: &crate::types::context::TypeContext,
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
    type_ctx: Option<&crate::types::context::TypeContext>,
) -> crate::types::decl::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;

    let (path, env, type_ctx) = match (mty.ident_or_alias_path(), env, type_ctx) {
        (Some(path), Some(env), Some(type_ctx)) => (*path, env, type_ctx),
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
            &DeclMty::MtyIdent(path),
            Some(env),
            &mut no_persistent_env,
            type_ctx,
        )
    });
    let Some(sig) = resolved_sig else {
        return mty;
    };

    let mut sig = sig;
    let rewrite_target = std::sync::Arc::new(Path::pident(*local_id));
    crate::cmi::persistent_env::rewrite_sig_by_path_prefix(&sig, &path, &rewrite_target, type_ctx);
    crate::cmi::persistent_env::rewrite_sig_paths_by_path_prefix(
        &mut sig,
        &path,
        &rewrite_target,
        type_ctx,
    );
    strip_self_module_prefix_in_sig(&sig, local_id, type_ctx);
    DeclMty::MtySignature(std::sync::Arc::new(sig))
}

fn localize_alias_child_module_sig_paths_in_structure_sig(
    ta: &TypedArena,
    sig: &mut [crate::types::decl::SignatureItem],
    structure: &Structure,
    module_path: &Path,
    type_ctx: &crate::types::context::TypeContext,
) {
    use crate::types::decl::{ModuleType as DeclMty, SignatureItem};

    fn localize_alias_child_module_sig(
        ta: &TypedArena,
        sub_sig: &mut [crate::types::decl::SignatureItem],
        child_path: &Path,
        mod_expr: &ModuleExpr,
        type_ctx: &crate::types::context::TypeContext,
    ) {
        if matches!(
            mod_expr.mod_desc,
            ModuleExprDesc::Tmod_ident(path, _) if matches!(path.view(), PathView::Pdot(..))
        ) {
            crate::types::typecore::rebind_direct_sig_type_family_to_access_path(
                type_ctx, child_path, sub_sig,
            );
            crate::cmi::persistent_env::substitute_type_paths_in_sig(sub_sig, child_path, type_ctx);
            crate::cmi::persistent_env::substitute_sig_decl_paths_in_place(
                sub_sig, child_path, type_ctx,
            );
        }

        if let ModuleExprDesc::Tmod_structure(sub_structure) = &mod_expr.mod_desc {
            localize_alias_child_module_sig_paths_in_structure_sig(
                ta,
                sub_sig,
                sub_structure,
                child_path,
                type_ctx,
            );
        }
    }

    let mut sig_cursor = 0usize;
    for item in ta.structure_items(structure.str_items) {
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
                        let child_path = Path::pdot(*module_path, id.name());
                        localize_alias_child_module_sig(
                            ta,
                            crate::types::decl::signature_mut(sub_sig),
                            &child_path,
                            ta.module_expr(mb.mb_expr),
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
                            let child_path = Path::pdot(*module_path, id.name());
                            localize_alias_child_module_sig(
                                ta,
                                crate::types::decl::signature_mut(sub_sig),
                                &child_path,
                                ta.module_expr(mb.mb_expr),
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

fn module_expr_has_dotted_alias_child_modules(ta: &TypedArena, mod_expr: &ModuleExpr) -> bool {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(path, _) if matches!(path.view(), PathView::Pdot(..)) => true,
        ModuleExprDesc::Tmod_structure(structure) => {
            structure_has_dotted_alias_child_modules(ta, structure)
        }
        ModuleExprDesc::Tmod_ident(_, _)
        | ModuleExprDesc::Tmod_apply(_, _, _)
        | ModuleExprDesc::Tmod_functor(_, _, _, _)
        | ModuleExprDesc::Tmod_constraint(_, _, _, _)
        | ModuleExprDesc::Tmod_unpack(_, _) => false,
    }
}

fn structure_has_dotted_alias_child_modules(ta: &TypedArena, structure: &Structure) -> bool {
    ta.structure_items(structure.str_items)
        .iter()
        .any(|item| match &item.str_desc {
            StructureItemDesc::Tstr_module(mb) => {
                module_expr_has_dotted_alias_child_modules(ta, ta.module_expr(mb.mb_expr))
            }
            StructureItemDesc::Tstr_recmodule(mbs) => mbs.iter().any(|mb| {
                module_expr_has_dotted_alias_child_modules(ta, ta.module_expr(mb.mb_expr))
            }),
            _ => false,
        })
}

fn module_expr_contains_unpack_for_sig_localization(
    ta: &TypedArena,
    mod_expr: &ModuleExpr,
) -> bool {
    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(_, _) => false,
        ModuleExprDesc::Tmod_structure(structure) => ta
            .structure_items(structure.str_items)
            .iter()
            .any(|item| match &item.str_desc {
                StructureItemDesc::Tstr_module(mb) => {
                    module_expr_contains_unpack_for_sig_localization(ta, ta.module_expr(mb.mb_expr))
                }
                StructureItemDesc::Tstr_recmodule(mbs) => mbs.iter().any(|mb| {
                    module_expr_contains_unpack_for_sig_localization(ta, ta.module_expr(mb.mb_expr))
                }),
                StructureItemDesc::Tstr_include(include) => {
                    module_expr_contains_unpack_for_sig_localization(
                        ta,
                        ta.module_expr(include.incl_mod),
                    )
                }
                _ => false,
            }),
        ModuleExprDesc::Tmod_apply(functor, arg, _) => {
            module_expr_contains_unpack_for_sig_localization(ta, ta.module_expr(*functor))
                || module_expr_contains_unpack_for_sig_localization(ta, ta.module_expr(*arg))
        }
        ModuleExprDesc::Tmod_functor(_, _, _, body) => {
            module_expr_contains_unpack_for_sig_localization(ta, ta.module_expr(*body))
        }
        ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
            module_expr_contains_unpack_for_sig_localization(ta, ta.module_expr(*inner))
        }
        ModuleExprDesc::Tmod_unpack(_, _) => true,
    }
}

fn localize_raw_unpack_module_type_family(
    sig: &[crate::types::decl::SignatureItem],
    local_id: &Ident,
    type_ctx: &crate::types::context::TypeContext,
) {
    use crate::types::decl::SignatureItem;
    use crate::types::type_expr::TypeDesc;

    let mut rewrites = Vec::<(Path, Path)>::new();
    for item in sig {
        if let SignatureItem::SigType(id, decl, _) = item {
            let new_path = Path::pdot(Path::pident(*local_id), id.name());
            if let Some(old_path) = decl.type_path.as_ref() {
                if !old_path.same(&new_path) {
                    rewrites.push((*old_path, new_path));
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
                        rewrites.push((*path, new_path));
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
        let rewrite_target = std::sync::Arc::new(new_path);
        crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
            sig,
            &old_path,
            &rewrite_target,
            type_ctx,
        );
    }
    strip_self_module_prefix_in_sig(sig, local_id, type_ctx);
}

fn localize_raw_unpack_modules_in_structure_sig(
    ta: &TypedArena,
    sig: &[crate::types::decl::SignatureItem],
    structure: &Structure,
    type_ctx: &crate::types::context::TypeContext,
) {
    use crate::types::decl::{ModuleType as DeclMty, SignatureItem};

    let mut sig_cursor = 0usize;
    for item in ta.structure_items(structure.str_items) {
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
                        if module_expr_contains_unpack_for_sig_localization(
                            ta,
                            ta.module_expr(mb.mb_expr),
                        ) {
                            localize_raw_unpack_module_type_family(sub_sig, &mb.mb_id, type_ctx);
                        }
                        if let ModuleExprDesc::Tmod_structure(sub_structure) =
                            &ta.module_expr(mb.mb_expr).mod_desc
                        {
                            localize_raw_unpack_modules_in_structure_sig(
                                ta,
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
                            if module_expr_contains_unpack_for_sig_localization(
                                ta,
                                ta.module_expr(mb.mb_expr),
                            ) {
                                localize_raw_unpack_module_type_family(
                                    sub_sig, &mb.mb_id, type_ctx,
                                );
                            }
                            if let ModuleExprDesc::Tmod_structure(sub_structure) =
                                &ta.module_expr(mb.mb_expr).mod_desc
                            {
                                localize_raw_unpack_modules_in_structure_sig(
                                    ta,
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

fn extract_module_type_from_mod_expr_inner(
    ta: &TypedArena,
    mod_expr: &ModuleExpr,
    env: Option<&Env>,
    type_ctx: Option<&crate::types::context::TypeContext>,
) -> Option<crate::types::decl::ModuleType> {
    fn preserve_structure_module_alias(
        mod_expr: &ModuleExpr,
    ) -> Option<crate::types::decl::ModuleType> {
        use crate::types::decl::{AliasPresence, ModuleType as DeclMty};

        match &mod_expr.mod_desc {
            ModuleExprDesc::Tmod_ident(path, _) => Some(DeclMty::MtyAlias(
                AliasPresence::MtaAbsent,
                std::sync::Arc::new(*path),
            )),
            _ => None,
        }
    }

    use crate::types::decl::ModuleType as DeclMty;
    use crate::types::decl::SignatureItem as SigItem;
    use crate::types::decl::ValueDescription;

    fn resolve_modtype_to_sig_in_env(
        mty: &crate::types::decl::ModuleType,
        env: &Env,
        type_ctx: Option<&crate::types::context::TypeContext>,
    ) -> Option<crate::types::decl::Signature> {
        use crate::types::decl::ModuleType as DeclMty;
        fn resolve_path(
            path: &Path,
            env: &Env,
            type_ctx: Option<&crate::types::context::TypeContext>,
            visiting: &mut HashSet<Path>,
        ) -> Option<crate::types::decl::Signature> {
            use crate::types::decl::SignatureItem as SigItem;

            if !visiting.insert(*path) {
                return None;
            }

            let result = match path.view() {
                PathView::Pident(id) => {
                    if let Ok(md) = env.lookup_module(&Path::pident(*id)) {
                        let anchored_mty = anchored_module_type(&Path::pident(*id), &md.md_type);
                        if let Some(sig) = resolve_mty(&anchored_mty, env, type_ctx, visiting) {
                            return Some(sig);
                        }
                    }
                    if let Ok(mtd) = env.lookup_modtype(&Path::pident(*id)) {
                        if let Some(mty) = &mtd.mtd_type {
                            let anchored_mty = anchored_module_type(&Path::pident(*id), mty);
                            return resolve_mty(&anchored_mty, env, type_ctx, visiting);
                        }
                    }
                    None
                }
                PathView::Pdot(parent, name, _) => {
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
                            let child_mty = anchored_module_type(&owner_path, &md.md_type);
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
                                let child_mty = anchored_module_type(&owner_path, mty);
                                return resolve_mty(&child_mty, env, Some(type_ctx), visiting);
                            }
                        }
                    }

                    let parent_sig = resolve_path(parent, env, type_ctx, visiting)?;
                    let owner_path = Path::pdot(*parent, name.as_str());
                    parent_sig.iter().find_map(|item| match item {
                        SigItem::SigModule(id, md, _) if id.name() == name.as_str() => {
                            let child_mty = if let Some(type_ctx) = type_ctx {
                                substituted_and_anchored_module_type(
                                    &parent_sig,
                                    parent,
                                    &owner_path,
                                    &md.md_type,
                                    type_ctx,
                                )
                            } else {
                                anchored_module_type(&owner_path, &md.md_type)
                            };
                            resolve_mty(&child_mty, env, type_ctx, visiting)
                        }
                        SigItem::SigModtype(id, mtd) if id.name() == name.as_str() => {
                            mtd.mtd_type.as_ref().and_then(|mty| {
                                let child_mty = if let Some(type_ctx) = type_ctx {
                                    substituted_and_anchored_module_type(
                                        &parent_sig,
                                        parent,
                                        &owner_path,
                                        mty,
                                        type_ctx,
                                    )
                                } else {
                                    anchored_module_type(&owner_path, mty)
                                };
                                resolve_mty(&child_mty, env, type_ctx, visiting)
                            })
                        }
                        _ => None,
                    })
                }
                PathView::Papply(_, _) => None,
            };

            visiting.remove(path);
            result
        }

        fn resolve_mty(
            mty: &crate::types::decl::ModuleType,
            env: &Env,
            type_ctx: Option<&crate::types::context::TypeContext>,
            visiting: &mut HashSet<Path>,
        ) -> Option<crate::types::decl::Signature> {
            match mty {
                DeclMty::MtySignature(sig) => Some((**sig).clone()),
                DeclMty::MtyIdent(_) | DeclMty::MtyAlias(..) => {
                    let path = mty.ident_or_alias_path().unwrap();
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
        type_ctx: Option<&crate::types::context::TypeContext>,
    ) -> Option<crate::types::decl::ModuleType> {
        use crate::types::decl::ModuleType as DeclMty;
        use crate::types::decl::SignatureItem as SigItem;

        match path.view() {
            PathView::Pident(id) => {
                if let Ok(md) = env.lookup_module(&Path::pident(*id)) {
                    return Some(anchored_module_type(&Path::pident(*id), &md.md_type));
                }
                if let Ok(mtd) = env.lookup_modtype(&Path::pident(*id)) {
                    if let Some(mty) = &mtd.mtd_type {
                        return Some(anchored_module_type(&Path::pident(*id), mty));
                    }
                }
                None
            }
            PathView::Pdot(parent, name, _) => {
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
                        return Some(anchored_module_type(&owner_path, &md.md_type));
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
                            return Some(anchored_module_type(&owner_path, mty));
                        }
                    }
                }

                let parent_mty = resolve_module_type_path_in_env(parent, env, type_ctx)?;
                let parent_sig = resolve_modtype_to_sig_in_env(&parent_mty, env, type_ctx)?;
                let owner_path = Path::pdot(*parent, name.as_str());
                for item in &parent_sig {
                    match item {
                        SigItem::SigModule(id, md, _) if id.name() == name.as_str() => {
                            if let Some(type_ctx) = type_ctx {
                                return Some(substituted_and_anchored_module_type(
                                    &parent_sig,
                                    parent,
                                    &owner_path,
                                    &md.md_type,
                                    type_ctx,
                                ));
                            }
                            return Some(anchored_module_type(&owner_path, &md.md_type));
                        }
                        SigItem::SigModtype(id, mtd) if id.name() == name.as_str() => {
                            if let Some(mty) = &mtd.mtd_type {
                                if let Some(type_ctx) = type_ctx {
                                    return Some(substituted_and_anchored_module_type(
                                        &parent_sig,
                                        parent,
                                        &owner_path,
                                        mty,
                                        type_ctx,
                                    ));
                                }
                                return Some(anchored_module_type(&owner_path, mty));
                            }
                        }
                        _ => {}
                    }
                }
                None
            }
            PathView::Papply(_, _) => Some(DeclMty::MtyIdent(*path)),
        }
    }

    fn decl_module_type_from_typed_module_type(
        mty: &ModuleType,
    ) -> Option<crate::types::decl::ModuleType> {
        decl_module_type_from_typed(mty)
    }

    use crate::types::includemod::add_sig_item_to_env;

    match &mod_expr.mod_desc {
        ModuleExprDesc::Tmod_ident(_, _) => Some(mod_expr.mod_type.clone()),
        ModuleExprDesc::Tmod_unpack(_, mty) => Some(mty.clone()),
        ModuleExprDesc::Tmod_structure(structure) => {
            let has_include = ta
                .structure_items(structure.str_items)
                .iter()
                .any(|item| matches!(item.str_desc, StructureItemDesc::Tstr_include(_)));
            let needs_precise_structure_sig =
                ta.structure_items(structure.str_items)
                    .iter()
                    .any(|item| match &item.str_desc {
                        StructureItemDesc::Tstr_recmodule(_) => true,
                        StructureItemDesc::Tstr_module(mb) => !matches!(
                            ta.module_expr(mb.mb_expr).mod_desc,
                            ModuleExprDesc::Tmod_ident(_, _)
                        ),
                        _ => false,
                    });
            if !has_include && needs_precise_structure_sig {
                let sig = structure.str_type.clone();
                if let Some(type_ctx) = type_ctx {
                    localize_raw_unpack_modules_in_structure_sig(ta, &sig, structure, type_ctx);
                }
                return Some(DeclMty::MtySignature(std::sync::Arc::new(sig)));
            }

            let mut sig_items = Vec::new();
            let mut local_env = env.cloned();
            for item in ta.structure_items(structure.str_items) {
                let current_env_snapshot = local_env.clone();
                let current_env = current_env_snapshot.as_ref().or(env);
                match &item.str_desc {
                    // A derived item declares its bindings as regular values.
                    StructureItemDesc::Tstr_derived(idx) => {
                        for bound in ta.derived.bound(*idx) {
                            sig_items.push(SigItem::SigValue(
                                bound.ident,
                                crate::types::decl::ValueDescription {
                                    val_type: bound.ty,
                                    val_kind: crate::types::decl::ValueKind::ValReg,
                                    val_loc: crate::types::DeclLoc::none(),
                                    val_attributes: Default::default(),
                                    val_path: None,
                                },
                            ));
                        }
                    }
                    StructureItemDesc::Tstr_value(_, bindings) => {
                        for vb in ta.value_bindings(*bindings) {
                            extract_sig_values_from_pattern(
                                ta,
                                ta.pattern(vb.vb_pat),
                                ta.pattern(vb.vb_pat).pat_type,
                                &mut sig_items,
                            );
                        }
                    }
                    StructureItemDesc::Tstr_primitive(vd) => {
                        let vd = ta.value_description(*vd);
                        let id = vd.val_id;
                        let value_desc = ValueDescription {
                            val_type: ta.core_type(vd.val_desc).ctyp_type,
                            // typedecl.ml:1878-1915: the kind as typed.
                            val_kind: vd.val_kind.clone(),
                            val_loc: crate::types::DeclLoc::none(),
                            val_attributes: Default::default(),
                            val_path: None,
                        };
                        sig_items.push(SigItem::SigValue(id, value_desc.clone()));
                        if let Some(env_mut) = local_env.as_mut() {
                            env_mut.add_value(id, value_desc);
                        }
                    }
                    StructureItemDesc::Tstr_module(mb) => {
                        let inner_mty = preserve_structure_module_alias(ta.module_expr(mb.mb_expr))
                            .or_else(|| {
                                extract_module_type_from_mod_expr_inner(
                                    ta,
                                    ta.module_expr(mb.mb_expr),
                                    current_env,
                                    type_ctx,
                                )
                            })
                            .unwrap_or(DeclMty::MtySignature(std::sync::Arc::new(vec![])));
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
                            md_loc: crate::types::DeclLoc::none(),
                            md_path: None,
                        };
                        sig_items.push(SigItem::SigModule(
                            mb.mb_id,
                            module_decl.clone(),
                            crate::types::decl::RecStatus::TrecNot,
                        ));
                        if let Some(env_mut) = local_env.as_mut() {
                            env_mut.add_module(mb.mb_id, module_decl);
                        }
                    }
                    StructureItemDesc::Tstr_recmodule(mbs) => {
                        for mb in mbs {
                            let inner_mty =
                                preserve_structure_module_alias(ta.module_expr(mb.mb_expr))
                                    .or_else(|| {
                                        extract_module_type_from_mod_expr_inner(
                                            ta,
                                            ta.module_expr(mb.mb_expr),
                                            current_env,
                                            type_ctx,
                                        )
                                    })
                                    .unwrap_or(DeclMty::MtySignature(std::sync::Arc::new(vec![])));
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
                                md_loc: crate::types::DeclLoc::none(),
                                md_path: None,
                            };
                            sig_items.push(SigItem::SigModule(
                                mb.mb_id,
                                module_decl.clone(),
                                crate::types::decl::RecStatus::TrecFirst,
                            ));
                            if let Some(env_mut) = local_env.as_mut() {
                                env_mut.add_module(mb.mb_id, module_decl);
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
                                decl.typ_id,
                                std::sync::Arc::new(decl.typ_type.clone()),
                                rec_status,
                            ));
                            if let Some(env_mut) = local_env.as_mut() {
                                env_mut.store_type(type_ctx.expect("module type extraction runs with a type context"), decl.typ_id, decl.typ_type.clone());
                            }
                        }
                    }
                    StructureItemDesc::Tstr_exception(ext_cstr) => {
                        sig_items.push(SigItem::SigTypext(
                            ta.extension_constructor(*ext_cstr).ext_id,
                            ta.extension_constructor(*ext_cstr).ext_type.clone(),
                            crate::types::decl::ExtStatus::TextException,
                        ));
                    }
                    StructureItemDesc::Tstr_typext(type_ext) => {
                        for ext_cstr in &type_ext.tyext_constructors {
                            sig_items.push(SigItem::SigTypext(
                                ext_cstr.ext_id,
                                ext_cstr.ext_type.clone(),
                                crate::types::decl::ExtStatus::TextFirst,
                            ));
                        }
                    }
                    StructureItemDesc::Tstr_modtype(mtd) => {
                        let modtype_decl = crate::types::decl::ModtypeDeclaration {
                            mtd_type: mtd.mtd_type.and_then(|mty| {
                                decl_module_type_from_typed_module_type(ta.module_type(mty))
                            }),
                            mtd_attributes: vec![],
                            mtd_loc: crate::types::DeclLoc::none(),
                        };
                        sig_items.push(SigItem::SigModtype(mtd.mtd_id, modtype_decl.clone()));
                        if let Some(env_mut) = local_env.as_mut() {
                            env_mut.add_modtype(mtd.mtd_id, modtype_decl);
                        }
                    }
                    StructureItemDesc::Tstr_include(incl) => {
                        let mut included = false;
                        if !incl.incl_type.is_empty() {
                            for sig_item in incl.incl_type.clone() {
                                if let Some(env_mut) = local_env.as_mut() {
                                    add_sig_item_to_env(type_ctx.expect("module type extraction runs with a type context"), &sig_item, env_mut);
                                }
                                sig_items.push(sig_item);
                            }
                            included = true;
                        }
                        if !included {
                            if let Some(inner_mty) = extract_module_type_from_mod_expr_inner(
                                ta,
                                ta.module_expr(incl.incl_mod),
                                current_env,
                                type_ctx,
                            ) {
                                let inner_sig_opt = match inner_mty {
                                    DeclMty::MtySignature(inner_sig) => Some(std::sync::Arc::unwrap_or_clone(inner_sig)),
                                    other => current_env
                                        .and_then(|env| resolve_modtype_to_sig_in_env(&other, env, type_ctx))
                                        .or_else(|| match &other {
                                            DeclMty::MtyIdent(_) | DeclMty::MtyAlias(..) => {
                                                let path = other.ident_or_alias_path().unwrap();
                                                let name = path.last();
                                                sig_items.iter().rev().find_map(|item| match item {
                                                    SigItem::SigModtype(id, mtd)
                                                        if id.name() == name =>
                                                    {
                                                        mtd.mtd_type.as_ref().and_then(|mty| match mty {
                                                            DeclMty::MtySignature(sig) => Some((**sig).clone()),
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
                                            add_sig_item_to_env(type_ctx.expect("module type extraction runs with a type context"), &sig_item, env_mut);
                                        }
                                        sig_items.push(sig_item);
                                    }
                                    included = true;
                                }
                            }
                        }
                        if !included {
                            if let ModuleExprDesc::Tmod_ident(path, _) =
                                &ta.module_expr(incl.incl_mod).mod_desc
                            {
                                let mod_name: Option<&str> = match path.view() {
                                    crate::types::path::PathView::Pident(id) => Some(id.name()),
                                    crate::types::path::PathView::Pdot(_, name, _) => {
                                        Some(name.as_ref())
                                    }
                                    _ => None,
                                };
                                if let Some(mod_name) = mod_name {
                                    let found_sig: Option<Vec<SigItem>> =
                                        sig_items.iter().find_map(|si| {
                                            if let SigItem::SigModule(id, md, _) = si {
                                                if id.name() == mod_name {
                                                    return match &md.md_type {
                                                        DeclMty::MtySignature(inner) => {
                                                            Some((**inner).clone())
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
                                                add_sig_item_to_env(type_ctx.expect("module type extraction runs with a type context"), &sig_item, env_mut);
                                            }
                                            sig_items.push(sig_item);
                                        }
                                        included = true;
                                    }
                                }
                                if !included {
                                    if let Some(env) = current_env {
                                        if let Some(inner_sig) = resolve_modtype_to_sig_in_env(
                                            &DeclMty::MtyIdent(*path),
                                            env,
                                            type_ctx,
                                        ) {
                                            for sig_item in inner_sig {
                                                if let Some(env_mut) = local_env.as_mut() {
                                                    add_sig_item_to_env(type_ctx.expect("module type extraction runs with a type context"), &sig_item, env_mut);
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
            Some(DeclMty::MtySignature(std::sync::Arc::new(sig_items)))
        }
        ModuleExprDesc::Tmod_functor(param_id, _name, param_mty, body) => {
            let decl_param_mty = param_mty
                .and_then(|mty| decl_module_type_from_typed_module_type(ta.module_type(mty)));

            let body_env_storage: Option<Env>;
            let body_env = if let Some(parent_env) = env {
                let mut extended = parent_env.clone();
                if let Some(ref param_decl) = decl_param_mty {
                    extended.add_module(
                        *param_id,
                        crate::types::decl::ModuleDeclaration {
                            md_type: param_decl.clone(),
                            md_attributes: vec![],
                            md_loc: crate::types::DeclLoc::none(),
                            md_path: None,
                        },
                    );
                }
                body_env_storage = Some(extended);
                body_env_storage.as_ref()
            } else {
                None
            };

            let result_mty = extract_module_type_from_mod_expr_inner(
                ta,
                ta.module_expr(*body),
                body_env,
                type_ctx,
            )?;
            Some(DeclMty::MtyFunctor {
                param: *param_id,
                param_type: decl_param_mty.map(Box::new),
                result: Box::new(result_mty),
            })
        }
        ModuleExprDesc::Tmod_apply(functor, _arg, _) => {
            let extracted_functor_mty = extract_module_type_from_mod_expr_inner(
                ta,
                ta.module_expr(*functor),
                env,
                type_ctx,
            );
            if let Some(functor_mty) = extracted_functor_mty {
                let resolved_functor_mty = match &functor_mty {
                    DeclMty::MtyIdent(_) | DeclMty::MtyAlias(..) => env
                        .and_then(|env| {
                            let path = functor_mty.ident_or_alias_path().unwrap();
                            resolve_module_type_path_in_env(path, env, type_ctx)
                        })
                        .unwrap_or(functor_mty),
                    _ => functor_mty,
                };
                if let DeclMty::MtyFunctor { result, .. } = resolved_functor_mty {
                    return Some(*result);
                }
            }
            if let (Some(env), ModuleExprDesc::Tmod_ident(path, _)) =
                (env, &ta.module_expr(*functor).mod_desc)
            {
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
                    decl_module_type_from_typed_module_type(ta.module_type(*mty))
                }
                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit => {
                    Some(constrained_mty.clone()).or_else(|| {
                        match &ta.module_expr(*inner).mod_desc {
                            ModuleExprDesc::Tmod_structure(structure) => {
                                Some(DeclMty::MtySignature(std::sync::Arc::new(
                                    crate::types::includemod::simplify_signature(
                                        &structure.str_type,
                                    ),
                                )))
                            }
                            _ => None,
                        }
                    })
                }
            };
            constrained.or_else(|| {
                extract_module_type_from_mod_expr_inner(ta, ta.module_expr(*inner), env, type_ctx)
            })
        }
    }
}

// ============================================================================
// Module Expression Type Checking
// ============================================================================

fn module_type_contains_type(env: &Env, mty: &crate::types::decl::ModuleType) -> bool {
    match mty {
        crate::types::decl::ModuleType::MtyIdent(path) => env
            .lookup_modtype(path)
            .ok()
            .and_then(|mtd| mtd.mtd_type.as_ref())
            .is_none_or(|mty| module_type_contains_type(env, mty)),
        crate::types::decl::ModuleType::MtySignature(sig) => sig
            .iter()
            .any(|item| signature_item_contains_type(env, item)),
        crate::types::decl::ModuleType::MtyFunctor { result, .. } => {
            module_type_contains_type(env, result)
        }
        crate::types::decl::ModuleType::MtyAlias(_, _) => false,
    }
}

fn signature_item_contains_type(env: &Env, item: &crate::types::decl::SignatureItem) -> bool {
    match item {
        crate::types::decl::SignatureItem::SigType(_, decl, _) => {
            decl.type_manifest.is_none()
                || (matches!(decl.type_kind, crate::types::decl::TypeKind::TypeAbstract)
                    && matches!(decl.type_private, crate::types::PrivateFlag::Private))
        }
        crate::types::decl::SignatureItem::SigModtype(_, _) => true,
        crate::types::decl::SignatureItem::SigTypext(_, ext, _) => {
            matches!(
                ext.ext_args,
                crate::types::decl::ConstructorArguments::CstrRecord(_)
            )
        }
        crate::types::decl::SignatureItem::SigModule(_, md, _) => {
            module_type_contains_type(env, &md.md_type)
        }
        crate::types::decl::SignatureItem::SigValue(_, _)
        | crate::types::decl::SignatureItem::SigClass
        | crate::types::decl::SignatureItem::SigClassType => false,
    }
}

fn type_var_report_name(name: Option<&str>) -> String {
    name.map(|name| format!("'{name}"))
        .unwrap_or_else(|| "_".to_string())
}

// Mirrors OCaml `Ctype.closed_type_decl`/`closed_type` for declaration-level
// unbound variables: declared params are marked as allowed, constructor payloads
// and record fields are checked before the manifest, and each checked type
// expression reports the last free variable seen by `free_vars_rec`.
fn collect_unbound_type_vars_in_type_expr(
    ctx: &crate::types::context::TypeContext,
    ty: TypeExprRef,
    allowed: &HashSet<TypeExprRef>,
    visited: &mut HashSet<TypeExprRef>,
    vars: &mut Vec<TypeExprRef>,
) {
    let ty = ctx.repr(ty);
    if allowed.contains(&ty) || !visited.insert(ty) {
        return;
    }

    match &*ctx.get_desc(ty) {
        TypeDesc::Tvar(..) => vars.push(ty),
        TypeDesc::Tobject { fields, .. } => {
            collect_unbound_type_vars_in_type_expr(ctx, *fields, allowed, visited, vars);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            collect_unbound_type_vars_in_type_expr(ctx, *typ, allowed, visited, vars);
            collect_unbound_type_vars_in_type_expr(ctx, *rest, allowed, visited, vars);
        }
        TypeDesc::Tvariant(row) => {
            let row = crate::types::btype::row_repr(ctx, &ctx.row_desc(row));
            for (_, field) in &row.row_fields {
                match crate::types::btype::row_field_repr(ctx, field) {
                    crate::types::RowField::Rpresent(Some(ty)) => {
                        collect_unbound_type_vars_in_type_expr(ctx, ty, allowed, visited, vars);
                    }
                    crate::types::RowField::Reither { types, .. } => {
                        for ty in types {
                            collect_unbound_type_vars_in_type_expr(ctx, ty, allowed, visited, vars);
                        }
                    }
                    _ => {}
                }
            }
            if !crate::types::btype::static_row(ctx, &row) {
                collect_unbound_type_vars_in_type_expr(ctx, row.row_more, allowed, visited, vars);
            }
        }
        _ => {
            crate::types::btype::iter_type_expr(ctx, ty, |child| {
                collect_unbound_type_vars_in_type_expr(ctx, child, allowed, visited, vars);
            });
        }
    }
}

fn find_unbound_type_var_in_type_expr(
    ctx: &crate::types::context::TypeContext,
    ty: TypeExprRef,
    allowed: &HashSet<TypeExprRef>,
) -> Option<TypeExprRef> {
    let mut vars = Vec::new();
    let mut visited = HashSet::new();
    collect_unbound_type_vars_in_type_expr(ctx, ty, allowed, &mut visited, &mut vars);
    vars.last().copied()
}

fn find_unbound_type_var_in_constructor_args(
    ctx: &crate::types::context::TypeContext,
    args: &crate::types::ConstructorArguments,
    allowed: &HashSet<TypeExprRef>,
) -> Option<TypeExprRef> {
    match args {
        crate::types::ConstructorArguments::CstrTuple(types) => types
            .iter()
            .find_map(|ty| find_unbound_type_var_in_type_expr(ctx, *ty, allowed)),
        crate::types::ConstructorArguments::CstrRecord(labels) => labels
            .iter()
            .find_map(|label| find_unbound_type_var_in_type_expr(ctx, label.ld_type, allowed)),
    }
}

fn find_unbound_type_var_in_type_decl(
    ctx: &crate::types::context::TypeContext,
    decl: &crate::types::TypeDeclaration,
) -> Option<TypeExprRef> {
    // OCaml `Ctype.closed_type_decl` (ctype.ml) first runs `mark_type` on every
    // parameter, which marks all nodes reachable from it; variables that a
    // constraint unified into a parameter are therefore bound.
    fn mark_type(
        ctx: &crate::types::context::TypeContext,
        ty: TypeExprRef,
        marked: &mut HashSet<TypeExprRef>,
    ) {
        let ty = ctx.repr(ty);
        if !marked.insert(ty) {
            return;
        }
        let mut children = Vec::new();
        crate::types::btype::iter_type_expr(ctx, ty, |child| children.push(child));
        for child in children {
            mark_type(ctx, child, marked);
        }
    }
    let mut allowed: HashSet<TypeExprRef> = HashSet::new();
    for param in &decl.type_params {
        mark_type(ctx, *param, &mut allowed);
    }
    let allowed = allowed;

    match &decl.type_kind {
        crate::types::TypeKind::TypeVariant(constructors, _) => {
            for cstr in constructors {
                if cstr.cd_res.is_none()
                    && let Some(ty) =
                        find_unbound_type_var_in_constructor_args(ctx, &cstr.cd_args, &allowed)
                {
                    return Some(ty);
                }
            }
        }
        crate::types::TypeKind::TypeRecord(labels, _) => {
            for label in labels {
                if let Some(ty) = find_unbound_type_var_in_type_expr(ctx, label.ld_type, &allowed) {
                    return Some(ty);
                }
            }
        }
        crate::types::TypeKind::TypeAbstract | crate::types::TypeKind::TypeOpen => {}
    }

    decl.type_manifest
        .and_then(|manifest| find_unbound_type_var_in_type_expr(ctx, manifest, &allowed))
}

fn type_var_report_name_from_type_expr(
    ctx: &crate::types::context::TypeContext,
    ty: TypeExprRef,
) -> String {
    match &*ctx.get_desc(ctx.repr(ty)) {
        TypeDesc::Tvar(name) | TypeDesc::Tunivar(name) => type_var_report_name(name.as_deref()),
        _ => "_".to_string(),
    }
}

fn constructor_args_display_type(
    ctx: &crate::types::context::TypeContext,
    args: &crate::types::ConstructorArguments,
) -> Option<TypeExprRef> {
    match args {
        crate::types::ConstructorArguments::CstrTuple(types) => match types.as_slice() {
            [] => None,
            [ty] => Some(*ty),
            _ => Some(ctx.new_tuple(types.clone())),
        },
        crate::types::ConstructorArguments::CstrRecord(labels) => {
            let types = labels.iter().map(|label| label.ld_type).collect::<Vec<_>>();
            match types.as_slice() {
                [] => None,
                [ty] => Some(*ty),
                _ => Some(ctx.new_tuple(types)),
            }
        }
    }
}

fn row_field_display_type(
    ctx: &crate::types::context::TypeContext,
    field: &crate::types::RowField,
) -> Option<TypeExprRef> {
    match crate::types::btype::row_field_repr(ctx, field) {
        crate::types::RowField::Rpresent(Some(ty)) => Some(ty),
        crate::types::RowField::Reither { types, .. } => match types.as_slice() {
            [] => Some(ctx.new_tuple(Vec::new())),
            [ty] => Some(*ty),
            _ => Some(ctx.new_tuple(types)),
        },
        _ => None,
    }
}

/// `explain_unbound_single` (typedecl.ml:2096-2123): `None` when
/// `explain_unbound_gen`'s `List.find` raises `Not_found`.
fn find_unbound_type_var_detail_in_single_type(
    ctx: &crate::types::context::TypeContext,
    unbound: TypeExprRef,
    ty: TypeExprRef,
) -> Option<UnboundTypeVarDetail> {
    let ty = ctx.repr(ty);
    let trivial = || {
        crate::types::ctype::deep_occur(ctx, unbound, ty)
            .then_some(UnboundTypeVarDetail::Type { ty })
    };
    let desc = ctx.get_desc(ty).into_desc();
    match desc {
        TypeDesc::Tobject { fields, .. } => {
            let (fields, rest) = crate::types::ctype::flatten_fields(ctx, fields);
            if rest == ctx.repr(unbound) {
                return trivial();
            }
            fields.into_iter().find_map(|field| {
                crate::types::ctype::deep_occur(ctx, unbound, field.typ).then_some(
                    UnboundTypeVarDetail::Method {
                        name: field.name.to_string(),
                        ty: field.typ,
                    },
                )
            })
        }
        TypeDesc::Tvariant(row) => {
            let row = crate::types::btype::row_repr(ctx, &ctx.row_desc(row));
            if ctx.repr(row.row_more) == ctx.repr(unbound) {
                return trivial();
            }
            row.row_fields.iter().find_map(|(label, field)| {
                let field_ty =
                    row_field_display_type(ctx, field).unwrap_or_else(|| ctx.new_tuple(Vec::new()));
                crate::types::ctype::deep_occur(ctx, unbound, field_ty).then(|| {
                    UnboundTypeVarDetail::Case {
                        name: label.to_string(),
                        ty: field_ty,
                        polymorphic: true,
                    }
                })
            })
        }
        _ => trivial(),
    }
}

fn find_unbound_type_var_detail_in_type_decl(
    ctx: &crate::types::context::TypeContext,
    decl: &crate::types::TypeDeclaration,
    unbound: TypeExprRef,
) -> Option<UnboundTypeVarDetail> {
    match &decl.type_kind {
        crate::types::TypeKind::TypeVariant(constructors, _) => {
            for cstr in constructors {
                if let Some(display_ty) = constructor_args_display_type(ctx, &cstr.cd_args)
                    && crate::types::ctype::deep_occur(ctx, unbound, display_ty)
                {
                    return Some(UnboundTypeVarDetail::Constructor {
                        name: cstr.cd_id.name().to_string(),
                        args: cstr.cd_args.clone(),
                    });
                }
            }
            None
        }
        crate::types::TypeKind::TypeRecord(labels, _) => {
            for label in labels {
                if crate::types::ctype::deep_occur(ctx, unbound, label.ld_type) {
                    return Some(UnboundTypeVarDetail::Field {
                        name: label.ld_id.name().to_string(),
                        ty: label.ld_type,
                    });
                }
            }
            None
        }
        crate::types::TypeKind::TypeAbstract => decl.type_manifest.and_then(|manifest| {
            find_unbound_type_var_detail_in_single_type(ctx, unbound, manifest)
        }),
        crate::types::TypeKind::TypeOpen => None,
    }
}

fn find_unbound_type_var_in_typed_core_type_before_closed_decl(
    ta: &TypedArena,
    ctx: &crate::types::context::TypeContext,
    ctyp: &TypedCoreType,
    allowed: &HashSet<TypeExprRef>,
) -> Option<(String, LocIdx)> {
    match &ctyp.ctyp_desc {
        TypedCoreTypeDesc::Ttyp_var(name) => {
            let ty = ctx.repr(ctyp.ctyp_type);
            match &*ctx.get_desc(ty) {
                TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) => {
                    (!allowed.contains(&ty)).then(|| (type_var_report_name(name.as_deref()), ctyp.ctyp_loc))
                }
                _ => None,
            }
        }
        TypedCoreTypeDesc::Ttyp_arrow(args, ret) => args
            .iter()
            .find_map(|arg| {
                find_unbound_type_var_in_typed_core_type_before_closed_decl(
                    ta,
                    ctx,
                    ta.core_type(arg.typ),
                    allowed,
                )
            })
            .or_else(|| {
                find_unbound_type_var_in_typed_core_type_before_closed_decl(
                    ta,
                    ctx,
                    ta.core_type(*ret),
                    allowed,
                )
            }),
        TypedCoreTypeDesc::Ttyp_tuple(types) | TypedCoreTypeDesc::Ttyp_constr(_, _, types) => {
            ta.core_types(*types).find_map(|ctyp| {
                find_unbound_type_var_in_typed_core_type_before_closed_decl(ta, ctx, ctyp, allowed)
            })
        }
        TypedCoreTypeDesc::Ttyp_poly(_, body) => {
            let mut allowed = allowed.clone();
            if let TypeDesc::Tpoly { vars, .. } = &*ctx.get_desc(ctx.repr(ctyp.ctyp_type)) {
                allowed.extend(ctx.type_list(vars).iter().map(|var| ctx.repr(var)));
            }
            find_unbound_type_var_in_typed_core_type_before_closed_decl(
                ta,
                ctx,
                ta.core_type(*body),
                &allowed,
            )
        }
        TypedCoreTypeDesc::Ttyp_alias(body, _) => {
            find_unbound_type_var_in_typed_core_type_before_closed_decl(
                ta,
                ctx,
                ta.core_type(*body),
                allowed,
            )
        }
        TypedCoreTypeDesc::Ttyp_object(_, _)
        | TypedCoreTypeDesc::Ttyp_variant(_, _, _)
        | TypedCoreTypeDesc::Ttyp_package(_) => None,
    }
}

fn find_unbound_type_var_in_typed_core_type(
    ta: &TypedArena,
    ctx: &crate::types::context::TypeContext,
    ctyp: &TypedCoreType,
    allowed: &HashSet<TypeExprRef>,
) -> Option<(String, LocIdx)> {
    match &ctyp.ctyp_desc {
        TypedCoreTypeDesc::Ttyp_var(name) => {
            let ty = ctx.repr(ctyp.ctyp_type);
            match &*ctx.get_desc(ty) {
                TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) => {
                    (!allowed.contains(&ty)).then(|| (type_var_report_name(name.as_deref()), ctyp.ctyp_loc))
                }
                _ => None,
            }
        }
        TypedCoreTypeDesc::Ttyp_arrow(args, ret) => args
            .iter()
            .find_map(|arg| {
                find_unbound_type_var_in_typed_core_type(ta, ctx, ta.core_type(arg.typ), allowed)
            })
            .or_else(|| {
                find_unbound_type_var_in_typed_core_type(ta, ctx, ta.core_type(*ret), allowed)
            }),
        TypedCoreTypeDesc::Ttyp_tuple(types) | TypedCoreTypeDesc::Ttyp_constr(_, _, types) => ta
            .core_types(*types)
            .find_map(|ctyp| find_unbound_type_var_in_typed_core_type(ta, ctx, ctyp, allowed)),
        TypedCoreTypeDesc::Ttyp_poly(_, body) => {
            let mut allowed = allowed.clone();
            if let TypeDesc::Tpoly { vars, .. } = &*ctx.get_desc(ctx.repr(ctyp.ctyp_type)) {
                allowed.extend(ctx.type_list(vars).iter().map(|var| ctx.repr(var)));
            }
            find_unbound_type_var_in_typed_core_type(ta, ctx, ta.core_type(*body), &allowed)
        }
        TypedCoreTypeDesc::Ttyp_alias(body, _) => {
            find_unbound_type_var_in_typed_core_type(ta, ctx, ta.core_type(*body), allowed)
        }
        TypedCoreTypeDesc::Ttyp_object(fields, _) => {
            fields.iter().find_map(|field| match &field.of_desc {
                crate::types::typedtree::ObjectFieldDesc::OTtag(_, ty)
                | crate::types::typedtree::ObjectFieldDesc::OTinherit(ty) => {
                    find_unbound_type_var_in_typed_core_type(ta, ctx, ta.core_type(*ty), allowed)
                }
            })
        }
        TypedCoreTypeDesc::Ttyp_variant(rows, _, _) => {
            rows.iter().find_map(|row| match &row.rf_desc {
                crate::types::typedtree::RowFieldDesc::Rtag(_, _, types) => {
                    ta.core_types(*types).find_map(|ctyp| {
                        find_unbound_type_var_in_typed_core_type(ta, ctx, ctyp, allowed)
                    })
                }
                crate::types::typedtree::RowFieldDesc::Rinherit(ctyp) => {
                    find_unbound_type_var_in_typed_core_type(ta, ctx, ta.core_type(*ctyp), allowed)
                }
            })
        }
        TypedCoreTypeDesc::Ttyp_package(package) => {
            package.pack_fields.iter().find_map(|(_, ctyp)| {
                find_unbound_type_var_in_typed_core_type(ta, ctx, ta.core_type(*ctyp), allowed)
            })
        }
    }
}

fn find_unbound_type_var_in_typed_type_constructor_args_before_closed_decl(
    ta: &TypedArena,
    ctx: &crate::types::context::TypeContext,
    args: &TypedConstructorArguments,
    allowed: &HashSet<TypeExprRef>,
) -> Option<(String, LocIdx)> {
    match args {
        TypedConstructorArguments::Cstr_tuple(types) => ta.core_types(*types).find_map(|ctyp| {
            find_unbound_type_var_in_typed_core_type_before_closed_decl(ta, ctx, ctyp, allowed)
        }),
        TypedConstructorArguments::Cstr_record(labels) => labels.iter().find_map(|label| {
            find_unbound_type_var_in_typed_core_type_before_closed_decl(
                ta,
                ctx,
                ta.core_type(label.ld_type),
                allowed,
            )
        }),
    }
}

fn find_unbound_type_var_in_typed_type_decl_before_closed_decl(
    ta: &TypedArena,
    ctx: &crate::types::context::TypeContext,
    decl: &TypedTypeDeclaration,
) -> Option<(String, LocIdx)> {
    let mut allowed: HashSet<TypeExprRef> = decl
        .typ_type
        .type_params
        .iter()
        .map(|ty_ref| ctx.repr(*ty_ref))
        .collect();
    // OCaml typedecl.ml `transl_declaration` translates the constraints with
    // `transl_simple_type env false` after the parameters, so the type
    // variables they introduce are in the type-variable table when the kind
    // and manifest are translated with the fixed policy.
    fn collect_type_vars(
        ctx: &crate::types::context::TypeContext,
        ty: TypeExprRef,
        visited: &mut HashSet<TypeExprRef>,
        out: &mut HashSet<TypeExprRef>,
    ) {
        let ty = ctx.repr(ty);
        if !visited.insert(ty) {
            return;
        }
        if matches!(&*ctx.borrow_desc(ty), TypeDesc::Tvar(..)) {
            out.insert(ty);
            return;
        }
        let mut children = Vec::new();
        crate::types::btype::iter_type_expr(ctx, ty, |child| children.push(child));
        for child in children {
            collect_type_vars(ctx, child, visited, out);
        }
    }
    let mut visited = HashSet::new();
    for (cty, cty2, _) in &decl.typ_cstrs {
        collect_type_vars(
            ctx,
            ta.core_type(*cty).ctyp_type,
            &mut visited,
            &mut allowed,
        );
        collect_type_vars(
            ctx,
            ta.core_type(*cty2).ctyp_type,
            &mut visited,
            &mut allowed,
        );
    }
    let allowed = allowed;
    match &decl.typ_kind {
        TypedTypeKind::Ttype_variant(constructors) => constructors.iter().find_map(|cstr| {
            // OCaml Typedecl.make_constructor locally quantifies GADT
            // constructor arguments/results, so they do not become unbound
            // declaration parameters at this earlier type-expression phase.
            if cstr.cd_res.is_some() {
                None
            } else {
                find_unbound_type_var_in_typed_type_constructor_args_before_closed_decl(
                    ta,
                    ctx,
                    &cstr.cd_args,
                    &allowed,
                )
            }
        }),
        TypedTypeKind::Ttype_record(labels) => labels.iter().find_map(|label| {
            find_unbound_type_var_in_typed_core_type_before_closed_decl(
                ta,
                ctx,
                ta.core_type(label.ld_type),
                &allowed,
            )
        }),
        TypedTypeKind::Ttype_abstract | TypedTypeKind::Ttype_open => {
            decl.typ_manifest.as_ref().and_then(|ctyp| {
                find_unbound_type_var_in_typed_core_type_before_closed_decl(
                    ta,
                    ctx,
                    ta.core_type(*ctyp),
                    &allowed,
                )
            })
        }
    }
}

fn find_unbound_type_var_in_typed_constructor_args(
    ta: &TypedArena,
    ctx: &crate::types::context::TypeContext,
    args: &crate::types::typedtree::ConstructorArgument,
    allowed: &HashSet<TypeExprRef>,
) -> Option<(String, LocIdx)> {
    match args {
        crate::types::typedtree::ConstructorArgument::Cstr_tuple(types) => ta
            .core_types(*types)
            .find_map(|ctyp| find_unbound_type_var_in_typed_core_type(ta, ctx, ctyp, allowed)),
        crate::types::typedtree::ConstructorArgument::Cstr_record(labels) => {
            labels.iter().find_map(|label| {
                find_unbound_type_var_in_typed_core_type(
                    ta,
                    ctx,
                    ta.core_type(label.ld_type),
                    allowed,
                )
            })
        }
    }
}

fn find_unbound_type_var_in_typed_type_decl(
    ta: &TypedArena,
    ctx: &crate::types::context::TypeContext,
    decl: &TypedTypeDeclaration,
) -> Option<(
    String,
    LocIdx,
    Option<UnboundTypeVarDetail>,
    Option<TypeExprRef>,
)> {
    if let Some((name, loc)) =
        find_unbound_type_var_in_typed_type_decl_before_closed_decl(ta, ctx, decl)
    {
        return Some((name, loc, None, None));
    }

    if let Some(unbound) = find_unbound_type_var_in_type_decl(ctx, &decl.typ_type) {
        // typedecl.ml:2182-2201: no explanation when no constructor, field or
        // manifest mentions the variable.
        let detail = find_unbound_type_var_detail_in_type_decl(ctx, &decl.typ_type, unbound);
        return Some((
            type_var_report_name_from_type_expr(ctx, unbound),
            decl.typ_loc,
            detail,
            Some(unbound),
        ));
    }

    None
}

pub(crate) fn type_expr_has_free_variables(
    ctx: &crate::types::context::TypeContext,
    ty: TypeExprRef,
) -> bool {
    // OCaml `Ctype.free_variables` only traverses unmarked nodes and reports
    // `Tvar` nodes for this env-less call site.
    fn loop_(
        ctx: &crate::types::context::TypeContext,
        ty: TypeExprRef,
        visited: &mut HashSet<TypeExprRef>,
    ) -> bool {
        let ty = ctx.repr(ty);
        if ctx.get_level(ty) < LOWEST_LEVEL {
            return false;
        }
        if !visited.insert(ty) {
            return false;
        }
        match &*ctx.get_desc(ty) {
            crate::types::type_expr::TypeDesc::Tvar(..) => true,
            _ => {
                let mut has_free = false;
                crate::types::btype::iter_type_expr(ctx, ty, |child| {
                    if !has_free && loop_(ctx, child, visited) {
                        has_free = true;
                    }
                });
                has_free
            }
        }
    }

    loop_(ctx, ty, &mut HashSet::default())
}

fn type_module_expr_with_alias<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
    alias: bool,
    sttn: bool,
) -> TypeModResult<ModuleExpr> {
    // OCaml compiler/ml/typemod.ml:1222 wraps every `type_module` call in
    // `Builtin_attributes.warning_scope smod.pmod_attributes`.
    with_warning_scope(tctx, arena, &mod_expr.pmod_attributes, true, |tctx| {
        type_module_expr_with_alias_inner(tctx, env, arena, mod_expr, alias, sttn)
    })
}

fn type_module_expr_with_alias_inner<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
    alias: bool,
    sttn: bool,
) -> TypeModResult<ModuleExpr> {
    let loc = mod_expr.pmod_loc;

    match &mod_expr.pmod_desc {
        ParsedModuleExprDesc::Pmod_ident(lid) => {
            // Module identifier: M
            // Look up the module path in the environment
            let longident = tctx.resolve_lid(lid.txt).clone();
            crate::types::typecore::mark_open_lid_use(
                tctx.type_ctx,
                env,
                arena,
                &longident,
                crate::types::env::OpenLookupKind::Module,
                Some(mod_expr.pmod_loc),
            );
            let path =
                lookup_module_path_for_module_expr(tctx, env, arena, &longident, !alias, loc)?;
            let aliasable = !env.is_functor_arg_path(&path);
            let mod_type = if alias && aliasable {
                None
            } else if alias {
                // Match compiler/ml/typemod.ml:1238-1260: aliases rooted in
                // functor parameters are not aliasable, so OCaml falls back
                // to the module declaration type from Env.find_module.
                lookup_module_type_by_lid(
                    &longident,
                    arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
            } else {
                // OCaml compiler/ml/typemod.ml:1227-1255 keeps
                // `Typetexp.lookup_module` path lookup separate from the later
                // `Env.find_module` alias branch. For dotted aliases such as
                // `Belt.Id.MakeComparable`, preserve the parent alias without
                // forcing the final child module-declaration thunk; the actual
                // expansion happens below when matching typemod.ml:1245-1255.
                lookup_module_alias_by_lid(
                    &longident,
                    arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .map(|(alias_presence, alias_path)| {
                    crate::types::decl::ModuleType::MtyAlias(alias_presence, alias_path)
                })
                .or_else(|| {
                    lookup_module_type_by_lid(
                        &longident,
                        arena,
                        env,
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )
                })
            };
            let path_clone = path;
            let env_ref = tctx.type_ctx.store_typed_env(env);
            // OCaml compiler/ml/typemod.ml:1227-1235 keeps the looked-up path
            // in `Tmod_ident`, while compiler/ml/env.ml:781-793 and 800-813
            // resolve later qualified type lookups through `find_module_descr`
            // component tables. For ReScript flattened submodules, those
            // components point at the flattened compile unit; keep the printed
            // module path intact but store that flattened alias as the semantic
            // module type so `S.t` reaches `Belt_MutableStack.t` before forcing
            // `Belt.ps_sig`.
            let semantic_alias_path = if alias {
                // OCaml compiler/ml/typemod.ml:1227-1235 uses the looked-up
                // path itself for `Pmod_ident` in alias mode. Later value
                // lookup/normalization follows that alias through Env
                // components, which preserves runtime aliases like
                // `Js.Dict -> Js_dict` instead of guessing `Js_Dict`.
                path
            } else {
                flattened_persistent_alias_path(&path, tctx.persistent_env.as_ref()).unwrap_or(path)
            };
            let alias_mod_type = crate::types::decl::ModuleType::MtyAlias(
                crate::types::decl::AliasPresence::MtaAbsent,
                std::sync::Arc::new(semantic_alias_path),
            );
            let wraps_alias = !alias
                && matches!(
                    mod_type,
                    Some(crate::types::decl::ModuleType::MtyAlias(_, _))
                );
            let semantic_mod_type = if alias && aliasable {
                alias_mod_type.clone()
            } else if wraps_alias {
                // OCaml compiler/ml/typemod.ml:1227-1255 builds the inner
                // `Tmod_ident` with `Mty_alias(Mta_absent, path)`, then only
                // expands and strengthens the normalized alias target for the
                // outer implicit `Tmod_constraint`. Avoid strengthening this
                // throwaway inner alias eagerly; that would force
                // Subst.modtype work before typemod.ml:1245-1255 does.
                alias_mod_type.clone()
            } else {
                // typemod.ml:1253-1256: strengthen only when `sttn`.
                mod_type
                    .clone()
                    .map(|mty| {
                        if sttn {
                            strengthen_semantic_ident_module_type(
                                env,
                                &path,
                                mty,
                                &mut tctx.persistent_env,
                                tctx.type_ctx,
                            )
                        } else {
                            mty
                        }
                    })
                    .unwrap_or_else(|| crate::types::decl::ModuleType::MtyIdent(path))
            };
            let ident_mod = ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_ident(path, *lid),
                mod_loc: loc,
                mod_type: semantic_mod_type,
                mod_env: env_ref,
                mod_attributes: mod_expr.pmod_attributes.clone(),
            };

            if wraps_alias {
                // OCaml (typemod.ml line 1245-1252): when the module type is an alias
                // and we're not in alias mode, wrap with Tcoerce_alias(p1, Tcoerce_none)
                // where p1 is the alias target path. The inner Tmod_ident should have
                // mod_type = Mty_alias(Mta_absent, path).
                let alias_target = match &mod_type {
                    Some(crate::types::decl::ModuleType::MtyAlias(_, p1)) => {
                        // Match OCaml compiler/ml/typemod.ml:1245-1252:
                        // normalize the alias target before Tcoerce_alias.
                        match normalize_module_alias_path_checked(
                            env,
                            &mut tctx.persistent_env,
                            tctx.type_ctx,
                            p1,
                        ) {
                            Ok(alias_target) => alias_target,
                            Err((path, expanded)) => {
                                return Err(TypeModError::MissingModule {
                                    loc,
                                    path,
                                    expanded,
                                });
                            }
                        }
                    }
                    _ => path_clone,
                };
                let mut inner = ident_mod;
                inner.mod_type = crate::types::decl::ModuleType::MtyAlias(
                    crate::types::decl::AliasPresence::MtaAbsent,
                    std::sync::Arc::new(path_clone),
                );
                let constrained_mod_type = resolve_module_path_module_type(
                    &alias_target,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .unwrap_or(crate::types::decl::ModuleType::MtyIdent(alias_target));
                // typemod.ml:1250-1251: strengthen only when `sttn`.
                let outer_mod_type = if sttn {
                    strengthen_semantic_ident_module_type(
                        env,
                        &alias_target,
                        constrained_mod_type.clone(),
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )
                } else {
                    constrained_mod_type.clone()
                };

                Ok(ModuleExpr {
                    mod_desc: ModuleExprDesc::Tmod_constraint(
                        tctx.typed.push_module_expr(inner),
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
            let structure_mty = crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(
                structure.str_type.clone(),
            ));

            // Match compiler/ml/typemod.ml:1263-1282. OCaml first builds the
            // raw `Tmod_structure`, then calls `simplify_signature`; if that
            // shrinks the signature, `wrap_constraint` runs the inclusion
            // check at compiler/ml/typemod.ml:1205-1217.
            let simplified_structure_sig = simplified_structure_signature(&structure);
            // typemod.ml: `check_js_names ~toplevel:false sg'` on the
            // simplified signature.
            check_js_names(
                tctx.type_ctx,
                false,
                simplified_structure_sig
                    .as_deref()
                    .unwrap_or(&structure.str_type),
            )?;

            let md = ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_structure(structure),
                mod_loc: loc,
                mod_type: structure_mty.clone(),
                mod_env: env_ref,
                mod_attributes: mod_expr.pmod_attributes.clone(),
            };

            if let Some(simplified_structure_sig) = simplified_structure_sig {
                let simplified = crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(
                    simplified_structure_sig,
                ));
                let mut inclusion_warnings = Vec::new();
                // typemod.ml:1279-1281: `wrap_constraint (Env.implicit_coercion
                // env)`, so the inclusion marks nothing used.
                let coercion_result = crate::types::includemod::modtypes_with_warnings(
                    tctx.type_ctx,
                    &env.implicit_coercion(),
                    &md.mod_type,
                    &simplified,
                    &mut inclusion_warnings,
                );
                report_inclusion_warnings(tctx, loc, inclusion_warnings);
                let coercion_result =
                    crate::types::includemod::escaped(tctx.type_ctx, coercion_result)?;
                let coercion = coercion_result.map_err(|err| TypeModError::SignatureMismatch {
                    loc,
                    error: Box::new(err),
                })?;
                Ok(ModuleExpr {
                    mod_desc: ModuleExprDesc::Tmod_constraint(
                        tctx.typed.push_module_expr(md),
                        simplified.clone(),
                        crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
                        coercion,
                    ),
                    mod_loc: loc,
                    mod_type: simplified,
                    mod_env: env_ref,
                    mod_attributes: Attributes::new(),
                })
            } else {
                Ok(md)
            }
        }

        ParsedModuleExprDesc::Pmod_functor(inner) => {
            let (ref name, ref param_type, ref body_idx) = **inner;
            // Functor: (X: S) => ME
            let param_name = arena.get_string(name.txt).to_string();

            // OCaml translates the parameter module type before creating the
            // functor parameter ident (Typemod.type_module, Pmod_functor).
            let typed_param_type = match param_type {
                Some(pt) => Some(Box::new(transl_modtype(
                    tctx,
                    env,
                    arena,
                    arena.get_mod_type(*pt),
                )?)),
                None => None,
            };
            let param_decl_type = typed_param_type.as_ref().map(|mty| mty.mty_type.clone());
            let param_id = tctx.type_ctx.create_ident(&param_name);

            // Extend environment with the functor parameter module
            let mut functor_env = env.clone();
            if let Some(param_decl_type) = param_decl_type {
                functor_env.add_module_arg(
                    param_id,
                    crate::types::decl::ModuleDeclaration {
                        md_type: param_decl_type,
                        md_attributes: vec![],
                        md_loc: crate::types::DeclLoc::none(),
                        md_path: None,
                    },
                );
            }

            // OCaml typemod.ml calls Ctype.init_def(Ident.current_time()) before
            // typing functor bodies.
            let ctx = tctx.type_ctx;
            ctx.init_def(ctx.current_stamp());
            let env_ref = tctx.type_ctx.store_typed_env(env);

            // Type check the functor body with the extended environment
            let body = arena.get_mod_expr(*body_idx);
            let previous_applicative_functor_body_depth = tctx.applicative_functor_body_depth;
            if typed_param_type.is_some() {
                tctx.applicative_functor_body_depth += 1;
            }
            let typed_body_result =
                type_module_expr_with_alias(tctx, &functor_env, arena, body, false, sttn);
            tctx.applicative_functor_body_depth = previous_applicative_functor_body_depth;
            let typed_body = typed_body_result?;
            let functor_mty = crate::types::decl::ModuleType::MtyFunctor {
                param: param_id,
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
                    typed_param_type.map(|mty| tctx.typed.push_module_type(*mty)),
                    tctx.typed.push_module_expr(typed_body),
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
            // OCaml compiler/ml/typemod.ml:1305-1307 types the argument
            // before the functor, computes `path_of_module arg`, then types
            // the functor. Keep that order because package/type-constraint
            // forcing during argument typing must happen before functor
            // substitution can allocate hidden identifiers.
            let typed_arg = type_module_expr_with_alias(tctx, env, arena, arg, false, true)?;
            let arg_path = path_of_typed_module_expr(&tctx.typed, &typed_arg);
            let typed_functor = type_module_expr_with_alias(
                tctx,
                env,
                arena,
                functor,
                false,
                sttn && arg_path.is_some(),
            )?;
            let arg_mty = typed_arg.mod_type.clone();
            let functor_mty = typed_functor.mod_type.clone();
            let functor_mty = scrape_alias_module_type(
                &functor_mty,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .unwrap_or(functor_mty);
            if matches!(
                &functor_mty,
                crate::types::decl::ModuleType::MtyFunctor {
                    param_type: None,
                    ..
                }
            ) && !matches!(
                &arg.pmod_desc,
                ParsedModuleExprDesc::Pmod_structure(items) if items.is_empty()
            ) {
                return Err(TypeModError::ApplyGenerative {
                    loc: functor.pmod_loc,
                });
            }
            if matches!(
                &functor_mty,
                crate::types::decl::ModuleType::MtyFunctor {
                    param_type: None,
                    ..
                }
            ) && tctx.applicative_functor_body_depth > 0
                && module_type_contains_type(env, &typed_functor.mod_type)
            {
                return Err(TypeModError::NotAllowedInFunctorBody { loc });
            }
            let env_ref = tctx.type_ctx.store_typed_env(env);
            let coercion = match &functor_mty {
                crate::types::decl::ModuleType::MtyFunctor { param_type, .. } => {
                    let param_mty = param_type
                        .as_ref()
                        .map(|inner| (**inner).clone())
                        .unwrap_or_else(|| {
                            crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(
                                vec![],
                            ))
                        });
                    let mut inclusion_warnings = Vec::new();
                    let coercion_result = crate::types::includemod::modtypes_with_warnings(
                        tctx.type_ctx,
                        env,
                        &arg_mty,
                        &param_mty,
                        &mut inclusion_warnings,
                    );
                    report_inclusion_warnings(tctx, arg.pmod_loc, inclusion_warnings);
                    let coercion_result =
                        crate::types::includemod::escaped(tctx.type_ctx, coercion_result)?;
                    coercion_result.map_err(|err| TypeModError::SignatureMismatch {
                        loc: arg.pmod_loc,
                        error: Box::new(err),
                    })?
                }
                _ => {
                    return Err(TypeModError::CannotApply {
                        loc: functor.pmod_loc,
                        mty: typed_functor.mod_type.clone(),
                        origin: persistent_module_origin(&typed_functor),
                    });
                }
            };
            let applied_mty = match &functor_mty {
                crate::types::decl::ModuleType::MtyFunctor {
                    param,
                    param_type,
                    result,
                } => {
                    match arg_path.as_ref() {
                        Some(path) => {
                            crate::cmi::persistent_env::substitute_functor_result_module_path(
                                result,
                                param,
                                path,
                                tctx.type_ctx,
                            )
                        }
                        None => {
                            // OCaml: Mtype.nondep_supertype
                            //   (Env.add_module ~arg:true param arg.mod_type env)
                            //   param mty_res
                            let generative = param_type.is_none();
                            if generative {
                                (**result).clone()
                            } else {
                                let mut nondep_env = env.clone();
                                nondep_env.add_module_arg(
                                    *param,
                                    crate::types::decl::ModuleDeclaration {
                                        md_type: arg_mty.clone(),
                                        md_attributes: vec![],
                                        md_loc: crate::types::DeclLoc::none(),
                                        md_path: None,
                                    },
                                );
                                nondep_supertype(tctx.type_ctx, &nondep_env, param, result)
                                    .ok_or_else(|| TypeModError::CannotEliminateDependency {
                                        loc,
                                        mty: functor_mty.clone(),
                                    })?
                            }
                        }
                    }
                }
                _ => crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(vec![])),
            };
            let typed_apply = ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_apply(
                    tctx.typed.push_module_expr(typed_functor),
                    tctx.typed.push_module_expr(typed_arg),
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
            let typed_mod =
                type_module_expr_with_alias(tctx, env, arena, mod_expr_inner, alias, true)?;
            let typed_mty = transl_modtype(tctx, env, arena, arena.get_mod_type(*mod_type_idx))?;
            // OCaml compiler/ml/typemod.ml:1359-1367 passes
            // `mty.mty_type` from the just-translated module type directly to
            // `wrap_constraint`; it does not re-run module-type translation.
            let decl_mty = decl_module_type_from_typed(&typed_mty).unwrap_or(
                crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(vec![])),
            );
            let typed_mty_idx = tctx.typed.push_module_type(typed_mty);
            let constrained = wrap_constraint_with_decl_mty(
                tctx,
                env,
                typed_mod,
                decl_mty,
                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(typed_mty_idx),
                loc,
                mod_expr.pmod_attributes.clone(),
            )?;
            Ok(constrained)
        }

        ParsedModuleExprDesc::Pmod_unpack(expr_idx) => {
            // Unpack: unpack(E)
            let expr = arena.get_expanded_expr(*expr_idx);
            // Matches compiler/ml/typemod.ml:1358-1366: `Pmod_unpack` types
            // its payload with `Typecore.type_exp`, not top-level
            // `type_expression`, so no extra begin_def/end_def scope is added.
            let typed_expr = type_exp(tctx, env, expr, None)?;
            let expanded =
                crate::types::ctype::expand_head(tctx.type_ctx, env, typed_expr.exp_type);
            let unpack_mty = match &*tctx.type_ctx.get_desc(tctx.type_ctx.repr(expanded)) {
                crate::types::type_expr::TypeDesc::Tpackage { path, lids, args } => {
                    if tctx
                        .type_ctx
                        .type_list(args)
                        .iter()
                        .any(|arg| type_expr_has_free_variables(tctx.type_ctx, arg))
                    {
                        return Err(TypeModError::IncompletePackedModule { loc, ty: expanded });
                    }
                    module_type_from_typed_unpack_expr(tctx, env, arena, &typed_expr)
                        .unwrap_or_else(|| {
                            modtype_of_package(
                                env,
                                path,
                                &tctx.type_ctx.package_lids(lids),
                                &tctx.type_ctx.type_list(args).to_smallvec::<4>(),
                                arena,
                                &mut tctx.persistent_env,
                                tctx.type_ctx,
                            )
                            .unwrap_or({ crate::types::decl::ModuleType::MtyIdent(*path) })
                        })
                }
                crate::types::type_expr::TypeDesc::Tvar(..)
                | crate::types::type_expr::TypeDesc::Tunivar(..) => {
                    return Err(TypeModError::CoreError(
                        TypeCoreError::CannotInferSignature { loc },
                    ));
                }
                _ => {
                    return Err(TypeModError::NotAPackedModule { loc, ty: expanded });
                }
            };
            if tctx.applicative_functor_body_depth > 0
                && module_type_contains_type(env, &unpack_mty)
            {
                return Err(TypeModError::NotAllowedInFunctorBody { loc });
            }
            let env_ref = tctx.type_ctx.store_typed_env(env);
            tctx.module_expr_semantic_types
                .insert(mod_expr.pmod_loc, unpack_mty.clone());

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_unpack(
                    tctx.push_expr(typed_expr),
                    unpack_mty.clone(),
                ),
                mod_loc: loc,
                mod_type: unpack_mty,
                mod_env: env_ref,
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_extension(ext) => Err(TypeModError::CoreError(
            crate::types::typecore::builtin_extension_error(arena, ext),
        )),

        // typemod.ml `Pmod_await`: the builtin ppx turns the dynamic import
        // forms into `unpack` and removes any other `await`, which has no
        // effect; this only types a tree that bypassed it.
        ParsedModuleExprDesc::Pmod_await(inner) => {
            let mut arg = type_module_expr_with_alias(
                tctx,
                env,
                arena,
                arena.get_mod_expr(*inner),
                alias,
                sttn,
            )?;
            arg.mod_loc = loc;
            arg.mod_attributes
                .extend(mod_expr.pmod_attributes.iter().cloned());
            Ok(arg)
        }
    }
}

fn wrap_constraint_with_decl_mty<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arg: ModuleExpr,
    decl_mty: crate::types::decl::ModuleType,
    explicit: crate::types::typedtree::ModuleTypeConstraint,
    mod_loc: LocIdx,
    mod_attributes: Attributes,
) -> TypeModResult<ModuleExpr> {
    let arg_mty = decl_module_type_from_typed_module_expr_for_constraint_arg(&arg)
        .or_else(|| {
            extract_module_type_from_mod_expr_with_ctx(&tctx.typed, &arg, Some(env), tctx.type_ctx)
        })
        .or_else(|| Some(arg.mod_type.clone()))
        .unwrap_or(crate::types::decl::ModuleType::MtySignature(
            std::sync::Arc::new(vec![]),
        ));
    let include_decl_mty = decl_mty.clone();
    wrap_checked_constraint(
        tctx,
        env,
        arg,
        &arg_mty,
        &include_decl_mty,
        ConstraintNode {
            mty: decl_mty,
            explicit,
            loc: mod_loc,
            attributes: mod_attributes,
        },
    )
}

/// The `Tmod_constraint` node wrapped around a module expression.
struct ConstraintNode {
    /// The module type the constraint gives the module.
    mty: crate::types::decl::ModuleType,
    explicit: crate::types::typedtree::ModuleTypeConstraint,
    loc: LocIdx,
    attributes: Attributes,
}

/// Check that `arg_mty` is included in `decl_mty` and wrap `arg` in the
/// resulting coercion.
fn wrap_checked_constraint<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arg: ModuleExpr,
    arg_mty: &crate::types::decl::ModuleType,
    decl_mty: &crate::types::decl::ModuleType,
    node: ConstraintNode,
) -> TypeModResult<ModuleExpr> {
    let error_loc = arg.mod_loc;
    let mut inclusion_warnings = Vec::new();
    let coercion_result = crate::types::includemod::modtypes_with_warnings(
        tctx.type_ctx,
        env,
        arg_mty,
        decl_mty,
        &mut inclusion_warnings,
    );
    report_inclusion_warnings(tctx, error_loc, inclusion_warnings);
    let coercion_result =
        crate::types::includemod::escaped(tctx.type_ctx, coercion_result)?;
    let coercion = coercion_result.map_err(|err| TypeModError::SignatureMismatch {
        loc: error_loc,
        error: Box::new(err),
    })?;
    let env_ref = tctx.type_ctx.store_typed_env(env);

    Ok(ModuleExpr {
        mod_desc: ModuleExprDesc::Tmod_constraint(
            tctx.typed.push_module_expr(arg),
            node.mty.clone(),
            node.explicit,
            coercion,
        ),
        mod_loc: node.loc,
        mod_type: node.mty,
        mod_env: env_ref,
        mod_attributes: node.attributes,
    })
}

fn recmodule_substitute_module_path(path: &Path, subst: &[(Ident, Path)]) -> Path {
    match path.view() {
        PathView::Pident(id) => subst
            .iter()
            .find_map(|(old_id, new_path)| old_id.same(id).then_some(*new_path))
            .unwrap_or(*path),
        PathView::Pdot(prefix, name, pos) => {
            Path::pdot_pos(recmodule_substitute_module_path(prefix, subst), *name, *pos)
        }
        PathView::Papply(functor, arg) => Path::papply(
            recmodule_substitute_module_path(functor, subst),
            recmodule_substitute_module_path(arg, subst),
        ),
    }
}

fn recmodule_subst_modtype(
    ctx: &crate::types::context::TypeContext,
    subst: &[(Ident, Path)],
    mty: &crate::types::decl::ModuleType,
) -> crate::types::decl::ModuleType {
    crate::cmi::persistent_env::substitute_module_type_with_module_path_subst(mty, subst, ctx)
}

fn recmodule_subst_and_strengthen(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    subst: &[(Ident, Path)],
    id: &Ident,
    mty: &crate::types::decl::ModuleType,
) -> crate::types::decl::ModuleType {
    // OCaml compiler/ml/typemod.ml:1069-1072:
    //   Mtype.strengthen ~aliasable:false env (Subst.modtype s mty)
    //     (Subst.module_path s (Pident id))
    let substituted = recmodule_subst_modtype(ctx, subst, mty);
    let module_path = recmodule_substitute_module_path(&Path::pident(*id), subst);
    crate::types::ctype::strengthen_module_type_for_non_aliasable_path(
        ctx,
        env,
        &module_path,
        &substituted,
    )
}

/// Type check a module expression.
pub fn type_module_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
) -> TypeModResult<ModuleExpr> {
    type_module_expr_with_alias(tctx, env, arena, mod_expr, false, true)
}

/// Type check a module expression with explicit alias-preservation mode.
pub fn type_module_expr_with_alias_mode<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
    alias: bool,
) -> TypeModResult<ModuleExpr> {
    type_module_expr_with_alias(tctx, env, arena, mod_expr, alias, true)
}

/// Failure path of OCaml `type_open_` (compiler/ml/typemod.ml:88-95) once every
/// Rust open route failed: `Typetexp.lookup_module` raises for an unbound module,
/// and `extract_sig_open` raises `Structure_expected` for a non-structure.
pub(crate) fn open_failure_path(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    arena: &ParseArena,
    lid: &Longident,
    lid_loc: LocIdx,
) -> Result<Path, TypeModError> {
    let Some(path) =
        lookup_module_path_by_lid(lid, arena, env, &mut tctx.persistent_env, tctx.type_ctx)
    else {
        return Err(TypeModError::CoreError(
            crate::types::typecore::unbound_module_lookup_error(tctx, env, lid_loc, lid),
        ));
    };
    if let Some(err) = structure_expected_error_for_open(tctx, env, arena, lid, lid_loc) {
        return Err(err);
    }
    Ok(path)
}

fn structure_expected_error_for_open(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    arena: &ParseArena,
    lid: &Longident,
    loc: LocIdx,
) -> Option<TypeModError> {
    let path = lookup_module_path_by_lid(lid, arena, env, &mut tctx.persistent_env, tctx.type_ctx)?;
    let md = env.lookup_module(&path).ok()?;
    let mty = scrape_alias_module_type(&md.md_type, env, &mut tctx.persistent_env, tctx.type_ctx)
        .unwrap_or_else(|| md.md_type.clone());
    if matches!(
        mty,
        crate::types::decl::ModuleType::MtySignature(_)
            | crate::types::decl::ModuleType::MtyAlias(_, _)
    ) {
        None
    } else {
        Some(TypeModError::StructureExpected { loc, mty })
    }
}

/// Match OCaml `type_module_type_of` behavior for `module type of`.
///
/// OCaml special-cases `Pmod_ident` to avoid the regular `type_module` path,
/// which can wrap aliases in an implicit `Tmod_constraint`.
/// See `compiler/ml/typemod.ml` (`type_module_type_of`).
fn type_module_type_of_expr_raw<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
) -> TypeModResult<ModuleExpr> {
    match &mod_expr.pmod_desc {
        // typemod.ml `type_module_type_of`: turn off strengthening, and look
        // the module up in the warning scope of its attributes, as
        // `type_module` does.
        ParsedModuleExprDesc::Pmod_ident(lid) => {
            with_warning_scope(tctx, arena, &mod_expr.pmod_attributes, true, |tctx| {
                type_module_type_of_ident(tctx, env, arena, mod_expr, lid)
            })
        }
        _ => type_module_expr(tctx, env, arena, mod_expr),
    }
}

fn type_module_type_of_ident<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
    lid: &crate::parser::ast::Loc<crate::parse_arena::LidentIdx>,
) -> TypeModResult<ModuleExpr> {
    {
        {
            let longident = tctx.resolve_lid(lid.txt).clone();
            crate::types::typecore::mark_open_lid_use(
                tctx.type_ctx,
                env,
                arena,
                &longident,
                crate::types::env::OpenLookupKind::Module,
                Some(mod_expr.pmod_loc),
            );
            // `Typetexp.find_module` (typetexp.ml:86-96 via env.ml:1022-1036)
            // reports a recursive module still bound to its placeholder.
            if let Longident::Lident(mod_idx) = &longident
                && let Ok((_, md)) = env.find_module_with_id(arena.get_string(*mod_idx))
                && is_recursive_module_placeholder_type(&md.md_type)
            {
                return Err(TypeModError::CoreError(
                    TypeCoreError::IllegalReferenceToRecursiveModule {
                        loc: mod_expr.pmod_loc,
                    },
                ));
            }
            let path = match lookup_module_path_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            ) {
                Some(path) => path,
                None => {
                    return Err(TypeModError::CoreError(
                        crate::types::typecore::unbound_module_lookup_error(
                            tctx, env, lid.loc, &longident,
                        ),
                    ));
                }
            };
            let semantic_mty = match lookup_module_type_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            ) {
                Some(module_type) => module_type,
                None => {
                    return Err(TypeModError::CoreError(
                        crate::types::typecore::unbound_module_lookup_error(
                            tctx, env, lid.loc, &longident,
                        ),
                    ));
                }
            };

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_ident(path, *lid),
                mod_loc: mod_expr.pmod_loc,
                mod_type: semantic_mty,
                mod_env: tctx.type_ctx.store_typed_env(env),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }
    }
}

fn module_type_of_typed_module_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
    typed_mod_type: &crate::types::decl::ModuleType,
) -> TypeModResult<crate::types::decl::ModuleType> {
    let module_type = remove_module_type_aliases_for_typeof(
        typed_mod_type,
        env,
        &mut tctx.persistent_env,
        tctx.type_ctx,
    );
    if !closed_modtype(tctx.type_ctx, env, &module_type) {
        return Err(TypeModError::NonGeneralizableModule {
            loc: arena.to_location(mod_expr.pmod_loc),
            mty: module_type,
        });
    }
    Ok(module_type)
}

fn type_module_type_of<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
) -> TypeModResult<(ModuleExpr, crate::types::decl::ModuleType)> {
    let typed_mod_expr = type_module_type_of_expr_raw(tctx, env, arena, mod_expr)?;
    let module_type =
        module_type_of_typed_module_expr(tctx, env, arena, mod_expr, &typed_mod_expr.mod_type)?;
    Ok((typed_mod_expr, module_type))
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
    let mut with_mty = None;

    let desc = match &smty.pmty_desc {
        PMtyDesc::Pmty_ident(lid) => {
            let longident = tctx.resolve_lid(lid.txt).clone();
            crate::types::typecore::mark_open_lid_use(
                tctx.type_ctx,
                env,
                arena,
                &longident,
                crate::types::env::OpenLookupKind::Modtype,
                Some(smty.pmty_loc),
            );
            let path = lookup_modtype_path_or_error(tctx, &longident, smty.pmty_loc, arena, env)?;
            TMtyDesc::Tmty_ident(path, *lid)
        }
        PMtyDesc::Pmty_signature(sig_items) => {
            let typed_sig = transl_signature(tctx, env, arena, sig_items)?;
            TMtyDesc::Tmty_signature(typed_sig)
        }
        PMtyDesc::Pmty_functor(inner) => {
            let (ref name, ref param_type, ref result_type_idx) = **inner;
            let typed_param = match param_type {
                Some(pt) => Some(Box::new(transl_modtype(
                    tctx,
                    env,
                    arena,
                    arena.get_mod_type(*pt),
                )?)),
                None => None,
            };
            let param_decl = typed_param.as_ref().map(|mty| mty.mty_type.clone());
            let param_id = tctx.type_ctx.create_ident(arena.get_string(name.txt));
            let mut result_env = env.clone();
            result_env.add_module_arg(
                param_id,
                crate::types::decl::ModuleDeclaration {
                    md_type: param_decl.unwrap_or(crate::types::decl::ModuleType::MtySignature(
                        std::sync::Arc::new(vec![]),
                    )),
                    md_attributes: vec![],
                    md_loc: crate::types::DeclLoc::none(),
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
                typed_param.map(|mty| tctx.typed.push_module_type(*mty)),
                tctx.typed.push_module_type(typed_result),
            )
        }
        PMtyDesc::Pmty_with(inner) => {
            // typemod.ml:759-772: merge the constraints in order into the
            // body's signature, then `Mtype.freshen (Mty_signature final_sg)`.
            let (ref body_idx, ref constraints) = **inner;
            let body = arena.get_mod_type(*body_idx);
            let typed_body = transl_modtype(tctx, env, arena, body)?;
            let mut sg = extract_sig(tctx, env, body.pmty_loc, &typed_body.mty_type)?;
            let mut typed_constraints = Vec::with_capacity(constraints.len());
            for constraint in constraints {
                let (tcstr, merged) =
                    merge_constraint(tctx, env, arena, smty.pmty_loc, &sg, constraint)?;
                typed_constraints.push(tcstr);
                sg = merged;
            }
            let mut mty = crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(sg));
            crate::cmi::persistent_env::freshen_module_type_bound_idents(&mut mty, tctx.type_ctx);
            with_mty = Some(mty);
            TMtyDesc::Tmty_with(tctx.typed.push_module_type(typed_body), typed_constraints)
        }
        PMtyDesc::Pmty_typeof(me_idx) => {
            let me = arena.get_mod_expr(*me_idx);
            let (typed_me, _module_type) = type_module_type_of(tctx, env, arena, me)?;
            TMtyDesc::Tmty_typeof(tctx.typed.push_module_expr(typed_me))
        }
        PMtyDesc::Pmty_alias(lid) => {
            check_recursive_module_reference_lid(lid, arena, env)?;
            let longident = tctx.resolve_lid(lid.txt).clone();
            crate::types::typecore::mark_open_lid_use(
                tctx.type_ctx,
                env,
                arena,
                &longident,
                crate::types::env::OpenLookupKind::Module,
                Some(smty.pmty_loc),
            );
            // typemod.ml:670 `transl_module_alias` uses `Typetexp.lookup_module`,
            // whose default `~load:false` (typetexp.ml:126) leaves the unit
            // unloaded under `-no-alias-deps` (env.ml:1044-1045).
            let path = lookup_module_path_for_module_expr(
                tctx,
                env,
                arena,
                &longident,
                false,
                smty.pmty_loc,
            )?;
            TMtyDesc::Tmty_alias(path, *lid)
        }
        // OCaml `compiler/ml/typemod.ml:743-744`.
        PMtyDesc::Pmty_extension(ext) => {
            return Err(TypeModError::CoreError(
                crate::types::typecore::builtin_extension_error(arena, ext),
            ));
        }
    };
    let mut typed = TMty {
        mty_desc: desc,
        mty_type: crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(vec![])),
        mty_env: env_ref,
        mty_loc: loc,
        mty_attributes: attrs,
    };
    typed.mty_type = match with_mty {
        Some(mty) => mty,
        None => translate_module_type_to_decl_with_typed_hint(tctx, env, arena, smty, Some(MtyHint::Node(&typed)))
            .unwrap_or_else(|_| {
                crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(vec![]))
            }),
    };
    // typemod.ml `transl_modtype_aux`: `check_js_names ~toplevel:false
    // sg.sig_type` for a written signature.
    if let (TMtyDesc::Tmty_signature(_), crate::types::decl::ModuleType::MtySignature(sig_type)) =
        (&typed.mty_desc, &typed.mty_type)
    {
        check_js_names(tctx.type_ctx, false, sig_type)?;
    }
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
    let mut names = Names::default();

    for item in items {
        check_signature_item_names(&mut names, arena, item)?;
        let ctx = tctx.type_ctx;
        ctx.init_def(ctx.current_stamp());
        let mut loc = item.psig_loc;
        let desc = match &item.psig_desc {
            PSigDesc::Psig_value(vd) => {
                let name_str = arena.get_string(vd.pval_name.txt).to_string();
                // Use transl_type_scheme pattern: begin_def/end_def/generalize
                // OCaml: reset_type_variables() for each val declaration
                tctx.reset_type_variables();
                let ctx = tctx.type_ctx;
                ctx.begin_def();
                let (typed_ctype, val_ty) =
                    transl_type(tctx, &sig_env, arena.get_core_type(vd.pval_type))?;
                ctx.end_def();
                crate::types::ctype::generalize(ctx, val_ty);
                // OCaml compiler/ml/typemod.ml:756-763 delegates Psig_value
                // to compiler/ml/typedecl.ml:1878-1915. The extra
                // parse_arity/get_arity expansion happens only in the
                // primitive branch at typedecl.ml:1897-1898; ordinary
                // signature values must not force constructor heads before
                // Env.enter_value allocates val_id at typedecl.ml:1916-1919.
                let val_kind = match &vd.pval_prim {
                    None => crate::types::decl::ValueKind::ValReg,
                    Some(prim) => crate::types::decl::ValueKind::ValPrim(
                        std::sync::Arc::new(primitive_description_from_value_decl(
                            arena,
                            ctx,
                            &sig_env,
                            prim,
                            vd.pval_type,
                            val_ty,
                        )),
                    ),
                };
                // OCaml typedecl.ml:1875-1914 translates the type scheme before
                // Env.enter_value creates the value ident. Keep the same order so
                // lazy signature forcing during type translation consumes stamps
                // before the signature value id.
                let id = ctx.create_ast_ident(arena, vd.pval_name.txt);
                // typedecl.ml:1918-1919: `Env.enter_value ~check:(fun s ->
                // Unused_value_declaration s)`.
                // `Types.val_loc` is the signature item loc passed by
                // typemod.ml:755-757 (typedecl.ml:1883-1889).
                tctx.add_value_usage_check(
                    &name_str,
                    arena.to_location(item.psig_loc),
                    item.psig_loc,
                    Warning::UnusedValueDeclaration {
                        name: name_str.clone(),
                    },
                );
                let val_prim = vd.pval_prim.clone();
                let val_desc = tctx.typed.push_core_type(typed_ctype);
                TSigDesc::Tsig_value(tctx.typed.push_value_description(
                    crate::types::typedtree::TypedValueDescription {
                        val_id: id,
                        val_name: Located {
                            txt: name_str,
                            loc: vd.pval_name.loc,
                        },
                        val_desc,
                        val_prim,
                        val_kind,
                        val_loc: vd.pval_loc,
                        // typedecl.ml transl_value_decl: the attributes as written.
                        val_attributes: crate::ast_jsx_component::description_attributes(arena, vd),
                    },
                ))
            }
            PSigDesc::Psig_type(inner) => {
                let (ref rec_flag, ref decls) = **inner;
                let typed_decls =
                    transl_sig_type_declarations(tctx, &sig_env, arena, *rec_flag, decls)?;
                // Match OCaml transl_signature/Typedecl.transl_type_decl:
                // all signature types, including abstract ones, enter the
                // threaded environment for subsequent signature items.
                for td in &typed_decls {
                    sig_env.store_type(tctx.type_ctx, td.typ_id, td.typ_type.clone());
                }
                // typedecl.ml:1535-1538 adds them with `Env.add_type
                // ~check:true`, which registers the unused-type checks in
                // signatures too (exported ones are marked used by the final
                // inclusion check).
                register_type_declaration_usage_checks(tctx, &sig_env, &typed_decls);
                TSigDesc::Tsig_type(*rec_flag, typed_decls)
            }
            PSigDesc::Psig_typext(ext) => {
                let (typed_item, _item_sig, new_env) =
                    transl_type_extension(tctx, &sig_env, arena, loc, ext, false)?;
                sig_env = new_env;
                match typed_item.str_desc {
                    StructureItemDesc::Tstr_typext(typed_ext) => TSigDesc::Tsig_typext(typed_ext),
                    _ => TSigDesc::Tsig_attribute((
                        Located {
                            txt: crate::intern::StrIdx(0),
                            loc: LocIdx(0),
                        },
                        crate::parser::ast::Payload::PStr(Box::default()),
                    )),
                }
            }
            PSigDesc::Psig_exception(ext) => {
                let structure_item = ParsedStructureItem {
                    pstr_desc: ParsedStructureItemDesc::Pstr_exception(ext.clone()),
                    pstr_loc: loc,
                };
                let (typed_item, _item_sig, new_env) =
                    type_structure_item(tctx, &sig_env, arena, &structure_item)?;
                sig_env = new_env;
                match typed_item.str_desc {
                    StructureItemDesc::Tstr_exception(typed_ext) => {
                        TSigDesc::Tsig_exception(typed_ext)
                    }
                    _ => TSigDesc::Tsig_attribute((
                        Located {
                            txt: crate::intern::StrIdx(0),
                            loc: LocIdx(0),
                        },
                        crate::parser::ast::Payload::PStr(Box::default()),
                    )),
                }
            }
            PSigDesc::Psig_module(md) => {
                let name_str = arena.get_string(md.pmd_name.txt).to_string();
                let id = ctx.create_ident(&name_str);
                let typed_mty =
                    transl_modtype(tctx, &sig_env, arena, arena.get_mod_type(md.pmd_type))?;
                // Add module to sig_env so subsequent items (Psig_open etc.) can find it.
                // This matches OCaml's transl_sig: `let newenv = Env.enter_module_declaration id md env`.
                // OCaml compiler/ml/typemod.ml:806-834 uses the
                // `tmty.mty_type` produced by `transl_modtype` as the
                // declaration's `md_type`. Re-translating here would repeat
                // side effects such as `Mtype.freshen` for `Pmty_with`.
                let decl_mty = decl_module_type_from_typed(&typed_mty).unwrap_or(
                    crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(vec![])),
                );
                // typemod.ml:836-843: `Env.enter_module_declaration` of a
                // declaration carrying `pmd_attributes`.
                store_module_deprecated(
                    tctx.type_ctx,
                    &parser_attrs_to_decl_attrs(arena, tctx.type_ctx, &md.pmd_attributes),
                )?;
                sig_env.add_module(
                    id,
                    crate::types::decl::ModuleDeclaration {
                        md_type: decl_mty,
                        md_attributes: vec![],
                        md_loc: tctx.intern_ast_loc(arena, md.pmd_loc),
                        md_path: None,
                    },
                );
                tctx.check_module_usage(&name_str, arena.to_location(md.pmd_loc), md.pmd_loc);
                TSigDesc::Tsig_module(TypedModuleDeclaration {
                    md_id: id,
                    md_name: Located {
                        txt: name_str,
                        loc: md.pmd_name.loc,
                    },
                    md_type: tctx.typed.push_module_type(typed_mty),
                    md_attributes: md.pmd_attributes.clone(),
                    md_loc: md.pmd_loc,
                })
            }
            PSigDesc::Psig_recmodule(sdecls) => {
                // typemod.ml:824-841: transl_recmodule_modtypes, whose env2
                // (modules added with `~arg:true`, no usage checks) types the
                // rest of the signature.
                let rec_type_decls: Vec<RecModuleTypeDecl> = sdecls
                    .iter()
                    .map(|pmd| {
                        (
                            arena.get_string(pmd.pmd_name.txt).to_string(),
                            pmd.pmd_name.loc,
                            pmd.pmd_type,
                            pmd.pmd_attributes.clone(),
                            pmd.pmd_loc,
                        )
                    })
                    .collect();
                let (decls, rec_env) =
                    transl_recmodule_modtypes(tctx, &sig_env, arena, &rec_type_decls)?;
                sig_env = rec_env;
                TSigDesc::Tsig_recmodule(decls)
            }
            PSigDesc::Psig_modtype(mtd) => {
                let name_str = arena.get_string(mtd.pmtd_name.txt).to_string();
                // typemod.ml:887-889: `warning_scope pmtd_attributes`.
                let typed_mty =
                    with_warning_scope(tctx, arena, &mtd.pmtd_attributes, true, |tctx| match &mtd
                        .pmtd_type
                    {
                        Some(mt) => Ok::<_, TypeModError>(Some(transl_modtype(
                            tctx,
                            &sig_env,
                            arena,
                            arena.get_mod_type(*mt),
                        )?)),
                        None => Ok(None),
                    })?;
                let decl_mtd = crate::types::ModtypeDeclaration {
                    mtd_type: typed_mty.as_ref().map(|tmty| tmty.mty_type.clone()),
                    mtd_attributes: vec![],
                    mtd_loc: crate::types::DeclLoc::none(),
                };
                // OCaml compiler/ml/typemod.ml:895-913 translates the module
                // type first, then allocates exactly one id via
                // Env.enter_modtype for both the declaration and typedtree.
                let id = ctx.create_ident(&name_str);
                sig_env.add_modtype(id, decl_mtd);
                TSigDesc::Tsig_modtype(crate::types::typedtree::ModuleTypeDeclaration {
                    mtd_id: id,
                    mtd_name: Located {
                        txt: name_str,
                        loc: mtd.pmtd_name.loc,
                    },
                    mtd_type: typed_mty.map(|mty| tctx.typed.push_module_type(mty)),
                    mtd_attributes: mtd.pmtd_attributes.clone(),
                    mtd_loc: mtd.pmtd_loc,
                })
            }
            PSigDesc::Psig_include(incl) => {
                let typed_mty =
                    transl_modtype(tctx, &sig_env, arena, arena.get_mod_type(incl.pincl_mod))?;
                let include_sig = freshened_signature_from_module_type(
                    tctx,
                    &sig_env,
                    &typed_mty.mty_type,
                    arena.get_mod_type(incl.pincl_mod).pmty_loc,
                )?;
                // OCaml compiler/ml/typemod.ml:859.
                check_included_signature_names(&mut names, item.psig_loc, &include_sig)?;
                add_signature_items_to_env(tctx.type_ctx, &include_sig, &mut sig_env)?;
                TSigDesc::Tsig_include(IncludeDescription {
                    incl_mod: tctx.typed.push_module_type(typed_mty),
                    incl_type: include_sig,
                    incl_attributes: incl.pincl_attributes.clone(),
                    incl_loc: incl.pincl_loc,
                })
            }
            PSigDesc::Psig_open(od) => {
                // Env.open_signature reports unused/shadow warnings at the
                // open description location, not the module longident.
                loc = od.popen_loc;
                let longident = tctx.resolve_lid(od.popen_lid.txt).clone();
                let open_lid = arena.get_longident(od.popen_lid.txt);
                crate::types::typecore::mark_open_lid_use(
                    tctx.type_ctx,
                    &sig_env,
                    arena,
                    open_lid,
                    crate::types::env::OpenLookupKind::Module,
                    Some(od.popen_lid.loc),
                );
                let slot = tctx.open_signature_slot(od.popen_override, od.popen_loc);
                // Resolve the module and extend the environment with opened bindings.
                // This matches OCaml's transl_signature which calls type_open/Env.open_signature.
                let path = if let Some(path) = open_direct_persistent_module(
                    &mut sig_env,
                    open_lid,
                    arena,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                    slot,
                ) {
                    path
                } else if let Some(path) = {
                    let lookup_env = sig_env.clone();
                    crate::types::typecore::open_module_lid_components_into_env(
                        open_lid,
                        arena,
                        &lookup_env,
                        &mut sig_env,
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                        slot,
                    )
                } {
                    path
                } else {
                    open_failure_path(tctx, &sig_env, arena, &longident, od.popen_lid.loc)?
                };
                tctx.set_open_slot_root(slot, &path);
                TSigDesc::Tsig_open(crate::types::typedtree::OpenDeclaration {
                    open_path: path,
                    open_txt: od.popen_lid,
                    open_override: od.popen_override,
                    open_attributes: od.popen_attributes.clone(),
                })
            }
            PSigDesc::Psig_attribute(attr) => {
                // typemod.ml:906.
                apply_warning_attribute(tctx, arena, attr)?;
                TSigDesc::Tsig_attribute((**attr).clone())
            }
            PSigDesc::Psig_extension(inner) => {
                let (extension, _attrs) = &**inner;
                return Err(TypeModError::CoreError(
                    crate::types::typecore::builtin_extension_error(arena, extension),
                ));
            }
        };

        let typed_item = TypedSignatureItem {
            sig_desc: desc,
            sig_env: EnvRef(0),
            sig_loc: loc,
        };
        typed_items.push(typed_item);
    }

    Ok(crate::types::typedtree::TypedSignature {
        sig_items: tctx.typed.push_signature_items(typed_items),
    })
}

// ============================================================================
// Structure Type Checking
// ============================================================================

/// typedecl.ml:1527-1540 `inline_types`: the record declarations of a group
/// whose source origin is `Inline_record_definition`, in declaration order.
fn group_inline_record_types(
    origins: &[crate::parser::ast::TypeDeclarationOrigin],
    typed_decls: &[TypedTypeDeclaration],
) -> Vec<crate::types::decl::TypeInlinedType> {
    debug_assert_eq!(origins.len(), typed_decls.len());
    origins
        .iter()
        .zip(typed_decls)
        .filter_map(
            |(origin, tdecl)| match (origin, &tdecl.typ_type.type_kind) {
                (
                    crate::parser::ast::TypeDeclarationOrigin::Inline_record_definition,
                    crate::types::TypeKind::TypeRecord(labels, _),
                ) => Some(crate::types::decl::TypeInlinedType::Record {
                    type_name: tdecl.typ_name.txt.clone(),
                    labels: labels.to_vec(),
                }),
                _ => None,
            },
        )
        .collect()
}

fn rescript_hide_attributes(attrs: &Attributes, arena: &ParseArena) -> bool {
    attrs
        .as_slice()
        .iter()
        .any(|(name, _)| arena.get_string(name.txt) == "internal.local")
}

fn rescript_hide_structure_item(desc: &StructureItemDesc, arena: &ParseArena) -> bool {
    match desc {
        StructureItemDesc::Tstr_module(mb) => rescript_hide_attributes(&mb.mb_attributes, arena),
        _ => false,
    }
}

/// Type check a structure (module body).
///
/// OCaml `Typemod.type_structure` (typemod.ml:1617-1668) runs inside
/// `Builtin_attributes.warning_scope []`: floating `@@warning` attributes of
/// the structure do not outlive it, so the later phases see the warning
/// state from before typing.
pub fn type_structure<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    items: &[ParsedStructureItem],
) -> TypeModResult<(Structure, Env)> {
    tctx.drain_open_slot_uses();
    let previous_config = tctx.warning_config.clone();
    tctx.type_ctx.note_report_warning_config(&previous_config);
    let result = type_structure_unscoped(tctx, env, arena, items);
    tctx.drain_open_slot_uses();
    tctx.warning_config = previous_config;
    result
}

fn type_structure_unscoped<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    items: &[ParsedStructureItem],
) -> TypeModResult<(Structure, Env)> {
    let mut typed_items = Vec::new();
    let mut sig_items = Vec::new();
    let mut current_env = env.clone();
    let mut names = Names::default();

    for item in items {
        check_structure_item_names(&mut names, arena, item)?;
        let ctx = tctx.type_ctx;
        ctx.init_def(ctx.current_stamp());
        tctx.set_unify_env(&current_env);
        let (typed_item, item_sig, new_env) = if tctx.derived_census.is_some() {
            type_structure_item_with_census(tctx, &current_env, arena, item)
        } else {
            type_structure_item(tctx, &current_env, arena, item)
        }?;
        if let StructureItemDesc::Tstr_include(incl) = &typed_item.str_desc {
            // OCaml compiler/ml/typemod.ml:1579.
            check_included_signature_names(&mut names, item.pstr_loc, &incl.incl_type)?;
        }
        if !rescript_hide_structure_item(&typed_item.str_desc, arena) {
            sig_items.extend(item_sig);
        }
        typed_items.push(typed_item);
        current_env = new_env;
    }
    // typemod.ml:1596-1599: `type_struct` also runs `Ctype.init_def
    // (Ident.current_time ())` for the empty rest of the structure.
    tctx.type_ctx.init_def(tctx.type_ctx.current_stamp());

    let structure = Structure {
        str_items: tctx.typed.push_structure_items(typed_items),
        str_type: sig_items,
        str_final_env: EnvRef(0),
    };

    Ok((structure, current_env))
}

/// O(1) census bookkeeping around the existing item checker. Keep timer/counter
/// snapshots and attribution outside the ordinary structure loop's code and stack.
#[cold]
#[inline(never)]
fn type_structure_item_with_census<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    item: &ParsedStructureItem,
) -> TypeModResult<(StructureItem, Vec<crate::types::decl::SignatureItem>, Env)> {
    let census_start = crate::derived_census::start(true);
    let census_before = tctx
        .derived_census
        .as_ref()
        .map_or(0, |c| c.typecheck.total());
    let counter_before = tctx
        .derived_census
        .as_ref()
        .and_then(|c| c.counter_snapshot(tctx.type_ctx));
    let (typed_item, item_sig, new_env) = type_structure_item(tctx, env, arena, item)?;
    if let (Some(census), Some(start)) = (&mut tctx.derived_census, census_start) {
        let derived = crate::binary_ast::derive::is_derived_item(item, arena);
        census.account_counters(tctx.type_ctx, derived, counter_before);
        let children = census.typecheck.total() - census_before;
        let elapsed = crate::derived_census::nanos(start.elapsed()).saturating_sub(children);
        census.typecheck.add(derived, elapsed);
        if let Some(reason) = census.general_group(item) {
            census.general_typecheck_ns[reason.census_index()] += elapsed;
        }
        if matches!(typed_item.str_desc, StructureItemDesc::Tstr_derived(_)) {
            census.planned_typecheck_ns += elapsed;
        }
        if derived && let StructureItemDesc::Tstr_value(_, group) = typed_item.str_desc {
            census.mark_typed_group(group.start());
        }
    }
    Ok((typed_item, item_sig, new_env))
}

fn closed_modtype(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    mty: &crate::types::decl::ModuleType,
) -> bool {
    match mty {
        crate::types::decl::ModuleType::MtyIdent(_)
        | crate::types::decl::ModuleType::MtyAlias(_, _) => true,
        crate::types::decl::ModuleType::MtySignature(sig) => {
            let mut sig_env = env.clone();
            for item in sig.iter() {
                crate::types::includemod::add_sig_item_to_env(ctx, item, &mut sig_env);
            }
            sig.iter()
                .all(|item| closed_signature_item(ctx, &sig_env, item))
        }
        crate::types::decl::ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            let mut functor_env = env.clone();
            functor_env.add_module_arg(
                *param,
                crate::types::decl::ModuleDeclaration {
                    md_type: default_module_type(param_type.as_deref().cloned()),
                    md_attributes: vec![],
                    md_loc: crate::types::DeclLoc::none(),
                    md_path: None,
                },
            );
            closed_modtype(ctx, &functor_env, result)
        }
    }
}

fn closed_signature_item(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    item: &crate::types::decl::SignatureItem,
) -> bool {
    match item {
        crate::types::decl::SignatureItem::SigValue(_, desc) => {
            crate::types::ctype::closed_schema(ctx, env, desc.val_type)
        }
        crate::types::decl::SignatureItem::SigModule(_, md, _) => {
            closed_modtype(ctx, env, &md.md_type)
        }
        _ => true,
    }
}

fn check_nongen_scheme(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    item: &crate::types::decl::SignatureItem,
) -> TypeModResult<()> {
    match item {
        crate::types::decl::SignatureItem::SigValue(_, desc)
            if !crate::types::ctype::closed_schema(ctx, env, desc.val_type) =>
        {
            Err(TypeModError::NonGeneralizable {
                loc: ctx.resolve_loc(desc.val_loc),
                typ: desc.val_type,
            })
        }
        crate::types::decl::SignatureItem::SigModule(_, md, _)
            if !closed_modtype(ctx, env, &md.md_type) =>
        {
            Err(TypeModError::NonGeneralizableModule {
                loc: ctx.resolve_loc(md.md_loc),
                mty: md.md_type.clone(),
            })
        }
        _ => Ok(()),
    }
}

/// Check that all core type schemes in a structure signature are closed.
///
/// Mirrors OCaml `Typemod.check_nongen_schemes`, which runs after inferred
/// signature inclusion and before signature normalization when there is no
/// explicit `.resi` interface.
pub fn check_nongen_schemes(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    sig: &[crate::types::decl::SignatureItem],
) -> TypeModResult<()> {
    for item in sig {
        check_nongen_scheme(ctx, env, item)?;
    }
    Ok(())
}

/// Type check a structure item.
/// OCaml `Typedecl.transl_type_extension extend env loc styext`
/// (typedecl.ml:1802-1897): `extend` is true for a structure item
/// (typemod.ml:1485) and false for a signature item (typemod.ml:813).
fn transl_type_extension<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    loc: LocIdx,
    ext: &crate::parser::ast::TypeExtension,
    extend: bool,
) -> TypeModResult<(StructureItem, Vec<crate::types::decl::SignatureItem>, Env)> {
    let ctx = tctx.type_ctx;
    // Type extension: type t += ...
    let resolved_lid = tctx.resolve_lid(ext.ptyext_path.txt).clone();
    // OCaml `transl_type_extension` (compiler/ml/typedecl.ml:1754-1757)
    // resolves the target with `Typetexp.find_type`, which raises for an
    // unbound type constructor.
    let (path, found_decl) =
        crate::types::typecore::find_type_for_lid(tctx, env, ext.ptyext_path.loc, &resolved_lid)
            .map_err(TypeModError::CoreError)?;

    // OCaml typedecl.ml transl_type_extension rejects incompatible
    // targets before translating any extension constructors.
    let target_type_decl = Some(env.lookup_type(&path).ok().cloned().unwrap_or_else(|| (*found_decl).clone()));
    if let Some(type_decl) = &target_type_decl {
        if !matches!(type_decl.type_kind, crate::types::TypeKind::TypeOpen) {
            return Err(TypeModError::NotExtensibleType { loc, path });
        }

        // typedecl.ml:1811: `Private when extend`, where a signature's
        // extension passes `extend = false` (typemod.ml:813).
        if extend && matches!(type_decl.type_private, crate::types::PrivateFlag::Private) {
            if let Some(decl_constructor) = ext.ptyext_constructors.iter().find(|ec| {
                matches!(
                    ec.pext_kind,
                    crate::parser::ast::ExtensionConstructorKind::Pext_decl(_, _)
                )
            }) {
                return Err(TypeModError::CannotExtendPrivateType {
                    loc: decl_constructor.pext_loc,
                    path,
                });
            }
        }

        let mismatch = if type_decl.type_arity != ext.ptyext_params.len() as i32 {
            Some(TypeExtensionMismatch::Arity)
        } else {
            let variance_ok = type_decl.type_variance.len() == ext.ptyext_params.len()
                && type_decl
                    .type_variance
                    .iter()
                    .zip(ext.ptyext_params.iter())
                    .all(|(type_variance, (_, extension_variance))| {
                        let (co, cn) = type_variance.get_upper();
                        let type_allows_covariant = !cn;
                        let type_allows_contravariant = !co;
                        let (requires_covariant, requires_contravariant) = match extension_variance
                        {
                            ParserVariance::Covariant => (true, false),
                            ParserVariance::Contravariant => (false, true),
                            ParserVariance::Invariant => (false, false),
                        };

                        (!requires_covariant || type_allows_covariant)
                            && (!requires_contravariant || type_allows_contravariant)
                    });
            (!variance_ok).then_some(TypeExtensionMismatch::Variance)
        };
        if let Some(mismatch) = mismatch {
            return Err(TypeModError::ExtensionMismatch {
                loc,
                path,
                mismatch,
            });
        }
    }

    // OCaml typedecl.ml: begin_def/end_def/generalize around type extension
    // constructor translation, matching Pstr_exception treatment. This ensures
    // arg types are at GENERIC_LEVEL so instance() creates fresh copies.
    tctx.reset_type_variables();
    ctx.begin_def();

    // typedecl.ml:1793 `make_params env styext.ptyext_params`
    // (Typetexp.transl_type_param: a repeated variable is an error).
    let (typed_params, typed_param_type_refs) =
        translate_type_declaration_params(tctx, arena, &ext.ptyext_params)?;
    let allowed_type_params: HashSet<TypeExprRef> = typed_param_type_refs
        .iter()
        .map(|ty_ref| ctx.repr(*ty_ref))
        .collect();

    // The result type for non-GADT extension constructors. OCaml passes
    // `typext_params` through `make_constructor`, so use the extension
    // parameter nodes rather than the original declaration parameters.
    let ext_res_ty = ctx.new_generic_constr(path, typed_param_type_refs.clone());

    // Translate constructors; OCaml adds them to the environment only
    // after generalization, closedness checks, and variance checks pass.
    let mut typed_constructors = Vec::new();
    let mut constructor_descriptions = Vec::new();
    let mut ext_types_to_generalize: Vec<TypeExprRef> = Vec::new();
    let ext_private = parser_private_to_type_private(ext.ptyext_private);
    for ec in &ext.ptyext_constructors {
        let name_str = arena.get_string(ec.pext_name.txt).to_string();
        let id = ctx.create_ident(&name_str);

        let (ext_kind, ext_args, cstr_args, cstr_inlined, ext_ret_ty) = match &ec.pext_kind {
            crate::parser::ast::ExtensionConstructorKind::Pext_decl(args, ret) => {
                let mut arg_ty_refs = Vec::new();
                let (typed_args, ext_args, cstr_args, cstr_inlined) = match args {
                    crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                        let mut typed = Vec::new();
                        for ty in types {
                            let (typed_ct, ty_ref) = transl_decl_arg_type(
                                tctx,
                                env,
                                arena.get_core_type(*ty),
                                ret.is_none(),
                            )?;
                            arg_ty_refs.push(ty_ref);
                            typed.push(typed_ct);
                        }
                        (
                            crate::types::typedtree::ConstructorArgument::Cstr_tuple(tctx.typed.push_core_types(typed)),
                            crate::types::ConstructorArguments::CstrTuple(arg_ty_refs.clone()),
                            arg_ty_refs.clone(),
                            None,
                        )
                    }
                    crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                        check_duplicate_label_declarations(arena, labels, None)?;
                        let mut typed_labels = Vec::new();
                        let mut decl_labels = Vec::new();
                        for label in labels {
                            check_extra_as_attribute(arena, label)?;
                            let label_name = arena.get_string(label.pld_name.txt).to_string();
                            let (typed_ct, ty_ref) =
                                transl_label_type(tctx, env, arena, label, ret.is_none())?;
                            let (poly_typed_ct, poly_ty_ref) =
                                force_poly_typed_core_type(&mut tctx.typed, ctx, typed_ct, ty_ref);
                            let internal_ty_ref = match &*ctx.get_desc(poly_ty_ref) {
                                crate::types::type_expr::TypeDesc::Tpoly { body, vars }
                                    if vars.is_empty() =>
                                {
                                    *body
                                }
                                _ => poly_ty_ref,
                            };
                            let label_id = ctx.create_ast_ident(arena, label.pld_name.txt);
                            typed_labels.push(crate::types::typedtree::LabelDeclaration {
                                ld_id: label_id,
                                ld_name: crate::parse_arena::Located {
                                    txt: label_name.clone(),
                                    loc: label.pld_name.loc,
                                },
                                ld_runtime_name:
                                    crate::types::record_runtime::parsetree_runtime_name(
                                        label, arena,
                                    ),
                                ld_mutable: label.pld_mutable,
                                ld_optional: label.pld_optional,
                                ld_type: tctx.typed.push_core_type(poly_typed_ct),
                                ld_loc: label.pld_loc,
                                ld_attributes: label.pld_attributes.clone(),
                            });
                            decl_labels.push(crate::types::LabelDeclaration {
                                ld_id: label_id,
                                ld_runtime_name:
                                    crate::types::record_runtime::parsetree_runtime_name(
                                        label, arena,
                                    ),
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
                                ld_loc: tctx.intern_ast_loc(arena, label.pld_loc),
                                ld_attributes: vec![],
                            });
                        }
                        let inline_path = Path::pident(id);
                        let inline_ty = ctx.new_generic_constr(inline_path, vec![]);
                        let inline_decl = crate::types::TypeDeclaration {
                            type_params: vec![],
                            type_arity: 0,
                            type_kind: crate::types::TypeKind::TypeRecord(
                                crate::types::decl::SharedVec::from(decl_labels.clone()),
                                crate::types::RecordRepresentation::RecordExtension,
                            ),
                            type_private: crate::types::PrivateFlag::Public,
                            type_manifest: None,
                            type_variance: vec![],
                            type_newtype_level: None,
                            type_loc: crate::types::DeclLoc::none(),
                            type_attributes: vec![],
                            type_immediate: false,
                            type_representation: crate::types::TypeRepresentation::Boxed,
                            type_shape: crate::types::ValueShape::Unstated,
                            type_inlined_types: vec![],
                            type_path: None,
                        };
                        (
                            crate::types::typedtree::ConstructorArgument::Cstr_record(typed_labels),
                            crate::types::ConstructorArguments::CstrRecord(decl_labels),
                            vec![inline_ty],
                            Some(Box::new(inline_decl)),
                        )
                    }
                };
                let (typed_ret, ext_ret_ty) = match ret {
                    Some(ct) => {
                        let ret_type = arena.get_core_type(*ct);
                        let (typed_ct, ty_ref) = transl_type(tctx, env, ret_type)?;
                        let ret_repr = ctx.repr(ty_ref);
                        let ret_matches_extension = matches!(
                            &*ctx.get_desc(ret_repr),
                            crate::types::type_expr::TypeDesc::Tconstr { path: ret_path, .. }
                                if ret_path.same(&path)
                        );
                        if !ret_matches_extension {
                            return Err(TypeModError::ConstraintFailed {
                                loc: ret_type.ptyp_loc,
                                actual: ty_ref,
                                expected: ctx.new_constr(path, typed_param_type_refs.clone()),
                            });
                        }
                        (Some(typed_ct), Some(ty_ref))
                    }
                    None => (None, None),
                };
                (
                    crate::types::typedtree::ExtensionConstructorKind::Text_decl(
                        typed_args, typed_ret.map(|ct| tctx.typed.push_core_type(ct)),
                    ),
                    ext_args,
                    cstr_args,
                    cstr_inlined,
                    ext_ret_ty,
                )
            }
            crate::parser::ast::ExtensionConstructorKind::Pext_rebind(lid) => {
                let (rebind_path, rebind_desc) = lookup_rebind_constructor(tctx, env, lid)?;
                let (inst_args, cstr_res) = crate::types::instance_constructor(ctx, &rebind_desc);
                let (res, ret_type) = if rebind_desc.cstr_generalized {
                    let type_params = target_type_decl
                        .as_ref()
                        .map(|decl| crate::types::ctype::instance_list(ctx, &decl.type_params))
                        .unwrap_or_default();
                    let res = ctx.new_constr(path, type_params.clone());
                    let ret_type = Some(ctx.new_constr(path, type_params));
                    (res, ret_type)
                } else {
                    (ext_res_ty, None)
                };
                if let Err(err) =
                    crate::types::ctype::unify(ctx, &mut tctx.unify_state, cstr_res, res)
                {
                    return Err(TypeModError::RebindWrongType {
                        loc: lid.loc,
                        lid: tctx.resolve_lid(lid.txt).clone(),
                        trace: match err {
                            crate::types::ctype::TypeError::Unify(trace) if !trace.is_empty() => {
                                trace
                            }
                            _ => vec![(cstr_res, res)],
                        },
                        env: tctx.type_ctx.store_typed_env(env),
                    });
                }
                if matches!(rebind_desc.cstr_private, crate::types::PrivateFlag::Private)
                    && matches!(ext_private, crate::types::PrivateFlag::Public)
                {
                    return Err(TypeModError::RebindPrivate {
                        loc: lid.loc,
                        lid: tctx.resolve_lid(lid.txt).clone(),
                    });
                }
                let ext_args = rebind_constructor_arguments(tctx, &rebind_desc, &inst_args);
                // `Datarepr.extension_descr` -> `constructor_args`
                // (compiler/ml/datarepr.ml:64-92).
                let (cstr_args, cstr_inlined) =
                    rebound_constructor_args(ctx, &Path::pident(id), &ext_args);
                (
                    crate::types::typedtree::ExtensionConstructorKind::Text_rebind(
                        rebind_path,
                        *lid,
                    ),
                    ext_args,
                    cstr_args.unwrap_or(inst_args),
                    cstr_inlined.or_else(|| rebind_desc.cstr_inlined.clone()),
                    ret_type,
                )
            }
        };

        crate::types::btype::iter_type_expr_cstr_args(&ext_args, |ty| {
            ext_types_to_generalize.push(ty);
        });
        if let Some(ret_ty) = ext_ret_ty {
            ext_types_to_generalize.push(ret_ty);
        }

        // Register the extension constructor in the environment
        let ext_path = Path::pident(id);
        let cstr_res = ext_ret_ty.unwrap_or(ext_res_ty);
        let cstr_existentials =
            crate::types::env::constructor_existentials(ctx, &cstr_args, ext_ret_ty);
        let cstr_desc = crate::types::decl::ConstructorDescription {
            cstr_name: name_str.clone(),
            cstr_res,
            cstr_existentials,
            cstr_args: cstr_args.clone(),
            cstr_arity: cstr_args.len() as i32,
            cstr_kind: crate::types::ConstructorKind::Extension(ext_path),
            cstr_generalized: ext_ret_ty.is_some(),
            cstr_private: ext_private,
            // `Datarepr.extension_descr`: `cstr_loc = ext.ext_loc`.
            cstr_loc: tctx.intern_ast_loc(arena, ec.pext_loc),
            cstr_attributes: parser_attrs_to_decl_attrs(arena, tctx.type_ctx, &ec.pext_attributes),
            cstr_inlined: cstr_inlined.clone(),
        };
        constructor_descriptions.push((id, cstr_desc));

        typed_constructors.push(crate::types::typedtree::ExtensionConstructor {
            ext_id: id,
            ext_name: crate::parse_arena::Located {
                txt: name_str,
                loc: ec.pext_name.loc,
            },
            ext_type: crate::types::ExtensionConstructor {
                ext_type_path: path,
                ext_type_params: vec![],
                ext_args,
                ext_ret_type: ext_ret_ty,
                ext_private,
                ext_loc: tctx.intern_ast_loc(arena, ec.pext_loc),
                ext_attributes: parser_attrs_to_decl_attrs(
                    arena,
                    tctx.type_ctx,
                    &ec.pext_attributes,
                ),
                ext_is_exception: false,
            },
            ext_kind,
            ext_loc: ec.pext_loc,
            ext_attributes: ec.pext_attributes.clone(),
        });
    }

    // OCaml typedecl.ml: end_def and generalize constructor arg types
    ctx.end_def();
    for ty_ref in &typed_param_type_refs {
        crate::types::generalize(ctx, *ty_ref);
    }
    for ty_ref in &ext_types_to_generalize {
        crate::types::generalize(ctx, *ty_ref);
    }

    for ext_cstr in &mut typed_constructors {
        ext_cstr.ext_type.ext_type_params = typed_param_type_refs.clone();
        if let crate::types::typedtree::ExtensionConstructorKind::Text_decl(typed_args, typed_ret) =
            &ext_cstr.ext_kind
        {
            if typed_ret.is_none() {
                // Non-GADT extension constructors use the fixed policy
                // and reject stray variables. GADT extension variables
                // are constructor-local, as in OCaml typedecl.ml.
                if let Some((name, loc)) = find_unbound_type_var_in_typed_constructor_args(
                    &tctx.typed,
                    ctx,
                    typed_args,
                    &allowed_type_params,
                ) {
                    return Err(TypeModError::UnboundTypeVarExt { loc, name });
                }
            }
        }
        // `Ctype.closed_extension_constructor` (ctype.ml:454-464,
        // typedecl.ml:1813-1818).
        if ext_cstr.ext_type.ext_ret_type.is_none() {
            if let Some(var) = find_unbound_type_var_in_constructor_args(
                ctx,
                &ext_cstr.ext_type.ext_args,
                &allowed_type_params,
            ) {
                return Err(TypeModError::UnboundTypeVarInExtension {
                    loc: ext_cstr.ext_loc,
                    var,
                    args: ext_cstr.ext_type.ext_args.clone(),
                });
            }
        }
        if let Some(type_decl) = &target_type_decl {
            check_extension_constructor_variance_requirements(
                ctx,
                env,
                loc,
                type_decl,
                &ext_cstr.ext_type,
            )?;
        }
    }

    let mut new_env = env.clone();
    for ((id, cstr_desc), ext_cstr) in constructor_descriptions
        .into_iter()
        .zip(typed_constructors.iter())
    {
        // OCaml compiler/ml/env.ml:1693-1716 registers extension
        // constructors through `Datarepr.extension_descr` only; inline
        // record labels produced at compiler/ml/datarepr.ml:190-214 are
        // not added to `env.labels`.
        // typedecl.ml:1830: `Env.add_extension ~check:true`.
        tctx.check_extension_usage(
            ext_cstr.ext_type.ext_type_path.last(),
            id.name(),
            false,
            tctx.resolve_loc(ext_cstr.ext_type.ext_loc),
            ext_cstr.ext_loc,
            env.is_in_signature(),
        );
        new_env.add_constructor(id, cstr_desc);
    }

    let item_sig = typed_constructors
        .iter()
        .enumerate()
        .map(|(index, ext_cstr)| {
            crate::types::decl::SignatureItem::SigTypext(
                ext_cstr.ext_id,
                ext_cstr.ext_type.clone(),
                sig_ext_status(index),
            )
        })
        .collect();
    let desc = StructureItemDesc::Tstr_typext(TypeExtension {
        tyext_path: path,
        tyext_params: typed_params.into_iter().map(|(ct, v)| (tctx.typed.push_core_type(ct), v)).collect(),
        tyext_constructors: typed_constructors,
        tyext_private: ext.ptyext_private,
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

fn type_structure_item<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    item: &ParsedStructureItem,
) -> TypeModResult<(StructureItem, Vec<crate::types::decl::SignatureItem>, Env)> {
    let loc = item.pstr_loc;

    match &item.pstr_desc {
        ParsedStructureItemDesc::Pstr_eval(inner) => {
            let (ref expr, ref attrs) = **inner;
            // Evaluated expression: E
            // OCaml compiler/ml/typemod.ml:1391-1394 scopes warnings from
            // `Pstr_eval` attributes around expression typing.
            let typed_expr = with_warning_scope(tctx, arena, attrs, true, |tctx| {
                type_expression(tctx, env, arena.get_expanded_expr(*expr)).map_err(TypeModError::CoreError)
            })?;

            let desc = StructureItemDesc::Tstr_eval(tctx.push_expr(typed_expr), attrs.clone());
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

        // A derived item: discharge the obligations of its plan. When one
        // fails the unit is compiled again with plans off.
        ParsedStructureItemDesc::Pstr_derived(idx) => {
            match crate::types::derived::discharge(tctx, env, *idx) {
                Ok(discharged) => Ok((
                    StructureItem {
                        str_desc: StructureItemDesc::Tstr_derived(*idx),
                        str_loc: loc,
                        str_env: EnvRef(0),
                    },
                    discharged.sig_items,
                    discharged.env,
                )),
                Err(crate::types::derived::Fallback) => {
                    tctx.derived_fallback = true;
                    Err(TypeModError::DerivedFallback)
                }
            }
        }

        ParsedStructureItemDesc::Pstr_value(inner) => {
            let (ref rec_flag, ref bindings) = *inner;

            let (typed_bindings, new_env) =
                type_binding(tctx, env, *rec_flag, arena.vb_list(*bindings))?;

            // typemod.ml type_structure: the environment keeps let-bound
            // values without attributes, so uses in this module do not warn.
            // The signature carries their `deprecated` attributes, so uses
            // from other modules do, and the effects they declare (`@pure`,
            // `@mutates`), which other modules' pure bindings rely on.
            let mut sig_items = Vec::new();
            for vb in &typed_bindings {
                let start = sig_items.len();
                push_sig_values_from_env_pattern(
                    &tctx.typed,
                    &new_env,
                    tctx.typed.pattern(vb.vb_pat),
                    &mut sig_items,
                );
                let deprecated: Attributes = vb
                    .vb_attributes
                    .iter()
                    .filter(|(name, _)| {
                        let name = arena.get_string(name.txt);
                        name == "deprecated" || crate::verify::purity::is_effect_attribute(name)
                    })
                    .cloned()
                    .collect();
                if deprecated.is_empty() {
                    continue;
                }
                let deprecated = parser_attrs_to_decl_attrs(arena, tctx.type_ctx, &deprecated);
                for item in &mut sig_items[start..] {
                    if let crate::types::decl::SignatureItem::SigValue(_, vd) = item {
                        let mut attrs = deprecated.clone();
                        attrs.extend(vd.val_attributes.iter().cloned());
                        vd.val_attributes = attrs.into();
                    }
                }
            }

            let desc = StructureItemDesc::Tstr_value(
                *rec_flag,
                tctx.typed.push_value_bindings(typed_bindings),
            );
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

            // Translate the type annotation using transl_type_scheme pattern:
            // OCaml: reset_type_variables() clears type var map so each declaration
            // gets fresh Tvars (e.g., 'a in log and 'a in log2 are separate nodes).
            tctx.reset_type_variables();
            let ctx = tctx.type_ctx;
            ctx.begin_def();
            let (typed_ctype, val_ty) = transl_type(tctx, env, arena.get_core_type(vd.pval_type))?;
            ctx.end_def();
            crate::types::ctype::generalize(ctx, val_ty);

            // OCaml compiler/ml/typedecl.ml:1889-1908 calls parse_arity and
            // Primitive.parse_declaration before Env.enter_value allocates the
            // external id. parse_arity itself delegates to Ctype.get_arity at
            // typedecl.ml:1863-1872; do not expand the whole value type here.
            let Some(prim) = &vd.pval_prim else {
                unreachable!("an external always carries a primitive (typedecl.ml:1890-1896)")
            };
            let prim_desc =
                primitive_description_from_value_decl(arena, ctx, env, prim, vd.pval_type, val_ty);
            // compiler/ml/typedecl.ml:1898-1905 permits nullary compiler
            // primitives and digested externals, but rejects an ordinary
            // external whose translated type has no arguments.
            let internal_native_name = !matches!(
                prim_desc.prim_kind,
                crate::types::decl::PrimKind::KindIntrinsic
            );
            let compiler_primitive = prim_desc
                .prim_name
                .as_bytes()
                .first()
                .is_some_and(|first| matches!(first, b'%' | b'#'));
            if prim_desc.prim_arity == 0
                && !internal_native_name
                && (prim_desc.prim_name.is_empty() || !compiler_primitive)
            {
                return Err(TypeModError::NullArityExternal {
                    loc: arena.get_core_type(vd.pval_type).ptyp_loc,
                });
            }

            let val_prim = vd.pval_prim.clone();

            // OCaml Typedecl.transl_value_decl enters the value after translating
            // the type and parsing primitive metadata, so type lookup side effects
            // consume stamps before the external binding id is allocated.
            let id = tctx.type_ctx.create_ident(&name_str);

            // Add the external value to the environment
            let mut new_env = env.clone();
            // typedecl.ml transl_value_decl: the attributes as written.
            let val_attributes = parser_attrs_to_decl_attrs(
                arena,
                tctx.type_ctx,
                &crate::ast_jsx_component::description_attributes(arena, vd),
            );
            let val_desc_for_env = crate::types::ValueDescription {
                val_type: val_ty,
                val_kind: crate::types::ValueKind::ValPrim(std::sync::Arc::new(prim_desc)),
                val_loc: tctx.intern_ast_loc(arena, loc),
                val_attributes: val_attributes.into(),
                val_path: None,
            };
            let sig_item =
                crate::types::decl::SignatureItem::SigValue(id, val_desc_for_env.clone());
            // `Env.enter_value` runs `check_value_name` (env.ml:1574-1591).
            check_value_name_for_env(tctx.type_ctx, &id, &val_desc_for_env)?;
            // typedecl.ml:1918-1919: `Env.enter_value ~check:(fun s ->
            // Unused_value_declaration s)`.
            tctx.add_value_usage_check(
                &name_str,
                tctx.resolve_loc(val_desc_for_env.val_loc),
                loc,
                Warning::UnusedValueDeclaration {
                    name: name_str.clone(),
                },
            );
            let val_kind = val_desc_for_env.val_kind.clone();
            new_env.add_value(id, val_desc_for_env);

            let val_desc = tctx.typed.push_core_type(typed_ctype);
            let desc = StructureItemDesc::Tstr_primitive(tctx.typed.push_value_description(
                crate::types::typedtree::TypedValueDescription {
                    val_id: id,
                    val_name: Located {
                        txt: name_str,
                        loc: vd.pval_name.loc,
                    },
                    val_desc,
                    val_prim,
                    val_kind,
                    val_loc: vd.pval_loc,
                    // typedecl.ml transl_value_decl: the attributes as written.
                    val_attributes: crate::ast_jsx_component::description_attributes(arena, vd),
                },
            ));
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
            // typedecl.ml:1527-1533 pairs each typed declaration with its
            // source declaration (`List.combine sdecl_list tdecls`); this is
            // the source origin of each entry of `typed_tree_decls`.
            let mut typed_tree_decl_origins: Vec<crate::parser::ast::TypeDeclarationOrigin> =
                Vec::new();
            let mut internal_decls_for_generalize: Vec<crate::types::TypeDeclaration> = Vec::new();
            // OCaml typedecl.ml:1500 `type_record_as_object`: set when a
            // spread-only record becomes an object manifest; it then skips
            // manifest constraint checks for the whole group.
            let mut type_record_as_object = false;
            // Collect env-description TypeExprRefs (cstr_res, label ty_res) that
            // are separate from the TypeKind and need explicit generalization.
            let mut env_desc_types_for_generalize: Vec<crate::types::TypeExprRef> = Vec::new();

            // OCaml resets the type variables per declaration inside
            // `transl_declaration` (typedecl.ml:385), after `begin_def`.
            tctx.type_variables.clear();

            // OCaml typedecl.ml:1447-1484 prepends synthetic `t#row`
            // declarations for fixed private rows, allocates their identifiers
            // before the real type identifiers, and enters row placeholders even
            // for Nonrecursive groups.
            // OCaml typedecl.ml:1456 `Variant_type_spread.expand_variant_spreads`
            // runs over the whole group in the outer env before identifiers are
            // created or any declaration is translated.
            let mut pre_spread_sources = Vec::with_capacity(decls.len());
            for decl in decls.iter() {
                pre_spread_sources.push(match &decl.ptype_kind {
                    crate::parser::ast::TypeKind::Ptype_variant(cstrs) => Some(
                        resolve_variant_spread_sources(tctx, env, arena, decl, cstrs)?,
                    ),
                    _ => None,
                });
            }

            let fixed_row_type_ids = collect_fixed_row_type_ids(ctx, arena, decls);
            let has_fixed_rows = !fixed_row_type_ids.is_empty();

            // Predeclare type names in the environment so recursive references
            // resolve to the current declaration group (matching OCaml typedecl).
            // OCaml: enter_type adds placeholders for Recursive declarations and
            // for Nonrecursive fixed-row synthetic declarations.
            let mut declared_type_ids: Vec<Ident> = Vec::with_capacity(decls.len());
            let type_entry_capacity = decls.len() + fixed_row_type_ids.len();
            let mut type_entry_ids: Vec<Ident> = Vec::with_capacity(type_entry_capacity);
            let mut type_entry_parser_indices: Vec<usize> = Vec::with_capacity(type_entry_capacity);
            let mut type_entry_is_synthetic_row: Vec<bool> =
                Vec::with_capacity(type_entry_capacity);
            let needs_placeholder = matches!(rec_flag, crate::parser::ast::RecFlag::Recursive);
            for decl in decls.iter() {
                check_nonrecursive_gadt_enter_type(*rec_flag, decl)?;
                let type_name = decl.ptype_name.txt;
                let type_name_str = arena.get_string(type_name);
                let type_id = ctx.create_ident(type_name_str);
                declared_type_ids.push(type_id);
            }
            // OCaml typedecl.ml:1467-1475: with the fresh identifiers created,
            // raise the definition level to at least their binding time, then
            // `begin_def` for the declarations.
            ctx.init_def(ctx.current_stamp());
            ctx.begin_def();
            // typedecl.ml:1476 `enter_type` (typedecl.ml:73-108), after
            // `begin_def`: fresh generic parameters, and a fresh variable as
            // manifest when the declaration has one.
            for row_id in &fixed_row_type_ids {
                let placeholder_decl =
                    fixed_row_placeholder_decl(ctx, arena, &decls[row_id.decl_idx], &row_id.id);
                new_env.add_type(row_id.id, placeholder_decl);
            }
            if needs_placeholder {
                for (decl, type_id) in decls.iter().zip(declared_type_ids.iter()) {
                    let arity = decl.ptype_params.len();
                    let placeholder_decl = crate::types::TypeDeclaration {
                        type_params: (0..arity).map(|_| ctx.new_generic_var(None)).collect(),
                        type_arity: arity as i32,
                        type_kind: crate::types::TypeKind::TypeAbstract,
                        type_private: match decl.ptype_private {
                            crate::parser::ast::PrivateFlag::Public => {
                                crate::types::PrivateFlag::Public
                            }
                            crate::parser::ast::PrivateFlag::Private => {
                                crate::types::PrivateFlag::Private
                            }
                        },
                        type_manifest: decl.ptype_manifest.map(|_| ctx.new_var(None)),
                        type_variance: (0..arity).map(|_| TypesVariance::full()).collect(),
                        type_newtype_level: None,
                        type_loc: tctx.intern_ast_loc(arena, decl.ptype_loc),
                        type_attributes: parser_attrs_to_decl_attrs(
                            arena,
                            tctx.type_ctx,
                            &decl.ptype_attributes,
                        ),
                        type_immediate: false,
                        type_representation: crate::types::TypeRepresentation::Boxed,
                        type_shape: crate::types::ValueShape::Unstated,
                        type_inlined_types: vec![],
                        type_path: Some(Path::pident(*type_id)),
                    };
                    new_env.add_type(*type_id, placeholder_decl);
                }
            }
            // typedecl.ml:1476 `enter_type` adds the placeholders with
            // `Env.add_type ~check:true` (typedecl.ml:108), registering their
            // usage checks: fixed rows first, then a recursive group.
            for row_id in &fixed_row_type_ids {
                let row_loc = decls[row_id.decl_idx].ptype_loc;
                tctx.check_type_usage(&row_id.name, arena.to_location(row_loc), row_loc);
            }
            if needs_placeholder {
                for decl in decls.iter() {
                    let name = arena.get_string(decl.ptype_name.txt);
                    tctx.check_type_usage(name, arena.to_location(decl.ptype_loc), decl.ptype_loc);
                }
            }
            // typedecl.ml:1478-1498: in a recursive group, a use of one of its
            // types while a declaration is translated only records a
            // dependency in that declaration's slot.
            let warn_unused_types =
                tctx.warning_config
                    .is_active(&Warning::UnusedTypeDeclaration {
                        name: String::new(),
                    });
            let rec_slot = |tctx: &mut TypeCheckContext<'_>, name: &str, loc: LocIdx| {
                if needs_placeholder && warn_unused_types {
                    tctx.type_ctx
                        .usage()
                        .set_type_rec_slot_callback(name, arena.to_location(loc))
                } else {
                    None
                }
            };
            let row_slots: Vec<_> = fixed_row_type_ids
                .iter()
                .map(|row_id| rec_slot(tctx, &row_id.name, decls[row_id.decl_idx].ptype_loc))
                .collect();
            let decl_slots: Vec<_> = decls
                .iter()
                .map(|decl| rec_slot(tctx, arena.get_string(decl.ptype_name.txt), decl.ptype_loc))
                .collect();

            // OCaml: temp_env is the environment used for translating type bodies.
            // For Recursive, it has abstract placeholders so types can self-reference.
            // For Nonrecursive, it equals the original env — types in the same group
            // are NOT visible to each other (they resolve to outer scope definitions).
            // new_env accumulates the final declarations and is returned.
            let temp_env = new_env.clone();
            // typedecl.ml:1534-1538 builds the final env with `List.fold_right`
            // over the declarations (fixed-row types first), each through
            // `Env.store_type`; collect them and add them after the loop.
            // A declaration with its constructors and labels.
            type FinalEnvEntry = (
                Ident,
                crate::types::TypeDeclaration,
                Vec<(Ident, crate::types::ConstructorDescription)>,
                Vec<(Ident, crate::types::LabelDescription)>,
            );
            let mut final_env_entries: Vec<FinalEnvEntry> = Vec::new();

            for (row_index, row_id) in fixed_row_type_ids.iter().enumerate() {
                tctx.type_ctx
                    .usage()
                    .set_current_type_slot(row_slots[row_index]);
                let typed_row_decl = translate_fixed_row_type_declaration(
                    tctx,
                    arena,
                    row_id.id,
                    row_id.name.clone(),
                    &decls[row_id.decl_idx],
                    None,
                )?;
                let row_internal_decl = typed_row_decl.typ_type.clone();
                final_env_entries.push((
                    row_id.id,
                    row_internal_decl.clone(),
                    Vec::new(),
                    Vec::new(),
                ));
                type_entry_ids.push(row_id.id);
                type_entry_parser_indices.push(row_id.decl_idx);
                type_entry_is_synthetic_row.push(true);
                internal_decls_for_generalize.push(row_internal_decl);
                typed_tree_decls.push(typed_row_decl);
                typed_tree_decl_origins.push(decls[row_id.decl_idx].ptype_origin);
            }

            for (decl_idx, decl) in decls.iter().enumerate() {
                tctx.type_ctx
                    .usage()
                    .set_current_type_slot(decl_slots[decl_idx]);
                // typedecl.ml:385 `reset_type_variables ()` (after the group's
                // init_def/begin_def), so global variables sit at this level.
                tctx.reset_type_variables();
                // typedecl.ml:1500-1503: each declaration is translated in
                // `Builtin_attributes.warning_scope ptype_attributes`.
                tctx.drain_open_slot_uses();
                let decl_warning_config = tctx.warning_config.clone();
                for attr in decl.ptype_attributes.iter().rev() {
                    if let Err(error) =
                        apply_warning_attribute_with_ppwarning(tctx, arena, attr, true)
                    {
                        tctx.warning_config = decl_warning_config;
                        return Err(error.into());
                    }
                }
                let type_name = decl.ptype_name.txt;
                let type_name_str = arena.get_string(type_name);
                let type_id = declared_type_ids[decl_idx];
                let saved_type_variables = std::mem::take(&mut tctx.type_variables);

                check_declaration_runtime_annotation(arena, decl)?;

                // Create the type path for self-reference
                let type_path = Path::pident(type_id);

                // Convert type parameters: (CoreType, Variance) -> (TypedCoreType, Variance)
                let mut typ_params: Vec<(TypedCoreType, TypesVariance)> = Vec::new();
                let mut internal_type_params: Vec<TypeExprRef> = Vec::new();
                for (core_type, parser_var) in &decl.ptype_params {
                    let core_type = arena.get_core_type(*core_type);
                    let (typed_core_type, type_ref) = match &core_type.ptyp_desc {
                        crate::parser::ast::CoreTypeDesc::Ptyp_any => {
                            // Use new_var (current_level) instead of new_global_var so
                            // type params are at the elevated level from begin_def and
                            // get properly generalized by end_def + generalize.
                            // OCaml creates type params with newvar() at !current_level.
                            let type_ref = ctx.new_var(Some(crate::name::Name::new("_")));
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
                            let name = arena.get_string(*name);
                            check_type_variable_name(core_type.ptyp_loc, name)?;
                            if tctx.type_variables.contains_key(name) {
                                return Err(TypeModError::RepeatedParameter {
                                    loc: core_type.ptyp_loc,
                                });
                            }
                            let type_ref = ctx.new_var(Some(crate::name::Name::new(name)));
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
                    if let crate::parser::ast::CoreTypeDesc::Ptyp_var(name) = &core_type.ptyp_desc {
                        tctx.type_variables
                            .insert(arena.get_string(*name).to_string(), type_ref);
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

                // OCaml typedecl.ml warns after translating type constraints
                // when those constraints are attached to a GADT declaration.
                check_type_declaration_constraint_on_gadt(tctx, decl);

                check_unboxed_type_attributes(arena, decl)?;

                // Check for @unboxed attribute (only applies to single-constructor variants)
                let decl_has_unboxed_attr =
                    parser_attrs_have_unboxed(arena, &decl.ptype_attributes);

                // OCaml compiler/ml/typedecl.ml:449-607 translates the kind
                // first, creating variant constructor identifiers at
                // typedecl.ml:481-482, then translates the manifest at
                // typedecl.ml:692-699. Keep this ordering because manifest
                // lookup can force persistent signatures and consume stamps.
                let mut manifest_from_kind = None;

                // Convert the type kind - create both internal and typed tree versions
                let type_variant_layout = matches!(
                    &decl.ptype_kind,
                    crate::parser::ast::TypeKind::Ptype_variant(_)
                )
                .then(|| ctx.pending_variant_layout());
                let (internal_type_kind, typed_tree_kind, constructors) = match &decl.ptype_kind {
                    crate::parser::ast::TypeKind::Ptype_abstract => (
                        crate::types::TypeKind::TypeAbstract,
                        TypedTypeKind::Ttype_abstract,
                        vec![],
                    ),
                    crate::parser::ast::TypeKind::Ptype_variant(cstrs) => {
                        // OCaml copies the @tag attributes of the type decl to
                        // each constructor (copy_tag_attr_from_decl in typedecl.ml)
                        let tag_attrs: Vec<_> = decl
                            .ptype_attributes
                            .iter()
                            .filter(|attr| arena.get_string(attr.0.txt) == "tag")
                            .cloned()
                            .collect();

                        // Collect spread source type info for variant spread expansion.
                        // Maps from spread index to the source type's constructor declarations.
                        // Uses transl_type to resolve the spread source type (handles qualified paths like S.x).
                        // (constructors, is_pdot) - is_pdot=true means source is from a sub-module,
                        // where OCaml's Subst.type_declaration creates fresh type copies
                        let spread_sources = pre_spread_sources[decl_idx]
                            .take()
                            .expect("variant spread sources resolved before the group");
                        // OCaml typedecl.ml:1456 expands (and validates) variant
                        // spreads before transl_declaration checks for duplicate
                        // constructors (typedecl.ml:461-467).
                        check_duplicate_constructor_declarations(arena, decl.ptype_loc, cstrs)?;
                        check_unboxed_on_constructors(arena, cstrs)?;

                        let mut internal_cstrs = Vec::new();
                        let mut typed_tree_cstrs = Vec::new();
                        let mut cstr_descs = Vec::new();
                        // @unboxed is only the single-constructor OCaml-style unboxed
                        // when there's exactly one constructor with an unboxable payload.
                        // Otherwise @unboxed is ReScript's "untagged variants" which uses
                        // different handling.
                        let has_unboxed =
                            unboxed_type_representation(arena, decl, decl_has_unboxed_attr)
                                == crate::types::TypeRepresentation::Unboxed;

                        for (cstr_idx, cstr) in cstrs.iter().enumerate() {
                            // typedecl.ml:589-591: each constructor is made in
                            // `Builtin_attributes.warning_scope pcd_attributes`.
                            let cstr_warning_scope =
                                enter_warning_scope(tctx, arena, &cstr.pcd_attributes)?;
                            // Handle variant spread expansion
                            // Like OCaml's typedecl.ml: spread markers return None (filtered out)
                            // and expanded constructors get real types from the source type
                            if let Some((ref source_cstrs, is_pdot_source)) =
                                spread_sources[cstr_idx]
                            {
                                // OCaml creates an Ident for the dummy spread
                                // constructor before returning None for it.
                                ctx.create_ident(arena.get_string(cstr.pcd_name.txt));
                                // `make_constructor` still translates the spread's
                                // argument (typedecl.ml:477-481), which reports
                                // arity errors such as `...bool<bool>`.
                                if let crate::parser::ast::ConstructorArguments::Pcstr_tuple(
                                    types,
                                ) = &cstr.pcd_args
                                {
                                    for core_type in types {
                                        transl_type(
                                            tctx,
                                            &temp_env,
                                            arena.get_core_type(*core_type),
                                        )?;
                                    }
                                }
                                // Expand the source type's constructors into this type
                                // The spread marker itself is NOT included in any output
                                for source_cstr in source_cstrs {
                                    let SpreadConstructor {
                                        id: sc_id,
                                        name: sc_name,
                                        args: sc_args,
                                        inlined_labels: sc_inlined_labels,
                                        internal,
                                        typed,
                                    } = build_spread_constructor(
                                        &mut tctx.typed,
                                        ctx,
                                        arena,
                                        cstr,
                                        source_cstr,
                                        is_pdot_source,
                                        &tag_attrs,
                                    );
                                    let res_ty = ctx.new_constr(
                                        type_path,
                                        internal_type_params.clone(),
                                    );
                                    // Spread constructor cstr_res must be generalized
                                    // (like non-spread constructors at line 5348) so that
                                    // instance_constructor creates fresh copies.
                                    env_desc_types_for_generalize.push(res_ty);
                                    let sc_arity = sc_args.len() as i32;
                                    internal_cstrs.push(internal);
                                    typed_tree_cstrs.push(typed);
                                    let (sc_desc_args, sc_desc_arity, sc_desc_inlined) =
                                        if let Some(inline_lbls) = &sc_inlined_labels {
                                            // Mirror OCaml datarepr.constructor_args for inline records:
                                            // cstr_args = [Tconstr(type_path.Constructor, params)],
                                            // cstr_inlined = Some synthetic record declaration.
                                            let inline_params =
                                                inline_record_type_params(ctx, inline_lbls);
                                            let position = internal_cstrs.len() - 1;
                                            let inline_decl = crate::types::TypeDeclaration {
                                                type_params: inline_params.clone(),
                                                type_arity: inline_params.len() as i32,
                                                type_kind: crate::types::TypeKind::TypeRecord(
                                                    crate::types::decl::SharedVec::from(inline_lbls.clone()),
                                                    crate::types::RecordRepresentation::RecordInlined {
                                                        name: sc_name.clone(),
                                                        representation: crate::types::ConstructorReference {
                                                            variant: type_variant_layout.expect(
                                                                "variant declaration layout",
                                                            ),
                                                            position,
                                                        },
                                                    },
                                                ),
                                                type_private: crate::types::PrivateFlag::Public,
                                                type_manifest: None,
                                                type_variance: inline_params
                                                    .iter()
                                                    .map(|_| TypesVariance::full())
                                                    .collect(),
                                                type_newtype_level: None,
                                                type_loc: crate::types::DeclLoc::none(),
                                                type_attributes: vec![],
                                                type_immediate: false,
                                                type_representation: crate::types::TypeRepresentation::Boxed,
                                                type_shape: crate::types::ValueShape::Unstated,
                                                type_inlined_types: vec![],
                                                type_path: None,
                                            };
                                            let inline_constr = ctx.new_constr(
                                                Path::pdot(type_path, sc_name.clone()),
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
                                            cstr_kind: crate::types::ConstructorKind::Ordinary(
                                                crate::types::ConstructorReference {
                                                    variant: type_variant_layout
                                                        .expect("variant declaration layout"),
                                                    position: cstr_descs.len(),
                                                },
                                            ),
                                            cstr_generalized: source_cstr.cd_res.is_some(),
                                            // OCaml Datarepr.constructor_descrs uses the
                                            // declaration's `type_private`.
                                            cstr_private: parser_private_to_type_private(
                                                decl.ptype_private,
                                            ),
                                            cstr_loc: source_cstr.cd_loc,
                                            cstr_attributes: source_cstr.cd_attributes.clone(),
                                            cstr_inlined: sc_desc_inlined,
                                        },
                                    ));
                                }
                                exit_warning_scope(tctx, cstr_warning_scope);
                                continue;
                            }

                            let cstr_name_str = arena.get_string(cstr.pcd_name.txt);
                            let cstr_id = ctx.create_ident(cstr_name_str);
                            // typedecl.ml `make_cstr`: the runtime tag is
                            // decoded right after the constructor's ident.
                            let runtime_tag =
                                process_constructor_tag(arena, cstr).map_err(|(loc, error)| {
                                    ast_untagged_variant_error(arena.to_location(loc), error)
                                })?;
                            // OCaml `make_constructor` (compiler/ml/typedecl.ml:337-356):
                            // a generalized constructor is translated after
                            // `narrow ()` and `reset_type_variables ()`, so its type
                            // variables are fresh rather than the declaration's
                            // parameters, and `widen` restores both afterwards.
                            let gadt_scope = cstr.pcd_res.is_some().then(|| {
                                let global_level = ctx.increase_global_level();
                                let type_variables = std::mem::take(&mut tctx.type_variables);
                                tctx.reset_type_variables();
                                (global_level, type_variables)
                            });

                            // Convert constructor arguments using transl_type
                            let (cstr_args, internal_cd_args, typed_tree_cd_args) = match &cstr
                                .pcd_args
                            {
                                crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                                    let mut typed_args: Vec<TypeExprRef> = Vec::new();
                                    let mut typed_tree_args: Vec<TypedCoreType> = Vec::new();
                                    for core_type in types {
                                        let (typed_core_type, type_ref) = transl_decl_arg_type(
                                            tctx,
                                            &temp_env,
                                            arena.get_core_type(*core_type),
                                            cstr.pcd_res.is_none(),
                                        )?;
                                        typed_args.push(type_ref);
                                        typed_tree_args.push(typed_core_type);
                                    }
                                    (
                                        typed_args.clone(),
                                        crate::types::ConstructorArguments::CstrTuple(typed_args),
                                        TypedConstructorArguments::Cstr_tuple(
                                            tctx.typed.push_core_types(typed_tree_args),
                                        ),
                                    )
                                }
                                crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                                    check_duplicate_label_declarations(arena, labels, None)?;
                                    let mut typed_labels: Vec<TypedLabelDeclaration> = Vec::new();
                                    let mut internal_labels: Vec<crate::types::LabelDeclaration> =
                                        Vec::new();
                                    for lbl in labels {
                                        check_extra_as_attribute(arena, lbl)?;
                                        let (typed_core_type, type_ref) = transl_label_type(
                                            tctx,
                                            &temp_env,
                                            arena,
                                            lbl,
                                            cstr.pcd_res.is_none(),
                                        )?;
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
                                                &mut tctx.typed,
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
                                        let label_id = ctx.create_ast_ident(arena, lbl.pld_name.txt);
                                        internal_labels.push(crate::types::LabelDeclaration {
                                            ld_id: label_id,
                                            ld_runtime_name: crate::types::record_runtime::parsetree_runtime_name(lbl, arena),
                                            ld_mutable: mutable_flag,
                                            ld_optional: lbl.pld_optional,
                                            ld_type: internal_type_ref,
                                            ld_loc: tctx.intern_ast_loc(arena, lbl.pld_loc),
                                            ld_attributes: parser_attrs_to_decl_attrs(
                                                arena, tctx.type_ctx,
                                                &lbl.pld_attributes,
                                            ),
                                        });
                                        typed_labels.push(TypedLabelDeclaration {
                                            ld_id: label_id,
                                            ld_name: crate::parse_arena::Located {
                                                txt: lbl_name_str.to_string(),
                                                loc: lbl.pld_name.loc,
                                            },
                                            ld_runtime_name: crate::types::record_runtime::parsetree_runtime_name(lbl, arena),
                                            ld_mutable: lbl.pld_mutable,
                                            ld_optional: lbl.pld_optional,
                                            ld_type: tctx.typed.push_core_type(poly_typed_core_type),
                                            ld_loc: lbl.pld_loc,
                                            ld_attributes: lbl.pld_attributes.clone(),
                                            ld_types_attributes: None,
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
                                                            &mut tctx.typed,
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
                                                ptyp_desc:
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
                                                TypedConstructorArguments::Cstr_tuple(
                                                    tctx.typed
                                                        .push_core_types(vec![typed_core_type]),
                                                ),
                                            )
                                        } else {
                                            reject_object_spread_with_record_field(arena, labels)?;
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
                                    // OCaml `make_constructor` (compiler/ml/typedecl.ml:345-353):
                                    // the result must be an instance of the declared type.
                                    let is_instance = matches!(
                                        &*ctx.get_desc(ctx.repr(res_ty)),
                                        TypeDesc::Tconstr { path, .. } if path.same(&type_path)
                                    );
                                    if !is_instance {
                                        return Err(TypeModError::ConstraintFailed {
                                            loc: typed_res.ctyp_loc,
                                            actual: res_ty,
                                            expected: ctx.new_constr(
                                                type_path,
                                                internal_type_params.clone(),
                                            ),
                                        });
                                    }
                                    (Some(typed_res), Some(res_ty))
                                }
                                None => (None, None),
                            };
                            if let Some((global_level, type_variables)) = gadt_scope {
                                ctx.restore_global_level(global_level);
                                tctx.type_variables = type_variables;
                            }

                            let mut combined_parser_attrs = tag_attrs.clone();
                            combined_parser_attrs.extend(cstr.pcd_attributes.iter().cloned());
                            let combined_typed_attrs =
                                Attributes::from_vec(combined_parser_attrs.clone());
                            let combined_decl_attrs = parser_attrs_to_decl_attrs(
                                arena,
                                tctx.type_ctx,
                                &combined_typed_attrs,
                            );

                            // For inline records, create a synthetic type declaration and
                            // set cstr_args to [Tconstr(path, type_params)] matching OCaml's datarepr.ml
                            let (cstr_args, cstr_inlined) =
                                if let crate::types::ConstructorArguments::CstrRecord(ref lbls) =
                                    internal_cd_args
                                {
                                    let inline_params = inline_record_type_params(ctx, lbls);
                                    // Build path: Pdot(Pident(type_name), cstr_name)
                                    let inline_path =
                                        Path::pdot(type_path, cstr_name_str.to_string());
                                    // Create synthetic inline type declaration
                                    let inline_repres = if has_unboxed {
                                        // compiler/ml/datarepr.ml:163-164: unboxed inline records use `Record_unboxed true`.
                                        crate::types::RecordRepresentation::RecordUnboxed(true)
                                    } else {
                                        crate::types::RecordRepresentation::RecordInlined {
                                            name: cstr_name_str.to_string(),
                                            representation: crate::types::ConstructorReference {
                                                variant: type_variant_layout
                                                    .expect("variant declaration layout"),
                                                position: internal_cstrs.len(),
                                            },
                                        }
                                    };
                                    let inline_decl = crate::types::TypeDeclaration {
                                        type_params: inline_params.clone(),
                                        type_arity: inline_params.len() as i32,
                                        type_kind: crate::types::TypeKind::TypeRecord(
                                            crate::types::decl::SharedVec::from(lbls.clone()),
                                            inline_repres,
                                        ),
                                        type_private: crate::types::PrivateFlag::Public,
                                        type_manifest: None,
                                        type_variance: inline_params
                                            .iter()
                                            .map(|_| TypesVariance::full())
                                            .collect(),
                                        type_newtype_level: None,
                                        type_loc: crate::types::DeclLoc::none(),
                                        type_attributes: vec![],
                                        type_immediate: false,
                                        type_representation:
                                            crate::types::TypeRepresentation::Boxed,
                                        type_shape: crate::types::ValueShape::Unstated,
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
                                cd_id: cstr_id,
                                cd_runtime_tag: runtime_tag.clone(),
                                cd_args: internal_cd_args,
                                cd_res: internal_cd_res,
                                cd_loc: tctx.intern_ast_loc(arena, cstr.pcd_loc),
                                cd_attributes: combined_decl_attrs.clone(),
                            });

                            // Create typed tree constructor declaration
                            typed_tree_cstrs.push(TypedConstructorDeclaration {
                                cd_id: cstr_id,
                                cd_name: crate::parse_arena::Located {
                                    txt: cstr_name_str.to_string(),
                                    loc: cstr.pcd_name.loc,
                                },
                                cd_runtime_tag: runtime_tag,
                                cd_args: typed_tree_cd_args,
                                cd_res: typed_cd_res.map(|ct| tctx.typed.push_core_type(ct)),
                                cd_loc: cstr.pcd_loc,
                                cd_attributes: combined_typed_attrs,
                            });

                            // Create constructor description for the environment
                            let cstr_arity = cstr_args.len() as i32;
                            let cstr_desc_res = internal_cd_res.unwrap_or_else(|| {
                                ctx.new_constr(type_path, internal_type_params.clone())
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
                                    cstr_kind: crate::types::ConstructorKind::Ordinary(
                                        crate::types::ConstructorReference {
                                            variant: type_variant_layout.expect("variant declaration layout"),
                                            position: cstr_descs.len(),
                                        },
                                    ),
                                    cstr_generalized: internal_cd_res.is_some(),
                                    // OCaml Datarepr.constructor_descrs uses the
                                    // declaration's `type_private`.
                                    cstr_private: parser_private_to_type_private(
                                        decl.ptype_private,
                                    ),
                                    cstr_loc: tctx.intern_ast_loc(arena, cstr.pcd_loc),
                                    cstr_attributes:
                                        crate::types::decl::constructor_description_attrs_for_variant(
                                            &internal_cstrs,
                                            internal_cstrs.last().expect("constructor just pushed"),
                                        ),
                                    cstr_inlined,
                                },
                            ));
                            exit_warning_scope(tctx, cstr_warning_scope);
                        }

                        // OCaml compiler/ml/datarepr.ml:166-189 post-processes the
                        // complete constructor list from describe_constructors before
                        // adding optional_shape. Doing this while Rust's
                        // internal_cstrs is still partial misses the first constructor
                        // of `type t = None | Some(_)`.
                        if crate::types::decl::variant_has_optional_shape(&internal_cstrs) {
                            for (cstr_id, desc) in &mut cstr_descs {
                                if let Some(cd) = internal_cstrs.iter().find(|cd| {
                                    cd.cd_id.stamp() == cstr_id.stamp()
                                        || cd.cd_id.name() == cstr_id.name()
                                }) {
                                    desc.cstr_attributes =
                                        crate::types::decl::constructor_description_attrs_for_variant(
                                            &internal_cstrs,
                                            cd,
                                        );
                                }
                            }
                        }

                        (
                            crate::types::TypeKind::TypeVariant(
                                crate::types::decl::SharedVec::from(internal_cstrs),
                                type_variant_layout.expect("variant declaration layout"),
                            ),
                            TypedTypeKind::Ttype_variant(typed_tree_cstrs),
                            cstr_descs,
                        )
                    }
                    crate::parser::ast::TypeKind::Ptype_record(labels) => {
                        check_duplicate_label_declarations(
                            arena,
                            labels,
                            Some(arena.get_string(decl.ptype_name.txt)),
                        )?;
                        let mut internal_labels: Vec<crate::types::LabelDeclaration> = Vec::new();
                        let mut typed_tree_labels: Vec<TypedLabelDeclaration> = Vec::new();
                        for lbl in labels {
                            check_extra_as_attribute(arena, lbl)?;
                            let lbl_name_str = arena.get_string(lbl.pld_name.txt);
                            // typedecl.ml:223: `transl_labels` translates each
                            // label in `warning_scope pld_attributes`.
                            let label_warning_scope =
                                enter_warning_scope(tctx, arena, &lbl.pld_attributes)?;
                            let (typed_core_type, type_ref) =
                                transl_label_type(tctx, &temp_env, arena, lbl, true)?;
                            exit_warning_scope(tctx, label_warning_scope);
                            let mutable_flag = match lbl.pld_mutable {
                                crate::parser::ast::MutableFlag::Immutable => {
                                    crate::types::MutableFlag::Immutable
                                }
                                crate::parser::ast::MutableFlag::Mutable => {
                                    crate::types::MutableFlag::Mutable
                                }
                            };
                            // OCaml wraps label types in Tpoly via force_poly + transl_simple_type.
                            let (poly_typed_core_type, poly_type_ref) = force_poly_typed_core_type(
                                &mut tctx.typed,
                                ctx,
                                typed_core_type,
                                type_ref,
                            );
                            let internal_type_ref = match &*ctx.get_desc(poly_type_ref) {
                                crate::types::type_expr::TypeDesc::Tpoly { body, vars }
                                    if vars.is_empty() =>
                                {
                                    *body
                                }
                                _ => poly_type_ref,
                            };
                            let label_id = ctx.create_ast_ident(arena, lbl.pld_name.txt);
                            internal_labels.push(crate::types::LabelDeclaration {
                                ld_id: label_id,
                                ld_runtime_name:
                                    crate::types::record_runtime::parsetree_runtime_name(lbl, arena),
                                ld_mutable: mutable_flag,
                                ld_optional: lbl.pld_optional,
                                ld_type: internal_type_ref,
                                ld_loc: tctx.intern_ast_loc(arena, lbl.pld_loc),
                                ld_attributes: parser_attrs_to_decl_attrs(
                                    arena,
                                    tctx.type_ctx,
                                    &lbl.pld_attributes,
                                ),
                            });
                            typed_tree_labels.push(TypedLabelDeclaration {
                                ld_id: label_id,
                                ld_name: crate::parse_arena::Located {
                                    txt: lbl_name_str.to_string(),
                                    loc: lbl.pld_name.loc,
                                },
                                ld_runtime_name:
                                    crate::types::record_runtime::parsetree_runtime_name(lbl, arena),
                                ld_mutable: lbl.pld_mutable,
                                ld_optional: lbl.pld_optional,
                                ld_type: tctx.typed.push_core_type(poly_typed_core_type),
                                ld_loc: lbl.pld_loc,
                                ld_attributes: lbl.pld_attributes.clone(),
                                ld_types_attributes: None,
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
                                                &mut tctx.typed,
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
                                                        label.pld_type,
                                                    ))
                                                } else {
                                                    None
                                                }
                                            })
                                            .collect::<Vec<_>>();
                                        let object_manifest = crate::parser::ast::CoreType {
                                            ptyp_desc:
                                                crate::parser::ast::CoreTypeDesc::Ptyp_object(
                                                    Box::new((
                                                        object_fields,
                                                        crate::parser::ast::ClosedFlag::Closed,
                                                    )),
                                                ),
                                            ptyp_loc: decl.ptype_loc,
                                            ptyp_attributes: Attributes::new(),
                                        };
                                        (expanded_internal, expanded_typed, Some(object_manifest))
                                    } else {
                                        reject_object_spread_with_record_field(arena, labels)?;
                                        (expanded_internal, expanded_typed, None)
                                    }
                                }
                            } else {
                                (internal_labels, typed_tree_labels, None)
                            };
                        if let Some(object_manifest) = spread_only_object_manifest {
                            type_record_as_object = true;
                            // OCaml compiler/ml/typedecl.ml:630-689 rewrites
                            // spread-only records to an abstract declaration
                            // with an object manifest, and that manifest is
                            // still translated later by typedecl.ml:692-699.
                            manifest_from_kind = Some(object_manifest);
                            (
                                crate::types::TypeKind::TypeAbstract,
                                TypedTypeKind::Ttype_abstract,
                                vec![],
                            )
                        } else {
                            check_duplicate_typed_label_declarations(
                                decl.ptype_loc,
                                &typed_tree_labels,
                                Some(arena.get_string(decl.ptype_name.txt)),
                            )?;
                            let repres = if decl_has_unboxed_attr && internal_labels.len() == 1 {
                                crate::types::RecordRepresentation::RecordUnboxed(false)
                            } else {
                                crate::types::record_runtime::boxed_representation(&internal_labels)
                            };
                            (
                                crate::types::TypeKind::TypeRecord(
                                    crate::types::decl::SharedVec::from(internal_labels),
                                    repres,
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

                // OCaml compiler/ml/typedecl.ml:692-699 translates the
                // manifest after the kind has been translated.
                let (typ_manifest, manifest_type_ref) = if let Some(object_manifest) =
                    manifest_from_kind.as_ref()
                {
                    // OCaml typedecl.ml translates every manifest with
                    // `transl_simple_type env no_row`.
                    let (typed_manifest, type_ref) = if type_decl_manifest_uses_fixed_type_variables(
                        arena,
                        decl,
                        object_manifest,
                    ) {
                        transl_type_fixed(tctx, &temp_env, object_manifest)?
                    } else {
                        transl_type(tctx, &temp_env, object_manifest)?
                    };
                    (Some(typed_manifest), Some(type_ref))
                } else {
                    match &decl.ptype_manifest {
                        Some(manifest) => {
                            let manifest_ct = arena.get_core_type(*manifest);
                            let is_fixed_type = type_decl_is_fixed_type(arena, decl, manifest_ct);
                            let (typed_manifest, type_ref) =
                                if type_decl_manifest_uses_fixed_type_variables(
                                    arena,
                                    decl,
                                    manifest_ct,
                                ) {
                                    transl_type_fixed(tctx, &temp_env, manifest_ct)?
                                } else {
                                    transl_type(tctx, &temp_env, manifest_ct)?
                                };
                            if is_fixed_type {
                                let row_id =
                                    fixed_row_type_id_for_decl(&fixed_row_type_ids, decl_idx)
                                        .expect(
                                            "fixed private row type must have a synthetic row id",
                                        );
                                let row_path = Path::pident(row_id.id);
                                // typedecl.ml:720-723 finds the row with
                                // `Env.lookup_type`, which marks it used.
                                crate::types::typecore::mark_type_used(
                                    ctx,
                                    &temp_env,
                                    &row_id.name,
                                    arena.to_location(decl.ptype_loc),
                                );
                                set_fixed_row(
                                    ctx,
                                    &temp_env,
                                    decl.ptype_loc,
                                    &row_path,
                                    &internal_type_params,
                                    type_ref,
                                )?;
                            }
                            (Some(typed_manifest), Some(type_ref))
                        }
                        None => (None, None),
                    }
                };

                // OCaml Typedecl.transl_declaration unifies declaration
                // constraints before end_def/generalization, so constrained
                // parameters are linked in the stored declaration.
                unify_type_declaration_constraints(tctx, &typ_cstrs)?;
                // OCaml typedecl.ml:724-730: `Ctype.cyclic_abbrev env id ty`.
                if let Some(manifest) = manifest_type_ref
                    && crate::types::ctype::cyclic_abbrev(ctx, &temp_env, &type_id, manifest)
                {
                    return Err(TypeModError::RecursiveAbbrev {
                        loc: decl.ptype_loc,
                        name: arena.get_string(decl.ptype_name.txt).to_string(),
                    });
                }

                let type_attributes =
                    parser_attrs_to_decl_attrs(arena, tctx.type_ctx, &decl.ptype_attributes);
                let type_representation =
                    unboxed_type_representation(arena, decl, decl_has_unboxed_attr);
                let type_immediate = compute_type_immediacy(
                    ctx,
                    &temp_env,
                    &internal_type_kind,
                    manifest_type_ref,
                    &type_attributes,
                    type_representation,
                );
                if decl_attrs_mark_immediate(&type_attributes) && !type_immediate {
                    return Err(TypeModError::BadImmediateAttribute {
                        loc: decl.ptype_loc,
                    });
                }

                // OCaml compiler/ml/typedecl.ml:700-706 stores the source
                // declaration's private flag in the environment declaration.
                // Keeping private aliases private here prevents ordinary
                // unification from expanding them as public aliases; coercion
                // handles the manifest through the subtype path.
                let type_private = match decl.ptype_private {
                    crate::parser::ast::PrivateFlag::Public => crate::types::PrivateFlag::Public,
                    crate::parser::ast::PrivateFlag::Private => crate::types::PrivateFlag::Private,
                };

                // Create internal type declaration for the environment
                let internal_decl = crate::types::TypeDeclaration {
                    type_params: internal_type_params,
                    type_arity,
                    type_kind: internal_type_kind,
                    type_private,
                    type_manifest: manifest_type_ref,
                    type_variance: typ_params.iter().map(|(_, v)| *v).collect(),
                    type_newtype_level: None,
                    type_loc: tctx.intern_ast_loc(arena, decl.ptype_loc),
                    type_attributes,
                    type_immediate,
                    type_representation,
                    type_shape: crate::types::ValueShape::Unstated,
                    type_inlined_types: vec![],
                    type_path: None,
                };

                // Save for generalization after the loop
                internal_decls_for_generalize.push(internal_decl.clone());

                // Add constructors to environment. OCaml
                // compiler/ml/datarepr.ml:273-284 exposes env labels only for
                // `Type_record`; inline-record labels on `Type_variant`
                // constructors remain inside `cstr_inlined`, and
                // compiler/ml/env.ml:1668-1676 therefore installs no labels for
                // them.
                let mut env_labels = Vec::new();
                // Add record labels to environment
                if let crate::types::TypeKind::TypeRecord(ref labels, _) =
                    internal_decl.type_kind
                {
                    // Create the record type reference: Tconstr(type_path, type_params)
                    let ty_res =
                        ctx.new_constr(type_path, internal_decl.type_params.clone());
                    env_desc_types_for_generalize.push(ty_res);
                    let mut label_descs = Vec::with_capacity(labels.len());
                    // `Datarepr.label_descrs` (compiler/ml/datarepr.ml:261-288).
                    for (ld, lbl_desc) in labels.iter().zip(crate::types::env_lazy::label_descrs(
                        ty_res, &internal_decl, internal_decl.type_private, ctx, |_| {},
                    )) {
                        label_descs.push((ld.ld_id, lbl_desc));
                    }
                    env_labels = label_descs;
                }
                final_env_entries.push((type_id, internal_decl.clone(), constructors, env_labels));

                // Convert private flag
                // Create typed tree type declaration
                let typed_tree_decl = TypedTypeDeclaration {
                    typ_id: type_id,
                    typ_name: crate::parse_arena::Located {
                        txt: type_name_str.to_string(),
                        loc: decl.ptype_name.loc,
                    },
                    typ_params: typ_params
                        .into_iter()
                        .map(|(ct, v)| (tctx.typed.push_core_type(ct), v))
                        .collect(),
                    typ_type: internal_decl,
                    typ_cstrs: typ_cstrs
                        .into_iter()
                        .map(|(c1, c2, l)| {
                            (
                                tctx.typed.push_core_type(c1),
                                tctx.typed.push_core_type(c2),
                                l,
                            )
                        })
                        .collect(),
                    typ_kind: typed_tree_kind,
                    typ_private: decl.ptype_private,
                    typ_manifest: typ_manifest.map(|ct| tctx.typed.push_core_type(ct)),
                    typ_loc: decl.ptype_loc,
                    typ_attributes: decl.ptype_attributes.clone(),
                };

                typed_tree_decls.push(typed_tree_decl);
                typed_tree_decl_origins.push(decl.ptype_origin);
                if has_fixed_rows {
                    type_entry_ids.push(type_id);
                    type_entry_parser_indices.push(decl_idx);
                    type_entry_is_synthetic_row.push(false);
                }
                tctx.type_variables = saved_type_variables;
                tctx.drain_open_slot_uses();
                tctx.warning_config = decl_warning_config;
            }

            // typedecl.ml:1530: `current_slot := None`.
            tctx.type_ctx.usage().set_current_type_slot(None);
            // OCaml Typedecl.check_duplicates runs after translating the
            // declaration group and before final env construction/end_def.
            check_type_declaration_duplicate_definitions(tctx, arena, decls);
            // typedecl.ml:1509-1526: every declaration of the group records
            // the group's inline record definitions for printing.
            let inline_types =
                group_inline_record_types(&typed_tree_decl_origins, &typed_tree_decls);
            if !inline_types.is_empty() {
                for (_, decl, _, _) in final_env_entries.iter_mut() {
                    decl.type_inlined_types = inline_types.clone();
                }
                for typed_decl in typed_tree_decls.iter_mut() {
                    typed_decl.typ_type.type_inlined_types = inline_types.clone();
                }
                for decl in internal_decls_for_generalize.iter_mut() {
                    decl.type_inlined_types = inline_types.clone();
                }
            }
            // typedecl.ml:1578-1580: what each declaration states about its
            // values at run time, resolved in the environment it is declared
            // in (`Variant_layout.resolve_shapes ~env decls`).
            {
                let ids: Vec<Ident> = final_env_entries.iter().map(|(id, ..)| *id).collect();
                let group: Vec<crate::types::TypeDeclaration> =
                    final_env_entries.iter().map(|(_, decl, ..)| decl.clone()).collect();
                let shapes = resolve_declaration_group_shapes(ctx, env, &ids, &group)?;
                for (type_id, decl, _, _) in final_env_entries.iter_mut() {
                    if let Some(shape) = shape_for(&shapes, type_id) {
                        decl.type_shape = shape;
                    }
                }
                for typed_decl in typed_tree_decls.iter_mut() {
                    if let Some(shape) = shape_for(&shapes, &typed_decl.typ_id) {
                        typed_decl.typ_type.type_shape = shape;
                    }
                }
                if internal_decls_for_generalize.len() == ids.len() {
                    for (decl, id) in internal_decls_for_generalize.iter_mut().zip(&ids) {
                        if let Some(shape) = shape_for(&shapes, id) {
                            decl.type_shape = shape;
                        }
                    }
                }
            }
            // typedecl.ml:1535-1538: `List.fold_right (fun (id, decl) env ->
            // Env.add_type ~check:true id decl env) decls env`; `store_type`
            // (env.ml:1623-1632) adds constructors and labels with
            // `List.fold_right` too.
            for (type_id, decl, constructors, labels) in final_env_entries.into_iter().rev() {
                new_env.add_type(type_id, decl);
                if let Some((_, first)) = labels.first() {
                    new_env.add_type_label_family(type_id, first.lbl_all);
                }
                for (cstr_id, cstr_desc) in constructors.into_iter().rev() {
                    new_env.add_constructor(cstr_id, cstr_desc);
                }
                for (ld_id, lbl_desc) in labels.into_iter().rev() {
                    new_env.add_label(ld_id, lbl_desc);
                }
            }
            // typedecl.ml:1534-1538: the final env adds the declarations with
            // `Env.add_type ~check:true` through `List.fold_right`, registering
            // the remaining type and constructor usage checks last to first.
            register_type_declaration_usage_checks(tctx, env, &typed_tree_decls);

            // typedecl.ml:1540-1546 `update_type` (typedecl.ml:110-124): unify
            // each recursive stub's manifest variable with the declared type.
            if needs_placeholder {
                for (decl, type_id) in decls.iter().zip(declared_type_ids.iter()) {
                    let Ok(stub) = temp_env.find_type_by_ident(type_id) else {
                        continue;
                    };
                    let Some(manifest) = stub.type_manifest else {
                        continue;
                    };
                    let params = stub.type_params.iter().map(|_| ctx.new_var(None)).collect();
                    let constr = ctx.new_constr(Path::pident(*type_id), params);
                    let mut unify_state = crate::types::UnifyState::new();
                    unify_state.set_env(&new_env);
                    if let Err(err) = crate::types::unify(ctx, &mut unify_state, constr, manifest) {
                        let trace = match err {
                            crate::types::ctype::TypeError::Unify(trace) if !trace.is_empty() => {
                                trace
                            }
                            _ => vec![(constr, manifest)],
                        };
                        return Err(TypeModError::TypeDeclTypeClash {
                            loc: decl.ptype_loc,
                            trace,
                        });
                    }
                }
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

            let original_internal_decls_for_checks: Vec<_> = if has_fixed_rows {
                internal_decls_for_generalize
                    .iter()
                    .zip(type_entry_is_synthetic_row.iter())
                    .filter_map(|(decl, is_row)| (!*is_row).then_some(decl.clone()))
                    .collect()
            } else {
                internal_decls_for_generalize.clone()
            };

            check_type_declaration_abbrev_cycles(
                ctx,
                &new_env,
                &declared_type_ids,
                decls,
                &original_internal_decls_for_checks,
            )?;

            for typed_decl in &typed_tree_decls {
                if let Some((name, loc, detail, var)) =
                    find_unbound_type_var_in_typed_type_decl(&tctx.typed, ctx, typed_decl)
                {
                    return Err(TypeModError::UnboundTypeVar {
                        loc,
                        name,
                        detail,
                        var,
                    });
                }
            }

            // OCaml typedecl.ml:1588-1592 runs untagged checks first, then
            // check_constraints over the finalized declaration group.
            for decl in &internal_decls_for_generalize {
                check_variant_declaration_well_formed(ctx, &new_env, decl)?;
            }
            // typedecl.ml:1650-1653 `check_manifest_annotation` over the group.
            for (sdecl, decl) in decls.iter().zip(original_internal_decls_for_checks.iter()) {
                crate::types::variant_layout::check_manifest_annotation(
                    ctx,
                    arena.to_location(sdecl.ptype_loc),
                    &new_env,
                    decl,
                )?;
            }
            // typedecl.ml:1603 `List.iter2 (check_constraints ...) sdecl_list decls`.
            for (sdecl, decl) in decls.iter().zip(original_internal_decls_for_checks.iter()) {
                check_constraints(
                    ctx,
                    arena,
                    &new_env,
                    &mut tctx.persistent_env,
                    type_record_as_object,
                    sdecl,
                    decl,
                )?;
            }

            // OCaml typedecl.ml compute_properties_fixpoint:
            // recompute variances for the whole declaration group as a fixpoint.
            if has_fixed_rows {
                let required_variances: Vec<Vec<(bool, bool, bool)>> = type_entry_parser_indices
                    .iter()
                    .map(|parser_idx| {
                        decls[*parser_idx]
                            .ptype_params
                            .iter()
                            .map(|(_, variance)| parser_variance_requirement(*variance))
                            .collect()
                    })
                    .collect();
                let resolved_variances = compute_type_variance_fixpoint(
                    ctx,
                    &new_env,
                    &type_entry_ids,
                    &required_variances,
                );
                if resolved_variances.len() == type_entry_ids.len() {
                    for (idx, type_id) in type_entry_ids.iter().enumerate() {
                        let Some(variance_row) = resolved_variances.get(idx) else {
                            continue;
                        };
                        if !type_entry_is_synthetic_row[idx]
                            && let Some(typed_decl) = typed_tree_decls.get(idx)
                        {
                            check_type_decl_variance_requirements(
                                &tctx.typed,
                                ctx,
                                &new_env,
                                &decls[type_entry_parser_indices[idx]],
                                typed_decl,
                                variance_row,
                            )?;
                        }
                        if new_env
                            .update_type_variance(*type_id, variance_row.clone())
                            .is_none()
                        {
                            continue;
                        }

                        if let Some(typed_decl) = typed_tree_decls.get_mut(idx) {
                            typed_decl.typ_type.type_variance = variance_row.clone();
                        }
                        if let Some(internal_decl) = internal_decls_for_generalize.get_mut(idx) {
                            internal_decl.type_variance = variance_row.clone();
                        }
                    }
                }

                for (entry_idx, internal_decl) in internal_decls_for_generalize.iter().enumerate() {
                    if type_entry_is_synthetic_row[entry_idx] {
                        continue;
                    }
                    let idx = type_entry_parser_indices[entry_idx];
                    let mut coherence_warnings = Vec::new();
                    let coherence = check_type_declaration_coherence(
                        ctx,
                        &new_env,
                        decls[idx].ptype_loc,
                        &declared_type_ids[idx],
                        internal_decl,
                        &mut coherence_warnings,
                    );
                    report_inclusion_warnings(tctx, decls[idx].ptype_loc, coherence_warnings);
                    coherence?;
                }
            } else {
                let required_variances: Vec<Vec<(bool, bool, bool)>> = decls
                    .iter()
                    .map(|decl| {
                        decl.ptype_params
                            .iter()
                            .map(|(_, variance)| parser_variance_requirement(*variance))
                            .collect()
                    })
                    .collect();
                let resolved_variances = compute_type_variance_fixpoint(
                    ctx,
                    &new_env,
                    &declared_type_ids,
                    &required_variances,
                );
                if resolved_variances.len() == declared_type_ids.len() {
                    for (idx, type_id) in declared_type_ids.iter().enumerate() {
                        let Some(variance_row) = resolved_variances.get(idx) else {
                            continue;
                        };
                        if let Some(typed_decl) = typed_tree_decls.get(idx) {
                            check_type_decl_variance_requirements(
                                &tctx.typed,
                                ctx,
                                &new_env,
                                &decls[idx],
                                typed_decl,
                                variance_row,
                            )?;
                        }
                        if new_env
                            .update_type_variance(*type_id, variance_row.clone())
                            .is_none()
                        {
                            continue;
                        }

                        if let Some(typed_decl) = typed_tree_decls.get_mut(idx) {
                            typed_decl.typ_type.type_variance = variance_row.clone();
                        }
                        if let Some(internal_decl) = internal_decls_for_generalize.get_mut(idx) {
                            internal_decl.type_variance = variance_row.clone();
                        }
                    }
                }

                for (idx, internal_decl) in internal_decls_for_generalize.iter().enumerate() {
                    let mut coherence_warnings = Vec::new();
                    let coherence = check_type_declaration_coherence(
                        ctx,
                        &new_env,
                        decls[idx].ptype_loc,
                        &declared_type_ids[idx],
                        internal_decl,
                        &mut coherence_warnings,
                    );
                    report_inclusion_warnings(tctx, decls[idx].ptype_loc, coherence_warnings);
                    coherence?;
                }
            }

            let item_sig = sig_type_rec_statuses(*rec_flag, typed_tree_decls.as_slice())
                .into_iter()
                .zip(typed_tree_decls.iter())
                .zip(internal_decls_for_generalize.iter())
                .map(|((rec_status, typed_decl), decl)| {
                    crate::types::decl::SignatureItem::SigType(
                        typed_decl.typ_id,
                        std::sync::Arc::new(decl.clone()),
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
            transl_type_extension(tctx, env, arena, loc, ext, true)
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
            tctx.reset_type_variables();
            ctx.begin_def();

            // Translate constructor arguments and collect type refs for env registration
            let (ext_kind, ext_args, cstr_args, cstr_inlined, ext_ret_ty) = match &ext_constr
                .pext_kind
            {
                crate::parser::ast::ExtensionConstructorKind::Pext_decl(args, ret) => {
                    let mut arg_ty_refs = Vec::new();
                    let (typed_args, ext_args, cstr_args, cstr_inlined) = match args {
                        crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                            let mut typed = Vec::new();
                            for ty in types {
                                let (typed_ct, ty_ref) = transl_decl_arg_type(
                                    tctx,
                                    env,
                                    arena.get_core_type(*ty),
                                    ret.is_none(),
                                )?;
                                arg_ty_refs.push(ty_ref);
                                typed.push(typed_ct);
                            }
                            (
                                crate::types::typedtree::ConstructorArgument::Cstr_tuple(
                                    tctx.typed.push_core_types(typed),
                                ),
                                crate::types::ConstructorArguments::CstrTuple(arg_ty_refs.clone()),
                                arg_ty_refs.clone(),
                                None,
                            )
                        }
                        crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                            check_duplicate_label_declarations(arena, labels, None)?;
                            let mut typed_labels = Vec::new();
                            let mut decl_labels = Vec::new();
                            for label in labels {
                                check_extra_as_attribute(arena, label)?;
                                let label_name = arena.get_string(label.pld_name.txt).to_string();
                                let (typed_ct, ty_ref) =
                                    transl_label_type(tctx, env, arena, label, ret.is_none())?;
                                let (poly_typed_ct, poly_ty_ref) = force_poly_typed_core_type(
                                    &mut tctx.typed,
                                    ctx,
                                    typed_ct,
                                    ty_ref,
                                );
                                let internal_ty_ref = match &*ctx.get_desc(poly_ty_ref) {
                                    crate::types::type_expr::TypeDesc::Tpoly { body, vars }
                                        if vars.is_empty() =>
                                    {
                                        *body
                                    }
                                    _ => poly_ty_ref,
                                };
                                let label_id = ctx.create_ast_ident(arena, label.pld_name.txt);
                                typed_labels.push(crate::types::typedtree::LabelDeclaration {
                                    ld_id: label_id,
                                    ld_name: crate::parse_arena::Located {
                                        txt: label_name.clone(),
                                        loc: label.pld_name.loc,
                                    },
                                    ld_runtime_name:
                                        crate::types::record_runtime::parsetree_runtime_name(
                                            label, arena,
                                        ),
                                    ld_mutable: label.pld_mutable,
                                    ld_optional: label.pld_optional,
                                    ld_type: tctx.typed.push_core_type(poly_typed_ct),
                                    ld_loc: label.pld_loc,
                                    ld_attributes: label.pld_attributes.clone(),
                                });
                                decl_labels.push(crate::types::LabelDeclaration {
                                    ld_id: label_id,
                                    ld_runtime_name:
                                        crate::types::record_runtime::parsetree_runtime_name(
                                            label, arena,
                                        ),
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
                                    ld_loc: tctx.intern_ast_loc(arena, label.pld_loc),
                                    ld_attributes: vec![],
                                });
                            }
                            let inline_path = Path::pident(id);
                            let inline_ty = ctx.new_generic_constr(inline_path, vec![]);
                            let inline_decl = crate::types::TypeDeclaration {
                                type_params: vec![],
                                type_arity: 0,
                                type_kind: crate::types::TypeKind::TypeRecord(
                                    crate::types::decl::SharedVec::from(decl_labels.clone()),
                                    crate::types::RecordRepresentation::RecordExtension,
                                ),
                                type_private: crate::types::PrivateFlag::Public,
                                type_manifest: None,
                                type_variance: vec![],
                                type_newtype_level: None,
                                type_loc: crate::types::DeclLoc::none(),
                                type_attributes: vec![],
                                type_immediate: false,
                                type_representation: crate::types::TypeRepresentation::Boxed,
                                type_shape: crate::types::ValueShape::Unstated,
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
                            let expected_exn =
                                ctx.new_predef_constr(crate::types::predef::path_exn(), vec![]);
                            let ret_repr = ctx.repr(ty_ref);
                            let ret_is_exn = matches!(
                                &*ctx.get_desc(ret_repr),
                                crate::types::type_expr::TypeDesc::Tconstr { path, .. }
                                    if path.same(&crate::types::predef::path_exn())
                            );
                            if !ret_is_exn {
                                return Err(TypeModError::ConstraintFailed {
                                    loc: arena.get_core_type(*ct).ptyp_loc,
                                    actual: ty_ref,
                                    expected: expected_exn,
                                });
                            }
                            (Some(typed_ct), Some(ty_ref))
                        }
                        None => (None, None),
                    };
                    (
                        crate::types::typedtree::ExtensionConstructorKind::Text_decl(
                            typed_args,
                            typed_ret.map(|ct| tctx.typed.push_core_type(ct)),
                        ),
                        ext_args,
                        cstr_args,
                        cstr_inlined,
                        ext_ret_ty,
                    )
                }
                crate::parser::ast::ExtensionConstructorKind::Pext_rebind(lid) => {
                    let (rebind_path, rebind_desc) = lookup_rebind_constructor(tctx, env, lid)?;
                    let (inst_args, cstr_res) =
                        crate::types::instance_constructor(ctx, &rebind_desc);
                    let (res, ret_type) = if rebind_desc.cstr_generalized {
                        let res = ctx.new_predef_constr(crate::types::predef::path_exn(), vec![]);
                        let ret_type =
                            Some(ctx.new_predef_constr(crate::types::predef::path_exn(), vec![]));
                        (res, ret_type)
                    } else {
                        (
                            ctx.new_predef_constr(crate::types::predef::path_exn(), vec![]),
                            None,
                        )
                    };
                    if let Err(err) =
                        crate::types::ctype::unify(ctx, &mut tctx.unify_state, cstr_res, res)
                    {
                        return Err(TypeModError::RebindWrongType {
                            loc: lid.loc,
                            lid: tctx.resolve_lid(lid.txt).clone(),
                            trace: match err {
                                crate::types::ctype::TypeError::Unify(trace)
                                    if !trace.is_empty() =>
                                {
                                    trace
                                }
                                _ => vec![(cstr_res, res)],
                            },
                            env: tctx.type_ctx.store_typed_env(env),
                        });
                    }
                    if matches!(rebind_desc.cstr_private, crate::types::PrivateFlag::Private) {
                        return Err(TypeModError::RebindPrivate {
                            loc: lid.loc,
                            lid: tctx.resolve_lid(lid.txt).clone(),
                        });
                    }
                    let ext_args = rebind_constructor_arguments(tctx, &rebind_desc, &inst_args);
                    // `Datarepr.extension_descr` -> `constructor_args`
                    // (compiler/ml/datarepr.ml:64-92): an inline record
                    // becomes a record type at the new constructor's path.
                    let (cstr_args, cstr_inlined) =
                        rebound_constructor_args(ctx, &Path::pident(id), &ext_args);
                    (
                        crate::types::typedtree::ExtensionConstructorKind::Text_rebind(
                            rebind_path,
                            *lid,
                        ),
                        ext_args,
                        cstr_args.unwrap_or(inst_args),
                        cstr_inlined.or_else(|| rebind_desc.cstr_inlined.clone()),
                        ret_type,
                    )
                }
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
            if let crate::types::typedtree::ExtensionConstructorKind::Text_decl(
                typed_args,
                typed_ret,
            ) = &ext_kind
            {
                if typed_ret.is_none() {
                    let allowed_type_params = HashSet::new();
                    if let Some((name, loc)) = find_unbound_type_var_in_typed_constructor_args(
                        &tctx.typed,
                        ctx,
                        typed_args,
                        &allowed_type_params,
                    ) {
                        return Err(TypeModError::UnboundTypeVarExt { loc, name });
                    }
                    // `Ctype.closed_extension_constructor` (ctype.ml:454-464,
                    // typedecl.ml:1857-1862).
                    if let Some(var) = find_unbound_type_var_in_constructor_args(
                        ctx,
                        &ext_args,
                        &allowed_type_params,
                    ) {
                        return Err(TypeModError::UnboundTypeVarInExtension {
                            loc: ext_constr.pext_loc,
                            var,
                            args: ext_args.clone(),
                        });
                    }
                }
            }

            // Register the exception constructor in the environment
            let exn_ty = tctx
                .type_ctx
                .new_generic_predef_constr(crate::types::predef::path_exn(), vec![]);
            let exn_path = Path::pident(id);
            let cstr_res = ext_ret_ty.unwrap_or(exn_ty);
            let cstr_existentials =
                crate::types::env::constructor_existentials(ctx, &cstr_args, ext_ret_ty);
            let cstr_desc = crate::types::decl::ConstructorDescription {
                cstr_name: name_str.clone(),
                cstr_res,
                cstr_existentials,
                cstr_args: cstr_args.clone(),
                cstr_arity: cstr_args.len() as i32,
                cstr_kind: crate::types::ConstructorKind::Extension(exn_path),
                cstr_generalized: ext_ret_ty.is_some(),
                cstr_private: crate::types::PrivateFlag::Public,
                // `Datarepr.extension_descr`: `cstr_loc = ext.ext_loc`.
                cstr_loc: tctx.intern_ast_loc(arena, ext_constr.pext_loc),
                // `Datarepr.extension_descr`: `cstr_attributes = ext.ext_attributes`
                // (typedecl.ml `ext_attributes = sext.pext_attributes`).
                cstr_attributes: parser_attrs_to_decl_attrs(
                    arena,
                    tctx.type_ctx,
                    &ext_constr.pext_attributes,
                ),
                cstr_inlined: cstr_inlined.clone(),
            };
            let mut new_env = env.clone();
            // Exceptions use the same OCaml path as extensions:
            // compiler/ml/env.ml:1693-1716 adds only the constructor, while
            // compiler/ml/datarepr.ml:190-214 keeps inline-record labels under
            // `cstr_inlined`.
            // typedecl.ml:1863: `Env.add_extension ~check:true`.
            tctx.check_extension_usage(
                "exn",
                &name_str,
                true,
                arena.to_location(ext_constr.pext_loc),
                ext_constr.pext_loc,
                env.is_in_signature(),
            );
            new_env.add_constructor(id, cstr_desc);

            let ext_type = crate::types::ExtensionConstructor {
                ext_type_path: crate::types::predef::path_exn(),
                ext_type_params: vec![],
                ext_args,
                ext_ret_type: ext_ret_ty,
                ext_private: crate::types::PrivateFlag::Public,
                ext_loc: tctx.intern_ast_loc(arena, ext_constr.pext_loc),
                ext_attributes: parser_attrs_to_decl_attrs(
                    arena,
                    tctx.type_ctx,
                    &ext_constr.pext_attributes,
                ),
                ext_is_exception: true,
            };
            let desc = StructureItemDesc::Tstr_exception(tctx.typed.push_extension_constructor(
                crate::types::typedtree::ExtensionConstructor {
                    ext_id: id,
                    ext_name: crate::parse_arena::Located {
                        txt: name_str,
                        loc: ext_constr.pext_name.loc,
                    },
                    ext_type: ext_type.clone(),
                    ext_kind,
                    ext_loc: ext_constr.pext_loc,
                    ext_attributes: ext_constr.pext_attributes.clone(),
                },
            ));
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
            // OCaml compiler/ml/typemod.ml:1453-1456 scopes warnings from
            // module-binding attributes around module expression typing.
            let typed_mod = with_warning_scope(tctx, arena, &mb.pmb_attributes, true, |tctx| {
                type_module_expr_with_alias(
                    tctx,
                    env,
                    arena,
                    arena.get_mod_expr(mb.pmb_expr),
                    true,
                    true,
                )
            })?;

            // Extend environment with the new module
            let mut new_env = env.clone();
            let mut decl_mod_type =
                decl_module_type_from_typed_module_expr_for_sig(&tctx.typed, &typed_mod)
                    .unwrap_or_else(|| {
                        crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(vec![]))
                    });
            anchor_local_module_aliases_to_owner(&mut decl_mod_type, &Path::pident(mod_id));
            // OCaml compiler/ml/typemod.ml:1451-1471 stores
            // `enrich_module_type anchor name modl.mod_type env` directly in the
            // module declaration. For a non-structure module expression such as an
            // applicative functor application, that preserves the result
            // signature's applicative paths until Env component forcing reaches
            // compiler/ml/env.ml:1744-1756 `components_of_functor_appl`.
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
                        if !structure_has_dotted_alias_child_modules(&tctx.typed, structure) {
                            decl_mod_type.clone()
                        } else {
                            let mut sig = crate::types::typecore::copy_lookup_signature_for_subst(
                                sig,
                                tctx.type_ctx,
                            );
                            localize_alias_child_module_sig_paths_in_structure_sig(
                                &tctx.typed,
                                &mut sig,
                                structure,
                                &Path::pident(mod_id),
                                tctx.type_ctx,
                            );
                            crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(sig))
                        }
                    } else {
                        decl_mod_type.clone()
                    }
                }
                _ => decl_mod_type.clone(),
            };
            let item_sig_mod_type = localized_decl_mod_type.clone();
            let module_attributes =
                parser_attrs_to_decl_attrs(arena, tctx.type_ctx, &mb.pmb_attributes);
            // typemod.ml:1517: `Env.enter_module_declaration id md env`.
            store_module_deprecated(tctx.type_ctx, &module_attributes)?;
            new_env.add_module(
                mod_id,
                crate::types::decl::ModuleDeclaration {
                    md_type: localized_decl_mod_type,
                    md_attributes: module_attributes.clone(),
                    md_loc: tctx.intern_ast_loc(arena, mb.pmb_loc),
                    md_path: None,
                },
            );
            // typemod.ml:1470: `Env.enter_module_declaration` registers the
            // unused-module check.
            tctx.check_module_usage(mod_name_str, arena.to_location(mb.pmb_loc), mb.pmb_loc);
            let item_sig = vec![crate::types::decl::SignatureItem::SigModule(
                mod_id,
                crate::types::decl::ModuleDeclaration {
                    md_type: item_sig_mod_type,
                    md_attributes: module_attributes,
                    md_loc: tctx.intern_ast_loc(arena, mb.pmb_loc),
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
                mb_expr: tctx.typed.push_module_expr(typed_mod),
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
            // Recursive modules: module rec M : S = ...
            let mut rec_bindings = Vec::with_capacity(mbs.len());
            for mb in mbs.iter() {
                let mod_name_str = arena.get_string(mb.pmb_name.txt);
                let mb_expr = arena.get_mod_expr(mb.pmb_expr);
                let (inner_expr, mty) = match &mb_expr.pmod_desc {
                    ParsedModuleExprDesc::Pmod_constraint(inner_expr, mty) => (*inner_expr, *mty),
                    _ => {
                        return Err(TypeModError::RecursiveModuleRequiresExplicitType {
                            loc: mb_expr.pmod_loc,
                        });
                    }
                };
                rec_bindings.push((
                    mod_name_str.to_string(),
                    mb.pmb_name.loc,
                    inner_expr,
                    mty,
                    mb.pmb_attributes.clone(),
                    mb.pmb_loc,
                ));
            }

            // OCaml transl_recmodule_modtypes (typemod.ml:914-981).
            let rec_type_decls: Vec<_> = rec_bindings
                .iter()
                .map(|(name, name_loc, _, mty_idx, attrs, mb_loc)| {
                    (name.clone(), *name_loc, *mty_idx, attrs.clone(), *mb_loc)
                })
                .collect();
            let (dcl2, rec_env) = transl_recmodule_modtypes(tctx, env, arena, &rec_type_decls)?;

            // Type-check each module body with the environment produced by the
            // second recursive-module-type transition.
            // Match OCaml: for Pmod_constraint(expr, typ), type-check only expr (inner body),
            // then wrap in Tmod_constraint with mod_loc from the inner module (not the
            // constraint wrapper). OCaml does this in check_recmodule_inclusion.
            let mut body_bindings = Vec::with_capacity(rec_bindings.len());
            for ((name, name_loc, inner_expr, _, attrs, mb_loc), decl) in
                rec_bindings.iter().zip(dcl2.iter())
            {
                let typed_inner =
                    type_module_expr(tctx, &rec_env, arena, arena.get_mod_expr(*inner_expr))?;
                body_bindings.push((
                    name.clone(),
                    *name_loc,
                    typed_inner,
                    decl.clone(),
                    attrs.clone(),
                    *mb_loc,
                ));
            }
            // typemod.ml:1535-1545: once the bodies are typed, the modules
            // enter the environment with their declarations and
            // `Env.add_module_declaration ~check:true`.
            let mut new_env = env.clone();
            for ((name, _, _, _, attrs, mb_loc), decl) in rec_bindings.iter().zip(dcl2.iter()) {
                let md_attributes = parser_attrs_to_decl_attrs(arena, tctx.type_ctx, attrs);
                // typemod.ml:1591: `Env.add_module_declaration ~check:true`.
                store_module_deprecated(tctx.type_ctx, &md_attributes)?;
                new_env.add_module(
                    decl.md_id,
                    crate::types::decl::ModuleDeclaration {
                        md_type: tctx.typed.module_type(decl.md_type).mty_type.clone(),
                        md_attributes,
                        md_loc: tctx.intern_ast_loc(arena, *mb_loc),
                        md_path: None,
                    },
                );
                tctx.check_module_usage(name, arena.to_location(*mb_loc), *mb_loc);
            }

            // Match OCaml compiler/ml/typemod.ml:1056-1120
            // `check_recmodule_inclusion`: unroll recursive module actual types
            // a finite number of times, using the number of recursive bindings
            // as the depth. Inclusion is then checked under that unrolled
            // environment while the emitted constraint keeps the declared
            // module type.
            let mut inclusion_env = new_env.clone();
            let mut inclusion_subst: Vec<(Ident, Path)> = Vec::new();
            let mut first_time = true;
            for _ in 0..body_bindings.len() {
                let renamed_ids = body_bindings
                    .iter()
                    .map(|(_, _, _, decl, _, _)| tctx.type_ctx.rename_ident(&decl.md_id))
                    .collect::<Vec<_>>();
                let mut next_subst = Vec::with_capacity(body_bindings.len());
                for ((_, _, typed_inner, decl, _, _), renamed_id) in
                    body_bindings.iter().zip(renamed_ids.iter())
                {
                    let actual_mty = if first_time {
                        typed_inner.mod_type.clone()
                    } else {
                        recmodule_subst_and_strengthen(
                            tctx.type_ctx,
                            &inclusion_env,
                            &inclusion_subst,
                            &decl.md_id,
                            &typed_inner.mod_type,
                        )
                    };
                    inclusion_env.add_module(*renamed_id, empty_module_decl(actual_mty));
                    next_subst.push((decl.md_id, Path::pident(*renamed_id)));
                }
                inclusion_subst = next_subst;
                first_time = false;
            }

            let mut typed_bindings = Vec::with_capacity(body_bindings.len());
            for (name, name_loc, typed_inner, decl, attrs, mb_loc) in body_bindings {
                let inner_loc = typed_inner.mod_loc;
                let include_decl_mty = recmodule_subst_modtype(
                    tctx.type_ctx,
                    &inclusion_subst,
                    &tctx.typed.module_type(decl.md_type).mty_type,
                );
                let include_actual_mty = recmodule_subst_and_strengthen(
                    tctx.type_ctx,
                    &inclusion_env,
                    &inclusion_subst,
                    &decl.md_id,
                    &typed_inner.mod_type,
                );
                let typed_mod = wrap_checked_constraint(
                    tctx,
                    &inclusion_env,
                    typed_inner,
                    &include_actual_mty,
                    &include_decl_mty,
                    ConstraintNode {
                        mty: tctx.typed.module_type(decl.md_type).mty_type.clone(),
                        explicit: crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(
                            decl.md_type,
                        ),
                        loc: inner_loc,
                        attributes: Attributes::new(),
                    },
                )?;
                typed_bindings.push(ModuleBinding {
                    mb_id: decl.md_id,
                    mb_name: Located {
                        txt: name,
                        loc: name_loc,
                    },
                    mb_expr: tctx.typed.push_module_expr(typed_mod),
                    mb_attributes: attrs,
                    mb_loc,
                });
            }
            let item_sig = typed_bindings
                .iter()
                .enumerate()
                .map(|(index, mb)| {
                    // typemod.ml:1551-1557.
                    crate::types::decl::SignatureItem::SigModule(
                        mb.mb_id,
                        crate::types::decl::ModuleDeclaration {
                            md_type: tctx.typed.module_expr(mb.mb_expr).mod_type.clone(),
                            md_attributes: parser_attrs_to_decl_attrs(
                                arena,
                                tctx.type_ctx,
                                &mb.mb_attributes,
                            ),
                            md_loc: tctx.intern_ast_loc(arena, mb.mb_loc),
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

            // typemod.ml:887-889: `transl_modtype_decl` runs in
            // `Builtin_attributes.warning_scope pmtd_attributes`.
            let (typed_mty, mtd_id) =
                with_warning_scope(tctx, arena, &mtd.pmtd_attributes, true, |tctx| {
                    let typed_mty = match &mtd.pmtd_type {
                        Some(mt) => {
                            Some(transl_modtype(tctx, env, arena, arena.get_mod_type(*mt))?)
                        }
                        None => None,
                    };
                    let mtd_id = tctx.type_ctx.create_ident(mtd_name_str);
                    Ok::<_, TypeModError>((typed_mty, mtd_id))
                })?;
            let decl_mtd_type = typed_mty.as_ref().map(|tmty| tmty.mty_type.clone());

            let desc = StructureItemDesc::Tstr_modtype(ModuleTypeDeclaration {
                mtd_id,
                mtd_name: Located {
                    txt: mtd_name_str.to_string(),
                    loc: mtd.pmtd_name.loc,
                },
                mtd_type: typed_mty.map(|mty| tctx.typed.push_module_type(mty)),
                mtd_attributes: mtd.pmtd_attributes.clone(),
                mtd_loc: mtd.pmtd_loc,
            });

            // Add the module type to the environment
            let mut new_env = env.clone();
            let mtd_attributes =
                parser_attrs_to_decl_attrs(arena, tctx.type_ctx, &mtd.pmtd_attributes);
            let decl_mtd = crate::types::decl::ModtypeDeclaration {
                mtd_type: decl_mtd_type,
                mtd_attributes,
                mtd_loc: tctx.intern_ast_loc(arena, mtd.pmtd_loc),
            };
            new_env.add_modtype(mtd_id, decl_mtd.clone());

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
            crate::types::typecore::mark_open_lid_use(
                tctx.type_ctx,
                env,
                arena,
                &longident,
                crate::types::env::OpenLookupKind::Module,
                Some(open_desc.popen_lid.loc),
            );
            // OCaml `type_open_` (compiler/ml/typemod.ml:88-89) starts with
            // `Typetexp.lookup_module ~load:true`, which raises for an unbound module.
            let Some(fallback_path) = lookup_module_path_by_lid(
                &longident,
                arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            ) else {
                return Err(TypeModError::CoreError(
                    crate::types::typecore::unbound_module_lookup_error(
                        tctx,
                        env,
                        open_desc.popen_lid.loc,
                        &longident,
                    ),
                ));
            };

            // Extend the environment with the opened module's bindings using the
            // same alias-rewritten module resolution path as value lookup.
            let open_lid = arena.get_longident(open_desc.popen_lid.txt);
            let mut new_env = env.clone();
            let slot = tctx.open_signature_slot(open_desc.popen_override, open_desc.popen_loc);
            let path = if let Some(path) = open_direct_persistent_module(
                &mut new_env,
                open_lid,
                arena,
                &mut tctx.persistent_env,
                tctx.type_ctx,
                slot,
            ) {
                // OCaml compiler/ml/typemod.ml:88-90 handles structure opens
                // through `Env.open_signature`; for persistent roots that reaches
                // compiler/ml/env.ml:1874-1877 and forces the cached `ps_comps`
                // table from env.ml:669-678.
                path
            } else if let Some(path) = {
                let lookup_env = env.clone();
                crate::types::typecore::open_module_lid_components_into_env(
                    open_lid,
                    arena,
                    &lookup_env,
                    &mut new_env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                    slot,
                )
            } {
                path
            } else {
                // OCaml compiler/ml/typemod.ml:88-95 first calls
                // `Env.open_signature`; only when that fails does it call
                // `Env.find_module`/`extract_sig_open` to raise
                // `Structure_expected`. Keep this scrape on the failure path so
                // successful opens do not force module aliases before the
                // opened component table is installed.
                if let Some(err) = structure_expected_error_for_open(
                    tctx,
                    env,
                    arena,
                    &longident,
                    open_desc.popen_lid.loc,
                ) {
                    return Err(err);
                }
                fallback_path
            };
            tctx.set_open_slot_root(slot, &path);

            let desc = StructureItemDesc::Tstr_open(OpenDeclaration {
                open_path: path,
                open_txt: open_desc.popen_lid,
                open_override: open_desc.popen_override,
                open_attributes: open_desc.popen_attributes.clone(),
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    // typemod.ml:1603 `str_loc = pstr.pstr_loc` for every item;
                    // `type_open` keeps `popen_loc` for its own warnings.
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                vec![],
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_include(incl) => {
            // Include declaration: include ME
            // OCaml compiler/ml/typemod.ml:1524-1527 scopes include
            // attributes around the included module expression typing.
            let typed_mod =
                with_warning_scope(tctx, arena, &incl.pincl_attributes, true, |tctx| {
                    type_module_expr(tctx, env, arena, arena.get_mod_expr(incl.pincl_mod))
                })?;
            // OCaml `extract_sig_open` (compiler/ml/typemod.ml:80-84) raises
            // `Structure_expected` when the included module is a functor.
            {
                let scraped = scrape_alias_module_type(
                    &typed_mod.mod_type,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .unwrap_or_else(|| typed_mod.mod_type.clone());
                if matches!(scraped, crate::types::decl::ModuleType::MtyFunctor { .. }) {
                    return Err(TypeModError::StructureExpected {
                        loc: arena.get_mod_expr(incl.pincl_mod).pmod_loc,
                        mty: scraped,
                    });
                }
            }
            let final_include_sig = resolve_mod_type_to_sig(
                &typed_mod.mod_type,
                Some(env),
                &mut tctx.persistent_env,
                tctx.type_ctx,
            );
            let stored_include_sig = final_include_sig.as_ref().map(|sig_items| {
                crate::cmi::persistent_env::freshened_signature_bound_idents_from_kind(
                    "typemod_include_stored_sig",
                    sig_items,
                    tctx.type_ctx,
                )
            });
            let localized_include_sig = stored_include_sig.as_ref().map(|sig_items| {
                let mut sig = crate::types::typecore::copy_lookup_signature_for_subst(
                    sig_items,
                    tctx.type_ctx,
                );
                let include_root_path = include_module_root_path(&tctx.typed, &typed_mod);
                let include_alias_heads = include_module_alias_heads(
                    &tctx.typed,
                    &typed_mod,
                    tctx.persistent_env.as_ref(),
                    tctx.type_ctx,
                );
                let local_include_types: HashMap<String, Ident> = sig
                    .iter()
                    .filter_map(|item| match item {
                        crate::types::decl::SignatureItem::SigType(id, _, _) => {
                            Some((id.name().to_string(), *id))
                        }
                        _ => None,
                    })
                    .collect();
                let local_include_modules: HashMap<String, Ident> = sig
                    .iter()
                    .filter_map(|item| match item {
                        crate::types::decl::SignatureItem::SigModule(id, _, _) => {
                            Some((id.name().to_string(), *id))
                        }
                        _ => None,
                    })
                    .collect();
                let local_include_modtypes: HashMap<String, Ident> = sig
                    .iter()
                    .filter_map(|item| match item {
                        crate::types::decl::SignatureItem::SigModtype(id, _) => {
                            Some((id.name().to_string(), *id))
                        }
                        _ => None,
                    })
                    .collect();
                let mut visited = HashSet::new();
                rewrite_included_signature_paths_to_local(
                    tctx.type_ctx,
                    &mut sig,
                    &IncludeLocalization {
                        root_path: include_root_path.as_ref(),
                        alias_heads: &include_alias_heads,
                        types: &local_include_types,
                        modules: &local_include_modules,
                        modtypes: &local_include_modtypes,
                    },
                    &mut visited,
                );
                sig
            });
            let mut new_env = env.clone();
            if let Some(sig_items) = &localized_include_sig {
                // OCaml's include adds all signature items directly to the environment
                // as if they were defined locally (Pident paths, not Pdot paths).
                // This matches OCaml's Env.add_signature behavior.
                for (sig_index, item) in sig_items.iter().enumerate() {
                    match item {
                        crate::types::decl::SignatureItem::SigValue(id, desc) => {
                            check_value_name_for_env(tctx.type_ctx, id, desc)?;
                            new_env.add_value(*id, desc.clone());
                        }
                        crate::types::decl::SignatureItem::SigType(id, decl, _) => {
                            new_env.add_type(*id, decl.clone());
                            if let crate::types::TypeKind::TypeVariant(constructors, _) =
                                &decl.type_kind
                            {
                                // Include should expose constructors from included variant types
                                // in the current scope, matching OCaml's Env.add_signature.
                                let ty_res = tctx.type_ctx.new_constr(
                                    crate::types::path::Path::pident(*id),
                                    decl.type_params.clone(),
                                );
                                crate::types::ctype::force_generalize_sig_type(
                                    tctx.type_ctx,
                                    ty_res,
                                );

                                let mut inline_record_descs: Option<
                                    Vec<crate::types::ConstructorDescription>,
                                > = None;
                                for (position, cd) in constructors.iter().enumerate() {
                                    // `Datarepr.constructor_args` (datarepr.ml:64-92): an
                                    // inline record is one argument, the record type at
                                    // `Pdot (type_path, cstr_name)`, with its declaration
                                    // in `cstr_inlined`.
                                    let (cstr_args, cstr_arity, cstr_inlined) = match &cd.cd_args {
                                        crate::types::decl::ConstructorArguments::CstrTuple(
                                            args,
                                        ) => (args.clone(), args.len() as i32, None),
                                        crate::types::decl::ConstructorArguments::CstrRecord(_) => {
                                            let inlined = inline_record_descs
                                                .get_or_insert_with(|| {
                                                    crate::types::env_lazy::constructors_of_type_path(
                                                        &crate::types::path::Path::pident(*id),
                                                        decl,
                                                        tctx.type_ctx,
                                                    )
                                                })
                                                .iter()
                                                .find(|desc| desc.cstr_name == cd.cd_id.name())
                                                .expect("a descriptor per constructor");
                                            (
                                                inlined.cstr_args.clone(),
                                                inlined.cstr_arity,
                                                inlined.cstr_inlined.clone(),
                                            )
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
                                        cstr_kind: crate::types::ConstructorKind::Ordinary(
                                            crate::types::ConstructorReference {
                                                variant: decl.variant_layout_ref().expect("variant layout"),
                                                position,
                                            },
                                        ),
                                        cstr_generalized: cd.cd_res.is_some(),
                                        cstr_private: decl.type_private,
                                        cstr_loc: cd.cd_loc,
                                        cstr_attributes:
                                            crate::types::decl::constructor_description_attrs_for_variant(
                                                constructors, cd,
                                            ),
                                        cstr_inlined,
                                    };
                                    new_env.add_constructor(cd.cd_id, cstr_desc);
                                }
                            }
                            if let crate::types::TypeKind::TypeRecord(labels, _) =
                                &decl.type_kind
                            {
                                // Include should expose record labels from included types
                                // in the current scope, matching OCaml's Env.add_signature.
                                let ty_res = tctx.type_ctx.new_constr(
                                    crate::types::path::Path::pident(*id),
                                    decl.type_params.clone(),
                                );
                                // Include signatures can carry non-generic nodes in Rust.
                                // Promote the shared label scheme to generic-level so
                                // instance_label can instantiate fresh per-use copies.
                                crate::types::ctype::force_generalize_sig_type(
                                    tctx.type_ctx,
                                    ty_res,
                                );
                                // `Datarepr.label_descrs` (compiler/ml/datarepr.ml:261-288).
                                let descs = crate::types::env_lazy::label_descrs(
                                    ty_res,
                                    decl,
                                    decl.type_private,
                                    tctx.type_ctx,
                                    |descs| {
                                        for desc in descs {
                                            crate::types::ctype::force_generalize_sig_type(
                                                tctx.type_ctx,
                                                desc.lbl_arg,
                                            );
                                        }
                                    },
                                );
                                if let Some(first) = descs.first() {
                                    new_env.add_type_label_family(*id, first.lbl_all);
                                }
                                for (ld, lbl_desc) in labels.iter().zip(descs) {
                                    new_env.add_label(ld.ld_id, lbl_desc);
                                }
                            }
                        }
                        crate::types::decl::SignatureItem::SigModule(id, md, _) => {
                            let env_md = if module_type_is_self_alias(&md.md_type, id) {
                                // OCaml compiler/ml/typemod.ml:1575-1581
                                // computes `sg = Subst.signature identity
                                // (extract_sig_open ...)` and passes that same
                                // signature to `Env.add_signature`. Do not let
                                // Rust's include-local path rewrite turn a
                                // child alias such as `DB__Scene__Read.Key`
                                // into `Key = Key`; env.ml:1718-1731 would
                                // store an empty self-alias component table.
                                stored_include_sig
                                    .as_ref()
                                    .and_then(|stored_sig| match stored_sig.get(sig_index) {
                                        Some(crate::types::decl::SignatureItem::SigModule(
                                            _,
                                            stored_md,
                                            _,
                                        )) => Some(stored_md.clone()),
                                        _ => None,
                                    })
                                    .unwrap_or_else(|| md.clone())
                            } else {
                                md.clone()
                            };
                            new_env.add_module(*id, env_md);
                        }
                        crate::types::decl::SignatureItem::SigModtype(id, mtd) => {
                            new_env.add_modtype(*id, mtd.clone());
                        }
                        _ => {}
                    }
                }
            }

            // typemod.ml:1568-1589: the environment and the structure's
            // signature both take the same `Subst.signature` of the included
            // module type, whose items name each other locally.
            let item_sig = localized_include_sig
                .or(stored_include_sig)
                .unwrap_or_default();
            let desc = StructureItemDesc::Tstr_include(IncludeDeclaration {
                incl_mod: tctx.typed.push_module_expr(typed_mod),
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
            // typemod.ml:1643.
            apply_warning_attribute(tctx, arena, attr)?;
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
            let (extension, _attrs) = &**inner;
            Err(TypeModError::CoreError(
                crate::types::typecore::builtin_extension_error(arena, extension),
            ))
        }
        // typemod.ml: the built-in PPX lowers raw JavaScript before type
        // checking.
        ParsedStructureItemDesc::Pstr_raw(raw) => Err(TypeModError::CoreError(
            crate::types::typecore::uninterpreted_raw_error(raw.name_loc, "raw"),
        )),
    }
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
    rec_flag: RecFlag,
    decls: &[crate::parser::ast::TypeDeclaration],
) -> TypeModResult<Vec<TypedTypeDeclaration>> {
    transl_sig_type_declarations_with_ids(tctx, env, arena, rec_flag, decls, None)
}

fn transl_sig_type_declarations_with_ids<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    rec_flag: RecFlag,
    decls: &[crate::parser::ast::TypeDeclaration],
    predeclared_type_ids: Option<&[Ident]>,
) -> TypeModResult<Vec<TypedTypeDeclaration>> {
    transl_sig_type_declarations_with_ids_and_originals(
        tctx,
        env,
        arena,
        rec_flag,
        decls,
        predeclared_type_ids,
        None,
    )
}

fn transl_sig_type_declarations_with_ids_and_originals<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    rec_flag: RecFlag,
    decls: &[crate::parser::ast::TypeDeclaration],
    predeclared_type_ids: Option<&[Ident]>,
    with_constraint_original_decls: Option<&[crate::types::decl::TypeDeclaration]>,
) -> TypeModResult<Vec<TypedTypeDeclaration>> {
    let ctx = tctx.type_ctx;
    let mut typed_tree_decls = Vec::new();
    let mut typed_tree_decl_origins: Vec<crate::parser::ast::TypeDeclarationOrigin> = Vec::new();
    let mut internal_decls_for_generalize: Vec<crate::types::TypeDeclaration> = Vec::new();
    // OCaml typedecl.ml:1447-1484 prepends synthetic `t#row`
    // declarations for fixed private rows before the user-written
    // declarations. Signature declarations go through the same
    // Typedecl.transl_type_decl path as structures.
    // OCaml typedecl.ml:1456 expands variant spreads for the whole group
    // before translating any declaration.
    let mut pre_spread_sources = Vec::with_capacity(decls.len());
    for decl in decls {
        pre_spread_sources.push(match &decl.ptype_kind {
            crate::parser::ast::TypeKind::Ptype_variant(cstrs) => Some(
                resolve_variant_spread_sources(tctx, env, arena, decl, cstrs)?,
            ),
            _ => None,
        });
    }
    let fixed_row_type_ids = collect_fixed_row_type_ids(ctx, arena, decls);
    let has_fixed_rows = !fixed_row_type_ids.is_empty();
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
    let mut temp_env = env.clone();
    let type_entry_capacity = decls.len() + fixed_row_type_ids.len();
    let mut type_entry_ids: Vec<Ident> = Vec::with_capacity(type_entry_capacity);
    let mut type_entry_parser_indices: Vec<usize> = Vec::with_capacity(type_entry_capacity);
    let mut type_entry_is_synthetic_row: Vec<bool> = Vec::with_capacity(type_entry_capacity);
    for decl in decls {
        check_nonrecursive_gadt_enter_type(rec_flag, decl)?;
    }
    // Match OCaml Typedecl.transl_type_decl flow for signatures:
    // `init_def (Ident.current_time ())` once the identifiers exist
    // (typedecl.ml:1467-1475), translate inside begin_def/end_def, then
    // generalize declarations.
    ctx.init_def(ctx.current_stamp());
    ctx.begin_def();
    // typedecl.ml:1476 `enter_type` (typedecl.ml:73-108), after `begin_def`:
    // fresh generic parameters, and a fresh variable as manifest when the
    // declaration has one.
    for row_id in &fixed_row_type_ids {
        let placeholder_decl =
            fixed_row_placeholder_decl(ctx, arena, &decls[row_id.decl_idx], &row_id.id);
        temp_env.add_type(row_id.id, placeholder_decl);
    }
    if matches!(rec_flag, RecFlag::Recursive) {
        for (type_id, decl) in declared_type_ids.iter().zip(decls.iter()) {
            let arity = decl.ptype_params.len();
            let placeholder_decl = crate::types::TypeDeclaration {
                type_params: (0..arity).map(|_| ctx.new_generic_var(None)).collect(),
                type_arity: arity as i32,
                type_kind: crate::types::TypeKind::TypeAbstract,
                type_private: match decl.ptype_private {
                    crate::parser::ast::PrivateFlag::Public => crate::types::PrivateFlag::Public,
                    crate::parser::ast::PrivateFlag::Private => crate::types::PrivateFlag::Private,
                },
                type_manifest: decl.ptype_manifest.map(|_| ctx.new_var(None)),
                type_variance: (0..arity).map(|_| TypesVariance::full()).collect(),
                type_newtype_level: None,
                type_loc: tctx.intern_ast_loc(arena, decl.ptype_loc),
                type_attributes: parser_attrs_to_decl_attrs(
                    arena,
                    tctx.type_ctx,
                    &decl.ptype_attributes,
                ),
                type_immediate: false,
                type_representation: crate::types::TypeRepresentation::Boxed,
                type_shape: crate::types::ValueShape::Unstated,
                type_inlined_types: vec![],
                type_path: Some(Path::pident(*type_id)),
            };
            temp_env.add_type(*type_id, placeholder_decl);
        }
    }

    // typedecl.ml:1476 `enter_type` adds the placeholders with
    // `Env.add_type ~check:true` (typedecl.ml:108), registering their usage
    // checks before translation: fixed rows first, then a recursive group.
    for row_id in &fixed_row_type_ids {
        let row_loc = decls[row_id.decl_idx].ptype_loc;
        tctx.check_type_usage(&row_id.name, arena.to_location(row_loc), row_loc);
    }
    if matches!(rec_flag, RecFlag::Recursive) {
        for decl in decls {
            let name = arena.get_string(decl.ptype_name.txt);
            tctx.check_type_usage(name, arena.to_location(decl.ptype_loc), decl.ptype_loc);
        }
    }
    let loop_result: TypeModResult<()> = (|| {
        for row_id in &fixed_row_type_ids {
            let typed_row_decl = translate_fixed_row_type_declaration(
                tctx,
                arena,
                row_id.id,
                row_id.name.clone(),
                &decls[row_id.decl_idx],
                Some(Path::pident(row_id.id)),
            )?;
            let row_internal_decl = typed_row_decl.typ_type.clone();
            type_entry_ids.push(row_id.id);
            type_entry_parser_indices.push(row_id.decl_idx);
            type_entry_is_synthetic_row.push(true);
            internal_decls_for_generalize.push(row_internal_decl);
            typed_tree_decls.push(typed_row_decl);
            typed_tree_decl_origins.push(decls[row_id.decl_idx].ptype_origin);
        }

        for (decl_idx, decl) in decls.iter().enumerate() {
            // typedecl.ml:1500-1503: `Builtin_attributes.warning_scope
            // ptype_attributes` around each declaration.
            tctx.drain_open_slot_uses();
            let decl_warning_config = tctx.warning_config.clone();
            for attr in decl.ptype_attributes.iter().rev() {
                if let Err(error) =
                    apply_warning_attribute_with_ppwarning(tctx, arena, attr, true)
                {
                    tctx.warning_config = decl_warning_config;
                    return Err(error.into());
                }
            }
            let type_name = decl.ptype_name.txt;
            let type_name_str = arena.get_string(type_name);
            let type_id = declared_type_ids[decl_idx];
            let type_path = Path::pident(type_id);

            check_declaration_runtime_annotation(arena, decl)?;

            // OCaml: reset_type_variables() before each type declaration
            tctx.reset_type_variables();

            // Convert type parameters
            let mut typ_params: Vec<(TypedCoreType, TypesVariance)> = Vec::new();
            let mut internal_type_params: Vec<TypeExprRef> = Vec::new();
            for (core_type_idx, parser_var) in &decl.ptype_params {
                let core_type = arena.get_core_type(*core_type_idx);
                let (typed_core_type, type_ref) = match &core_type.ptyp_desc {
                    crate::parser::ast::CoreTypeDesc::Ptyp_any => {
                        let type_ref = ctx.new_var(Some(crate::name::Name::new("_")));
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
                        let name = arena.get_string(*name);
                        check_type_variable_name(core_type.ptyp_loc, name)?;
                        if tctx.type_variables.contains_key(name) {
                            return Err(TypeModError::RepeatedParameter {
                                loc: core_type.ptyp_loc,
                            });
                        }
                        let type_ref = ctx.new_var(Some(crate::name::Name::new(name)));
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
                // Insert type params into type_variables so record field/manifest
                // translation can find them and share the same Tvar node.
                // Matches OCaml's transl_type_param which inserts into type_variables.
                if let crate::parser::ast::CoreTypeDesc::Ptyp_var(name) = &core_type.ptyp_desc {
                    tctx.type_variables
                        .insert(arena.get_string(*name).to_string(), type_ref);
                }
                let types_var = match parser_var {
                    ParserVariance::Covariant => TypesVariance::covariant(),
                    ParserVariance::Contravariant => TypesVariance::contravariant(),
                    ParserVariance::Invariant => TypesVariance::null(),
                };
                typ_params.push((typed_core_type, types_var));
            }

            if let Some(original_decl) =
                with_constraint_original_decls.and_then(|decls| decls.get(decl_idx))
            {
                unify_with_constraint_original_params(
                    tctx,
                    decl.ptype_loc,
                    &internal_type_params,
                    original_decl,
                )?;
            }

            // Convert type constraints
            let mut typ_cstrs: Vec<(TypedCoreType, TypedCoreType, LocIdx)> = Vec::new();
            for (ct1, ct2, cstr_loc) in &decl.ptype_cstrs {
                let (typed_ct1, _) = transl_type(tctx, &temp_env, arena.get_core_type(*ct1))?;
                let (typed_ct2, _) = transl_type(tctx, &temp_env, arena.get_core_type(*ct2))?;
                typ_cstrs.push((typed_ct1, typed_ct2, *cstr_loc));
            }

            // OCaml typedecl.ml warns after translating type constraints
            // when those constraints are attached to a GADT declaration.
            check_type_declaration_constraint_on_gadt(tctx, decl);

            check_unboxed_type_attributes(arena, decl)?;
            let decl_has_unboxed_attr = parser_attrs_have_unboxed(arena, &decl.ptype_attributes);

            // Preserve signature type kind like OCaml transl_signature -> Typedecl.transl_type_decl.
            let type_variant_layout = matches!(
                &decl.ptype_kind,
                crate::parser::ast::TypeKind::Ptype_variant(_)
            )
            .then(|| ctx.pending_variant_layout());
            let (internal_type_kind, typed_tree_kind) = match &decl.ptype_kind {
                crate::parser::ast::TypeKind::Ptype_abstract => (
                    crate::types::TypeKind::TypeAbstract,
                    TypedTypeKind::Ttype_abstract,
                ),
                crate::parser::ast::TypeKind::Ptype_open => {
                    (crate::types::TypeKind::TypeOpen, TypedTypeKind::Ttype_open)
                }
                crate::parser::ast::TypeKind::Ptype_record(labels) => {
                    check_duplicate_label_declarations(
                        arena,
                        labels,
                        Some(arena.get_string(decl.ptype_name.txt)),
                    )?;
                    let mut internal_labels = Vec::with_capacity(labels.len());
                    let mut typed_tree_labels = Vec::with_capacity(labels.len());

                    for label in labels {
                        check_extra_as_attribute(arena, label)?;
                        let lbl_name = arena.get_string(label.pld_name.txt);
                        let (typed_label_ty, lbl_type) =
                            transl_label_type(tctx, &temp_env, arena, label, true)?;
                        let (poly_typed_core_type, poly_lbl_type) = force_poly_typed_core_type(
                            &mut tctx.typed,
                            tctx.type_ctx,
                            typed_label_ty,
                            lbl_type,
                        );
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
                        let label_id = ctx.create_ast_ident(arena, label.pld_name.txt);
                        internal_labels.push(crate::types::LabelDeclaration {
                            ld_id: label_id,
                            ld_runtime_name: crate::types::record_runtime::parsetree_runtime_name(
                                label, arena,
                            ),
                            ld_mutable: mutable_flag,
                            ld_optional: label.pld_optional,
                            ld_type: internal_lbl_type,
                            ld_loc: tctx.intern_ast_loc(arena, label.pld_loc),
                            ld_attributes: parser_attrs_to_decl_attrs(
                                arena,
                                tctx.type_ctx,
                                &label.pld_attributes,
                            ),
                        });

                        typed_tree_labels.push(TypedLabelDeclaration {
                            ld_id: label_id,
                            ld_name: Located {
                                txt: lbl_name.to_string(),
                                loc: label.pld_name.loc,
                            },
                            ld_runtime_name: crate::types::record_runtime::parsetree_runtime_name(
                                label, arena,
                            ),
                            ld_mutable: label.pld_mutable,
                            ld_optional: label.pld_optional,
                            ld_type: tctx.typed.push_core_type(poly_typed_core_type),
                            ld_loc: label.pld_loc,
                            ld_attributes: label.pld_attributes.clone(),
                            ld_types_attributes: None,
                        });
                    }
                    // OCaml compiler/ml/typedecl.ml:631-646 runs
                    // Record_type_spread.expand_labels_with_type_spreads for
                    // both structures and signatures before publishing the
                    // Type_record. Keep `.resi` record spreads expanded too,
                    // so downstream record literals see the same lbl_all order
                    // and runtime names as modules loaded from OCaml `.cmi`.
                    let has_spread = internal_labels
                        .iter()
                        .any(|label| label.ld_id.name() == "...");
                    if has_spread {
                        let mut expanded_internal_labels = Vec::new();
                        let mut expanded_typed_labels = Vec::new();
                        let mut all_spreads_resolved = true;

                        for (internal_label, typed_label) in
                            internal_labels.iter().zip(typed_tree_labels.iter())
                        {
                            if internal_label.ld_id.name() != "..." {
                                expanded_internal_labels.push(internal_label.clone());
                                expanded_typed_labels.push(typed_label.clone());
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
                                    expanded_typed_labels.push(make_typed_spread_label(
                                        &mut tctx.typed,
                                        arena,
                                        ctx,
                                        typed_label,
                                        &resolved_field,
                                    ));
                                    expanded_internal_labels.push(resolved_field);
                                }
                            } else {
                                all_spreads_resolved = false;
                                expanded_internal_labels.push(internal_label.clone());
                                expanded_typed_labels.push(typed_label.clone());
                            }
                        }

                        if all_spreads_resolved {
                            internal_labels = expanded_internal_labels;
                            typed_tree_labels = expanded_typed_labels;
                        } else {
                            reject_object_spread_with_record_field(arena, labels)?;
                        }
                    }

                    check_duplicate_typed_label_declarations(
                        decl.ptype_loc,
                        &typed_tree_labels,
                        Some(arena.get_string(decl.ptype_name.txt)),
                    )?;
                    // typedecl.ml:643-647 (shared by structures and
                    // signatures): `if unbox then Record_unboxed false`.
                    let repres = if decl_has_unboxed_attr && internal_labels.len() == 1 {
                        crate::types::RecordRepresentation::RecordUnboxed(false)
                    } else {
                        crate::types::record_runtime::boxed_representation(&internal_labels)
                    };
                    (
                        crate::types::TypeKind::TypeRecord(
                            crate::types::decl::SharedVec::from(internal_labels),
                            repres,
                        ),
                        TypedTypeKind::Ttype_record(typed_tree_labels),
                    )
                }
                crate::parser::ast::TypeKind::Ptype_variant(cstrs) => {
                    // OCaml typedecl.ml:1456 expands variant spreads for
                    // signatures too, before transl_declaration checks for
                    // duplicate constructors (typedecl.ml:461-467).
                    let spread_sources = pre_spread_sources[decl_idx]
                        .take()
                        .expect("variant spread sources resolved before the group");
                    check_duplicate_constructor_declarations(arena, decl.ptype_loc, cstrs)?;
                    check_unboxed_on_constructors(arena, cstrs)?;
                    let mut internal_cstrs = Vec::with_capacity(cstrs.len());
                    let mut typed_tree_cstrs = Vec::with_capacity(cstrs.len());
                    // typedecl.ml `copy_tag_attr_from_decl`: only the @tag
                    // attributes of the type decl are copied to constructors.
                    let tag_attrs: Vec<_> = decl
                        .ptype_attributes
                        .iter()
                        .filter(|attr| arena.get_string(attr.0.txt) == "tag")
                        .cloned()
                        .collect();

                    for (cstr_idx, cstr) in cstrs.iter().enumerate() {
                        if let Some((source_cstrs, is_pdot_source)) = &spread_sources[cstr_idx] {
                            // typedecl.ml:477-500: the `...t` constructor gets an
                            // ident and its argument is translated, then it is
                            // replaced by the source's constructors.
                            ctx.create_ident(arena.get_string(cstr.pcd_name.txt));
                            if let crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) =
                                &cstr.pcd_args
                            {
                                for core_type in types {
                                    transl_type(tctx, &temp_env, arena.get_core_type(*core_type))?;
                                }
                            }
                            for source_cstr in source_cstrs {
                                let spread = build_spread_constructor(
                                    &mut tctx.typed,
                                    ctx,
                                    arena,
                                    cstr,
                                    source_cstr,
                                    *is_pdot_source,
                                    &tag_attrs,
                                );
                                internal_cstrs.push(spread.internal);
                                typed_tree_cstrs.push(spread.typed);
                            }
                            continue;
                        }
                        let cstr_name = arena.get_string(cstr.pcd_name.txt);
                        // OCaml compiler/ml/typedecl.ml:481-484 creates
                        // the constructor id before make_constructor
                        // translates inline record labels.
                        let cstr_id = ctx.create_ident(cstr_name);
                        // typedecl.ml `make_cstr`.
                        let runtime_tag =
                            process_constructor_tag(arena, cstr).map_err(|(loc, error)| {
                                ast_untagged_variant_error(arena.to_location(loc), error)
                            })?;
                        // OCaml `make_constructor` (compiler/ml/typedecl.ml:337-356): narrow,
                        // reset the type variables for a generalized constructor, then widen.
                        let gadt_scope = cstr.pcd_res.is_some().then(|| {
                            let global_level = ctx.increase_global_level();
                            let type_variables = std::mem::take(&mut tctx.type_variables);
                            tctx.reset_type_variables();
                            (global_level, type_variables)
                        });
                        let (internal_args, typed_args) = match &cstr.pcd_args {
                            crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
                                let mut internal_tuple_args = Vec::with_capacity(args.len());
                                let mut typed_tuple_args = Vec::with_capacity(args.len());
                                for arg in args {
                                    let (typed_arg, arg_ref) = transl_decl_arg_type(
                                        tctx,
                                        &temp_env,
                                        arena.get_core_type(*arg),
                                        cstr.pcd_res.is_none(),
                                    )?;
                                    internal_tuple_args.push(arg_ref);
                                    typed_tuple_args.push(typed_arg);
                                }
                                (
                                    crate::types::ConstructorArguments::CstrTuple(
                                        internal_tuple_args,
                                    ),
                                    TypedConstructorArguments::Cstr_tuple(
                                        tctx.typed.push_core_types(typed_tuple_args),
                                    ),
                                )
                            }
                            crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                                check_duplicate_label_declarations(arena, labels, None)?;
                                let mut internal_record_labels = Vec::with_capacity(labels.len());
                                let mut typed_record_labels = Vec::with_capacity(labels.len());
                                for label in labels {
                                    check_extra_as_attribute(arena, label)?;
                                    let lbl_name = arena.get_string(label.pld_name.txt);
                                    let (typed_label_ty, lbl_type) = transl_label_type(
                                        tctx,
                                        &temp_env,
                                        arena,
                                        label,
                                        cstr.pcd_res.is_none(),
                                    )?;
                                    let (poly_typed_core_type, poly_lbl_type) =
                                        force_poly_typed_core_type(
                                            &mut tctx.typed,
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
                                    let label_id = ctx.create_ast_ident(arena, label.pld_name.txt);
                                    internal_record_labels.push(crate::types::LabelDeclaration {
                                        ld_id: label_id,
                                        ld_runtime_name:
                                            crate::types::record_runtime::parsetree_runtime_name(
                                                label, arena,
                                            ),
                                        ld_mutable: mutable_flag,
                                        ld_optional: label.pld_optional,
                                        ld_type: internal_lbl_type,
                                        ld_loc: tctx.intern_ast_loc(arena, label.pld_loc),
                                        ld_attributes: parser_attrs_to_decl_attrs(
                                            arena,
                                            tctx.type_ctx,
                                            &label.pld_attributes,
                                        ),
                                    });
                                    typed_record_labels.push(TypedLabelDeclaration {
                                        ld_id: label_id,
                                        ld_name: Located {
                                            txt: lbl_name.to_string(),
                                            loc: label.pld_name.loc,
                                        },
                                        ld_runtime_name:
                                            crate::types::record_runtime::parsetree_runtime_name(
                                                label, arena,
                                            ),
                                        ld_mutable: label.pld_mutable,
                                        ld_optional: label.pld_optional,
                                        ld_type: tctx.typed.push_core_type(poly_typed_core_type),
                                        ld_loc: label.pld_loc,
                                        ld_attributes: label.pld_attributes.clone(),
                                        ld_types_attributes: None,
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
                                    transl_type(tctx, &temp_env, arena.get_core_type(*res_type))?;
                                // OCaml `make_constructor` (compiler/ml/typedecl.ml:345-353).
                                let is_instance = matches!(
                                    &*ctx.get_desc(ctx.repr(internal)),
                                    TypeDesc::Tconstr { path, .. } if path.same(&type_path)
                                );
                                if !is_instance {
                                    return Err(TypeModError::ConstraintFailed {
                                        loc: typed.ctyp_loc,
                                        actual: internal,
                                        expected: ctx.new_constr(
                                            type_path,
                                            internal_type_params.clone(),
                                        ),
                                    });
                                }
                                (Some(typed), Some(internal))
                            }
                            None => (None, None),
                        };
                        if let Some((global_level, type_variables)) = gadt_scope {
                            ctx.restore_global_level(global_level);
                            tctx.type_variables = type_variables;
                        }

                        internal_cstrs.push(crate::types::ConstructorDeclaration {
                            cd_id: cstr_id,
                            cd_runtime_tag: runtime_tag.clone(),
                            cd_args: internal_args,
                            cd_res: internal_res,
                            cd_loc: tctx.intern_ast_loc(arena, cstr.pcd_loc),
                            cd_attributes: {
                                let mut attrs = tag_attrs.clone();
                                attrs.extend(cstr.pcd_attributes.iter().cloned());
                                parser_attrs_to_decl_attrs(
                                    arena,
                                    tctx.type_ctx,
                                    &Attributes::from_vec(attrs),
                                )
                            },
                        });
                        typed_tree_cstrs.push(TypedConstructorDeclaration {
                            cd_id: cstr_id,
                            cd_name: Located {
                                txt: cstr_name.to_string(),
                                loc: cstr.pcd_name.loc,
                            },
                            cd_runtime_tag: runtime_tag,
                            cd_args: typed_args,
                            cd_res: typed_res.map(|ct| tctx.typed.push_core_type(ct)),
                            cd_loc: cstr.pcd_loc,
                            cd_attributes: {
                                let mut attrs = tag_attrs.clone();
                                attrs.extend(cstr.pcd_attributes.iter().cloned());
                                Attributes::from_vec(attrs)
                            },
                        });
                    }

                    (
                        crate::types::TypeKind::TypeVariant(
                            crate::types::decl::SharedVec::from(internal_cstrs),
                            type_variant_layout.expect("variant declaration layout"),
                        ),
                        TypedTypeKind::Ttype_variant(typed_tree_cstrs),
                    )
                }
            };

            // OCaml compiler/ml/typedecl.ml:449-607 translates the kind
            // before typedecl.ml:692-698 translates the manifest. The same
            // temp_env from typedecl.ml:1484 and :1511-1513 is used here so
            // recursive manifests see forward type identifiers.
            let (typ_manifest, manifest_type_ref) = match &decl.ptype_manifest {
                Some(manifest) => {
                    let manifest_ct = arena.get_core_type(*manifest);
                    let is_fixed_type = type_decl_is_fixed_type(arena, decl, manifest_ct);
                    let (typed_manifest, manifest_ref) =
                        if type_decl_manifest_uses_fixed_type_variables(arena, decl, manifest_ct) {
                            transl_type_fixed(tctx, &temp_env, manifest_ct)?
                        } else {
                            transl_type(tctx, &temp_env, manifest_ct)?
                        };
                    if is_fixed_type {
                        let row_id = fixed_row_type_id_for_decl(&fixed_row_type_ids, decl_idx)
                            .expect("fixed private row type must have a synthetic row id");
                        let row_path = Path::pident(row_id.id);
                        // typedecl.ml:720-723: `Env.lookup_type` marks the row used.
                        crate::types::typecore::mark_type_used(
                            ctx,
                            &temp_env,
                            &row_id.name,
                            arena.to_location(decl.ptype_loc),
                        );
                        set_fixed_row(
                            ctx,
                            &temp_env,
                            decl.ptype_loc,
                            &row_path,
                            &internal_type_params,
                            manifest_ref,
                        )?;
                    }
                    (Some(typed_manifest), Some(manifest_ref))
                }
                None => (None, None),
            };
            // OCaml Typedecl.transl_declaration unifies declaration
            // constraints before end_def/generalization, so constrained
            // parameters are linked in the stored declaration.
            unify_type_declaration_constraints(tctx, &typ_cstrs)?;
            // OCaml typedecl.ml:724-730: `Ctype.cyclic_abbrev env id ty`.
            if let Some(manifest) = manifest_type_ref
                && crate::types::ctype::cyclic_abbrev(ctx, &temp_env, &type_id, manifest)
            {
                return Err(TypeModError::RecursiveAbbrev {
                    loc: decl.ptype_loc,
                    name: arena.get_string(decl.ptype_name.txt).to_string(),
                });
            }

            let typ_private = decl.ptype_private;

            let type_attributes =
                parser_attrs_to_decl_attrs(arena, tctx.type_ctx, &decl.ptype_attributes);
            let type_representation =
                unboxed_type_representation(arena, decl, decl_has_unboxed_attr);
            // OCaml computes signature declaration immediacy after translating
            // the declaration body (`compiler/ml/typedecl.ml:2005`), using the
            // same `compute_immediacy` helper as implementation declarations.
            let type_immediate = compute_type_immediacy(
                ctx,
                &temp_env,
                &internal_type_kind,
                manifest_type_ref,
                &type_attributes,
                type_representation,
            );
            if decl_attrs_mark_immediate(&type_attributes) && !type_immediate {
                return Err(TypeModError::BadImmediateAttribute {
                    loc: decl.ptype_loc,
                });
            }

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
                type_loc: tctx.intern_ast_loc(arena, decl.ptype_loc),
                type_attributes,
                type_immediate,
                type_representation,
                type_shape: crate::types::ValueShape::Unstated,
                type_inlined_types: vec![],
                type_path: Some(type_path),
            };
            internal_decls_for_generalize.push(internal_decl.clone());

            typed_tree_decls.push(TypedTypeDeclaration {
                typ_id: type_id,
                typ_name: crate::parse_arena::Located {
                    txt: type_name_str.to_string(),
                    loc: decl.ptype_name.loc,
                },
                typ_params: typ_params
                    .into_iter()
                    .map(|(ct, v)| (tctx.typed.push_core_type(ct), v))
                    .collect(),
                typ_type: internal_decl,
                typ_cstrs: typ_cstrs
                    .into_iter()
                    .map(|(c1, c2, l)| {
                        (
                            tctx.typed.push_core_type(c1),
                            tctx.typed.push_core_type(c2),
                            l,
                        )
                    })
                    .collect(),
                typ_kind: typed_tree_kind,
                typ_private,
                typ_manifest: typ_manifest.map(|ct| tctx.typed.push_core_type(ct)),
                typ_loc: decl.ptype_loc,
                typ_attributes: decl.ptype_attributes.clone(),
            });
            typed_tree_decl_origins.push(decl.ptype_origin);
            if has_fixed_rows {
                type_entry_ids.push(type_id);
                type_entry_parser_indices.push(decl_idx);
                type_entry_is_synthetic_row.push(false);
            }
            tctx.drain_open_slot_uses();
            tctx.warning_config = decl_warning_config;
        }
        Ok(())
    })();
    if loop_result.is_ok() {
        // OCaml Typedecl.check_duplicates runs after translating the declaration
        // group and before final env construction/end_def.
        check_type_declaration_duplicate_definitions(tctx, arena, decls);
        // typedecl.ml:1509-1526: every declaration of the group records
        // the group's inline record definitions for printing.
        let inline_types = group_inline_record_types(&typed_tree_decl_origins, &typed_tree_decls);
        if !inline_types.is_empty() {
            for typed_decl in typed_tree_decls.iter_mut() {
                typed_decl.typ_type.type_inlined_types = inline_types.clone();
            }
            for decl in internal_decls_for_generalize.iter_mut() {
                decl.type_inlined_types = inline_types.clone();
            }
        }
    }
    // typedecl.ml:1578-1580 `Variant_layout.resolve_shapes ~env decls`.
    let loop_result = loop_result.and_then(|()| {
        let ids: Vec<Ident> = if has_fixed_rows {
            type_entry_ids.clone()
        } else {
            declared_type_ids.clone()
        };
        let shapes =
            resolve_declaration_group_shapes(ctx, env, &ids, &internal_decls_for_generalize)?;
        for (decl, id) in internal_decls_for_generalize.iter_mut().zip(&ids) {
            if let Some(shape) = shape_for(&shapes, id) {
                decl.type_shape = shape;
            }
        }
        for typed_decl in typed_tree_decls.iter_mut() {
            if let Some(shape) = shape_for(&shapes, &typed_decl.typ_id) {
                typed_decl.typ_type.type_shape = shape;
            }
        }
        Ok(())
    });
    // typedecl.ml:1540-1546 `update_type` (typedecl.ml:110-124) in the final
    // env (typedecl.ml:1534-1538): unify each recursive stub's manifest
    // variable with the declared type.
    let loop_result = loop_result.and_then(|()| {
        if !matches!(rec_flag, RecFlag::Recursive) {
            return Ok(());
        }
        let mut newenv = env.clone();
        let entry_ids = if has_fixed_rows {
            &type_entry_ids
        } else {
            &declared_type_ids
        };
        for (type_id, decl) in entry_ids.iter().zip(internal_decls_for_generalize.iter()) {
            newenv.store_type(tctx.type_ctx, *type_id, decl.clone());
        }
        for (decl, type_id) in decls.iter().zip(declared_type_ids.iter()) {
            let Ok(stub) = temp_env.find_type_by_ident(type_id) else {
                continue;
            };
            let Some(manifest) = stub.type_manifest else {
                continue;
            };
            let params = stub.type_params.iter().map(|_| ctx.new_var(None)).collect();
            let constr = ctx.new_constr(Path::pident(*type_id), params);
            let mut unify_state = crate::types::UnifyState::new();
            unify_state.set_env(&newenv);
            if let Err(err) = crate::types::unify(ctx, &mut unify_state, constr, manifest) {
                let trace = match err {
                    crate::types::ctype::TypeError::Unify(trace) if !trace.is_empty() => trace,
                    _ => vec![(constr, manifest)],
                };
                return Err(TypeModError::TypeDeclTypeClash {
                    loc: decl.ptype_loc,
                    trace,
                });
            }
        }
        Ok(())
    });
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
    if has_fixed_rows {
        for (type_id, decl) in type_entry_ids
            .iter()
            .zip(internal_decls_for_generalize.iter())
        {
            variance_env.store_type(tctx.type_ctx, *type_id, decl.clone());
        }
    } else {
        for (type_id, decl) in declared_type_ids
            .iter()
            .zip(internal_decls_for_generalize.iter())
        {
            variance_env.store_type(tctx.type_ctx, *type_id, decl.clone());
        }
    }

    let original_internal_decls_for_checks: Vec<_> = if has_fixed_rows {
        internal_decls_for_generalize
            .iter()
            .zip(type_entry_is_synthetic_row.iter())
            .filter_map(|(decl, is_row)| (!*is_row).then_some(decl.clone()))
            .collect()
    } else {
        internal_decls_for_generalize.clone()
    };

    check_type_declaration_abbrev_cycles(
        ctx,
        &variance_env,
        &declared_type_ids,
        decls,
        &original_internal_decls_for_checks,
    )?;

    // Same unbound type variable check as the structure path: signature type
    // declarations also go through Typedecl.transl_type_decl, whose labels and
    // constructor arguments are translated with `closed = true`
    // (typedecl.ml:225, 264-269, 335).
    for typed_decl in &typed_tree_decls {
        if let Some((name, loc, detail, var)) =
            find_unbound_type_var_in_typed_type_decl(&tctx.typed, ctx, typed_decl)
        {
            return Err(TypeModError::UnboundTypeVar {
                loc,
                name,
                detail,
                var,
            });
        }
    }

    // OCaml transl_signature routes Psig_type through
    // Typedecl.transl_type_decl, whose typedecl.ml:1588-1592 runs
    // untagged checks before check_constraints and compute_properties_fixpoint.
    for decl in &internal_decls_for_generalize {
        check_variant_declaration_well_formed(ctx, &variance_env, decl)?;
    }
    // typedecl.ml:1650-1653 `check_manifest_annotation` over the group.
    for (sdecl, decl) in decls.iter().zip(original_internal_decls_for_checks.iter()) {
        crate::types::variant_layout::check_manifest_annotation(
            ctx,
            arena.to_location(sdecl.ptype_loc),
            &variance_env,
            decl,
        )?;
    }
    for (sdecl, decl) in decls.iter().zip(original_internal_decls_for_checks.iter()) {
        check_constraints(
            ctx,
            arena,
            &variance_env,
            &mut tctx.persistent_env,
            false,
            sdecl,
            decl,
        )?;
    }

    if has_fixed_rows {
        let required_variances: Vec<Vec<(bool, bool, bool)>> = type_entry_parser_indices
            .iter()
            .map(|parser_idx| {
                decls[*parser_idx]
                    .ptype_params
                    .iter()
                    .map(|(_, variance)| parser_variance_requirement(*variance))
                    .collect()
            })
            .collect();
        let resolved_variances = compute_type_variance_fixpoint(
            ctx,
            &variance_env,
            &type_entry_ids,
            &required_variances,
        );
        if resolved_variances.len() == type_entry_ids.len() {
            for (idx, variance_row) in resolved_variances.iter().enumerate() {
                if !type_entry_is_synthetic_row[idx]
                    && let Some(typed_decl) = typed_tree_decls.get(idx)
                {
                    check_type_decl_variance_requirements(
                        &tctx.typed,
                        ctx,
                        &variance_env,
                        &decls[type_entry_parser_indices[idx]],
                        typed_decl,
                        variance_row,
                    )?;
                }
                if let Some(typed_decl) = typed_tree_decls.get_mut(idx) {
                    typed_decl.typ_type.type_variance = variance_row.clone();
                }
                if let Some(internal_decl) = internal_decls_for_generalize.get_mut(idx) {
                    internal_decl.type_variance = variance_row.clone();
                }
            }
        }

        for (entry_idx, internal_decl) in internal_decls_for_generalize.iter().enumerate() {
            if type_entry_is_synthetic_row[entry_idx] {
                continue;
            }
            let idx = type_entry_parser_indices[entry_idx];
            let mut coherence_warnings = Vec::new();
            let coherence = check_type_declaration_coherence(
                ctx,
                &variance_env,
                decls[idx].ptype_loc,
                &declared_type_ids[idx],
                internal_decl,
                &mut coherence_warnings,
            );
            report_inclusion_warnings(tctx, decls[idx].ptype_loc, coherence_warnings);
            coherence?;
        }
    } else {
        let required_variances: Vec<Vec<(bool, bool, bool)>> = decls
            .iter()
            .map(|decl| {
                decl.ptype_params
                    .iter()
                    .map(|(_, variance)| parser_variance_requirement(*variance))
                    .collect()
            })
            .collect();
        let resolved_variances = compute_type_variance_fixpoint(
            ctx,
            &variance_env,
            &declared_type_ids,
            &required_variances,
        );
        if resolved_variances.len() == declared_type_ids.len() {
            for (idx, variance_row) in resolved_variances.iter().enumerate() {
                if let Some(typed_decl) = typed_tree_decls.get(idx) {
                    check_type_decl_variance_requirements(
                        &tctx.typed,
                        ctx,
                        &variance_env,
                        &decls[idx],
                        typed_decl,
                        variance_row,
                    )?;
                }
                if let Some(typed_decl) = typed_tree_decls.get_mut(idx) {
                    typed_decl.typ_type.type_variance = variance_row.clone();
                }
                if let Some(internal_decl) = internal_decls_for_generalize.get_mut(idx) {
                    internal_decl.type_variance = variance_row.clone();
                }
            }
        }

        for (idx, internal_decl) in internal_decls_for_generalize.iter().enumerate() {
            let mut coherence_warnings = Vec::new();
            let coherence = check_type_declaration_coherence(
                ctx,
                &variance_env,
                decls[idx].ptype_loc,
                &declared_type_ids[idx],
                internal_decl,
                &mut coherence_warnings,
            );
            report_inclusion_warnings(tctx, decls[idx].ptype_loc, coherence_warnings);
            coherence?;
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
        let core_error = TypeCoreError::MultiplyBoundVariable {
            loc: LocIdx::none(),
            name: "x".to_string(),
        };
        let mod_error: TypeModError = core_error.into();
        match mod_error {
            TypeModError::CoreError(_) => {}
            _ => panic!("Expected CoreError"),
        }
    }

    fn type_test_structure(source: &str) -> (Structure, TypedArena) {
        crate::ident::Ident::set_current_time(999);
        let id_gen = IdGenerator::with_start_stamp(999);
        let _ = id_gen.next_stamp();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut parser = Parser::new("test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "parse failed");
        let arena = parser.arena();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (typed, _) = type_structure(&mut tctx, &env, arena, &structure).expect("typecheck");
        (typed, tctx.take_typed_arena())
    }

    /// Type-check `source` after turning the payload `"BAD"` of its first
    /// type declaration's attribute into the template `{js|Fo\xo|js}`, as a
    /// PPX may emit it (compiler/ml/ast_mapper_from0.ml
    /// `template_source_from0` keeps a `js` source unchecked). Returns the
    /// error and the location of the payload expression.
    fn type_with_ppx_invalid_template(source: &str) -> (TypeModError, Location) {
        crate::ident::Ident::set_current_time(999);
        let id_gen = IdGenerator::with_start_stamp(999);
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut parser = Parser::new("test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "parse failed");
        let mut arena = parser.into_arena();
        let crate::parser::ast::StructureItemDesc::Pstr_type(group) = &structure[0].pstr_desc
        else {
            panic!("expected a type declaration");
        };
        let (_, ParsedPayload::PStr(items)) = &group.1[0].ptype_attributes[0] else {
            panic!("expected a structure payload");
        };
        let crate::parser::ast::StructureItemDesc::Pstr_eval(eval) = &items[0].pstr_desc else {
            panic!("expected an expression payload");
        };
        let expr_idx = eval.0;
        let source_idx = arena.intern("Fo\\xo");
        let expr = arena.get_expr_mut(expr_idx);
        let loc = expr.pexp_loc;
        expr.pexp_desc = crate::parser::ast::ExpressionDesc::Pexp_template(Box::new(
            crate::parser::ast::PexpTemplate {
                source_segments: vec![crate::parser::ast::Loc {
                    txt: source_idx,
                    loc,
                }],
                values: vec![],
            },
        ));
        let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
        let env = initial_env(&type_ctx);
        let error = type_structure(&mut tctx, &env, &arena, &structure)
            .expect_err("an invalid escape is an error");
        (error, arena.to_location(loc))
    }

    /// Types `source` after turning every `"BAD"` string into the template
    /// `Fo\xo`, which has an invalid escape, as a PPX may; the result and
    /// the locations of the rewritten strings, in source order.
    fn type_with_bad_strings(source: &str) -> (TypeModResult<()>, Vec<Location>) {
        crate::ident::Ident::set_current_time(999);
        let id_gen = IdGenerator::with_start_stamp(999);
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut parser = Parser::new("test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "parse failed");
        let mut arena = parser.into_arena();
        // The `"BAD"` string expressions, found by walking the parsed tree
        // (attribute payloads included).
        struct BadStrings(Vec<crate::parse_arena::ExprIdx>);
        impl crate::binary_ast::ast_iter::AstIter for BadStrings {
            fn expr(&mut self, arena: &ParseArena, idx: crate::parse_arena::ExprIdx) {
                if let crate::parser::ast::ExpressionDesc::Pexp_constant(constant) =
                    &arena.get_expanded_expr(idx).pexp_desc
                    && let crate::parser::ast::Constant::String(value) = constant
                    && value.semantic(arena) == "BAD"
                {
                    self.0.push(idx);
                }
                crate::binary_ast::ast_iter::walk_expr(self, arena, idx);
            }
        }
        let mut found = BadStrings(Vec::new());
        crate::binary_ast::ast_iter::walk_structure(&mut found, &arena, &structure);
        let source_idx = arena.intern("Fo\\xo");
        let mut locs = Vec::new();
        for expr_idx in found.0 {
            let loc = arena.get_expanded_expr(expr_idx).pexp_loc;
            locs.push(loc);
            arena.get_expr_mut(expr_idx).pexp_desc =
                crate::parser::ast::ExpressionDesc::Pexp_template(Box::new(
                    crate::parser::ast::PexpTemplate {
                        source_segments: vec![crate::parser::ast::Loc {
                            txt: source_idx,
                            loc,
                        }],
                        values: vec![],
                    },
                ));
        }
        crate::types::typecore::prepare_typecheck_arena(&mut arena);
        let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
        let env = initial_env(&type_ctx);
        let result = type_structure(&mut tctx, &env, &arena, &structure).map(|_| ());
        let mut locs: Vec<Location> = locs.into_iter().map(|loc| arena.to_location(loc)).collect();
        locs.sort_by_key(|loc| loc.loc_start.cnum);
        (result, locs)
    }

    /// The type checker's readers raise where OCaml's raise
    /// (`Builtin_attributes.warning_attribute`, `check_deprecated_inclusion`,
    /// `Env.store_module`), at the template; a valid backquoted or braced
    /// payload reads as its string, and unknown attributes are not read.
    #[test]
    fn type_checker_payload_readers_raise_on_an_invalid_template() {
        let column = |loc: &Location| loc.loc_start.cnum - loc.loc_start.bol;
        for (source, raised) in [
            // typemod.ml:1430 `warning_scope` of a value binding.
            ("@warning(\"BAD\") let x = 1\n", 0),
            // typedecl.ml:589-591: a constructor's warning scope.
            ("type t = @warning(\"BAD\") A | B\n", 0),
            // Reverse order (builtin_attributes.ml:164): the last attribute
            // is read first.
            ("@warning(\"BAD\") @warning(\"BAD\") let x = 1\n", 1),
            // includecore.ml:45 through the constraint's inclusion: the
            // signature side is read first.
            (
                concat!(
                    "module M: { @deprecated(\"BAD\") let x: int } = ",
                    "{ @deprecated(\"BAD\") let x = 1 }\n",
                ),
                0,
            ),
            // env.ml:1649 when the module enters the environment.
            ("@deprecated(\"BAD\") module M = {}\n", 0),
        ] {
            let (result, locs) = type_with_bad_strings(source);
            let loc = match result {
                Err(TypeModError::CoreError(TypeCoreError::InvalidStringEscapeSequence { .. })) => {
                    None
                }
                Err(TypeModError::CoreError(TypeCoreError::InvalidStringEscapeAt { loc })) => {
                    Some(loc)
                }
                other => panic!("{source}: {other:?}"),
            };
            if let Some(loc) = loc {
                assert_eq!(column(&loc), column(&locs[raised]), "{source}");
            }
        }
        for source in [
            "@deprecated({reason: `ok`}) let x = 1\n@deprecated({\"ok\"}) let y = 1\n",
            "@warning(`-27`) let f = u => 1\n",
            "@whatever(\"BAD\") let x = 1\n",
            // The record form reads as no string where the inclusion reads it
            // (builtin_attributes.ml:21-24, 59-62).
            "@deprecated({reason: \"BAD\"}) let x = 1\n",
        ] {
            let (result, _) = type_with_bad_strings(source);
            assert!(result.is_ok(), "{source}: {result:?}");
        }
    }

    /// The OCaml reference reports `Invalid string escape sequence` at the
    /// payload when a PPX gives `@instanceOf`, `@typeOf` or `@tag` such a
    /// template (`Ast_payload.semantic_string_of_expression`,
    /// compiler/ml/ast_payload.ml:39-51), e.g. for `@instanceOf("BAD")` at
    /// 1:13-17.
    #[test]
    fn ppx_template_with_invalid_escape_is_reported_at_the_payload() {
        for source in [
            "@instanceOf(\"BAD\")\ntype a\n",
            "@typeOf(\"BAD\")\ntype a\n",
            "@tag(\"BAD\")\ntype t = A({x: int}) | B\n",
        ] {
            let (error, payload_loc) = type_with_ppx_invalid_template(source);
            match error {
                TypeModError::InvalidStringEscape { loc } => {
                    assert_eq!(loc, payload_loc, "{source}")
                }
                other => panic!("{source}: {other:?}"),
            }
        }
        let (_, loc) = type_with_ppx_invalid_template("@instanceOf(\"BAD\")\ntype a\n");
        let column = |pos: crate::location::Position| pos.cnum - pos.bol;
        assert_eq!(
            (loc.loc_start.line, column(loc.loc_start), column(loc.loc_end)),
            (1, 12, 17)
        );
    }

    #[test]
    fn constrained_include_structure_localizes_alias_path() {
        let (typed, ta) = type_test_structure(
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

        let inner_structure = ta
            .structure_items(typed.str_items)
            .iter()
            .find_map(|item| match &item.str_desc {
                StructureItemDesc::Tstr_module(binding) if binding.mb_id.name() == "M3" => {
                    let ModuleExprDesc::Tmod_constraint(inner, _, _, _) =
                        &ta.module_expr(binding.mb_expr).mod_desc
                    else {
                        panic!("expected constrained module");
                    };
                    let ModuleExprDesc::Tmod_structure(structure) =
                        &ta.module_expr(*inner).mod_desc
                    else {
                        panic!("expected inner structure");
                    };
                    Some(structure)
                }
                _ => None,
            })
            .expect("M3 structure");

        let local_n = inner_structure
            .str_type
            .iter()
            .find_map(|item| match item {
                crate::types::decl::SignatureItem::SigModule(id, _, _) if id.name() == "N" => {
                    Some(*id)
                }
                _ => None,
            })
            .expect("N signature item");

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

        // OCaml compiler/ml/subst.ml:345-356 and compiler/ml/subst.ml:379
        // localize module aliases through `Subst.modtype` while copying a signature.
        assert!(matches!(
            n_prime_decl.md_type.ident_or_alias_path().map(|p| p.view()),
            Some(PathView::Pident(id)) if id.same(&local_n)
        ));
    }
}

/// `lbl_all` is the array `Datarepr.label_descrs` built for the record
/// (compiler/ml/datarepr.ml:261-288), whether a label is reached through the
/// environment, a module path or a literal.
#[cfg(test)]
mod label_family_tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::parser::{Parser, module};
    use crate::types::{TypeCheckContext, TypeContext, initial_env};
    use crate::types::LabelDescription;
    use crate::types::typedtree::{ExpressionDesc, PatternDesc, ValueBinding};

    fn with_typed(source: &str, check: impl FnOnce(&TypedArena, &Structure, &TypeContext)) {
        crate::ident::Ident::set_current_time(999);
        let id_gen = IdGenerator::with_start_stamp(999);
        let _ = id_gen.next_stamp();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut parser = Parser::new("test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "parse failed");
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let arena = parser.arena();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (typed, _) = type_structure(&mut tctx, &env, arena, &structure).expect("typecheck");
        check(&tctx.typed, &typed, &type_ctx);
    }

    fn binding<'s>(ta: &'s TypedArena, typed: &'s Structure, name: &str) -> &'s ValueBinding {
        ta.structure_items(typed.str_items).iter()
            .find_map(|item| match &item.str_desc {
                StructureItemDesc::Tstr_value(_, vbs) => ta.value_bindings(*vbs).iter().find(|vb| {
                    matches!(&ta.pattern(vb.vb_pat).pat_desc, PatternDesc::Tpat_var(id, _) if id.name() == name)
                }),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no binding `{name}`"))
    }

    fn field_label<'s>(ta: &'s TypedArena, typed: &'s Structure, name: &str) -> &'s LabelDescription {
        match &ta.expr(binding(ta, typed, name).vb_expr).exp_desc {
            ExpressionDesc::Texp_field(_, _, label) => label,
            other => panic!("`{name}` is not a field access: {other:?}"),
        }
    }

    fn literal_labels<'s>(ta: &'s TypedArena, typed: &'s Structure, name: &str) -> Vec<&'s LabelDescription> {
        match &ta.expr(binding(ta, typed, name).vb_expr).exp_desc {
            ExpressionDesc::Texp_record { fields, .. } => {
                ta.record_fields(*fields).iter().map(|(label, _, _)| label.as_ref()).collect()
            }
            other => panic!("`{name}` is not a record literal: {other:?}"),
        }
    }

    fn family_names(ctx: &TypeContext, label: &LabelDescription) -> Vec<String> {
        let family = ctx
            .label_family(label.lbl_all)
            .unwrap_or_else(|| panic!("label `{}` carries no lbl_all", label.lbl_name));
        family.iter().map(|l| l.lbl_name.to_string()).collect()
    }

    #[test]
    fn env_label_lookup_before_any_literal_has_its_family() {
        with_typed(
            r#"
type t = {a: int, b: string}
external mk_x: unit => t = "mk"
let x = mk_x()
let b = x.b
"#,
            |ta, typed, ctx| {
                let label = field_label(ta, typed, "b");
                assert_ne!(label.lbl_all, crate::types::decl::LabelArrayRef::NONE);
                assert_eq!(family_names(ctx, label), ["a", "b"]);
                assert_eq!(label.lbl_pos, 1);
            },
        );
    }

    #[test]
    fn two_records_with_no_literal_have_distinct_families() {
        with_typed(
            r#"
type t = {a: int}
type u = {a: int, c: int}
external mk_x: unit => t = "mk"
let x = mk_x()
external mk_y: unit => u = "mk"
let y = mk_y()
let fx = x.a
let fy = y.a
"#,
            |ta, typed, ctx| {
                let lx = field_label(ta, typed, "fx");
                let ly = field_label(ta, typed, "fy");
                assert_ne!(lx.lbl_all, ly.lbl_all);
                assert_eq!(family_names(ctx, lx), ["a"]);
                assert_eq!(family_names(ctx, ly), ["a", "c"]);
            },
        );
    }

    #[test]
    fn module_alias_open_and_shadowing_keep_the_reached_family() {
        with_typed(
            r#"
module M = {
  type t = {x: int, y: int}
}
module N = M
external mk_v: unit => N.t = "mk"
let v = mk_v()
let fy = v.N.y
open M
let fx = v.x
type t = {x: string}
external mk_w: unit => t = "mk"
let w = mk_w()
let fw = w.x
"#,
            |ta, typed, ctx| {
                assert_eq!(family_names(ctx, field_label(ta, typed, "fy")), ["x", "y"]);
                assert_eq!(family_names(ctx, field_label(ta, typed, "fx")), ["x", "y"]);
                let shadowing = field_label(ta, typed, "fw");
                assert_eq!(family_names(ctx, shadowing), ["x"]);
                assert_eq!(shadowing.lbl_pos, 0);
            },
        );
    }

    #[test]
    fn generic_record_literals_share_one_family_per_literal() {
        with_typed(
            r#"
type p<'a> = {v: 'a, w: int}
let a = {v: 1, w: 2}
let b = {w: 3, v: "s"}
"#,
            |ta, typed, ctx| {
                for name in ["a", "b"] {
                    let labels = literal_labels(ta, typed, name);
                    assert_eq!(labels.len(), 2);
                    // Written fields are ordered by position and all point at
                    // the array of the first one (typecore.ml:3058-3170).
                    assert_eq!(labels[0].lbl_name, "v");
                    assert_eq!(labels[1].lbl_name, "w");
                    assert_eq!(labels[0].lbl_all, labels[1].lbl_all);
                    assert_eq!(family_names(ctx, labels[0]), ["v", "w"]);
                }
            },
        );
    }

    #[test]
    fn record_pattern_labels_carry_their_family() {
        with_typed(
            r#"
type t = {a: int, b: int, c: int}
external mk_x: unit => t = "mk"
let x = mk_x()
let f = switch x {
| {b} => b
}
"#,
            |ta, typed, ctx| {
                let ExpressionDesc::Texp_match(_, cases, _, _) = &ta.expr(binding(ta, typed, "f").vb_expr).exp_desc
                else {
                    panic!("`f` is not a switch");
                };
                let PatternDesc::Tpat_record(fields, _, _) = &ta.pattern(ta.cases(*cases)[0].c_lhs).pat_desc else {
                    panic!("case is not a record pattern");
                };
                assert_eq!(family_names(ctx, &fields[0].1), ["a", "b", "c"]);
            },
        );
    }

    fn typecheck_result(source: &str) -> Result<(), TypeModError> {
        crate::ident::Ident::set_current_time(999);
        let id_gen = IdGenerator::with_start_stamp(999);
        let _ = id_gen.next_stamp();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut parser = Parser::new("test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "parse failed");
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let arena = parser.arena();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        type_structure(&mut tctx, &env, arena, &structure).map(|_| ())
    }

    #[test]
    fn empty_literal_of_an_immutable_record_generalizes() {
        // `{}` with no mutable field is non-expansive (typecore.ml:2098-2105).
        typecheck_result(
            r#"
type options<'a> = {value?: 'a}
let defaults: options<_> = {}
let ints: options<int> = defaults
let strings: options<string> = defaults
"#,
        )
        .expect("an immutable `{}` generalizes");
    }

    #[test]
    fn empty_literal_of_a_record_with_a_mutable_field_does_not_generalize() {
        // A mutable field makes `{}` expansive (typecore.ml:2098-2105).
        let result = typecheck_result(
            r#"
type cell<'a> = {tag?: int, mutable value?: 'a}
let cell: cell<_> = {}
cell.value = Some(1)
let s: option<string> = cell.value
"#,
        );
        assert!(result.is_err(), "a mutable `{{}}` must not generalize");
    }

    /// Type `program` after a record declaration `decl` and a polymorphic,
    /// non-expansive `base: <ty>` (`assert(false)` is non-expansive,
    /// typecore.ml `Texp_assert`), then use `binding` at two instances.
    /// The parameter is invariant (`'a => 'a`) so the relaxed value
    /// restriction cannot generalize an expansive `binding`.
    fn uses_at_two_types(decl: &str, ty: &str, binding: &str) -> Result<(), TypeModError> {
        typecheck_result(&format!(
            "{decl}\nlet base: {ty}<'a> = assert(false)\nlet x = {binding}\nlet ints: {ty}<int> = x\nlet strings: {ty}<string> = x\n"
        ))
    }

    #[test]
    fn spread_generalizes_only_when_every_field_is_immutable() {
        // The literal allocates every field of the record: written, copied
        // from the spread, or left out (typecore.ml:2088-2108). Each
        // immutable twin must generalize, so the mutable failure is the
        // value restriction and not some other error.
        let immutable = "type cell<'a> = {tag: int, value: option<'a => 'a>}";
        let mutable = "type cell<'a> = {tag: int, mutable value: option<'a => 'a>}";
        for binding in [
            // `value` copied from the spread
            "{...base, tag: 1}",
            // `value` written over the spread
            "{...base, value: None}",
            // every field written over the spread
            "{...base, tag: 1, value: None}",
        ] {
            uses_at_two_types(immutable, "cell", binding)
                .unwrap_or_else(|e| panic!("`{binding}` of an immutable record: {e:?}"));
            assert!(
                uses_at_two_types(mutable, "cell", binding).is_err(),
                "`{binding}` of a record with a mutable field must not generalize"
            );
        }
    }

    #[test]
    fn spread_of_an_expansive_base_does_not_generalize() {
        // `is_nonexpansive_opt extended_expression` (typecore.ml:2090).
        let decl = "type cell<'a> = {tag: int, value: option<'a => 'a>}\nlet make = (): cell<'a> => assert(false)";
        uses_at_two_types(decl, "cell", "{...base, tag: 1}").expect("a non-expansive spread generalizes");
        assert!(
            uses_at_two_types(decl, "cell", "{...make(), tag: 1}").is_err(),
            "an expansive spread must not generalize"
        );
    }

    #[test]
    fn literal_leaving_out_a_mutable_field_does_not_generalize() {
        // The omitted optional `value` is allocated too (typecore.ml:2106-2108).
        uses_at_two_types("type cell<'a> = {tag: int, value?: 'a => 'a}", "cell", "{tag: 1}")
            .expect("an immutable literal generalizes");
        assert!(
            uses_at_two_types("type cell<'a> = {tag: int, mutable value?: 'a => 'a}", "cell", "{tag: 1}")
                .is_err(),
            "an omitted mutable field must not generalize"
        );
    }

    #[test]
    fn inline_record_with_a_mutable_field_does_not_generalize() {
        // An inline record literal is a `Texp_record` whose `lbl_all` holds
        // the constructor's fields (typecore.ml:2106-2108).
        let immutable = "type t<'a> = A({tag: int, value: option<'a => 'a>})";
        let mutable = "type t<'a> = A({tag: int, mutable value: option<'a => 'a>})";
        let binding = "A({tag: 1, value: None})";
        uses_at_two_types(immutable, "t", binding).expect("an immutable inline record generalizes");
        assert!(
            uses_at_two_types(mutable, "t", binding).is_err(),
            "a mutable inline record must not generalize"
        );
    }

    #[test]
    fn spread_of_an_unboxed_record_generalizes() {
        uses_at_two_types(
            "@unboxed type box<'a> = {value: option<'a => 'a>}",
            "box",
            "{...base, value: None}",
        )
        .expect("an immutable unboxed spread generalizes");
    }

    /// The label of the field access a function `name` returns.
    fn body_field_label<'s>(ta: &'s TypedArena, typed: &'s Structure, name: &str) -> &'s LabelDescription {
        let mut expr = ta.expr(binding(ta, typed, name).vb_expr);
        while let ExpressionDesc::Texp_function { body, .. } = &expr.exp_desc {
            expr = ta.expr(*body);
        }
        match &expr.exp_desc {
            ExpressionDesc::Texp_field(_, _, label) => label,
            other => panic!("`{name}` does not return a field access: {other:?}"),
        }
    }

    #[test]
    fn type_directed_lookup_of_a_local_record_reads_its_installed_array() {
        // `u` shadows the label `a` by name; `v.a` finds `t`'s label through
        // the type, and the literal reads `find_type_descrs` of `t`
        // (env.ml:828 -> store_type, env.ml:1561-1569): one array.
        with_typed(
            r#"
type t = {a: int, b: int}
type u = {a: string}
let f = (v: t) => v.a
let lit = ({a: 1, b: 2}: t)
"#,
            |ta, typed, ctx| {
                let by_type = body_field_label(ta, typed, "f");
                let literal = literal_labels(ta, typed, "lit");
                assert_eq!(family_names(ctx, by_type), ["a", "b"]);
                assert_eq!(by_type.lbl_all, literal[0].lbl_all);
            },
        );
    }

    #[test]
    fn type_directed_and_qualified_lookup_share_the_component_array() {
        // `v.a` with no `a` in scope goes through `lookup_from_type`
        // (typecore.ml:976-981) to the component table of `M`; `w.M.a` looks
        // the label up by name in the same table (env.ml:1470-1485).
        with_typed(
            r#"
module M = {
  type t = {a: int, b: int}
}
let f = (v: M.t) => v.a
let g = (w: M.t) => w.M.a
let h = (x: M.t) => x.b
"#,
            |ta, typed, ctx| {
                let by_type = body_field_label(ta, typed, "f");
                let by_name = body_field_label(ta, typed, "g");
                let again = body_field_label(ta, typed, "h");
                assert_eq!(family_names(ctx, by_type), ["a", "b"]);
                assert_eq!(by_type.lbl_all, by_name.lbl_all);
                // A second type-directed lookup reuses the table's array.
                assert_eq!(by_type.lbl_all, again.lbl_all);
            },
        );
    }

    #[test]
    fn generic_record_through_an_alias_instantiates_per_use() {
        with_typed(
            r#"
module M = {
  type p<'a> = {v: 'a, n: int}
}
module N = M
let i = (x: N.p<int>) => x.v
let s = (y: N.p<string>) => y.v
"#,
            |ta, typed, ctx| {
                let li = body_field_label(ta, typed, "i");
                let ls = body_field_label(ta, typed, "s");
                assert_eq!(family_names(ctx, li), ["v", "n"]);
                assert_eq!(li.lbl_all, ls.lbl_all);
                let i_ty = ctx.repr(ta.expr(binding(ta, typed, "i").vb_expr).exp_type);
                let s_ty = ctx.repr(ta.expr(binding(ta, typed, "s").vb_expr).exp_type);
                assert_ne!(i_ty, s_ty);
            },
        );
    }

    #[test]
    fn inline_record_labels_get_a_new_array_per_lookup() {
        // `type_of_cstr` describes an inline record on every lookup
        // (env.ml:782-784).
        with_typed(
            r#"
type v = A({x: int, y: int})
let f = (A(r)) => r.x
let g = (A(r)) => r.y
"#,
            |ta, typed, ctx| {
                let lf = body_field_label(ta, typed, "f");
                let lg = body_field_label(ta, typed, "g");
                assert_eq!(family_names(ctx, lf), ["x", "y"]);
                assert_eq!(family_names(ctx, lg), ["x", "y"]);
                assert_ne!(lf.lbl_all, lg.lbl_all);
            },
        );
    }


    #[test]
    fn opened_labels_share_the_component_array_with_type_directed_lookup() {
        // `open M` installs the component table's labels (env.ml:1874-1877);
        // after `u` shadows `a`, `w.a` finds `M.t`'s label through
        // `find_type_descrs` of the same table (env.ml:828, 1470-1485).
        with_typed(
            r#"
module M = {
  type t = {a: int, b: int}
}
open M
let f = (v: t) => v.a
type u = {a: string}
let g = (w: M.t) => w.a
"#,
            |ta, typed, ctx| {
                let opened = body_field_label(ta, typed, "f");
                let by_type = body_field_label(ta, typed, "g");
                assert_eq!(family_names(ctx, opened), ["a", "b"]);
                assert_eq!(opened.lbl_all, by_type.lbl_all);
            },
        );
    }


    #[test]
    fn opening_a_module_with_an_empty_record_installs_its_other_labels() {
        // `type any = {}` describes no labels (datarepr.ml:261-288), so an
        // open installs none for it.
        with_typed(
            r#"
module M = {
  type any = {}
  type t = {a: int}
}
open M
let f = (v: t) => v.a
"#,
            |ta, typed, ctx| {
                assert_eq!(family_names(ctx, body_field_label(ta, typed, "f")), ["a"]);
            },
        );
    }


    /// The abstract `int` declaration of the initial environment.
    fn abstract_decl(env: &Env) -> crate::types::decl::TypeDeclaration {
        env.find_type("int").expect("predef int").clone()
    }

    fn record_decl(
        ctx: &TypeContext,
        env: &Env,
        names: &[&str],
    ) -> crate::types::decl::TypeDeclaration {
        let labels = names
            .iter()
            .map(|name| crate::types::decl::LabelDeclaration {
                ld_id: ctx.create_ident(*name),
                ld_runtime_name: None,
                ld_mutable: crate::types::MutableFlag::Immutable,
                ld_optional: false,
                ld_type: ctx.new_constr(Path::pident(crate::types::predef::ident_int()), vec![]),
                ld_loc: crate::types::DeclLoc::none(),
                ld_attributes: vec![],
            })
            .collect();
        crate::types::decl::TypeDeclaration {
            type_kind: crate::types::TypeKind::TypeRecord(
                labels,
                crate::types::RecordRepresentation::RecordRegular,
            ),
            ..abstract_decl(env)
        }
    }

    #[test]
    fn store_type_ties_labels_and_a_new_binding_drops_them() {
        // `store_type` (env.ml:1561-1569) installs the labels with the type;
        // binding the ident again describes the new declaration's labels.
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let mut env = initial_env(&ctx);
        let id = ctx.create_ident("t");
        let decl = record_decl(&ctx, &env, &["a", "b"]);
        env.store_type(&ctx, id, decl.clone());
        let family = env.type_label_family(&id).expect("store_type ties the labels");
        assert_eq!(env.find_label("a").unwrap().lbl_all, family);
        assert_eq!(ctx.label_family(family).unwrap().len(), 2);

        // A variance update keeps the labels of the same declaration.
        let updated = env
            .update_type_variance(id, decl.type_variance.clone())
            .expect("t is bound");
        assert_eq!(env.type_label_family(&id), Some(family));
        assert!(matches!(updated.type_kind, crate::types::TypeKind::TypeRecord(..)));

        // A new binding without labels (an abstract placeholder) has none.
        let placeholder = abstract_decl(&env);
        env.add_type(id, placeholder);
        assert_eq!(env.type_label_family(&id), None);

        // Storing a record again describes a new array.
        let decl = record_decl(&ctx, &env, &["c"]);
        env.store_type(&ctx, id, decl);
        let again = env.type_label_family(&id).unwrap();
        assert_ne!(again, family);
        assert_eq!(env.find_label("c").unwrap().lbl_all, again);
    }

    #[test]
    fn variance_updated_record_keeps_one_array() {
        // Rust re-adds a declaration with its computed variance after the
        // final environment; the labels installed with it stay the array of
        // both lookup by name and `find_type_descrs`.
        with_typed(
            r#"
type box<'a> = {v: 'a, n: int}
type other = {v: string}
let f = (b: box<int>) => b.v
let lit = ({v: 1, n: 2}: box<int>)
"#,
            |ta, typed, ctx| {
                let by_type = body_field_label(ta, typed, "f");
                assert_eq!(family_names(ctx, by_type), ["v", "n"]);
                assert_eq!(by_type.lbl_all, literal_labels(ta, typed, "lit")[0].lbl_all);
            },
        );
    }

    #[test]
    fn opening_a_module_does_not_install_inline_record_labels() {
        // `comp_labels` holds `labels_of_type`, empty for a variant
        // (datarepr.ml:292-298): `x` is unbound by name after `open M`.
        let result = typecheck_result(
            r#"
module M = {
  type v = A({x: int})
}
open M
let f = r => r.x
"#,
        );
        assert!(result.is_err(), "an inline record label is not bound by name");
    }
}
