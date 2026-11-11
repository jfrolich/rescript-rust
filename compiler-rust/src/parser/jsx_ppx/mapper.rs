//! The JSX mapper: `Ast_mapper.default_mapper` (compiler/ml/ast_mapper.ml)
//! with the overrides of `Jsx_ppx.get_mapper` (compiler/syntax/src/
//! jsx_ppx.ml:76-147): `expr` (a JSX element at version 4,
//! jsx_v4.ml:1315-1373), `module_binding` (nested module names,
//! jsx_v4.ml:1375-1383), `structure` and `signature` (`@@jsxConfig`, the
//! saved and restored configuration, and the component transform of each
//! mapped item).
//!
//! The traversal follows OCaml's evaluation order, which decides which error
//! is raised first and which warnings are printed before it: a node's
//! attributes are mapped before its description (`let attrs = sub.attributes
//! sub attrs in`), the arguments of the rebuilt constructor or `Ast_helper`
//! function are evaluated right to left in the order of its parameters (so
//! `Mb.mk name (module_expr ...) ~attrs ~loc` maps the module expression
//! before the attributes), record fields right to left in declaration order,
//! and `List.map` left to right.
//!
//! An error (`Jsx_common.raise_error`, `Location.raise_errorf`) is returned
//! with `?` from the point where OCaml raises it, so nothing after it is
//! visited, rebuilt or warned about. The configuration saved on entering a
//! structure is not restored then: the whole mapping has failed.
//!
//! A subtree the mapper cannot change (no JSX element, structure, signature,
//! extension or attribute payload that could hold one) is returned as it is
//! instead of being rebuilt.

use super::*;
use crate::parse_arena::{CaseList, ExprList, ModExprIdx, ModTypeIdx, PatIdx};

type R<T> = JsxPreprocessorResult<T>;

// ============================================================================
// Structures and signatures (jsx_ppx.ml:121-145)
// ============================================================================

/// The JSX `structure` override: `@@jsxConfig` is read before an item is
/// mapped, a mapped item gets the component transform at version 4, and the
/// configuration is restored when the structure ends.
pub(super) fn structure(items: Structure, c: &mut JsxConfig, a: &mut ParseArena) -> R<Structure> {
    let scope = c.enter_scope();
    let mut result = Vec::with_capacity(items.len());
    for item in items {
        if let StructureItemDesc::Pstr_attribute(attr) = &item.pstr_desc
            && a.get_string(attr.0.txt) == "jsxConfig"
        {
            update_config_from_attribute(a, attr, c)?;
        }
        let item = structure_item(item, c, a)?;
        if c.version == 4 {
            result.extend(transform_structure_item4(item, c, a)?);
        } else {
            result.push(item);
        }
    }
    c.exit_scope(scope);
    Ok(result)
}

/// The JSX `signature` override (jsx_ppx.ml:105-120).
pub(super) fn signature(items: Signature, c: &mut JsxConfig, a: &mut ParseArena) -> R<Signature> {
    let scope = c.enter_scope();
    let mut result = Vec::with_capacity(items.len());
    for item in items {
        if let SignatureItemDesc::Psig_attribute(attr) = &item.psig_desc
            && a.get_string(attr.0.txt) == "jsxConfig"
        {
            update_config_from_attribute(a, attr, c)?;
        }
        let item = signature_item(item, c, a)?;
        if c.version == 4 {
            result.extend(transform_signature_item4(item, c, a)?);
        } else {
            result.push(item);
        }
    }
    c.exit_scope(scope);
    Ok(result)
}

/// `M.map_structure_item` (ast_mapper.ml:276-301).
fn structure_item(item: StructureItem, c: &mut JsxConfig, a: &mut ParseArena) -> R<StructureItem> {
    let pstr_desc = match item.pstr_desc {
        // `eval ~loc ~attrs:(sub.attributes sub attrs) (sub.expr sub x)`.
        StructureItemDesc::Pstr_eval(inner) => {
            let (e, attrs) = *inner;
            let e = expr_idx(e, c, a)?;
            let attrs = attributes(attrs, c, a)?;
            StructureItemDesc::Pstr_eval(Box::new((e, attrs)))
        }
        StructureItemDesc::Pstr_value((rec_flag, vbs)) => {
            let vbs = a.vb_list(vbs).to_vec();
            let vbs = vbs
                .into_iter()
                .map(|vb| value_binding(vb, c, a))
                .collect::<R<Vec<_>>>()?;
            StructureItemDesc::Pstr_value((rec_flag, a.push_vb_list(&vbs)))
        }
        StructureItemDesc::Pstr_primitive(vd) => {
            StructureItemDesc::Pstr_primitive(Box::new(value_description(*vd, c, a)?))
        }
        StructureItemDesc::Pstr_type(inner) => {
            let (rec_flag, decls) = *inner;
            let decls = decls
                .into_iter()
                .map(|d| type_declaration(d, c, a))
                .collect::<R<_>>()?;
            StructureItemDesc::Pstr_type(Box::new((rec_flag, decls)))
        }
        StructureItemDesc::Pstr_typext(te) => {
            StructureItemDesc::Pstr_typext(Box::new(type_extension(*te, c, a)?))
        }
        StructureItemDesc::Pstr_exception(ec) => {
            StructureItemDesc::Pstr_exception(Box::new(extension_constructor(*ec, c, a)?))
        }
        StructureItemDesc::Pstr_module(mb) => {
            StructureItemDesc::Pstr_module(Box::new(module_binding(*mb, c, a)?))
        }
        StructureItemDesc::Pstr_recmodule(mbs) => StructureItemDesc::Pstr_recmodule(Box::new(
            mbs.into_iter()
                .map(|mb| module_binding(mb, c, a))
                .collect::<R<_>>()?,
        )),
        StructureItemDesc::Pstr_modtype(mtd) => {
            StructureItemDesc::Pstr_modtype(Box::new(module_type_declaration(*mtd, c, a)?))
        }
        StructureItemDesc::Pstr_open(od) => {
            StructureItemDesc::Pstr_open(Box::new(open_description(*od, c, a)?))
        }
        // `Incl.mk (this.module_expr this pincl_mod) ~loc ~attrs`.
        StructureItemDesc::Pstr_include(incl) => {
            let incl = *incl;
            let pincl_mod = module_expr_idx(incl.pincl_mod, c, a)?;
            let pincl_attributes = attributes(incl.pincl_attributes, c, a)?;
            StructureItemDesc::Pstr_include(Box::new(IncludeDeclaration {
                pincl_mod,
                pincl_attributes,
                ..incl
            }))
        }
        // `extension ~loc (sub.extension sub x) ~attrs:(sub.attributes sub attrs)`.
        StructureItemDesc::Pstr_extension(inner) => {
            let (ext, attrs) = *inner;
            let ext = extension(ext, c, a)?;
            let attrs = attributes(attrs, c, a)?;
            StructureItemDesc::Pstr_extension(Box::new((ext, attrs)))
        }
        StructureItemDesc::Pstr_raw(raw) => {
            let mut raw = *raw;
            raw.attrs = attributes(raw.attrs, c, a)?;
            StructureItemDesc::Pstr_raw(Box::new(raw))
        }
        StructureItemDesc::Pstr_attribute(attr) => {
            StructureItemDesc::Pstr_attribute(Box::new(attribute(*attr, c, a)?))
        }
    };
    Ok(StructureItem {
        pstr_desc,
        pstr_loc: item.pstr_loc,
    })
}

/// `MT.map_signature_item` (ast_mapper.ml:236-255).
fn signature_item(item: SignatureItem, c: &mut JsxConfig, a: &mut ParseArena) -> R<SignatureItem> {
    let psig_desc = match item.psig_desc {
        SignatureItemDesc::Psig_value(vd) => {
            SignatureItemDesc::Psig_value(Box::new(value_description(*vd, c, a)?))
        }
        SignatureItemDesc::Psig_type(inner) => {
            let (rec_flag, decls) = *inner;
            let decls = decls
                .into_iter()
                .map(|d| type_declaration(d, c, a))
                .collect::<R<_>>()?;
            SignatureItemDesc::Psig_type(Box::new((rec_flag, decls)))
        }
        SignatureItemDesc::Psig_typext(te) => {
            SignatureItemDesc::Psig_typext(Box::new(type_extension(*te, c, a)?))
        }
        SignatureItemDesc::Psig_exception(ec) => {
            SignatureItemDesc::Psig_exception(Box::new(extension_constructor(*ec, c, a)?))
        }
        SignatureItemDesc::Psig_module(md) => {
            SignatureItemDesc::Psig_module(Box::new(module_declaration(*md, c, a)?))
        }
        SignatureItemDesc::Psig_recmodule(mds) => SignatureItemDesc::Psig_recmodule(Box::new(
            mds.into_iter()
                .map(|md| module_declaration(md, c, a))
                .collect::<R<_>>()?,
        )),
        SignatureItemDesc::Psig_modtype(mtd) => {
            SignatureItemDesc::Psig_modtype(Box::new(module_type_declaration(*mtd, c, a)?))
        }
        SignatureItemDesc::Psig_open(od) => {
            SignatureItemDesc::Psig_open(Box::new(open_description(*od, c, a)?))
        }
        // `Incl.mk (this.module_type this pincl_mod) ~loc ~attrs`.
        SignatureItemDesc::Psig_include(incl) => {
            let incl = *incl;
            let pincl_mod = module_type_idx(incl.pincl_mod, c, a)?;
            let pincl_attributes = attributes(incl.pincl_attributes, c, a)?;
            SignatureItemDesc::Psig_include(Box::new(IncludeDescription {
                pincl_mod,
                pincl_attributes,
                ..incl
            }))
        }
        SignatureItemDesc::Psig_extension(inner) => {
            let (ext, attrs) = *inner;
            let ext = extension(ext, c, a)?;
            let attrs = attributes(attrs, c, a)?;
            SignatureItemDesc::Psig_extension(Box::new((ext, attrs)))
        }
        SignatureItemDesc::Psig_attribute(attr) => {
            SignatureItemDesc::Psig_attribute(Box::new(attribute(*attr, c, a)?))
        }
    };
    Ok(SignatureItem {
        psig_desc,
        psig_loc: item.psig_loc,
    })
}

// ============================================================================
// Declarations
// ============================================================================

/// The attributes with a component annotation put back where it was written
/// (`Jsx_component.put_back`, ast_helper.ml:395-403), mapped in that order;
/// the annotation's props type is its payload (`PTyp typ`).
fn attributes_with_component(
    attrs: Attributes,
    component: Option<Box<JsxComponent>>,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<(Attributes, Option<Box<JsxComponent>>)> {
    let Some(mut component) = component else {
        return Ok((attributes(attrs, c, a)?, None));
    };
    let component_start = a.loc_start(component.pjc_loc).cnum;
    let (earlier, later): (Vec<_>, Vec<_>) = attrs
        .iter()
        .cloned()
        .partition(|(name, _)| a.loc_start(name.loc).cnum < component_start);
    let mut mapped = earlier
        .into_iter()
        .map(|attr| attribute(attr, c, a))
        .collect::<R<Vec<_>>>()?;
    if let JsxComponentKind::Labelled(Some(typ)) = &mut component.pjc_kind {
        *typ = core_type(*typ, c, a)?;
    }
    for attr in later {
        mapped.push(attribute(attr, c, a)?);
    }
    Ok((Attributes::from_vec(mapped), Some(component)))
}

/// `default_mapper.value_binding` (ast_mapper.ml:593-611): the pattern, the
/// constraint's type, the expression, then the attributes.
fn value_binding(vb: ValueBinding, c: &mut JsxConfig, a: &mut ParseArena) -> R<ValueBinding> {
    let constraint = a.value_constraint(vb.pvb_pat).cloned();
    let mut pvb_pat = pattern(vb.pvb_pat, c, a)?;
    let constraint_type = match &constraint {
        Some(vc) => Some(core_type(vc.pvc_type, c, a)?),
        None => None,
    };
    let pvb_expr = expr_idx(vb.pvb_expr, c, a)?;
    let (pvb_attributes, pvb_jsx_component) =
        attributes_with_component(vb.pvb_attributes, vb.pvb_jsx_component, c, a)?;
    if let (Some(vc), Some(pvc_type)) = (constraint, constraint_type)
        && (pvb_pat != vb.pvb_pat || pvb_expr != vb.pvb_expr || pvc_type != vc.pvc_type)
    {
        // The constraint is kept beside the binding's pattern; give the
        // rebuilt binding its own pattern node so the original keeps its own.
        if pvb_pat == vb.pvb_pat {
            let copy = a.get_pat(pvb_pat).clone();
            pvb_pat = a.push_pat(copy);
        }
        let constraint = ValueConstraint {
            pvc_newtypes: vc.pvc_newtypes,
            pvc_type,
            pvc_pattern: None,
            pvc_expression: None,
        };
        a.set_value_constraint(pvb_pat, constraint, pvb_expr, vb.pvb_loc);
    }
    Ok(ValueBinding {
        pvb_pat,
        pvb_expr,
        pvb_jsx_component,
        pvb_attributes,
        pvb_loc: vb.pvb_loc,
    })
}

/// `default_mapper.value_description` (ast_mapper.ml:550-557): the type,
/// then the attributes with the component annotation.
fn value_description(
    vd: ValueDescription,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<ValueDescription> {
    let pval_type = core_type(vd.pval_type, c, a)?;
    let (pval_attributes, pval_jsx_component) =
        attributes_with_component(vd.pval_attributes, vd.pval_jsx_component, c, a)?;
    Ok(ValueDescription {
        pval_type,
        pval_attributes,
        pval_jsx_component,
        ..vd
    })
}

/// `T.map_type_declaration` (ast_mapper.ml:142-164): `Type.mk ?loc ?attrs
/// ?params ?cstrs ?kind ?priv ?manifest ?origin name` evaluates the manifest,
/// the kind, the constraints, the parameters, then the attributes.
fn type_declaration(
    d: TypeDeclaration,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<TypeDeclaration> {
    let ptype_manifest = match d.ptype_manifest {
        Some(t) => Some(core_type(t, c, a)?),
        None => None,
    };
    let ptype_kind = match d.ptype_kind {
        TypeKind::Ptype_variant(cds) => TypeKind::Ptype_variant(
            cds.into_iter()
                .map(|cd| constructor_declaration(cd, c, a))
                .collect::<R<_>>()?,
        ),
        TypeKind::Ptype_record(lds) => TypeKind::Ptype_record(
            lds.into_iter()
                .map(|ld| label_declaration(ld, c, a))
                .collect::<R<_>>()?,
        ),
        kind => kind,
    };
    // `map_tuple3 (sub.typ sub) (sub.typ sub) (sub.location sub)`.
    let ptype_cstrs = d
        .ptype_cstrs
        .into_iter()
        .map(|(t1, t2, loc)| {
            let t2 = core_type(t2, c, a)?;
            let t1 = core_type(t1, c, a)?;
            Ok((t1, t2, loc))
        })
        .collect::<R<_>>()?;
    let ptype_params = d
        .ptype_params
        .into_iter()
        .map(|(t, variance)| Ok((core_type(t, c, a)?, variance)))
        .collect::<R<_>>()?;
    let ptype_attributes = attributes(d.ptype_attributes, c, a)?;
    Ok(TypeDeclaration {
        ptype_params,
        ptype_cstrs,
        ptype_kind,
        ptype_manifest,
        ptype_attributes,
        ..d
    })
}

/// `default_mapper.constructor_declaration` (ast_mapper.ml:614-620): the
/// result type, the arguments, then the attributes.
fn constructor_declaration(
    cd: ConstructorDeclaration,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<ConstructorDeclaration> {
    let pcd_res = match cd.pcd_res {
        Some(t) => Some(core_type(t, c, a)?),
        None => None,
    };
    let pcd_args = constructor_arguments(cd.pcd_args, c, a)?;
    let pcd_attributes = attributes(cd.pcd_attributes, c, a)?;
    Ok(ConstructorDeclaration {
        pcd_res,
        pcd_args,
        pcd_attributes,
        ..cd
    })
}

fn constructor_arguments(
    args: ConstructorArguments,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<ConstructorArguments> {
    Ok(match args {
        ConstructorArguments::Pcstr_tuple(types) => ConstructorArguments::Pcstr_tuple(
            types
                .into_iter()
                .map(|t| core_type(t, c, a))
                .collect::<R<_>>()?,
        ),
        ConstructorArguments::Pcstr_record(lds) => ConstructorArguments::Pcstr_record(
            lds.into_iter()
                .map(|ld| label_declaration(ld, c, a))
                .collect::<R<_>>()?,
        ),
    })
}

/// `default_mapper.label_declaration` (ast_mapper.ml:621-629): the type, then
/// the attributes.
fn label_declaration(
    ld: LabelDeclaration,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<LabelDeclaration> {
    let pld_type = core_type(ld.pld_type, c, a)?;
    let pld_attributes = attributes(ld.pld_attributes, c, a)?;
    Ok(LabelDeclaration {
        pld_type,
        pld_attributes,
        ..ld
    })
}

/// `T.map_type_extension` (ast_mapper.ml:178-195): the constructors, the
/// parameters, then the attributes.
fn type_extension(te: TypeExtension, c: &mut JsxConfig, a: &mut ParseArena) -> R<TypeExtension> {
    let ptyext_constructors = te
        .ptyext_constructors
        .into_iter()
        .map(|ec| extension_constructor(ec, c, a))
        .collect::<R<_>>()?;
    let ptyext_params = te
        .ptyext_params
        .into_iter()
        .map(|(t, variance)| Ok((core_type(t, c, a)?, variance)))
        .collect::<R<_>>()?;
    let ptyext_attributes = attributes(te.ptyext_attributes, c, a)?;
    Ok(TypeExtension {
        ptyext_constructors,
        ptyext_params,
        ptyext_attributes,
        ..te
    })
}

/// `T.map_extension_constructor` (ast_mapper.ml:197-203): the kind (for
/// `Pext_decl` the result type, then the arguments), then the attributes.
fn extension_constructor(
    ec: ExtensionConstructor,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<ExtensionConstructor> {
    let pext_kind = match ec.pext_kind {
        ExtensionConstructorKind::Pext_decl(args, res) => {
            let res = match res {
                Some(t) => Some(core_type(t, c, a)?),
                None => None,
            };
            let args = constructor_arguments(args, c, a)?;
            ExtensionConstructorKind::Pext_decl(args, res)
        }
        kind => kind,
    };
    let pext_attributes = attributes(ec.pext_attributes, c, a)?;
    Ok(ExtensionConstructor {
        pext_kind,
        pext_attributes,
        ..ec
    })
}

// ============================================================================
// Modules
// ============================================================================

/// The JSX `module_binding` override (jsx_v4.ml:1375-1383) around
/// `default_mapper.module_binding`: `Mb.mk name (module_expr) ~attrs ~loc`
/// maps the module expression, then the attributes.
fn module_binding(mb: ModuleBinding, c: &mut JsxConfig, a: &mut ParseArena) -> R<ModuleBinding> {
    let name = a.get_string(mb.pmb_name.txt).to_string();
    c.nested_modules.push(name);
    let pmb_expr = module_expr_idx(mb.pmb_expr, c, a)?;
    let pmb_attributes = attributes(mb.pmb_attributes, c, a)?;
    c.nested_modules.pop();
    Ok(ModuleBinding {
        pmb_expr,
        pmb_attributes,
        ..mb
    })
}

/// `default_mapper.module_declaration`: `Md.mk name (module_type) ~attrs ~loc`.
fn module_declaration(
    md: ModuleDeclaration,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<ModuleDeclaration> {
    let pmd_type = module_type_idx(md.pmd_type, c, a)?;
    let pmd_attributes = attributes(md.pmd_attributes, c, a)?;
    Ok(ModuleDeclaration {
        pmd_type,
        pmd_attributes,
        ..md
    })
}

/// `default_mapper.module_type_declaration`: `Mtd.mk name ?typ ~attrs ~loc`.
fn module_type_declaration(
    mtd: ModuleTypeDeclaration,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<ModuleTypeDeclaration> {
    let pmtd_type = match mtd.pmtd_type {
        Some(t) => Some(module_type_idx(t, c, a)?),
        None => None,
    };
    let pmtd_attributes = attributes(mtd.pmtd_attributes, c, a)?;
    Ok(ModuleTypeDeclaration {
        pmtd_type,
        pmtd_attributes,
        ..mtd
    })
}

fn open_description(
    od: OpenDescription,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<OpenDescription> {
    let popen_attributes = attributes(od.popen_attributes, c, a)?;
    Ok(OpenDescription {
        popen_attributes,
        ..od
    })
}

fn module_expr_idx(idx: ModExprIdx, c: &mut JsxConfig, a: &mut ParseArena) -> R<ModExprIdx> {
    let me = a.get_mod_expr(idx).clone();
    let me = module_expr(me, c, a)?;
    Ok(a.push_mod_expr(me))
}

/// `M.map` (ast_mapper.ml:259-274).
fn module_expr(me: ModuleExpr, c: &mut JsxConfig, a: &mut ParseArena) -> R<ModuleExpr> {
    let pmod_attributes = attributes(me.pmod_attributes, c, a)?;
    let pmod_desc = match me.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => {
            ModuleExprDesc::Pmod_structure(Box::new(structure(*items, c, a)?))
        }
        // `functor_ ~loc ~attrs (map_loc sub arg) (Misc.may_map (sub.module_type
        // sub) arg_ty) (sub.module_expr sub body)`.
        ModuleExprDesc::Pmod_functor(inner) => {
            let (arg, arg_ty, body) = *inner;
            let body = module_expr_idx(body, c, a)?;
            let arg_ty = match arg_ty {
                Some(t) => Some(module_type_idx(t, c, a)?),
                None => None,
            };
            ModuleExprDesc::Pmod_functor(Box::new((arg, arg_ty, body)))
        }
        ModuleExprDesc::Pmod_apply(m1, m2) => {
            let m2 = module_expr_idx(m2, c, a)?;
            let m1 = module_expr_idx(m1, c, a)?;
            ModuleExprDesc::Pmod_apply(m1, m2)
        }
        ModuleExprDesc::Pmod_constraint(m, mty) => {
            let mty = module_type_idx(mty, c, a)?;
            let m = module_expr_idx(m, c, a)?;
            ModuleExprDesc::Pmod_constraint(m, mty)
        }
        ModuleExprDesc::Pmod_unpack(e) => ModuleExprDesc::Pmod_unpack(expr_idx(e, c, a)?),
        ModuleExprDesc::Pmod_extension(ext) => {
            ModuleExprDesc::Pmod_extension(Box::new(extension(*ext, c, a)?))
        }
        ModuleExprDesc::Pmod_await(m) => ModuleExprDesc::Pmod_await(module_expr_idx(m, c, a)?),
        desc @ ModuleExprDesc::Pmod_ident(_) => desc,
    };
    Ok(ModuleExpr {
        pmod_desc,
        pmod_loc: me.pmod_loc,
        pmod_attributes,
    })
}

fn module_type_idx(idx: ModTypeIdx, c: &mut JsxConfig, a: &mut ParseArena) -> R<ModTypeIdx> {
    let mt = a.get_mod_type(idx).clone();
    let mt = module_type(mt, c, a)?;
    Ok(a.push_mod_type(mt))
}

/// `MT.map` (ast_mapper.ml:208-224).
fn module_type(mt: ModuleType, c: &mut JsxConfig, a: &mut ParseArena) -> R<ModuleType> {
    let pmty_attributes = attributes(mt.pmty_attributes, c, a)?;
    let pmty_desc = match mt.pmty_desc {
        ModuleTypeDesc::Pmty_signature(items) => {
            ModuleTypeDesc::Pmty_signature(Box::new(signature(*items, c, a)?))
        }
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (name, arg, body) = *inner;
            let body = module_type_idx(body, c, a)?;
            let arg = match arg {
                Some(t) => Some(module_type_idx(t, c, a)?),
                None => None,
            };
            ModuleTypeDesc::Pmty_functor(Box::new((name, arg, body)))
        }
        // `with_ ~loc ~attrs (sub.module_type sub mt) (List.map
        // (sub.with_constraint sub) l)`: the constraints, then the base.
        ModuleTypeDesc::Pmty_with(inner) => {
            let (base, constraints) = *inner;
            let constraints = constraints
                .into_iter()
                .map(|wc| {
                    Ok(match wc {
                        WithConstraint::Pwith_type(lid, d) => {
                            WithConstraint::Pwith_type(lid, type_declaration(d, c, a)?)
                        }
                        WithConstraint::Pwith_typesubst(lid, d) => {
                            WithConstraint::Pwith_typesubst(lid, type_declaration(d, c, a)?)
                        }
                        wc => wc,
                    })
                })
                .collect::<R<_>>()?;
            let base = module_type_idx(base, c, a)?;
            ModuleTypeDesc::Pmty_with(Box::new((base, constraints)))
        }
        ModuleTypeDesc::Pmty_typeof(me) => ModuleTypeDesc::Pmty_typeof(module_expr_idx(me, c, a)?),
        ModuleTypeDesc::Pmty_extension(ext) => {
            ModuleTypeDesc::Pmty_extension(Box::new(extension(*ext, c, a)?))
        }
        desc @ (ModuleTypeDesc::Pmty_ident(_) | ModuleTypeDesc::Pmty_alias(_)) => desc,
    };
    Ok(ModuleType {
        pmty_desc,
        pmty_loc: mt.pmty_loc,
        pmty_attributes,
    })
}

// ============================================================================
// Attributes and payloads
// ============================================================================

fn attributes(attrs: Attributes, c: &mut JsxConfig, a: &mut ParseArena) -> R<Attributes> {
    if !attributes_may_change(&attrs, a, &mut c.unchanged_memo) {
        return Ok(attrs);
    }
    let mapped = attrs
        .iter()
        .cloned()
        .map(|attr| attribute(attr, c, a))
        .collect::<R<Vec<_>>>()?;
    Ok(Attributes::from_vec(mapped))
}

fn attribute(attr: Attribute, c: &mut JsxConfig, a: &mut ParseArena) -> R<Attribute> {
    let (name, p) = attr;
    Ok((name, payload(p, c, a)?))
}

fn extension(ext: Extension, c: &mut JsxConfig, a: &mut ParseArena) -> R<Extension> {
    let (name, p) = ext;
    Ok((name, payload(p, c, a)?))
}

/// `default_mapper.payload` (ast_mapper.ml:641-646).
fn payload(p: Payload, c: &mut JsxConfig, a: &mut ParseArena) -> R<Payload> {
    if !payload_may_change(&p, a, &mut c.unchanged_memo) {
        return Ok(p);
    }
    Ok(match p {
        Payload::PStr(items) => Payload::PStr(Box::new(structure(*items, c, a)?)),
        Payload::PSig(items) => Payload::PSig(Box::new(signature(*items, c, a)?)),
        Payload::PTyp(t) => Payload::PTyp(core_type(t, c, a)?),
        // `PPat (this.pat this x, map_opt (this.expr this) g)`.
        Payload::PPat(inner) => {
            let (pat, guard) = *inner;
            let guard = match guard {
                Some(g) => Some(expr_idx(g, c, a)?),
                None => None,
            };
            let pat = pattern(pat, c, a)?;
            Payload::PPat(Box::new((pat, guard)))
        }
    })
}

// ============================================================================
// Core types (T.map, ast_mapper.ml:79-140)
// ============================================================================

fn type_arg(mut targ: TypeArg, c: &mut JsxConfig, a: &mut ParseArena) -> R<TypeArg> {
    if targ.fixed.is_none() {
        targ.typ = core_type(targ.typ, c, a)?;
    }
    Ok(targ)
}

fn core_type(idx: CoreTypeIdx, c: &mut JsxConfig, a: &mut ParseArena) -> R<CoreTypeIdx> {
    if !type_may_change(idx, a, &mut c.unchanged_memo) {
        return Ok(idx);
    }
    let t = a.get_core_type(idx).clone();
    let ptyp_attributes = attributes(t.ptyp_attributes, c, a)?;
    let ptyp_desc = match t.ptyp_desc {
        // `Typ.arrow ~loc ~attrs (List.map ... params) (sub.typ sub ret)`: the
        // result, then the parameters' types.
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (arg, ret, arity) = *inner;
            let ret = core_type(ret, c, a)?;
            match a.nary_arrow_args_slice(&arg).map(<[TypeArg]>::to_vec) {
                Some(args) => {
                    let mut args = args
                        .into_iter()
                        .map(|targ| type_arg(targ, c, a))
                        .collect::<R<Vec<_>>>()?;
                    // The parameters are kept beside the first one's type;
                    // give the rebuilt arrow its own.
                    if args[0].typ == arg.typ {
                        let copy = a.get_core_type(arg.typ).clone();
                        args[0].typ = a.push_core_type(copy);
                    }
                    let first = Box::new(args[0].clone());
                    a.set_nary_arrow_args(arity, args);
                    CoreTypeDesc::Ptyp_arrow(Box::new((first, ret, arity)))
                }
                None => {
                    let arg = type_arg(*arg, c, a)?;
                    CoreTypeDesc::Ptyp_arrow(Box::new((Box::new(arg), ret, arity)))
                }
            }
        }
        CoreTypeDesc::Ptyp_tuple(types) => {
            let types = a.type_list(types).to_vec();
            let types = types
                .into_iter()
                .map(|t| core_type(t, c, a))
                .collect::<R<Vec<_>>>()?;
            CoreTypeDesc::Ptyp_tuple(a.push_type_list(&types))
        }
        CoreTypeDesc::Ptyp_constr((lid, types)) => {
            let types = a.type_list(types).to_vec();
            let types = types
                .into_iter()
                .map(|t| core_type(t, c, a))
                .collect::<R<Vec<_>>>()?;
            CoreTypeDesc::Ptyp_constr((lid, a.push_type_list(&types)))
        }
        // `Otag (map_loc sub l, sub.attributes sub attrs, sub.typ sub t)`.
        CoreTypeDesc::Ptyp_object(inner) => {
            let (fields, closed) = *inner;
            let fields = fields
                .into_iter()
                .map(|field| {
                    Ok(match field {
                        ObjectField::Otag(label, attrs, t) => {
                            let t = core_type(t, c, a)?;
                            let attrs = attributes(attrs, c, a)?;
                            ObjectField::Otag(label, attrs, t)
                        }
                        ObjectField::Oinherit(t) => ObjectField::Oinherit(core_type(t, c, a)?),
                    })
                })
                .collect::<R<_>>()?;
            CoreTypeDesc::Ptyp_object(Box::new((fields, closed)))
        }
        CoreTypeDesc::Ptyp_alias(inner) => {
            let (t, name) = *inner;
            CoreTypeDesc::Ptyp_alias(Box::new((core_type(t, c, a)?, name)))
        }
        // `Rtag (map_loc sub l, sub.attributes sub attrs, b, List.map ...
        // groups)`: the groups, then the attributes.
        CoreTypeDesc::Ptyp_variant(inner) => {
            let (rows, closed, labels) = *inner;
            let rows = rows
                .into_iter()
                .map(|row| {
                    Ok(match row {
                        RowField::Rtag(label, attrs, empty, groups) => {
                            let groups = groups
                                .into_iter()
                                .map(|group| {
                                    Ok(Located {
                                        txt: group
                                            .txt
                                            .into_iter()
                                            .map(|t| core_type(t, c, a))
                                            .collect::<R<_>>()?,
                                        loc: group.loc,
                                    })
                                })
                                .collect::<R<_>>()?;
                            let attrs = attributes(attrs, c, a)?;
                            RowField::Rtag(label, attrs, empty, groups)
                        }
                        RowField::Rinherit(t) => RowField::Rinherit(core_type(t, c, a)?),
                    })
                })
                .collect::<R<_>>()?;
            CoreTypeDesc::Ptyp_variant(Box::new((rows, closed, labels)))
        }
        CoreTypeDesc::Ptyp_poly(inner) => {
            let (names, t) = *inner;
            CoreTypeDesc::Ptyp_poly(Box::new((names, core_type(t, c, a)?)))
        }
        CoreTypeDesc::Ptyp_package(inner) => {
            let (lid, constraints) = *inner;
            let constraints = constraints
                .into_iter()
                .map(|(name, t)| Ok((name, core_type(t, c, a)?)))
                .collect::<R<_>>()?;
            CoreTypeDesc::Ptyp_package(Box::new((lid, constraints)))
        }
        CoreTypeDesc::Ptyp_extension(ext) => {
            CoreTypeDesc::Ptyp_extension(Box::new(extension(*ext, c, a)?))
        }
        desc @ (CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_)) => desc,
    };
    Ok(a.push_core_type(CoreType {
        ptyp_desc,
        ptyp_loc: t.ptyp_loc,
        ptyp_attributes,
    }))
}

// ============================================================================
// Patterns (P.map, ast_mapper.ml:477-528)
// ============================================================================

fn pat_list(
    list: crate::parse_arena::PatList,
    c: &mut JsxConfig,
    a: &mut ParseArena,
) -> R<crate::parse_arena::PatList> {
    let items = a.pat_list(list).to_vec();
    let items = items
        .into_iter()
        .map(|p| pattern(p, c, a))
        .collect::<R<Vec<_>>>()?;
    Ok(a.push_pat_list(&items))
}

fn pattern(idx: PatIdx, c: &mut JsxConfig, a: &mut ParseArena) -> R<PatIdx> {
    if !pattern_may_change(idx, a, &mut c.unchanged_memo) {
        return Ok(idx);
    }
    let p = a.get_pat(idx).clone();
    let ppat_attributes = attributes(p.ppat_attributes, c, a)?;
    let ppat_desc = match p.ppat_desc {
        PatternDesc::Ppat_alias(inner, name) => {
            PatternDesc::Ppat_alias(pattern(inner, c, a)?, name)
        }
        PatternDesc::Ppat_tuple(items) => PatternDesc::Ppat_tuple(pat_list(items, c, a)?),
        PatternDesc::Ppat_array(items) => PatternDesc::Ppat_array(pat_list(items, c, a)?),
        PatternDesc::Ppat_construct(lid, args) => PatternDesc::Ppat_construct(
            lid,
            Located {
                txt: pat_list(args.txt, c, a)?,
                loc: args.loc,
            },
        ),
        PatternDesc::Ppat_variant(inner) => {
            let (label, args) = *inner;
            let args = Located {
                txt: pat_list(args.txt, c, a)?,
                loc: args.loc,
            };
            PatternDesc::Ppat_variant(Box::new((label, args)))
        }
        PatternDesc::Ppat_dict(entries) => PatternDesc::Ppat_dict(Box::new(
            entries
                .into_iter()
                .map(|entry| {
                    Ok(DictPatternEntry {
                        pdp_pattern: pattern(entry.pdp_pattern, c, a)?,
                        ..entry
                    })
                })
                .collect::<R<_>>()?,
        )),
        // `record ~loc ~attrs ?rest:(...) (List.map ... lpl) cf`: the fields,
        // then the rest's type.
        PatternDesc::Ppat_record(inner) => {
            let (fields, closed, rest) = *inner;
            let fields = a.pat_field_list(fields).to_vec();
            let fields = fields
                .into_iter()
                .map(|field| {
                    Ok(PatternRecordField {
                        pat: pattern(field.pat, c, a)?,
                        ..field
                    })
                })
                .collect::<R<Vec<_>>>()?;
            let fields = a.push_pat_field_list(&fields);
            let rest = match rest {
                Some(rest) => Some(RecordPatRest {
                    rest_type: match rest.rest_type {
                        Some(t) => Some(core_type(t, c, a)?),
                        None => None,
                    },
                    ..rest
                }),
                None => None,
            };
            PatternDesc::Ppat_record(Box::new((fields, closed, rest)))
        }
        PatternDesc::Ppat_or(p1, p2) => {
            let p2 = pattern(p2, c, a)?;
            let p1 = pattern(p1, c, a)?;
            PatternDesc::Ppat_or(p1, p2)
        }
        PatternDesc::Ppat_constraint(inner) => {
            let (p, t) = *inner;
            let t = core_type(t, c, a)?;
            let p = pattern(p, c, a)?;
            PatternDesc::Ppat_constraint(Box::new((p, t)))
        }
        PatternDesc::Ppat_exception(p) => PatternDesc::Ppat_exception(pattern(p, c, a)?),
        PatternDesc::Ppat_extension(ext) => {
            PatternDesc::Ppat_extension(Box::new(extension(*ext, c, a)?))
        }
        desc => desc,
    };
    Ok(a.push_pat(Pattern {
        ppat_desc,
        ppat_loc: p.ppat_loc,
        ppat_attributes,
    }))
}

// ============================================================================
// Expressions
// ============================================================================

pub(super) fn expr_idx(idx: ExprIdx, c: &mut JsxConfig, a: &mut ParseArena) -> R<ExprIdx> {
    if !subtree_may_change(idx, a, &mut c.unchanged_memo) {
        return Ok(idx);
    }
    let e = a.get_expr(idx).clone();
    let e = expr(e, c, a)?;
    Ok(a.push_expr(e))
}

fn opt_expr(e: Option<ExprIdx>, c: &mut JsxConfig, a: &mut ParseArena) -> R<Option<ExprIdx>> {
    match e {
        Some(e) => Ok(Some(expr_idx(e, c, a)?)),
        None => Ok(None),
    }
}

/// The JSX `expr` override (jsx_v4.ml:1315-1373): a JSX element at version 4
/// becomes a call (its attributes are passed on unmapped), anything else is
/// `default_mapper.expr`.
pub(super) fn expr(e: Expression, c: &mut JsxConfig, a: &mut ParseArena) -> R<Expression> {
    if !expression_may_change(&e, a, &mut c.unchanged_memo) {
        return Ok(e);
    }
    match e.pexp_desc {
        ExpressionDesc::Pexp_jsx_element(jsx) if c.version == 4 => {
            let pexp_desc = transform_jsx_element(*jsx, c, &e.pexp_loc, a)?;
            Ok(Expression {
                pexp_desc,
                pexp_loc: e.pexp_loc,
                pexp_attributes: e.pexp_attributes,
            })
        }
        _ => default_expr(e, c, a),
    }
}

fn expr_list(list: ExprList, c: &mut JsxConfig, a: &mut ParseArena) -> R<ExprList> {
    let items = a.expr_list(list).to_vec();
    let items = items
        .into_iter()
        .map(|e| expr_idx(e, c, a))
        .collect::<R<Vec<_>>>()?;
    Ok(a.push_expr_list(&items))
}

fn expr_vec(items: Vec<ExprIdx>, c: &mut JsxConfig, a: &mut ParseArena) -> R<Vec<ExprIdx>> {
    items.into_iter().map(|e| expr_idx(e, c, a)).collect()
}

/// `cases = List.map case`; `case` builds `{pc_bar; pc_lhs; pc_guard;
/// pc_rhs}`, evaluating the right-hand side, the guard, then the pattern.
fn cases(list: CaseList, c: &mut JsxConfig, a: &mut ParseArena) -> R<CaseList> {
    let items = a.case_list(list).to_vec();
    let items = items
        .into_iter()
        .map(|case| {
            let pc_rhs = expr_idx(case.pc_rhs, c, a)?;
            let pc_guard = opt_expr(case.pc_guard, c, a)?;
            let pc_lhs = pattern(case.pc_lhs, c, a)?;
            Ok(Case {
                pc_bar: case.pc_bar,
                pc_lhs,
                pc_guard,
                pc_rhs,
            })
        })
        .collect::<R<Vec<_>>>()?;
    Ok(a.push_case_list(&items))
}

/// `E.map` (ast_mapper.ml:317-471): the attributes, then the description,
/// its children right to left.
fn default_expr(e: Expression, c: &mut JsxConfig, a: &mut ParseArena) -> R<Expression> {
    let pexp_attributes = attributes(e.pexp_attributes, c, a)?;
    let pexp_desc = match e.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) => ExpressionDesc::Pexp_braces(PexpBraces {
            expr: expr_idx(braces.expr, c, a)?,
            braces_loc: braces.braces_loc,
        }),
        // `let_ ~loc ~attrs r (List.map (sub.value_binding sub) vbs) (sub.expr
        // sub e)`: the body, then the bindings.
        ExpressionDesc::Pexp_let((rec_flag, vbs, body)) => {
            let body = expr_idx(body, c, a)?;
            let vbs = a.vb_list(vbs).to_vec();
            let vbs = vbs
                .into_iter()
                .map(|vb| value_binding(vb, c, a))
                .collect::<R<Vec<_>>>()?;
            ExpressionDesc::Pexp_let((rec_flag, a.push_vb_list(&vbs), body))
        }
        ExpressionDesc::Pexp_fun(fun) => function(*fun, c, a)?,
        // `apply ~loc ~attrs ~partial ~transformed_jsx (sub.expr sub e)
        // (List.map (map_snd (sub.expr sub)) l)`: the arguments, then the
        // function.
        ExpressionDesc::Pexp_apply(apply) => {
            let args = a.apply_args(apply.args).to_vec();
            let args = args
                .into_iter()
                .map(|(label, arg)| Ok((label, expr_idx(arg, c, a)?)))
                .collect::<R<Vec<_>>>()?;
            let args = a.push_apply_args(&args);
            let funct = expr_idx(apply.funct, c, a)?;
            ExpressionDesc::Pexp_apply(PexpApply {
                funct,
                args,
                ..apply
            })
        }
        // `match_ ~loc ~attrs (sub.expr sub e) (sub.cases sub pel)`.
        ExpressionDesc::Pexp_match((scrutinee, case_list)) => {
            let case_list = cases(case_list, c, a)?;
            let scrutinee = expr_idx(scrutinee, c, a)?;
            ExpressionDesc::Pexp_match((scrutinee, case_list))
        }
        // `try_ ~loc ~attrs ?finally:(...) (sub.expr sub e) (sub.cases sub
        // pel)`: the cases, the body, then the finally block.
        ExpressionDesc::Pexp_try((body, case_list, finally)) => {
            let case_list = cases(case_list, c, a)?;
            let body = expr_idx(body, c, a)?;
            let finally = opt_expr(finally, c, a)?;
            ExpressionDesc::Pexp_try((body, case_list, finally))
        }
        ExpressionDesc::Pexp_tuple(items) => ExpressionDesc::Pexp_tuple(expr_list(items, c, a)?),
        ExpressionDesc::Pexp_array(items) => ExpressionDesc::Pexp_array(expr_list(items, c, a)?),
        ExpressionDesc::Pexp_construct(lid, args) => ExpressionDesc::Pexp_construct(
            lid,
            Located {
                txt: expr_list(args.txt, c, a)?,
                loc: args.loc,
            },
        ),
        ExpressionDesc::Pexp_variant(inner) => {
            let (label, args) = *inner;
            let args = Located {
                txt: expr_list(args.txt, c, a)?,
                loc: args.loc,
            };
            ExpressionDesc::Pexp_variant(Box::new((label, args)))
        }
        // `record ~loc ~attrs (List.map ... l) (map_opt (sub.expr sub) eo)`:
        // the spread, then the fields.
        ExpressionDesc::Pexp_record((fields, spread)) => {
            let spread = opt_expr(spread, c, a)?;
            let fields = a.expr_field_list(fields).to_vec();
            let fields = fields
                .into_iter()
                .map(|field| {
                    Ok(ExpressionRecordField {
                        expr: expr_idx(field.expr, c, a)?,
                        ..field
                    })
                })
                .collect::<R<Vec<_>>>()?;
            ExpressionDesc::Pexp_record((a.push_expr_field_list(&fields), spread))
        }
        ExpressionDesc::Pexp_field(target, lid) => {
            ExpressionDesc::Pexp_field(expr_idx(target, c, a)?, lid)
        }
        ExpressionDesc::Pexp_setfield(inner) => {
            let (target, lid, value) = *inner;
            let value = expr_idx(value, c, a)?;
            let target = expr_idx(target, c, a)?;
            ExpressionDesc::Pexp_setfield(Box::new((target, lid, value)))
        }
        ExpressionDesc::Pexp_dict(entries) => ExpressionDesc::Pexp_dict(Box::new(
            entries
                .into_iter()
                .map(|entry| {
                    Ok(match entry {
                        DictEntry::Pdict_entry(key, e) => {
                            DictEntry::Pdict_entry(key, expr_idx(e, c, a)?)
                        }
                        DictEntry::Pdict_spread(e) => DictEntry::Pdict_spread(expr_idx(e, c, a)?),
                    })
                })
                .collect::<R<_>>()?,
        )),
        ExpressionDesc::Pexp_spread(kind, elements) => {
            let elements = a.spread_element_list(elements).to_vec();
            let elements = elements
                .into_iter()
                .map(|element| {
                    Ok(match element {
                        SpreadElement::Pspread_item(e) => {
                            SpreadElement::Pspread_item(expr_idx(e, c, a)?)
                        }
                        SpreadElement::Pspread(e) => SpreadElement::Pspread(expr_idx(e, c, a)?),
                    })
                })
                .collect::<R<Vec<_>>>()?;
            ExpressionDesc::Pexp_spread(kind, a.push_spread_element_list(&elements))
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (cond, then_, else_) = *inner;
            let else_ = opt_expr(else_, c, a)?;
            let then_ = expr_idx(then_, c, a)?;
            let cond = expr_idx(cond, c, a)?;
            ExpressionDesc::Pexp_ifthenelse(Box::new((cond, then_, else_)))
        }
        ExpressionDesc::Pexp_ternary(inner) => {
            let (cond, consequent, alternate) = *inner;
            let alternate = expr_idx(alternate, c, a)?;
            let consequent = expr_idx(consequent, c, a)?;
            let cond = expr_idx(cond, c, a)?;
            ExpressionDesc::Pexp_ternary(Box::new((cond, consequent, alternate)))
        }
        ExpressionDesc::Pexp_sequence(first, second) => {
            let second = expr_idx(second, c, a)?;
            let first = expr_idx(first, c, a)?;
            ExpressionDesc::Pexp_sequence(first, second)
        }
        ExpressionDesc::Pexp_while(cond, body) => {
            let body = expr_idx(body, c, a)?;
            let cond = expr_idx(cond, c, a)?;
            ExpressionDesc::Pexp_while(cond, body)
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (pat, start, finish, dir, body) = *inner;
            let body = expr_idx(body, c, a)?;
            let finish = expr_idx(finish, c, a)?;
            let start = expr_idx(start, c, a)?;
            let pat = pattern(pat, c, a)?;
            ExpressionDesc::Pexp_for(Box::new((pat, start, finish, dir, body)))
        }
        ExpressionDesc::Pexp_for_of(inner) => {
            let (pat, iterable, body) = *inner;
            let body = expr_idx(body, c, a)?;
            let iterable = expr_idx(iterable, c, a)?;
            let pat = pattern(pat, c, a)?;
            ExpressionDesc::Pexp_for_of(Box::new((pat, iterable, body)))
        }
        ExpressionDesc::Pexp_for_await_of(inner) => {
            let (pat, iterable, body) = *inner;
            let body = expr_idx(body, c, a)?;
            let iterable = expr_idx(iterable, c, a)?;
            let pat = pattern(pat, c, a)?;
            ExpressionDesc::Pexp_for_await_of(Box::new((pat, iterable, body)))
        }
        // `Exp.template ~loc ~attrs (List.map ...) (List.map (sub.expr sub) values)`.
        ExpressionDesc::Pexp_template(mut template) => {
            template.values = expr_vec(template.values, c, a)?;
            ExpressionDesc::Pexp_template(template)
        }
        // `Exp.tagged_template ~loc ~attrs (sub.expr sub tag) ... values`: the
        // values, then the tag.
        ExpressionDesc::Pexp_tagged_template(mut template) => {
            template.values = expr_vec(template.values, c, a)?;
            template.tag = expr_idx(template.tag, c, a)?;
            ExpressionDesc::Pexp_tagged_template(template)
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (e, from, to) = *inner;
            let to = core_type(to, c, a)?;
            let from = match from {
                Some(t) => Some(core_type(t, c, a)?),
                None => None,
            };
            let e = expr_idx(e, c, a)?;
            ExpressionDesc::Pexp_coerce(Box::new((e, from, to)))
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (e, t) = *inner;
            let t = core_type(t, c, a)?;
            let e = expr_idx(e, c, a)?;
            ExpressionDesc::Pexp_constraint(Box::new((e, t)))
        }
        ExpressionDesc::Pexp_object_get(inner) => {
            let (e, name) = *inner;
            ExpressionDesc::Pexp_object_get(Box::new((expr_idx(e, c, a)?, name)))
        }
        ExpressionDesc::Pexp_object_set(inner) => {
            let (e, name, value) = *inner;
            let value = expr_idx(value, c, a)?;
            let e = expr_idx(e, c, a)?;
            ExpressionDesc::Pexp_object_set(Box::new((e, name, value)))
        }
        ExpressionDesc::Pexp_object_literal(fields) => {
            ExpressionDesc::Pexp_object_literal(Box::new(
                fields
                    .into_iter()
                    .map(|(name, e)| Ok((name, expr_idx(e, c, a)?)))
                    .collect::<R<_>>()?,
            ))
        }
        // `letmodule ~loc ~attrs (map_loc sub s) (sub.module_expr sub me)
        // (sub.expr sub e)`: the body, then the module.
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (name, me, body) = *inner;
            let body = expr_idx(body, c, a)?;
            let me = module_expr_idx(me, c, a)?;
            ExpressionDesc::Pexp_letmodule(Box::new((name, me, body)))
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (ec, body) = *inner;
            let body = expr_idx(body, c, a)?;
            let ec = extension_constructor(ec, c, a)?;
            ExpressionDesc::Pexp_letexception(Box::new((ec, body)))
        }
        ExpressionDesc::Pexp_assert(e) => ExpressionDesc::Pexp_assert(expr_idx(e, c, a)?),
        ExpressionDesc::Pexp_await(e) => ExpressionDesc::Pexp_await(expr_idx(e, c, a)?),
        ExpressionDesc::Pexp_newtype(inner) => {
            let (name, body) = *inner;
            ExpressionDesc::Pexp_newtype(Box::new((name, expr_idx(body, c, a)?)))
        }
        ExpressionDesc::Pexp_pack(me) => ExpressionDesc::Pexp_pack(module_expr_idx(me, c, a)?),
        ExpressionDesc::Pexp_open(inner) => {
            let (flag, lid, e) = *inner;
            ExpressionDesc::Pexp_open(Box::new((flag, lid, expr_idx(e, c, a)?)))
        }
        ExpressionDesc::Pexp_extension(ext) => {
            ExpressionDesc::Pexp_extension(Box::new(extension(*ext, c, a)?))
        }
        ExpressionDesc::Pexp_jsx_element(jsx) => {
            ExpressionDesc::Pexp_jsx_element(Box::new(jsx_element(*jsx, c, a)?))
        }
        // `todo ~loc ~attrs ~name_loc (Option.map (sub.expr sub) message)`.
        ExpressionDesc::Pexp_todo(todo) => ExpressionDesc::Pexp_todo(PexpTodo {
            name_loc: todo.name_loc,
            message: todo
                .message
                .map(|message| expr_idx(message, c, a))
                .transpose()?,
        }),
        desc @ (ExpressionDesc::Pexp_ident(_)
        | ExpressionDesc::Pexp_constant(_)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue
        | ExpressionDesc::Pexp_regexp(_)
        | ExpressionDesc::Pexp_raw(_)) => desc,
    };
    Ok(Expression {
        pexp_desc,
        pexp_loc: e.pexp_loc,
        pexp_attributes,
    })
}

/// `Pexp_fun` (ast_mapper.ml:329-344): `fun_ ~loc ~attrs ~async ~newtypes
/// params body` maps the body, the parameters left to right (each
/// `{param with p_default; p_pat}` maps the pattern, then the default), then
/// the newtypes' attributes. The parameters of a function the parser grouped
/// are kept beside the first parameter's pattern; a function given as nested
/// `Pexp_fun` nodes (from a PPX) holds them in that chain.
fn function(fun: PexpFun, c: &mut JsxConfig, a: &mut ParseArena) -> R<ExpressionDesc> {
    let params = a.nary_fun_params(&fun).into_owned();
    let body = a.nary_fun_body(&fun);
    let newtypes = a.nary_fun_newtypes(&fun).to_vec();
    let grouped = a.stored_nary_fun_params(&fun).is_some() && a.get_arity(fun.arity).is_some();
    let unknown_arity = a.nary_fun_unknown_arity(&fun);
    // The nested nodes of a chain, outermost first.
    let mut chain = Vec::new();
    if !grouped {
        let mut next = fun.rhs;
        while chain.len() + 1 < params.len() {
            chain.push(next);
            let ExpressionDesc::Pexp_fun(inner) = &a.get_expr(next).pexp_desc else {
                break;
            };
            next = inner.rhs;
        }
    }

    let body = expr_idx(body, c, a)?;
    let mut params = params
        .into_iter()
        .map(|param| {
            let p_pat = pattern(param.p_pat, c, a)?;
            let p_default = opt_expr(param.p_default, c, a)?;
            Ok(FunParam {
                p_pat,
                p_default,
                ..param
            })
        })
        .collect::<R<Vec<_>>>()?;
    let newtypes = newtypes
        .into_iter()
        .map(|(name, attrs)| Ok((name, attributes(attrs, c, a)?)))
        .collect::<R<Vec<_>>>()?;

    // Tables keyed by the first parameter's pattern: give the rebuilt
    // function its own key.
    if params[0].p_pat == fun.lhs {
        let copy = a.get_pat(fun.lhs).clone();
        params[0].p_pat = a.push_pat(copy);
    }
    let first = params[0].clone();
    if !newtypes.is_empty() {
        a.set_nary_fun_newtypes(first.p_pat, newtypes);
    }
    let rhs = if grouped {
        a.set_nary_fun_params(fun.arity, params, unknown_arity);
        body
    } else {
        // Rebuild the chain from the innermost node out.
        let mut rhs = body;
        for (node, param) in chain.iter().zip(params.iter().skip(1)).rev() {
            let mut inner = a.get_expr(*node).clone();
            if let ExpressionDesc::Pexp_fun(inner_fun) = &mut inner.pexp_desc {
                inner_fun.lhs = param.p_pat;
                inner_fun.default = param.p_default;
                inner_fun.rhs = rhs;
            }
            rhs = a.push_expr(inner);
        }
        rhs
    };
    Ok(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
        default: first.p_default,
        lhs: first.p_pat,
        rhs,
        ..fun
    })))
}

/// `default_mapper.expr` on a JSX element (ast_mapper.ml:446-471): a
/// fragment's children, a unary element's props, a container's children and
/// then its props (the arguments of `jsx_container_element` are evaluated
/// right to left).
fn jsx_element(jsx: JsxElement, c: &mut JsxConfig, a: &mut ParseArena) -> R<JsxElement> {
    let props = |props: Vec<JsxProp>, c: &mut JsxConfig, a: &mut ParseArena| {
        props
            .into_iter()
            .map(|prop| {
                Ok(match prop {
                    JsxProp::Value {
                        name,
                        optional,
                        value,
                    } => JsxProp::Value {
                        name,
                        optional,
                        value: expr_idx(value, c, a)?,
                    },
                    JsxProp::Spreading { loc, expr } => JsxProp::Spreading {
                        loc,
                        expr: expr_idx(expr, c, a)?,
                    },
                    punning @ JsxProp::Punning { .. } => punning,
                })
            })
            .collect::<R<Vec<_>>>()
    };
    Ok(match jsx {
        JsxElement::Fragment(fragment) => JsxElement::Fragment(JsxFragment {
            children: expr_vec(fragment.children, c, a)?,
            ..fragment
        }),
        JsxElement::Unary(unary) => JsxElement::Unary(JsxUnaryElement {
            props: props(unary.props, c, a)?,
            ..unary
        }),
        JsxElement::Container(container) => {
            let new_children = expr_vec(container.children, c, a)?;
            let new_props = props(container.props, c, a)?;
            JsxElement::Container(JsxContainerElement {
                props: new_props,
                children: new_children,
                ..container
            })
        }
    })
}

// ============================================================================
// What the mapper may change
// ============================================================================
//
// The mapper rebuilds a node only when it, or something below it, holds a
// JSX element, a module expression, an extension, or an attribute payload
// other than a plain expression; anything else maps to itself without a
// side effect. Expressions are memoized by index (0 unknown, 1 unchanged,
// 2 may change).

fn attributes_may_change(attrs: &Attributes, a: &ParseArena, memo: &mut Vec<u8>) -> bool {
    attrs.iter().any(|(_, p)| payload_may_change(p, a, memo))
}

fn payload_may_change(p: &Payload, a: &ParseArena, memo: &mut Vec<u8>) -> bool {
    match p {
        // An empty structure, or one of plain expressions, maps to itself
        // (the component transform leaves `Pstr_eval` alone).
        Payload::PStr(items) => items.iter().any(|item| match &item.pstr_desc {
            StructureItemDesc::Pstr_eval(inner) => {
                subtree_may_change(inner.0, a, memo) || attributes_may_change(&inner.1, a, memo)
            }
            _ => true,
        }),
        Payload::PSig(items) => !items.is_empty(),
        Payload::PTyp(t) => type_may_change(*t, a, memo),
        Payload::PPat(inner) => {
            pattern_may_change(inner.0, a, memo)
                || inner.1.is_some_and(|g| subtree_may_change(g, a, memo))
        }
    }
}

fn type_may_change(idx: CoreTypeIdx, a: &ParseArena, memo: &mut Vec<u8>) -> bool {
    let t = a.get_core_type(idx);
    if attributes_may_change(&t.ptyp_attributes, a, memo) {
        return true;
    }
    let ty = |t: CoreTypeIdx, memo: &mut Vec<u8>| type_may_change(t, a, memo);
    match &t.ptyp_desc {
        CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) => false,
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (arg, ret, arity) = &**inner;
            ty(*ret, memo)
                || a.nary_arrow_args(arg, *arity)
                    .iter()
                    .any(|targ| targ.fixed.is_none() && ty(targ.typ, memo))
        }
        CoreTypeDesc::Ptyp_tuple(types) | CoreTypeDesc::Ptyp_constr((_, types)) => {
            a.type_list(*types).iter().any(|t| ty(*t, memo))
        }
        CoreTypeDesc::Ptyp_object(inner) => inner.0.iter().any(|field| match field {
            ObjectField::Otag(_, attrs, t) => attributes_may_change(attrs, a, memo) || ty(*t, memo),
            ObjectField::Oinherit(t) => ty(*t, memo),
        }),
        CoreTypeDesc::Ptyp_alias(inner) => ty(inner.0, memo),
        CoreTypeDesc::Ptyp_variant(inner) => inner.0.iter().any(|row| match row {
            RowField::Rtag(_, attrs, _, groups) => {
                attributes_may_change(attrs, a, memo)
                    || groups.iter().any(|g| g.txt.iter().any(|t| ty(*t, memo)))
            }
            RowField::Rinherit(t) => ty(*t, memo),
        }),
        CoreTypeDesc::Ptyp_poly(inner) => ty(inner.1, memo),
        CoreTypeDesc::Ptyp_package(inner) => inner.1.iter().any(|(_, t)| ty(*t, memo)),
        CoreTypeDesc::Ptyp_extension(_) => true,
    }
}

fn pattern_may_change(idx: PatIdx, a: &ParseArena, memo: &mut Vec<u8>) -> bool {
    let p = a.get_pat(idx);
    if attributes_may_change(&p.ppat_attributes, a, memo) {
        return true;
    }
    let pat = |p: PatIdx, memo: &mut Vec<u8>| pattern_may_change(p, a, memo);
    match &p.ppat_desc {
        PatternDesc::Ppat_any
        | PatternDesc::Ppat_var(_)
        | PatternDesc::Ppat_constant(_)
        | PatternDesc::Ppat_interval(_)
        | PatternDesc::Ppat_type(_)
        | PatternDesc::Ppat_variant_spread(_)
        | PatternDesc::Ppat_unpack(_) => false,
        PatternDesc::Ppat_alias(p, _) | PatternDesc::Ppat_exception(p) => pat(*p, memo),
        PatternDesc::Ppat_tuple(items) | PatternDesc::Ppat_array(items) => {
            a.pat_list(*items).iter().any(|p| pat(*p, memo))
        }
        PatternDesc::Ppat_construct(_, args) => a.pat_list(args.txt).iter().any(|p| pat(*p, memo)),
        PatternDesc::Ppat_variant(inner) => a.pat_list(inner.1.txt).iter().any(|p| pat(*p, memo)),
        PatternDesc::Ppat_dict(entries) => entries.iter().any(|e| pat(e.pdp_pattern, memo)),
        PatternDesc::Ppat_record(inner) => {
            a.pat_field_list(inner.0).iter().any(|f| pat(f.pat, memo))
                || inner
                    .2
                    .as_ref()
                    .and_then(|rest| rest.rest_type)
                    .is_some_and(|t| type_may_change(t, a, memo))
        }
        PatternDesc::Ppat_or(p1, p2) => pat(*p1, memo) || pat(*p2, memo),
        PatternDesc::Ppat_constraint(inner) => {
            pat(inner.0, memo) || type_may_change(inner.1, a, memo)
        }
        PatternDesc::Ppat_extension(_) => true,
    }
}

fn component_may_change(
    component: Option<&JsxComponent>,
    a: &ParseArena,
    memo: &mut Vec<u8>,
) -> bool {
    matches!(
        component.map(|c| &c.pjc_kind),
        Some(JsxComponentKind::Labelled(Some(t))) if type_may_change(*t, a, memo)
    )
}

fn value_binding_may_change(vb: &ValueBinding, a: &ParseArena, memo: &mut Vec<u8>) -> bool {
    subtree_may_change(vb.pvb_expr, a, memo)
        || pattern_may_change(vb.pvb_pat, a, memo)
        || attributes_may_change(&vb.pvb_attributes, a, memo)
        || component_may_change(vb.pvb_jsx_component.as_deref(), a, memo)
        || a.value_constraint(vb.pvb_pat)
            .is_some_and(|vc| type_may_change(vc.pvc_type, a, memo))
}

fn cases_may_change(list: CaseList, a: &ParseArena, memo: &mut Vec<u8>) -> bool {
    a.case_list(list).iter().any(|case| {
        subtree_may_change(case.pc_rhs, a, memo)
            || case
                .pc_guard
                .is_some_and(|g| subtree_may_change(g, a, memo))
            || pattern_may_change(case.pc_lhs, a, memo)
    })
}

/// Whether the mapper may rewrite `e` or its subtree.
pub(super) fn expression_may_change(e: &Expression, a: &ParseArena, memo: &mut Vec<u8>) -> bool {
    if attributes_may_change(&e.pexp_attributes, a, memo) {
        return true;
    }
    let child = |idx: ExprIdx, memo: &mut Vec<u8>| subtree_may_change(idx, a, memo);
    match &e.pexp_desc {
        ExpressionDesc::Pexp_ident(_)
        | ExpressionDesc::Pexp_constant(_)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue
        | ExpressionDesc::Pexp_regexp(_)
        | ExpressionDesc::Pexp_raw(_) => false,
        ExpressionDesc::Pexp_todo(todo) => todo.message.is_some_and(|message| child(message, memo)),
        ExpressionDesc::Pexp_let(inner) => {
            child(inner.2, memo)
                || a.vb_list(inner.1)
                    .iter()
                    .any(|vb| value_binding_may_change(vb, a, memo))
        }
        ExpressionDesc::Pexp_fun(fun) => {
            child(a.nary_fun_body(fun), memo)
                || a.nary_fun_params(fun).iter().any(|param| {
                    pattern_may_change(param.p_pat, a, memo)
                        || param.p_default.is_some_and(|d| child(d, memo))
                })
                || a.nary_fun_newtypes(fun)
                    .iter()
                    .any(|(_, attrs)| attributes_may_change(attrs, a, memo))
        }
        ExpressionDesc::Pexp_apply(apply) => {
            child(apply.funct, memo)
                || a.apply_args(apply.args)
                    .iter()
                    .any(|(_, arg)| child(*arg, memo))
        }
        ExpressionDesc::Pexp_match((scrutinee, case_list)) => {
            child(*scrutinee, memo) || cases_may_change(*case_list, a, memo)
        }
        ExpressionDesc::Pexp_try((body, case_list, finally)) => {
            child(*body, memo)
                || cases_may_change(*case_list, a, memo)
                || finally.is_some_and(|f| child(f, memo))
        }
        ExpressionDesc::Pexp_template(template) => {
            template.values.iter().any(|item| child(*item, memo))
        }
        ExpressionDesc::Pexp_tagged_template(template) => {
            child(template.tag, memo) || template.values.iter().any(|item| child(*item, memo))
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
            a.expr_list(*items).iter().any(|item| child(*item, memo))
        }
        ExpressionDesc::Pexp_dict(entries) => entries.iter().any(|entry| match entry {
            DictEntry::Pdict_entry(_, e) | DictEntry::Pdict_spread(e) => child(*e, memo),
        }),
        ExpressionDesc::Pexp_spread(_, elements) => a
            .spread_element_list(*elements)
            .iter()
            .any(|element| child(element.expr(), memo)),
        ExpressionDesc::Pexp_construct(_, args) => {
            a.expr_list(args.txt).iter().any(|arg| child(*arg, memo))
        }
        ExpressionDesc::Pexp_variant(inner) => {
            a.expr_list(inner.1.txt).iter().any(|arg| child(*arg, memo))
        }
        ExpressionDesc::Pexp_record(inner) => {
            a.expr_field_list(inner.0)
                .iter()
                .any(|field| child(field.expr, memo))
                || inner.1.is_some_and(|spread| child(spread, memo))
        }
        ExpressionDesc::Pexp_field(target, _) => child(*target, memo),
        ExpressionDesc::Pexp_setfield(inner) => child(inner.0, memo) || child(inner.2, memo),
        ExpressionDesc::Pexp_object_get(inner) => child(inner.0, memo),
        ExpressionDesc::Pexp_object_set(inner) => child(inner.0, memo) || child(inner.2, memo),
        ExpressionDesc::Pexp_object_literal(fields) => fields.iter().any(|(_, e)| child(*e, memo)),
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            child(inner.0, memo)
                || child(inner.1, memo)
                || inner.2.is_some_and(|else_| child(else_, memo))
        }
        ExpressionDesc::Pexp_ternary(inner) => {
            child(inner.0, memo) || child(inner.1, memo) || child(inner.2, memo)
        }
        ExpressionDesc::Pexp_braces(braces) => child(braces.expr, memo),
        ExpressionDesc::Pexp_sequence(first, second)
        | ExpressionDesc::Pexp_while(first, second) => child(*first, memo) || child(*second, memo),
        ExpressionDesc::Pexp_for(inner) => {
            pattern_may_change(inner.0, a, memo)
                || child(inner.1, memo)
                || child(inner.2, memo)
                || child(inner.4, memo)
        }
        ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
            pattern_may_change(inner.0, a, memo) || child(inner.1, memo) || child(inner.2, memo)
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            child(inner.0, memo) || type_may_change(inner.1, a, memo)
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            child(inner.0, memo)
                || inner.1.is_some_and(|t| type_may_change(t, a, memo))
                || type_may_change(inner.2, a, memo)
        }
        ExpressionDesc::Pexp_assert(inner) | ExpressionDesc::Pexp_await(inner) => {
            child(*inner, memo)
        }
        ExpressionDesc::Pexp_newtype(inner) => child(inner.1, memo),
        ExpressionDesc::Pexp_open(inner) => child(inner.2, memo),
        ExpressionDesc::Pexp_jsx_element(_)
        | ExpressionDesc::Pexp_letmodule(_)
        | ExpressionDesc::Pexp_letexception(_)
        | ExpressionDesc::Pexp_pack(_)
        | ExpressionDesc::Pexp_extension(_) => true,
    }
}

pub(super) fn subtree_may_change(idx: ExprIdx, a: &ParseArena, memo: &mut Vec<u8>) -> bool {
    let slot = idx.0 as usize;
    if let Some(&known) = memo.get(slot)
        && known != 0
    {
        return known == 2;
    }
    let may_change = expression_may_change(a.get_expr(idx), a, memo);
    if slot >= memo.len() {
        memo.resize(slot + 1, 0);
    }
    memo[slot] = if may_change { 2 } else { 1 };
    may_change
}
