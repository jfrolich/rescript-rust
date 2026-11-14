//! Lazy qualified module components, matching OCaml's EnvLazy backbone.
//!
//! OCaml memoizes `components_of_module_maker (env, sub, path, mty)` and then
//! answers repeated type/module/value lookups from that cached view. Rust used
//! to cache only copied signatures and still re-scan or re-copy declarations on
//! each lookup. This module provides the cached qualified view that the hot
//! module-resolution paths use as their source of truth.

use crate::fast_hash::AHashMap as HashMap;
use crate::types::path::PathView;
use std::cell::{OnceCell, RefCell};
use std::rc::Rc;
use std::sync::Arc;

use crate::ident::Ident;

use super::decl::{
    ConstructorDescription, ConstructorKind, LabelDescription, ModtypeDeclaration,
    ModuleDeclaration, ModuleType, Signature, SignatureItem, TypeDeclaration, ValueDescription,
    ValueKind,
};
use super::path::Path;

/// Name index of one signature's component tables.
///
/// OCaml compiler/ml/env.ml:1530-1578 fills `comp_values`, `comp_types` and
/// `comp_modules` from the signature items in order, so later same-name items
/// shadow earlier ones. The index depends only on the item list, so it is
/// computed once per signature and shared by every component table built from
/// it, instead of rebuilding three string-keyed maps on each build.
#[derive(Debug, Default)]
pub(crate) struct SignatureIndex {
    values: HashMap<smol_str::SmolStr, (usize, usize)>,
    types: HashMap<smol_str::SmolStr, usize>,
    /// By name: item index, runtime position, and ordinal among the module
    /// items (the index of the module's cell in a view's child table).
    modules: HashMap<smol_str::SmolStr, (usize, usize, u32)>,
    /// By ordinal among the module items: item index and runtime position.
    module_items: Vec<(u32, u32)>,
    /// Alias/ident module items, as (item index, runtime position), in order.
    alias_modules: Vec<(usize, usize)>,
    /// Module type items, in order.
    modtypes: Vec<usize>,
    /// By name: the module type item a lookup of the name reaches.
    modtype_names: HashMap<smol_str::SmolStr, usize>,
}

impl SignatureIndex {
    /// (item index, runtime position) of the value a lookup of `name`
    /// reaches. One hash probe.
    #[inline]
    pub(crate) fn value(&self, name: &str) -> Option<(usize, usize)> {
        self.values.get(name).copied()
    }

    /// Item index of the type a lookup of `name` reaches. One hash probe.
    #[inline]
    pub(crate) fn type_item(&self, name: &str) -> Option<usize> {
        self.types.get(name).copied()
    }

    /// (item index, runtime position) of the module a lookup of `name`
    /// reaches. One hash probe.
    #[inline]
    pub(crate) fn module(&self, name: &str) -> Option<(usize, usize)> {
        self.modules
            .get(name)
            .map(|&(idx, runtime_pos, _)| (idx, runtime_pos))
    }

    /// (item index, runtime position, ordinal among the module items) of the
    /// module a lookup of `name` reaches. One hash probe.
    #[inline]
    pub(crate) fn module_cell(&self, name: &str) -> Option<(usize, usize, usize)> {
        self.modules
            .get(name)
            .map(|&(idx, runtime_pos, ordinal)| (idx, runtime_pos, ordinal as usize))
    }

    /// Number of module items, shadowed ones included.
    #[inline]
    pub(crate) fn module_count(&self) -> usize {
        self.module_items.len()
    }

    /// (item index, runtime position) of the module item with `ordinal`.
    /// One read of a table indexed by the ordinal.
    #[inline]
    pub(crate) fn module_item(&self, ordinal: usize) -> (usize, usize) {
        let (idx, runtime_pos) = self.module_items[ordinal];
        (idx as usize, runtime_pos as usize)
    }

    /// Item index of the module type a lookup of `name` reaches. One hash
    /// probe.
    #[inline]
    pub(crate) fn modtype_item(&self, name: &str) -> Option<usize> {
        self.modtype_names.get(name).copied()
    }

    /// Number of child modules whose type is a path.
    #[inline]
    pub(crate) fn alias_module_count(&self) -> usize {
        self.alias_modules.len()
    }

    pub(crate) fn build(signature: &Signature) -> Self {
        // Size the tables up front: a signature is indexed once, and growing
        // three maps item by item rehashed each of them several times.
        let (mut values, mut types, mut modules) = (0, 0, 0);
        for item in signature.iter() {
            match item {
                SignatureItem::SigValue(..) => values += 1,
                SignatureItem::SigType(..) => types += 1,
                SignatureItem::SigModule(..) => modules += 1,
                _ => {}
            }
        }
        let mut index = SignatureIndex {
            values: HashMap::with_capacity(values),
            types: HashMap::with_capacity(types),
            modules: HashMap::with_capacity(modules),
            module_items: Vec::with_capacity(modules),
            ..SignatureIndex::default()
        };
        let mut runtime_pos = 0usize;
        for (idx, item) in signature.iter().enumerate() {
            match item {
                SignatureItem::SigValue(id, desc) => {
                    index
                        .values
                        .insert(smol_str::SmolStr::new_static(id.name()), (idx, runtime_pos));
                    if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                        runtime_pos += 1;
                    }
                }
                SignatureItem::SigType(id, _, _) => {
                    index
                        .types
                        .insert(smol_str::SmolStr::new_static(id.name()), idx);
                }
                SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                    runtime_pos += 1;
                }
                SignatureItem::SigModule(id, md, _) => {
                    if matches!(
                        md.md_type,
                        ModuleType::MtyAlias(_, _) | ModuleType::MtyIdent(_)
                    ) {
                        index.alias_modules.push((idx, runtime_pos));
                    }
                    index.modules.insert(
                        smol_str::SmolStr::new_static(id.name()),
                        (idx, runtime_pos, index.module_items.len() as u32),
                    );
                    index.module_items.push((idx as u32, runtime_pos as u32));
                    runtime_pos += 1;
                }
                SignatureItem::SigModtype(id, _) => {
                    index.modtypes.push(idx);
                    index
                        .modtype_names
                        .insert(smol_str::SmolStr::new_static(id.name()), idx);
                }
                SignatureItem::SigClassType => {}
            }
        }
        index
    }
}

/// In a store build, poison the build unless every type node reachable from
/// `signature` is store-resident: a view built from, say, the current unit's
/// in-memory signature is only valid in this compilation even though building
/// the view itself reads no type node.
fn check_signature_store_resident(signature: &[SignatureItem], ctx: &super::context::TypeContext) {
    if !ctx.in_store_build() {
        return;
    }
    fn module_type_roots(mty: &ModuleType, roots: &mut Vec<super::type_expr::TypeExprRef>) {
        match mty {
            ModuleType::MtySignature(items) => signature_roots(items, roots),
            ModuleType::MtyFunctor {
                param_type, result, ..
            } => {
                if let Some(param_type) = param_type {
                    module_type_roots(param_type, roots);
                }
                module_type_roots(result, roots);
            }
            ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        }
    }
    fn signature_roots(items: &[SignatureItem], roots: &mut Vec<super::type_expr::TypeExprRef>) {
        for item in items {
            match item {
                SignatureItem::SigValue(_, desc) => roots.push(desc.val_type),
                SignatureItem::SigType(_, decl, _) => {
                    roots.extend(decl.type_params.iter().copied());
                    roots.extend(decl.type_manifest);
                    super::btype::iter_type_expr_kind(&decl.type_kind, |ty| roots.push(ty));
                }
                SignatureItem::SigTypext(_, ext, _) => {
                    roots.extend(ext.ext_type_params.iter().copied());
                    super::btype::iter_type_expr_cstr_args(&ext.ext_args, |ty| roots.push(ty));
                    roots.extend(ext.ext_ret_type);
                }
                SignatureItem::SigModule(_, md, _) => module_type_roots(&md.md_type, roots),
                SignatureItem::SigModtype(_, mtd) => {
                    if let Some(mty) = &mtd.mtd_type {
                        module_type_roots(mty, roots);
                    }
                }
                SignatureItem::SigClass | SignatureItem::SigClassType => {}
            }
        }
    }
    let mut stack = Vec::new();
    signature_roots(signature, &mut stack);
    let mut seen = super::type_marks::visit_set();
    while let Some(ty) = stack.pop() {
        if !ty.is_store() {
            ctx.poison_store_build_for("unit-signature");
            return;
        }
        if seen.visit(ty) {
            super::btype::iter_type_expr(ctx, ty, |child| stack.push(child));
        }
    }
}

fn path_non_apply_root_is_persistent_or_global(path: &Path) -> bool {
    fn root_ident(path: &Path) -> Option<&Ident> {
        match path.view() {
            PathView::Pident(id) => Some(id),
            PathView::Pdot(prefix, _, _) => root_ident(prefix),
            PathView::Papply(_, _) => None,
        }
    }

    root_ident(path).is_some_and(|id| id.is_persistent() || id.stamp() == 0)
}

/// OCaml builds `comp_constrs` from the declarations after `prefix_idents`
/// and `Subst.type_declaration` (env.ml:1530-1547), so a component reached
/// through a module alias sees its own unit's types rooted at the component.
/// The descriptions here come from the unit's signature; re-root the ones that
/// still mention the alias source, copying their types like `Subst.type_expr`.
fn reroot_constructor_descriptions(
    descs: &mut [ConstructorDescription],
    signature: &[SignatureItem],
    access_path: &Path,
    ctx: &super::context::TypeContext,
) {
    let _ = signature;
    let prefixes = crate::cmi::persistent_env::alias_reroot_prefixes(access_path, ctx);
    if prefixes.is_empty() {
        return;
    }
    let mentions = |ty: super::type_expr::TypeExprRef| {
        crate::cmi::persistent_env::type_expr_mentions_path_prefixes(ty, &prefixes, ctx)
    };
    let map_path = crate::cmi::persistent_env::reroot_path_mapper(&prefixes, ctx);
    for desc in descs.iter_mut() {
        if !(desc.cstr_args.iter().any(|t| mentions(*t))
            || desc.cstr_existentials.iter().any(|t| mentions(*t))
            || mentions(desc.cstr_res))
        {
            continue;
        }
        let mut cache = super::type_expr::TypeExprRefMap::new();
        let mut copy = |ty: super::type_expr::TypeExprRef| {
            super::typecore::copy_type_expr_mapping_paths(ctx, ty, &mut cache, &map_path)
        };
        desc.cstr_res = copy(desc.cstr_res);
        desc.cstr_existentials = desc.cstr_existentials.iter().map(|t| copy(*t)).collect();
        desc.cstr_args = desc.cstr_args.iter().map(|t| copy(*t)).collect();
    }
}

fn build_matching_type_constructors(
    out: &mut Vec<ConstructorDescription>,
    access_path: &Path,
    type_name: &str,
    decl: &TypeDeclaration,
    constructor_name: &str,
    ctx: &super::context::TypeContext,
) {
    let type_path = Path::pdot(*access_path, type_name);
    build_type_constructors(&type_path, decl, Some(constructor_name), ctx, &mut |desc| {
        out.insert(0, desc)
    });
}

/// `fst (Env.find_type_descrs path env)` for a variant declaration whose
/// descriptors live at `type_path` (compiler/ml/datarepr.ml:111-172 via
/// compiler/ml/env.ml:1542-1547), in declaration order.
/// `Datarepr.constructor_existentials` (datarepr.ml:48-61): the type
/// variables of the declared arguments (label types for an inline record)
/// that do not occur in the GADT result.
fn declared_constructor_existentials(
    ctx: &super::context::TypeContext,
    args: &super::decl::ConstructorArguments,
    res: Option<crate::types::TypeExprRef>,
) -> Vec<crate::types::TypeExprRef> {
    let tyl: Vec<crate::types::TypeExprRef> = match args {
        super::decl::ConstructorArguments::CstrTuple(args) => args.clone(),
        super::decl::ConstructorArguments::CstrRecord(labels) => {
            labels.iter().map(|label| label.ld_type).collect()
        }
    };
    super::env::constructor_existentials(ctx, &tyl, res)
}

pub(crate) fn constructors_of_type_path(
    type_path: &Path,
    decl: &TypeDeclaration,
    ctx: &super::context::TypeContext,
) -> Vec<ConstructorDescription> {
    let mut out = Vec::new();
    build_type_constructors(type_path, decl, None, ctx, &mut |desc| out.push(desc));
    if let Some(access_path) = type_path.parent() {
        reroot_constructor_descriptions(&mut out, &[], &access_path, ctx);
    }
    out
}

/// `Datarepr.label_descrs` (compiler/ml/datarepr.ml:261-288): the labels of a
/// record declaration with result type `res_ty`, in position order, sharing
/// one `lbl_all` array. `adjust` applies what the caller applies to the
/// declaration before describing it (the component substitution,
/// compiler/ml/env.ml:1530-1548); the array is tied afterwards.
pub(crate) fn label_descrs(
    res_ty: super::type_expr::TypeExprRef,
    decl: &TypeDeclaration,
    private: super::asttypes::PrivateFlag,
    ctx: &super::context::TypeContext,
    adjust: impl FnOnce(&mut [LabelDescription]),
) -> Vec<LabelDescription> {
    let super::decl::TypeKind::TypeRecord(labels, repr) = &decl.type_kind else {
        return Vec::new();
    };
    let mut descs: Vec<LabelDescription> = labels
        .iter()
        .enumerate()
        .map(|(pos, ld)| LabelDescription {
            lbl_name: ld.ld_id.name_atom(),
            lbl_runtime_name: ld.declaration_name(),
            lbl_res: res_ty,
            lbl_arg: super::ctype::remap_label_type_to_params(ctx, ld.ld_type, &decl.type_params),
            lbl_mut: ld.ld_mutable,
            lbl_optional: ld.ld_optional,
            lbl_pos: pos as i32,
            lbl_all: super::decl::LabelArrayRef::NONE,
            lbl_repres: repr.clone(),
            lbl_private: private,
            lbl_loc: ld.ld_loc,
        })
        .collect();
    adjust(&mut descs);
    ctx.alloc_label_array(|lbl_all| {
        for desc in &mut descs {
            desc.lbl_all = lbl_all;
        }
        descs
    })
}

/// [`label_descrs`] returning only the handle of the tied array.
pub(crate) fn label_descrs_array(
    res_ty: super::type_expr::TypeExprRef,
    decl: &TypeDeclaration,
    ctx: &super::context::TypeContext,
    adjust: impl FnOnce(&mut [LabelDescription]),
) -> super::decl::LabelArrayRef {
    let mut handle = super::decl::LabelArrayRef::NONE;
    let descs = label_descrs(res_ty, decl, decl.type_private, ctx, adjust);
    if let Some(first) = descs.first() {
        handle = first.lbl_all;
    }
    handle
}

#[cfg(test)]
thread_local! {
    /// Constructors described by `build_type_constructors` on this thread.
    pub(crate) static CONSTRUCTOR_DESCRIPTIONS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Signature items scanned for the children of world views on this
    /// thread.
    pub(crate) static CHILD_SCAN_STEPS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Describe the constructors of `decl` (those named `constructor_name`, or
/// all), in declaration order, handing each to `emit`. One description per
/// constructor.
fn build_type_constructors(
    type_path: &Path,
    decl: &TypeDeclaration,
    constructor_name: Option<&str>,
    ctx: &super::context::TypeContext,
    emit: &mut impl FnMut(ConstructorDescription),
) {
    let super::decl::TypeKind::TypeVariant(cstrs, layout) = &decl.type_kind else {
        return;
    };

    let type_path = *type_path;
    for (position, cd) in cstrs.iter().enumerate() {
        if constructor_name.is_some_and(|name| cd.cd_id.name() != name) {
            continue;
        }
        #[cfg(test)]
        CONSTRUCTOR_DESCRIPTIONS.with(|count| count.set(count.get() + 1));

        let (cstr_args, cstr_arity, cstr_inlined) = match &cd.cd_args {
            super::decl::ConstructorArguments::CstrTuple(args) => {
                (args.clone(), args.len() as i32, None)
            }
            super::decl::ConstructorArguments::CstrRecord(labels) => {
                let inline_params = super::typecore::inline_record_type_params(ctx, labels);
                let inline_path = Path::pdot(type_path, cd.cd_id.name());
                let inline_constr = ctx.new_generic_constr(inline_path, inline_params.clone());
                let inline_decl = TypeDeclaration {
                    type_params: inline_params.clone(),
                    type_arity: inline_params.len() as i32,
                    type_kind: super::decl::TypeKind::TypeRecord(
                        crate::types::decl::SharedVec::from(labels.clone()),
                        if decl.type_representation == crate::types::TypeRepresentation::Unboxed {
                            super::decl::RecordRepresentation::RecordUnboxed(false)
                        } else {
                            super::decl::RecordRepresentation::RecordInlined {
                                name: cd.cd_id.name().to_string(),
                                representation: super::variant_runtime::ConstructorReference {
                                    variant: *layout,
                                    position,
                                },
                            }
                        },
                    ),
                    type_private: decl.type_private,
                    type_manifest: None,
                    type_variance: inline_params
                        .iter()
                        .map(|_| super::variance::Variance::full())
                        .collect(),
                    type_newtype_level: None,
                    type_loc: cd.cd_loc,
                    type_attributes: vec![],
                    type_immediate: false,
                    type_representation: crate::types::TypeRepresentation::Boxed,
                    type_shape: crate::types::ValueShape::Unstated,
                    type_inlined_types: vec![],
                    type_path: None,
                };
                (vec![inline_constr], 1, Some(Box::new(inline_decl)))
            }
        };
        let cstr_res = if let Some(res_ty) = cd.cd_res {
            let desc = ctx.get_desc(res_ty);
            match &*desc {
                super::type_expr::TypeDesc::Tconstr { path, args, .. } => {
                    let old_result_module_path = path.parent();
                    let new_result_module_path = type_path.parent();
                    let args = *args;
                    if let (Some(old_prefix), Some(new_prefix)) =
                        (old_result_module_path, new_result_module_path)
                    {
                        if !old_prefix.same(&new_prefix) {
                            // OCaml compiler/ml/env.ml:1542-1547 computes
                            // constructors from `decl' = Subst.type_declaration
                            // sub decl`, so the GADT result arguments have
                            // already gone through compiler/ml/subst.ml:303-309.
                            // Mirror that component-prefix substitution before
                            // exposing the constructor description table.
                            let new_prefix = Arc::new(new_prefix);
                            for arg in ctx.type_list(args).iter() {
                                crate::cmi::persistent_env::rewrite_type_expr_by_path_prefix(
                                    arg,
                                    &old_prefix,
                                    &new_prefix,
                                    ctx,
                                );
                            }
                        }
                    }
                    ctx.new_generic_constr(type_path, ctx.type_list(args).to_vec())
                }
                _ => {
                    res_ty
                }
            }
        } else {
            ctx.new_generic_constr(type_path, decl.type_params.clone())
        };
        emit(
            ConstructorDescription {
                cstr_name: cd.cd_id.name().to_string(),
                cstr_res,
                cstr_existentials: declared_constructor_existentials(ctx, &cd.cd_args, cd.cd_res),
                cstr_args,
                cstr_arity,
                cstr_kind: ConstructorKind::Ordinary(
                    super::variant_runtime::ConstructorReference {
                        variant: *layout,
                        position,
                    },
                ),
                cstr_generalized: cd.cd_res.is_some(),
                cstr_private: decl.type_private,
                cstr_loc: cd.cd_loc,
                cstr_attributes: super::decl::constructor_description_attrs_for_variant(cstrs, cd),
                cstr_inlined,
            },
        );
    }
}

/// The description of extension constructor `id` of a component at
/// `access_path` (env.ml:1560-1565), whose type is `ext_type_path` after the
/// component substitution. One description; no loop over the signature.
fn extension_constructor_description(
    access_path: &Path,
    id: Ident,
    ext: &super::decl::ExtensionConstructor,
    ext_slot: i32,
    ext_type_path: Path,
    ctx: &super::context::TypeContext,
) -> ConstructorDescription {
    let ext_path = Path::pdot_pos(*access_path, id.name(), ext_slot);
    let (cstr_args, cstr_arity, cstr_inlined) = match &ext.ext_args {
        super::decl::ConstructorArguments::CstrTuple(args) => {
            (args.clone(), args.len() as i32, None)
        }
        super::decl::ConstructorArguments::CstrRecord(labels) => {
            let inline_params = super::typecore::inline_record_type_params(ctx, labels);
            let inline_path = ext_path;
            let inline_constr =
                ctx.new_generic_constr(inline_path, inline_params.clone());
            let inline_decl = TypeDeclaration {
                type_params: inline_params.clone(),
                type_arity: inline_params.len() as i32,
                type_kind: super::decl::TypeKind::TypeRecord(
                    crate::types::decl::SharedVec::from(labels.clone()),
                    super::decl::RecordRepresentation::RecordExtension,
                ),
                type_private: ext.ext_private,
                type_manifest: None,
                type_variance: inline_params
                    .iter()
                    .map(|_| super::variance::Variance::full())
                    .collect(),
                type_newtype_level: None,
                type_loc: ext.ext_loc,
                type_attributes: vec![],
                type_immediate: false,
                type_representation: crate::types::TypeRepresentation::Boxed,
                type_shape: crate::types::ValueShape::Unstated,
                type_inlined_types: vec![],
                type_path: None,
            };
            (vec![inline_constr], 1, Some(Box::new(inline_decl)))
        }
    };
    let cstr_res = ctx.new_generic_constr(ext_type_path, ext.ext_type_params.clone());
    ConstructorDescription {
            cstr_name: id.name().to_string(),
            cstr_res,
            cstr_existentials: declared_constructor_existentials(
                ctx,
                &ext.ext_args,
                ext.ext_ret_type,
            ),
            cstr_args,
            cstr_arity,
            cstr_kind: ConstructorKind::Extension(ext_path),
            cstr_generalized: ext.ext_ret_type.is_some(),
            cstr_private: ext.ext_private,
            cstr_loc: ext.ext_loc,
            cstr_attributes: ext.ext_attributes.clone(),
            cstr_inlined,
        }
}

/// Every constructor of the component at `access_path`, by name, each
/// bucket in the order [`build_constructors_for_name`] returns it (latest
/// declaration first). One pass over `signature` and one description per
/// constructor; the component substitution is built at most once.
pub(crate) fn build_all_constructors(
    access_path: &Path,
    signature: &[SignatureItem],
    ctx: &super::context::TypeContext,
) -> crate::fast_hash::AHashMap<smol_str::SmolStr, Vec<ConstructorDescription>> {
    let mut buckets: crate::fast_hash::AHashMap<smol_str::SmolStr, Vec<ConstructorDescription>> =
        Default::default();
    let mut subst = None;
    let mut runtime_pos = 0i32;
    for item in signature {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    runtime_pos += 1;
                }
            }
            SignatureItem::SigType(id, decl, _) => {
                let type_path = Path::pdot(*access_path, id.name());
                build_type_constructors(&type_path, decl, None, ctx, &mut |desc| {
                    buckets
                        .entry(smol_str::SmolStr::new(&desc.cstr_name))
                        .or_default()
                        .push(desc)
                });
            }
            SignatureItem::SigTypext(id, ext, _) => {
                let ext_slot = runtime_pos;
                runtime_pos += 1;
                let subst = subst.get_or_insert_with(|| {
                    crate::cmi::persistent_env::ComponentSubst::new(signature, access_path, ctx)
                });
                let ext_type_path = subst.path(&ext.ext_type_path, ctx);
                buckets
                    .entry(smol_str::SmolStr::new_static(id.name()))
                    .or_default()
                    .push(extension_constructor_description(
                        access_path,
                        *id,
                        ext,
                        ext_slot,
                        ext_type_path,
                        ctx,
                    ));
            }
            SignatureItem::SigModule(_, _, _) | SignatureItem::SigClass => {
                runtime_pos += 1;
            }
            SignatureItem::SigModtype(_, _) | SignatureItem::SigClassType => {}
        }
    }
    for bucket in buckets.values_mut() {
        bucket.reverse();
        reroot_constructor_descriptions(bucket, signature, access_path, ctx);
    }
    buckets
}

fn build_constructors_for_name(
    access_path: &Path,
    signature: &[SignatureItem],
    constructor_name: &str,
    ctx: &super::context::TypeContext,
) -> Vec<ConstructorDescription> {
    let mut constructors = Vec::new();
    let mut runtime_pos = 0i32;

    for item in signature {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    runtime_pos += 1;
                }
            }
            SignatureItem::SigType(id, decl, _) => {
                build_matching_type_constructors(
                    &mut constructors,
                    access_path,
                    id.name(),
                    decl,
                    constructor_name,
                    ctx,
                );
            }
            SignatureItem::SigTypext(id, ext, _) => {
                let ext_slot = runtime_pos;
                runtime_pos += 1;
                if id.name() != constructor_name {
                    continue;
                }
                let ext_type_path = crate::cmi::persistent_env::substitute_sig_path(
                    &ext.ext_type_path,
                    signature,
                    access_path,
                    ctx,
                );
                constructors.insert(
                    0,
                    extension_constructor_description(
                        access_path,
                        *id,
                        ext,
                        ext_slot,
                        ext_type_path,
                        ctx,
                    ),
                );
            }
            SignatureItem::SigModule(_, _, _) | SignatureItem::SigClass => {
                runtime_pos += 1;
            }
            SignatureItem::SigModtype(_, _) | SignatureItem::SigClassType => {}
        }
    }

    constructors
}

#[derive(Debug, Clone)]
enum ChildComponentScanState {
    /// Items before `next_index` have been scanned.
    Pending(ChildScanCursor),
    /// Every item has been scanned; a missing child does not exist.
    Complete,
}

#[derive(Debug, Clone, Default)]
struct ChildScanCursor {
    /// Types, modules and module types scanned so far, created on first use.
    working_env: Option<super::env::Env>,
    next_index: usize,
    runtime_pos: usize,
    /// Module items scanned so far: the next module's ordinal.
    modules: u32,
}

impl ChildScanCursor {
    fn working_env_mut(&mut self) -> &mut super::env::Env {
        self.working_env.get_or_insert_with(super::env::Env::empty)
    }
}

/// A forced component value: its position in the signature, identifier and
/// declaration.
type ComponentValue = (usize, Ident, ValueDescription);

/// A forced child module's position in the signature and component tables.
type ChildComponents = (usize, Rc<StoredModuleComponents>);

/// A functor result substituted for one argument path, with the replay
/// record of computing it during a store build.
type FunctorResultSubst = (ModuleType, Option<Rc<super::context::StorePiece>>);

/// Each child module's substituted `Mty_alias`/`Mty_ident` target, whether
/// it is an alias, by name; `None` for a child with neither.
type ModuleAliasTargets = HashMap<String, Option<(bool, Arc<Path>)>>;

#[derive(Debug, Clone)]
struct StructureComponentTables {
    index: Arc<SignatureIndex>,
    component_values: RefCell<HashMap<String, Option<ComponentValue>>>,
    constructors: RefCell<HashMap<String, Arc<Vec<ConstructorDescription>>>>,
    labels: RefCell<HashMap<String, Arc<Vec<LabelDescription>>>>,
    /// The labels of each record type of the component, by type name: what
    /// `components_of_module_maker` stores in `comp_labels` for the type
    /// (compiler/ml/env.ml:1542-1548), one `lbl_all` array per type, built on
    /// the first lookup of one of its labels.
    label_families: RefCell<HashMap<String, super::decl::LabelArrayRef>>,
    /// The types whose families the last label lookup built, so a lookup
    /// whose store build is discarded discards them too.
    label_families_built: RefCell<Vec<String>>,
    modtypes: HashMap<String, (Ident, ModtypeDeclaration)>,
    // OCaml compiler/ml/env.ml:1568-1578 stores `comp_modules` and
    // `comp_modtypes` declarations in EnvLazy-backed component tables, and
    // env.ml:568-571/865-882 forces those thunks at most once per component
    // table. Rust clones component views out of the global cache before
    // running callbacks, so the forced-declaration memo must be shared by
    // those clones to preserve the same lazy identifier-renaming order.
    qualified_modules: RefCell<HashMap<String, (Ident, Arc<ModuleDeclaration>)>>,
    qualified_modtypes: RefCell<HashMap<String, (Ident, ModtypeDeclaration)>>,
    // OCaml keeps `comp_components` lazy (compiler/ml/env.ml:1573-1578).
    // Cache forced child component thunks by name, including misses, so a
    // lookup for one child does not materialize every sibling in the parent
    // signature.
    child_components: RefCell<HashMap<String, Option<ChildComponents>>>,
    child_component_scan: RefCell<ChildComponentScanState>,
    /// The `Mty_alias`/`Mty_ident` target of each child module after the
    /// component substitution (and whether it is an alias). OCaml forces a
    /// `comp_modules` declaration once per table (env.ml:1568), so every
    /// lookup sees the same substituted target block.
    module_alias_targets: RefCell<ModuleAliasTargets>,
    // The component substitution for value lookups depends only on the
    // signature and access path; build it once per component table.
    value_subst_maps: RefCell<Option<Arc<crate::cmi::persistent_env::ValueSubstMaps>>>,
    /// Built during a store build: the tables may be shared with later
    /// compilations on this worker, so entries are forced as store builds and
    /// carry the replay record of their forcing.
    in_store: std::cell::Cell<bool>,
    /// Store pieces per forced entry, one table per `ForcedKind` so lookups
    /// can borrow the entry name.
    store_pieces: RefCell<[HashMap<String, Rc<super::context::StorePiece>>; FORCED_KIND_COUNT]>,
    /// The layer tables `open` adds for this view, built on first open.
    opened_layers: OnceCell<(
        Rc<super::env::OpenedLayers>,
        Option<Rc<super::context::StorePiece>>,
    )>,
}

const FORCED_KIND_COUNT: usize = 6;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ForcedKind {
    Value,
    Constructors,
    Labels,
    /// The label family of one record type (`find_type_descrs`).
    TypeLabels,
    ChildComponents,
    QualifiedModule,
}

const _: () = assert!(ForcedKind::QualifiedModule as usize + 1 == FORCED_KIND_COUNT);

#[derive(Debug, Clone)]
pub(crate) struct QualifiedModuleComponents {
    access_path: Arc<Path>,
    signature: Arc<Signature>,
    tables: Rc<StructureComponentTables>,
    compiler_counters_enabled: bool,
    value_source_prefix: Option<Arc<Path>>,
}

/// The types and module types of an alias view of `source` (an in-process
/// unit or its child), as `scrape_alias` strengthens them: `Mtype.strengthen
/// ~aliasable:true env mty source` (env.ml:1440-1446, mtype.ml:41-91) gives a
/// type without a public manifest the manifest `source.t`, and an abstract
/// module type `source.T`. Child modules become aliases of `source`'s children
/// there; their views take `source` as their own source prefix.
fn strengthen_view_types(
    sig: &mut [SignatureItem],
    source: &Arc<Path>,
    ctx: &super::context::TypeContext,
) {
    for item in sig.iter_mut() {
        match item {
            SignatureItem::SigType(id, decl, _) => {
                *decl = Arc::new(super::typecore::strengthen_type_decl_with_shared_prefix(
                    ctx, source, id, decl,
                ));
            }
            SignatureItem::SigModtype(id, mtd) if mtd.mtd_type.is_none() => {
                mtd.mtd_type = Some(super::decl::ModuleType::MtyIdent(ctx.dotted_from_ident(
                    source.clone(),
                    *id,
                    super::path::NOPOS,
                )));
            }
            _ => {}
        }
    }
}

/// The declaration `store_module` puts in the evolving `env` for a child of a
/// component table built from an alias-scraped signature. OCaml
/// compiler/ml/env.ml:1364-1376 `scrape_alias` strengthens the signature it
/// reaches through an alias with `~aliasable:true`, and compiler/ml/mtype.ml:
/// 93-97 `strengthen_decl` turns each child module that is not already an
/// alias into `Mty_alias (Mta_present, P.child)`; env.ml:1504-1505 then stores
/// that declaration, so a sibling alias resolved through it reaches
/// `find_module P.child` (env.ml:865-882). `strengthen_source` is `P` when the
/// table's items are named through another module path than its access path.
fn strengthened_child_env_decl(
    md: &ModuleDeclaration,
    id: Ident,
    strengthen_source: Option<&Arc<Path>>,
    runtime_pos: usize,
    ctx: &super::context::TypeContext,
) -> ModuleDeclaration {
    match strengthen_source {
        Some(source) if !matches!(md.md_type, ModuleType::MtyAlias(..)) => ModuleDeclaration {
            md_type: ModuleType::MtyAlias(
                super::decl::AliasPresence::MtaPresent,
                std::sync::Arc::new(ctx.dotted_from_ident(source.clone(), id, runtime_pos as i32)),
            ),
            ..md.clone()
        },
        _ => md.clone(),
    }
}

/// Continue the scan of a component table's children up to `child_name`.
/// `signature` is the table's; `declared` is the same signature as the
/// module declares it (the table's own unless it is a world view of a child
/// module), which the evolving environment and each child's thunk are made
/// from. A child of the world view `view` that is declared with a signature
/// is marked as that view's child: its components are a world view too.
///
/// Cost: one step per item scanned; all calls together scan each item once.
#[allow(clippy::too_many_arguments)]
fn scan_child_component_from_signature(
    access_path: &Arc<Path>,
    source_prefix: Option<&Arc<Path>>,
    signature: &Arc<Signature>,
    declared: &Arc<Signature>,
    view: Option<&Arc<super::module_view::ModuleView>>,
    child_components: &mut HashMap<String, Option<(usize, Rc<StoredModuleComponents>)>>,
    state: &mut ChildComponentScanState,
    child_name: &str,
    ctx: &super::context::TypeContext,
) -> (Option<(usize, Rc<StoredModuleComponents>)>, usize) {
    let ChildComponentScanState::Pending(cursor) = state else {
        return (None, 0);
    };
    let start_index = cursor.next_index;
    let mut found = None;

    // OCaml compiler/ml/env.ml:1530-1578 computes component paths once,
    // stores module declarations in `comp_modules` at env.ml:1568-1569, and
    // separately stores child component thunks in `comp_components` at
    // env.ml:1573-1578. Persistent signatures need the same split so
    // qualified value lookup can descend through child components without
    // forcing `Subst.modtype` on the module declaration thunk.
    while cursor.next_index < declared.len() {
        let item = &declared[cursor.next_index];
        cursor.next_index += 1;
        match item {
            SignatureItem::SigValue(_, desc) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    cursor.runtime_pos += 1;
                }
            }
            SignatureItem::SigType(id, decl, _) => {
                cursor.working_env_mut().add_type(*id, decl.clone());
            }
            SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                cursor.runtime_pos += 1;
            }
            SignatureItem::SigModule(id, md, _) => {
                let runtime_pos = cursor.runtime_pos;
                let child_access_path =
                    ctx.dotted_from_ident(access_path.clone(), *id, runtime_pos as i32);
                let strengthen_source = source_prefix.filter(|source| !source.same(access_path));
                let stored = {
                    let working_env = cursor.working_env_mut();
                    working_env.add_module_with_component_context(
                        *id,
                        strengthened_child_env_decl(md, *id, strengthen_source, runtime_pos, ctx),
                        md.clone(),
                        child_access_path,
                        Some(((**access_path), signature.clone())),
                    );
                    working_env
                        .local_module_components_shared(&Path::pident(*id))
                        .map(|stored| (runtime_pos, stored))
                };
                if let (Some(source), Some((_, stored))) = (source_prefix, &stored) {
                    let _ = stored.source_prefix.set(ctx.dotted_from_ident(
                        source.clone(),
                        *id,
                        runtime_pos as i32,
                    ));
                }
                if let (Some(view), Some((_, stored))) = (view, &stored) {
                    stored.of_view.set(true);
                    if view.world_child_kind(cursor.modules).is_some() {
                        let _ = stored.world_child.set((view.clone(), cursor.modules));
                    }
                }
                cursor.modules += 1;
                // OCaml `Tbl.add` shadows earlier entries with the same name
                // (compiler/ml/env.ml:1577-1578), so keep the latest scanned
                // child component for this name.
                child_components.insert(id.name().to_string(), stored.clone());
                if id.name() == child_name {
                    found = stored;
                    cursor.runtime_pos += 1;
                    break;
                }
                cursor.runtime_pos += 1;
            }
            SignatureItem::SigModtype(id, mtd) => {
                cursor.working_env_mut().add_modtype(*id, mtd.clone());
            }
            SignatureItem::SigClassType => {}
        }
    }

    let scanned_items = cursor.next_index - start_index;
    if cursor.next_index >= declared.len() {
        *state = ChildComponentScanState::Complete;
        child_components
            .entry(child_name.to_string())
            .or_insert(None);
    }

    (found, scanned_items)
}

impl QualifiedModuleComponents {
    pub(crate) fn new(
        access_path: Path,
        signature: Signature,
        ctx: &super::context::TypeContext,
    ) -> Self {
        Self::new_with_child_components_arc(access_path, Arc::new(signature), HashMap::new(), ctx)
    }

    pub(crate) fn new_with_child_components_arc(
        access_path: Path,
        signature: Arc<Signature>,
        child_components: HashMap<String, (usize, Rc<StoredModuleComponents>)>,
        ctx: &super::context::TypeContext,
    ) -> Self {
        Self::new_with_child_components_arc_and_value_source_prefix(
            access_path,
            signature,
            child_components,
            None,
            ctx,
        )
    }

    pub(crate) fn new_with_complete_child_components_arc(
        access_path: Path,
        signature: Arc<Signature>,
        child_components: HashMap<String, (usize, Rc<StoredModuleComponents>)>,
        ctx: &super::context::TypeContext,
    ) -> Self {
        Self::new_with_child_components_arc_and_value_source_prefix_inner(
            access_path,
            signature,
            child_components,
            None,
            true,
            ctx,
        )
    }

    pub(crate) fn new_with_child_components_arc_and_value_source_prefix(
        access_path: Path,
        signature: Arc<Signature>,
        child_components: HashMap<String, (usize, Rc<StoredModuleComponents>)>,
        value_source_prefix: Option<Path>,
        ctx: &super::context::TypeContext,
    ) -> Self {
        Self::new_with_child_components_arc_and_value_source_prefix_inner(
            access_path,
            signature,
            child_components,
            value_source_prefix,
            false,
            ctx,
        )
    }

    fn new_with_child_components_arc_and_value_source_prefix_inner(
        access_path: Path,
        signature: Arc<Signature>,
        child_components: HashMap<String, (usize, Rc<StoredModuleComponents>)>,
        value_source_prefix: Option<Path>,
        child_component_scan_complete: bool,
        ctx: &super::context::TypeContext,
    ) -> Self {
        let value_source_prefix = value_source_prefix.map(Arc::new);
        let shared_access_path = Arc::new(access_path);
        // An in-process unit's signature names its own items through the unit
        // (`Unit.t`); OCaml's `prefix_idents` puts them at the component path
        // (env.ml:1454-1481, 1530-1538). Re-root a copy once, so values,
        // types, labels, constructors and child modules all see it.
        let signature = match &value_source_prefix {
            Some(source) if !source.same(&access_path) => {
                // Value types are re-rooted when a value is looked up or
                // opened (each use copies it anyway); copy and re-root the
                // other items here. Values are most of a unit's signature.
                let non_values: Vec<SignatureItem> = signature
                    .iter()
                    .filter(|item| !matches!(item, SignatureItem::SigValue(..)))
                    .cloned()
                    .collect();
                let mut copied =
                    super::typecore::copy_lookup_signature_for_subst(&non_values, ctx).into_iter();
                let mut rerooted: Vec<SignatureItem> = signature
                    .iter()
                    .map(|item| match item {
                        SignatureItem::SigValue(..) => item.clone(),
                        _ => copied.next().expect("copied non-value item"),
                    })
                    .collect();
                // A child module of the scraped unit is strengthened into an
                // alias of the unit's own child (mtype.ml:28-40 via
                // env.ml:1435-1449), whose components name the parent unit's
                // items through the unit; only the child's own items move to
                // the access path (`Unit.Sub.u` -> `Cat.Sub.u`).
                for item in &rerooted {
                    if matches!(item, SignatureItem::SigValue(..)) {
                        continue;
                    }
                    let (old_prefix, new_prefix) = match item {
                        SignatureItem::SigModule(id, _, _) => (
                            Path::pdot(**source, id.name()),
                            Arc::new(ctx.dotted_from_ident(
                                shared_access_path.clone(),
                                *id,
                                super::path::NOPOS,
                            )),
                        ),
                        _ => ((**source), shared_access_path.clone()),
                    };
                    crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                        std::slice::from_ref(item),
                        &old_prefix,
                        &new_prefix,
                        ctx,
                    );
                }
                crate::cmi::persistent_env::rewrite_sig_paths_by_path_prefix_shallow(
                    &mut rerooted,
                    source,
                    &shared_access_path,
                    ctx,
                );
                strengthen_view_types(&mut rerooted, source, ctx);
                Arc::new(rerooted)
            }
            _ => signature,
        };
        check_signature_store_resident(&signature, ctx);
        let index = ctx.signature_index(&signature);
        let mut component_modtypes = HashMap::new();
        // Replay the per-item side effects in signature order.
        let mut alias_items = index.alias_modules.iter().peekable();
        let mut modtype_items = index.modtypes.iter().peekable();
        loop {
            let next_alias = alias_items.peek().map(|(idx, _)| *idx);
            let next_modtype = modtype_items.peek().map(|idx| **idx);
            let take_alias = match (next_alias, next_modtype) {
                (Some(a), Some(m)) => a < m,
                (Some(_), None) => true,
                (None, Some(_)) => false,
                (None, None) => break,
            };
            if take_alias {
                let (idx, runtime_pos) = *alias_items.next().expect("peeked alias item");
                if let SignatureItem::SigModule(id, md, _) = &signature[idx]
                    && let super::decl::ModuleType::MtyAlias(..)
                    | super::decl::ModuleType::MtyIdent(_) = &md.md_type
                {
                    let alias_source = md.md_type.ident_or_alias_path().unwrap();
                    let component_path =
                        ctx.dotted_from_ident(shared_access_path.clone(), *id, runtime_pos as i32);
                    // OCaml compiler/ml/env.ml:1517 `scrape_alias` follows
                    // the module declaration's alias path through
                    // env.ml:865-882 `find_module`, then env.ml:1530-1578
                    // stores thunks under the selected component path.
                    // Preserve the actual source path from the declaration
                    // instead of recovering it from flattened spelling.
                    ctx.register_component_alias_source(component_path, *alias_source);
                }
            } else {
                let idx = *modtype_items.next().expect("peeked modtype item");
                if let SignatureItem::SigModtype(id, mtd) = &signature[idx] {
                    let mut component_mtd = mtd.clone();
                    // OCaml compiler/ml/env.ml:1513-1514 memoizes the component
                    // table being forced, then env.ml:1581-1585 applies
                    // `Subst.modtype_declaration` for that table. A later lookup
                    // that reaches a different Rust component view, such as a
                    // flattened backing unit, must not choose a different
                    // force-sharing rule based on output mode.
                    crate::cmi::persistent_env::freshen_component_modtype_declaration_bound_idents(
                        &mut component_mtd,
                        &signature,
                        &access_path,
                        ctx,
                    );
                    component_modtypes.insert(id.name().to_string(), (*id, component_mtd));
                }
            }
        }

        let child_components = child_components
            .into_iter()
            .map(|(name, component)| (name, Some(component)))
            .collect();

        Self {
            access_path: shared_access_path,
            signature,
            tables: Rc::new(StructureComponentTables {
                index,
                component_values: RefCell::new(HashMap::new()),
                constructors: RefCell::new(HashMap::new()),
                labels: RefCell::new(HashMap::new()),
                label_families: RefCell::new(HashMap::new()),
                label_families_built: RefCell::new(Vec::new()),
                modtypes: component_modtypes,
                qualified_modules: RefCell::new(HashMap::new()),
                qualified_modtypes: RefCell::new(HashMap::new()),
                child_components: RefCell::new(child_components),
                child_component_scan: RefCell::new(if child_component_scan_complete {
                    ChildComponentScanState::Complete
                } else {
                    ChildComponentScanState::Pending(ChildScanCursor::default())
                }),
                module_alias_targets: RefCell::new(HashMap::new()),
                value_subst_maps: RefCell::new(None),
                in_store: std::cell::Cell::new(super::thread_store::store_build_active()),
                store_pieces: RefCell::new(Default::default()),
                opened_layers: OnceCell::new(),
            }),
            compiler_counters_enabled: ctx.compiler_counters_enabled(),
            value_source_prefix,
        }
    }

    pub(crate) fn access_path(&self) -> &Path {
        self.access_path.as_ref()
    }

    /// The unit path this component's value types still name their own
    /// items through, when the component sits at a different access path;
    /// values are re-rooted when they are looked up or opened.
    pub(crate) fn rerooted_value_source(&self) -> Option<&Path> {
        self.value_source_prefix
            .as_deref()
            .filter(|source| !source.same(self.access_path()))
    }

    /// Force one lazily built entry of these tables. Store-resident tables
    /// force it as a store build: the result is kept (with its replay record)
    /// only when the build stayed independent of this compilation; later
    /// users replay the record the first time they read the entry.
    fn force_entry<R>(
        &self,
        kind: ForcedKind,
        name: &str,
        ctx: &super::context::TypeContext,
        force: impl FnOnce() -> R,
    ) -> R {
        if !self.tables.in_store.get() {
            return force();
        }
        let known = self.tables.store_pieces.borrow()[kind as usize]
            .get(name)
            .cloned();
        if let Some(piece) = known {
            ctx.touch_store_piece(&piece);
            // A hit normally allocates nothing; run it as a store build anyway
            // so a fall-through that does force cannot put compilation-local
            // nodes into shared tables.
            let (result, hit) = ctx.build_in_store(force);
            if hit.is_none() {
                self.forget_entry(kind, name);
            }
            return result;
        }
        let (result, piece) = ctx.build_in_store(force);
        match piece {
            Some(piece) => {
                self.tables.store_pieces.borrow_mut()[kind as usize]
                    .insert(name.to_string(), piece);
            }
            None => self.forget_entry(kind, name),
        }
        result
    }

    /// The layer tables that opening this view adds to an Env (OCaml
    /// compiler/ml/env.ml:1841-1877 opens the component table as is), built
    /// once per view by `build`.
    pub(crate) fn opened_layers(
        &self,
        ctx: &super::context::TypeContext,
        build: impl FnOnce() -> super::env::OpenedLayers,
    ) -> Rc<super::env::OpenedLayers> {
        if let Some((layers, piece)) = self.tables.opened_layers.get() {
            if let Some(piece) = piece {
                ctx.touch_store_piece(piece);
            }
            return layers.clone();
        }
        if self.tables.in_store.get() {
            let (layers, piece) = ctx.build_in_store(build);
            let layers = Rc::new(layers);
            if let Some(piece) = piece {
                let _ = self.tables.opened_layers.set((layers.clone(), Some(piece)));
            }
            return layers;
        }
        let layers = Rc::new(build());
        let _ = self.tables.opened_layers.set((layers.clone(), None));
        layers
    }

    /// Drop an entry forced from compilation-local state so that other
    /// compilations sharing these tables force it themselves.
    fn forget_entry(&self, kind: ForcedKind, name: &str) {
        match kind {
            ForcedKind::Value => {
                self.tables.component_values.borrow_mut().remove(name);
            }
            ForcedKind::Constructors => {
                self.tables.constructors.borrow_mut().remove(name);
            }
            ForcedKind::Labels | ForcedKind::TypeLabels => {
                if kind == ForcedKind::Labels {
                    self.tables.labels.borrow_mut().remove(name);
                }
                let mut families = self.tables.label_families.borrow_mut();
                for type_name in self.tables.label_families_built.borrow_mut().drain(..) {
                    families.remove(&type_name);
                }
            }
            ForcedKind::QualifiedModule => {
                self.tables.qualified_modules.borrow_mut().remove(name);
            }
            // Scanning children allocates no type nodes; the scanned entries
            // are the same for every compilation.
            ForcedKind::ChildComponents => {}
        }
    }

    pub(crate) fn signature(&self) -> &[SignatureItem] {
        self.signature.as_slice()
    }

    pub(crate) fn signature_arc(&self) -> Arc<Signature> {
        self.signature.clone()
    }

    fn cached_value_index(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, usize)> {
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_hit(ctx, crate::perf_counters::LazyLookupKind::Value);
        }
        self.tables.index.values.get(name).copied()
    }

    fn cached_type_index(&self, name: &str, ctx: &super::context::TypeContext) -> Option<usize> {
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_hit(ctx, crate::perf_counters::LazyLookupKind::Type);
        }
        self.tables.index.types.get(name).copied()
    }

    fn cached_module_index(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, usize)> {
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_hit(
                ctx,
                crate::perf_counters::LazyLookupKind::Module,
            );
        }
        self.tables.index.module(name)
    }

    pub(crate) fn lookup_value(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, &Ident, &ValueDescription)> {
        let (idx, runtime_pos) = self.cached_value_index(name, ctx)?;
        match &self.signature[idx] {
            SignatureItem::SigValue(id, desc) => Some((runtime_pos, id, desc)),
            _ => None,
        }
    }

    pub(crate) fn lookup_value_for_access(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, ValueDescription)> {
        self.force_entry(ForcedKind::Value, name, ctx, || {
            self.lookup_value_for_access_inner(name, ctx)
        })
    }

    fn lookup_value_for_access_inner(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, ValueDescription)> {
        if let Some(cached) = self.tables.component_values.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(
                    ctx,
                    crate::perf_counters::LazyLookupKind::Value,
                );
            }
            return cached;
        }

        let (runtime_pos, id, desc) = self.lookup_value(name, ctx)?;
        let mut desc = super::typecore::copy_lookup_value_description_for_subst(desc, ctx);
        // Re-root the copy like the component's other items (see
        // `new_with_child_components_arc_and_value_source_prefix_inner`).
        if let Some(source) = self.rerooted_value_source() {
            crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                &[SignatureItem::SigValue(*id, desc.clone())],
                source,
                &self.access_path,
                ctx,
            );
        }
        // OCaml compiler/ml/env.ml:1530-1538 builds `prefix_idents` for the
        // selected component path, then env.ml:1537 always applies
        // compiler/ml/subst.ml:303-309 `Subst.value_description` to component
        // values before typecore.ml:2421-2457 instances `desc.val_type`.
        // Keep the alias-strengthening boundary from compiler/ml/mtype.ml:41-49:
        // only the component substitution is applied here; alias target value
        // descriptions are not rewritten wholesale.
        let value_maps = self
            .tables
            .value_subst_maps
            .borrow_mut()
            .get_or_insert_with(|| {
                Arc::new(crate::cmi::persistent_env::build_value_subst_maps(
                    self.signature.as_ref(),
                    self.access_path(),
                    ctx,
                ))
            })
            .clone();
        crate::cmi::persistent_env::substitute_type_paths_in_value_with_maps(
            &mut desc,
            &value_maps,
            self.signature.as_ref(),
            self.access_path(),
            ctx,
        );
        // OCaml compiler/ml/env.ml:1513-1516 memoizes the whole
        // `components_of_module_maker` result, and env.ml:1537 stores the
        // `Subst.value_description` output in `comp_values`. Cache the
        // per-name Rust value view so repeated qualified value lookups reuse
        // the same substituted type nodes instead of rerunning the Rust-side
        // scan/copy/substitution path.
        let result = Some((runtime_pos, *id, desc));
        self.tables
            .component_values
            .borrow_mut()
            .insert(name.to_string(), result.clone());
        result
    }

    pub(crate) fn lookup_constructors(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Arc<Vec<ConstructorDescription>> {
        self.force_entry(ForcedKind::Constructors, name, ctx, || {
            self.lookup_constructors_inner(name, ctx)
        })
    }

    fn lookup_constructors_inner(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Arc<Vec<ConstructorDescription>> {
        if let Some(cached) = self.tables.constructors.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(
                    ctx,
                    crate::perf_counters::LazyLookupKind::Constructor,
                );
            }
            return cached;
        }

        // OCaml compiler/ml/env.ml:1542-1556 populates `comp_constrs`
        // while forcing a module's components. Rust keeps the canonical
        // signature immutable and forces only the requested constructor bucket,
        // preserving env.ml:1132-1137 lookup semantics without materializing
        // every constructor in large dependency signatures.
        let mut built =
            build_constructors_for_name(self.access_path(), self.signature.as_ref(), name, ctx);
        reroot_constructor_descriptions(
            &mut built,
            self.signature.as_ref(),
            self.access_path(),
            ctx,
        );
        let built = Arc::new(built);
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
                ctx,
                crate::perf_counters::LazyLookupKind::Constructor,
                self.signature.len(),
                built.len(),
            );
        }
        self.tables
            .constructors
            .borrow_mut()
            .insert(name.to_string(), built.clone());
        built
    }

    pub(crate) fn lookup_labels(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Arc<Vec<LabelDescription>> {
        self.force_entry(ForcedKind::Labels, name, ctx, || {
            self.lookup_labels_inner(name, ctx)
        })
    }

    fn lookup_labels_inner(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Arc<Vec<LabelDescription>> {
        if let Some(cached) = self.tables.labels.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(
                    ctx,
                    crate::perf_counters::LazyLookupKind::Label,
                );
            }
            return cached;
        }

        // OCaml compiler/ml/env.ml:1548-1559 computes `comp_labels` from the
        // selected component path. For normal compilation, force just the label
        // bucket requested by typecore.ml:1107-1126-style qualified lookup; this
        // avoids constructing hundreds of unused JSX record labels per module view.
        self.tables.label_families_built.borrow_mut().clear();
        let mut built = Vec::new();
        for item in self.signature.iter() {
            let SignatureItem::SigType(id, decl, _) = item else {
                continue;
            };
            let super::decl::TypeKind::TypeRecord(labels, _) = &decl.type_kind else {
                continue;
            };
            let Some(pos) = labels.iter().position(|ld| ld.ld_id.name() == name) else {
                continue;
            };
            let family = self.label_family_of_type(id.name(), decl, ctx);
            // Later declarations shadow earlier ones (`comp_labels` is a
            // `find_all` table, newest first).
            let family = ctx
                .label_family(family)
                .expect("a component label family is registered");
            built.insert(0, family[pos].clone());
        }
        let built = Arc::new(built);
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
                ctx,
                crate::perf_counters::LazyLookupKind::Label,
                self.signature.len(),
                built.len(),
            );
        }
        self.tables
            .labels
            .borrow_mut()
            .insert(name.to_string(), built.clone());
        built
    }

    /// `snd (find_type_descrs (Pdot (access_path, name)))` for a record type
    /// of this component (compiler/ml/env.ml:828, 1470-1485): the labels
    /// `components_of_module_maker` stored with the type in `comp_types`, the
    /// same array `lookup_labels` returns them in. `None` when `name` is not
    /// a record type of the component or has no labels.
    pub(crate) fn type_label_family(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<super::decl::LabelArrayRef> {
        let idx = self.cached_type_index(name, ctx)?;
        let SignatureItem::SigType(id, decl, _) = &self.signature[idx] else {
            return None;
        };
        if !matches!(&decl.type_kind, super::decl::TypeKind::TypeRecord(labels, _) if !labels.is_empty())
        {
            return None;
        }
        Some(self.force_entry(ForcedKind::TypeLabels, name, ctx, || {
            self.tables.label_families_built.borrow_mut().clear();
            self.label_family_of_type(id.name(), decl, ctx)
        }))
    }

    /// The label family of the component's record type `type_name`, described
    /// from its declaration (`Datarepr.labels_of_type path decl'`, env.ml:1475)
    /// the first time either lookup needs it.
    fn label_family_of_type(
        &self,
        type_name: &str,
        decl: &TypeDeclaration,
        ctx: &super::context::TypeContext,
    ) -> super::decl::LabelArrayRef {
        if let Some(family) = self.tables.label_families.borrow().get(type_name) {
            return *family;
        }
        let type_path = Path::pdot(*self.access_path(), type_name);
        let res_ty = ctx.new_generic_constr(type_path, decl.type_params.clone());
        // `decl` is already the component's substituted declaration: the
        // signature was copied and its paths prefixed for this access path
        // when the table was built (`Subst.type_declaration sub decl`,
        // env.ml:1470-1475).
        let family = label_descrs_array(res_ty, decl, ctx, |_| {});
        self.tables
            .label_families
            .borrow_mut()
            .insert(type_name.to_string(), family);
        self.tables
            .label_families_built
            .borrow_mut()
            .push(type_name.to_string());
        family
    }

    pub(crate) fn lookup_type(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(&Ident, &Arc<TypeDeclaration>)> {
        let idx = self.cached_type_index(name, ctx)?;
        match &self.signature[idx] {
            SignatureItem::SigType(id, decl, _) => Some((id, decl)),
            _ => None,
        }
    }

    pub(crate) fn lookup_module(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, &Ident, &ModuleDeclaration)> {
        let (idx, runtime_pos) = self.cached_module_index(name, ctx)?;
        match &self.signature[idx] {
            SignatureItem::SigModule(id, md, _) => Some((runtime_pos, id, md)),
            _ => None,
        }
    }

    /// The target of component module `name` when it is a module alias (or,
    /// with `include_ident`, a module type path), as forcing its
    /// `comp_modules` thunk (compiler/ml/env.ml:865-882, 446-448) returns
    /// it: the raw declaration under this table's `prefix_idents`
    /// substitution. Reading it renames no binder, as `Subst.modtype` on a
    /// path renames none (compiler/ml/subst.ml:345-364).
    pub(crate) fn lookup_module_alias_target(
        &self,
        name: &str,
        include_ident: bool,
        ctx: &super::context::TypeContext,
    ) -> Option<Arc<Path>> {
        let (_, _, md) = self.lookup_module(name, ctx)?;
        if !include_ident && !matches!(md.md_type, ModuleType::MtyAlias(..)) {
            return None;
        }
        if let Some(cached) = self.tables.module_alias_targets.borrow().get(name) {
            return cached
                .as_ref()
                .filter(|(alias, _)| include_ident || *alias)
                .map(|(_, target)| target.clone());
        }
        let target = crate::cmi::persistent_env::substitute_component_module_type_path(
            &md.md_type,
            &self.signature,
            self.access_path(),
            ctx,
        )
        .and_then(|mty| match mty {
            ModuleType::MtyAlias(_, target) => Some((true, target)),
            ModuleType::MtyIdent(target) => Some((false, Arc::new(target))),
            _ => None,
        });
        self.tables
            .module_alias_targets
            .borrow_mut()
            .insert(name.to_string(), target.clone());
        target.map(|(_, target)| target)
    }

    pub(crate) fn lookup_child_components(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Rc<StoredModuleComponents>)> {
        self.force_entry(ForcedKind::ChildComponents, name, ctx, || {
            self.lookup_child_components_inner(name, ctx)
        })
    }

    fn lookup_child_components_inner(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Rc<StoredModuleComponents>)> {
        if let Some(cached) = self.tables.child_components.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(
                    ctx,
                    crate::perf_counters::LazyLookupKind::ChildComponent,
                );
            }
            return cached;
        }

        let mut scan = self.tables.child_component_scan.borrow_mut();
        if matches!(*scan, ChildComponentScanState::Complete) {
            self.tables
                .child_components
                .borrow_mut()
                .insert(name.to_string(), None);
            return None;
        }

        let mut child_components = self.tables.child_components.borrow_mut();
        let (built, scanned_items) = scan_child_component_from_signature(
            &self.access_path,
            self.value_source_prefix.as_ref(),
            &self.signature,
            &self.signature,
            None,
            &mut child_components,
            &mut scan,
            name,
            ctx,
        );
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
                ctx,
                crate::perf_counters::LazyLookupKind::ChildComponent,
                scanned_items,
                usize::from(built.is_some()),
            );
        }
        built
    }

    pub(crate) fn lookup_qualified_module_shared(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, Arc<ModuleDeclaration>)> {
        self.force_entry(ForcedKind::QualifiedModule, name, ctx, || {
            self.lookup_qualified_module_shared_inner(name, ctx)
        })
    }

    fn lookup_qualified_module_shared_inner(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, Arc<ModuleDeclaration>)> {
        let (idx, runtime_pos) = self.cached_module_index(name, ctx)?;
        if let Some((id, md)) = self.tables.qualified_modules.borrow().get(name).cloned() {
            let selected_path =
                submodule_lookup_path(self.access_path.as_ref(), name, runtime_pos, &md);
            if !module_decl_is_self_alias_for_access_path(&md, &selected_path) {
                return Some((runtime_pos, id, md));
            }
            // OCaml compiler/ml/env.ml:865-882 `find_module` forces the
            // env.ml:1568 module-declaration thunk. If an earlier scrape cached
            // the compiler/ml/mtype.ml:98-102 strengthened self alias, keep
            // going so the raw component item below runs compiler/ml/subst.ml:351-364.
        }
        // Declarations forced through other views of the same module are
        // this compilation's state: a store build forces its own, so that
        // what the shared view holds does not depend on which compilation
        // built it.
        if !ctx.in_store_build() {
            // OCaml compiler/ml/env.ml:1513-1514 stores component tables as lazy
            // values, and env.ml:568-571/865-882 reuses the forced module-decl thunk
            // for the selected parent path. Rust can reach the same parent through
            // separate component views (`Stdlib.JSON` and `Stdlib_JSON`), so share the
            // forced declaration at the TypeContext level to preserve the same stamp
            // consumption.
            if let Some((id, md)) = ctx.find_qualified_module_decl(self.access_path.as_ref(), name)
            {
                let selected_path =
                    submodule_lookup_path(self.access_path.as_ref(), name, runtime_pos, &md);
                if !module_decl_is_self_alias_for_access_path(&md, &selected_path) {
                    self.tables
                        .qualified_modules
                        .borrow_mut()
                        .insert(name.to_string(), (id, md.clone()));
                    return Some((runtime_pos, id, md));
                }
                // Same OCaml env.ml:865-882 / subst.ml:351-364 force boundary as
                // above: do not let a TypeContext-level self-alias placeholder hide
                // the raw component module-declaration thunk.
            }
            for source_prefix in ctx.alias_sources_for_component_path(self.access_path.as_ref()) {
                if let Some((id, md)) = ctx.find_qualified_module_decl(&source_prefix, name) {
                    let selected_path =
                        submodule_lookup_path(self.access_path.as_ref(), name, runtime_pos, &md);
                    if module_decl_is_self_alias_for_access_path(&md, &selected_path) {
                        continue;
                    }
                    // OCaml compiler/ml/env.ml:1513-1519 creates one component
                    // table after `scrape_alias`; env.ml:1568-1578 stores both
                    // `comp_modules` and `comp_components` thunks under that table.
                    // A selected namespace path such as `Layout.Types` and its
                    // flattened backing unit `Layout__Types` therefore share the
                    // same forced env.ml:1568 module-declaration thunk. Rust has
                    // separate component views, so reuse the backing declaration
                    // instead of running compiler/ml/subst.ml:351-364 again.
                    self.tables
                        .qualified_modules
                        .borrow_mut()
                        .insert(name.to_string(), (id, md.clone()));
                    ctx.register_qualified_module_decl(
                        self.access_path.as_ref(),
                        name,
                        id,
                        md.clone(),
                    );
                    return Some((runtime_pos, id, md));
                }
            }
            for component_path in ctx.component_paths_for_alias_source(self.access_path.as_ref()) {
                let Some((id, md)) = ctx.find_qualified_module_decl(&component_path, name) else {
                    continue;
                };
                let selected_path =
                    submodule_lookup_path(self.access_path.as_ref(), name, runtime_pos, &md);
                if !module_decl_is_self_alias_for_access_path(&md, &selected_path) {
                    // Same sharing as above, but reached from the flattened backing
                    // component view after the selected path forced the declaration.
                    self.tables
                        .qualified_modules
                        .borrow_mut()
                        .insert(name.to_string(), (id, md.clone()));
                    ctx.register_qualified_module_decl(
                        self.access_path.as_ref(),
                        name,
                        id,
                        md.clone(),
                    );
                    return Some((runtime_pos, id, md));
                }
                // OCaml compiler/ml/env.ml:1568 stores the module-declaration thunk
                // from the raw component item. A cached self alias can be produced by
                // compiler/ml/mtype.ml:98-102 strengthening, but env.ml:865-882
                // `find_module` still forces the raw thunk and applies
                // compiler/ml/subst.ml:351-364 before returning it.
            }
        }

        let (id, md) = match &self.signature[idx] {
            SignatureItem::SigModule(id, md, _) => (*id, md.clone()),
            _ => return None,
        };
        if let Some((raw_id, raw_md, raw_parent_sig, raw_parent_path)) =
            self_alias_raw_parent_module_item(&self.access_path, name, runtime_pos, &md, ctx)
        {
            // OCaml compiler/ml/env.ml:1568 stores component module
            // declarations as `EnvLazy.create (sub, md)`, where `md` is the
            // raw parent signature item from env.ml:1530-1578. A strengthened
            // persistent child can appear here as a self alias, but forcing the
            // thunk must still apply compiler/ml/subst.ml:352-400 to the raw
            // child signature and consume those child binder stamps.
            let (raw_id, md) = force_component_module_declaration_thunk(
                self.access_path.as_ref(),
                name,
                self.access_path.as_ref(),
                &raw_parent_sig,
                raw_id,
                raw_md,
                ctx,
            );
            self.tables
                .qualified_modules
                .borrow_mut()
                .insert(name.to_string(), (raw_id, md.clone()));
            // OCaml compiler/ml/env.ml:1568 stores one lazy module-declaration
            // thunk for the raw component item, and env.ml:1517-1519 can reach
            // that same thunk through a strengthened alias path after
            // env.ml:1435-1449 `scrape_alias`. Rust has separate component
            // views for paths such as `Webapi.Fetch` and `Webapi__Fetch`; cache
            // the forced declaration under the raw parent too so a later direct
            // raw lookup observes the already-forced OCaml thunk instead of
            // running compiler/ml/subst.ml:351-400 a second time.
            if !raw_parent_path.same(self.access_path.as_ref()) {
                ctx.register_qualified_module_decl(&raw_parent_path, name, raw_id, md.clone());
            }
            return Some((runtime_pos, raw_id, md));
        }
        // OCaml compiler/ml/env.ml:1568 stores component modules as
        // EnvLazy thunks, and forcing them through env.ml:475 applies
        // `Subst.modtype sub md.md_type`. For `Mty_signature`, that reaches
        // compiler/ml/subst.ml:378-400 and renames the child signature's bound
        // identifiers before lookup observes them.
        let (id, md) = force_component_module_declaration_thunk(
            self.access_path.as_ref(),
            name,
            self.access_path.as_ref(),
            &self.signature,
            id,
            md,
            ctx,
        );
        self.tables
            .qualified_modules
            .borrow_mut()
            .insert(name.to_string(), (id, md.clone()));
        Some((runtime_pos, id, md))
    }

    pub(crate) fn lookup_modtype(
        &self,
        name: &str,
        _ctx: &super::context::TypeContext,
    ) -> Option<(Ident, ModtypeDeclaration)> {
        self.tables.modtypes.get(name).cloned()
    }

    pub(crate) fn lookup_qualified_modtype(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(Ident, ModtypeDeclaration)> {
        if let Some((id, mtd)) = self.tables.qualified_modtypes.borrow().get(name).cloned() {
            return Some((id, mtd));
        }

        // OCaml compiler/ml/env.ml:1581-1585 computes the component-table
        // modtype declaration once with `Subst.modtype_declaration` and later
        // lookup reads that cached declaration. Do not run the child-module
        // substitution pass again here; it would double-substitute package
        // identities that were already handled while building the component.
        let (id, mtd) = self.lookup_modtype(name, ctx)?;
        self.tables
            .qualified_modtypes
            .borrow_mut()
            .insert(name.to_string(), (id, mtd.clone()));
        Some((id, mtd))
    }
}

/// Ephemeral semantic lookup/comparison key, never retained as a component
/// path. Stored component paths use dotted_from_ident with the shared root.
fn submodule_lookup_path(
    parent_access_path: &Path,
    module_name: &str,
    runtime_pos: usize,
    _md: &ModuleDeclaration,
) -> Path {
    Path::pdot_pos(*parent_access_path, module_name, runtime_pos as i32)
}

fn module_decl_is_self_alias_for_access_path(md: &ModuleDeclaration, access_path: &Path) -> bool {
    matches!(&md.md_type, ModuleType::MtyAlias(_, target) if target.same(access_path))
}

pub(crate) fn force_component_module_declaration_thunk(
    cache_parent_path: &Path,
    child_name: &str,
    subst_parent_path: &Path,
    parent_sig: &[SignatureItem],
    id: Ident,
    mut md: ModuleDeclaration,
    ctx: &super::context::TypeContext,
) -> (Ident, Arc<ModuleDeclaration>) {
    // OCaml compiler/ml/env.ml:1568 stores `EnvLazy.create (sub, md)` in
    // `comp_modules`, env.ml:865-882 forces that thunk only for
    // `Env.find_module`, and env.ml:475-477 applies
    // `Subst.modtype sub md.md_type`. Keep all Rust component-declaration
    // freshening through this single force point so signature binder stamps are
    // consumed where the OCaml lazy thunk is forced.
    crate::cmi::persistent_env::freshen_component_module_declaration_bound_idents(
        &mut md,
        parent_sig,
        subst_parent_path,
        ctx,
    );
    let md = Arc::new(md);
    ctx.register_qualified_module_decl(cache_parent_path, child_name, id, md.clone());
    (id, md)
}

fn push_path_unique(candidates: &mut Vec<Path>, candidate: Path) {
    if !candidates.iter().any(|existing| existing.same(&candidate)) {
        candidates.push(candidate);
    }
}

fn raw_sig_candidate_paths_for_access_path(
    access_path: &Path,
    ctx: &super::context::TypeContext,
) -> Vec<Path> {
    let Ok((head, _components)) = access_path.flatten() else {
        return Vec::new();
    };
    if !(head.is_persistent() || head.stamp() == 0) {
        return Vec::new();
    }

    let mut candidates = Vec::new();
    // OCaml compiler/ml/env.ml:1517 scrapes the alias target before
    // env.ml:1530 `prefix_idents`; env.ml:1567-1578 then stores child
    // declaration/component thunks from that raw signature item. Rust records
    // the same alias-source-to-selected-component relation when building the
    // component table, so raw backing signatures come from the captured alias
    // declaration rather than flattened path spelling.
    for alias_source in ctx.alias_sources_for_component_path(access_path) {
        push_path_unique(&mut candidates, alias_source);
    }
    push_path_unique(&mut candidates, Path::pident(*head));
    candidates
}

fn self_alias_raw_parent_module_item(
    access_path: &Path,
    module_name: &str,
    runtime_pos: usize,
    md: &ModuleDeclaration,
    ctx: &super::context::TypeContext,
) -> Option<(Ident, ModuleDeclaration, Signature, Path)> {
    let selected_path = submodule_lookup_path(access_path, module_name, runtime_pos, md);
    let is_self_alias = matches!(
        &md.md_type,
        super::decl::ModuleType::MtyAlias(_, target)
            if target.same(&selected_path)
                || alias_target_matches_raw_parent_child(target, access_path, module_name, ctx)
    );
    if !is_self_alias {
        return None;
    }

    raw_sig_candidate_paths_for_access_path(access_path, ctx)
        .into_iter()
        .filter_map(|raw_parent_path| {
            let PathView::Pident(id) = raw_parent_path.view() else {
                return None;
            };
            if !(id.is_persistent() || id.stamp() == 0) {
                return None;
            }
            let raw_parent_sig = ctx.find_raw_module_sig(id.name())?;
            Some((raw_parent_sig, raw_parent_path))
        })
        .find_map(|(raw_parent_sig, raw_parent_path)| {
            raw_parent_sig.iter().find_map(|item| match item {
                SignatureItem::SigModule(id, raw_md, _) if id.name() == module_name => Some((
                    *id,
                    raw_md.clone(),
                    (*raw_parent_sig).clone(),
                    raw_parent_path,
                )),
                _ => None,
            })
        })
}

fn alias_target_matches_raw_parent_child(
    target: &Path,
    access_path: &Path,
    module_name: &str,
    ctx: &super::context::TypeContext,
) -> bool {
    if target.last() != module_name {
        return false;
    }
    let Some(parent) = target.parent() else {
        return false;
    };
    if parent.same(access_path) {
        return true;
    }

    raw_sig_candidate_paths_for_access_path(access_path, ctx)
        .into_iter()
        .any(|candidate| parent.same(&candidate))
}

fn access_path_is_direct_opened_component(env: &super::env::Env, access_path: &Path) -> bool {
    // OCaml compiler/core/res_compmisc.ml:56-62 opens implicit modules via
    // compiler/ml/env.ml:1874-1877, which adds opened component bindings
    // without a root module binding. Test that origin in Env rather than
    // matching root names.
    access_path
        .parent()
        .is_some_and(|p| p.as_pident().is_some())
        && env.path_starts_with_opened_component(access_path)
}

fn build_local_module_components(
    stored: &StoredModuleComponents,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &super::context::TypeContext,
    cache_mode: super::typecore::ComponentLookupApi,
) -> Option<QualifiedModuleComponents> {
    let env = stored.seed_env.as_ref();
    let access_path = &stored.access_path;
    let md = &stored.module_decl;
    let parent_substitution_context =
        stored
            .parent_context
            .as_ref()
            .map(|(parent_access_path, parent_sig)| {
                (parent_access_path, parent_sig.as_ref().as_slice())
            });
    let source_prefix = stored.source_prefix.get();
    if ctx.persistent_env_is_in_process()
        && let Some(alias_path) = md.md_type.ident_or_alias_path()
        && let PathView::Pident(alias_id) = alias_path.view()
        && alias_id.is_persistent()
    {
        let ps = {
            let pers = pers_env.as_mut()?;
            let ps = pers.find_pers_struct(alias_id.name(), ctx);
            // env.ml:872-875 forces `ps_sig = Subst.signature identity sign`
            // here, freshening the unit's bound identifiers. Reserve those
            // stamps (the rename itself stays deferred) so later identifiers
            // get OCaml's stamps.
            if ps.is_some() {
                ctx.trigger_module_sig_rename(alias_id.name());
            }
            ps
        };
        if let Some(ps) = ps {
            let source_prefix = Path::pident(Ident::create_persistent(alias_id.name()));
            // OCaml compiler/ml/env.ml:1516-1518 calls `scrape_alias` before
            // component-table construction; scrape_alias at env.ml:1435-1446
            // reaches `find_module`, whose persistent Pident branch at
            // env.ml:872-875 reads the persistent structure. In in-process
            // mode the portable signature has already been internalized into
            // the worker store, so share that component signature and let the
            // view apply the selected access path lazily to forced items
            // instead of renaming and copying the unit's signature.
            return Some(
                QualifiedModuleComponents::new_with_child_components_arc_and_value_source_prefix(
                    *access_path,
                    ps.ps_sig.clone(),
                    HashMap::new(),
                    Some(source_prefix),
                    ctx,
                ),
            );
        }
    }

    // A child of an in-process unit's alias view. OCaml builds that view from
    // `scrape_alias`, which strengthens the unit's signature with
    // `~aliasable:true` (env.ml:1440-1446, mtype.ml:96-100): this module is
    // `Mty_alias (Unit.Child)` there, so building its components reaches
    // `find_module` (env.ml:876-881), which forces the unit's `comp_modules`
    // thunk for it, `Subst.modtype` freshening its bound identifiers
    // (env.ml:475-477).
    if !matches!(md.md_type, super::decl::ModuleType::MtyAlias(..))
        && let Some(source) = source_prefix
        && let PathView::Pdot(parent, name, _) = source.view()
        && !source.same(access_path)
    {
        let _ = crate::types::typecore::lookup_module_in_resolved_path(
            parent,
            name.as_str(),
            env,
            pers_env,
            ctx,
        );
    }

    if let super::decl::ModuleType::MtyAlias(_, alias_path) = &md.md_type {
        // OCaml compiler/ml/env.ml:1517 calls `scrape_alias` before building
        // component tables. `scrape_alias` at env.ml:1440-1446 resolves an
        // alias with `find_module`, and env.ml:865-882 forces the final
        // env.ml:1568 `comp_modules` thunk for that target before returning
        // the module type whose signature is used below.
        match &alias_path.view() {
            PathView::Pdot(parent, name, _) => {
                // OCaml compiler/ml/env.ml:1517 calls `scrape_alias` for
                // component-table construction, and scrape_alias reaches
                // env.ml:865-882 `find_module`, which forces env.ml:1568's
                // module-declaration thunk.
                let _ = crate::types::typecore::lookup_module_in_resolved_path(
                    parent,
                    name.as_str(),
                    env,
                    pers_env,
                    ctx,
                );
            }
            PathView::Pident(id) if id.is_persistent() => {
                // OCaml compiler/ml/env.ml:1516-1518 scrapes aliases while
                // building component tables, which can force env.ml:719-721
                // `ps_sig` through env.ml:865-875.
                if let Some(pers) = pers_env.as_mut() {
                    let _ = pers.force_lazy_signature_rename(id.name(), ctx);
                } else if access_path_is_direct_opened_component(env, access_path)
                    && env.find_module(id.name_atom()).is_err()
                {
                    // OCaml compiler/ml/env.ml:1440-1446 reaches
                    // env.ml:865-875 for persistent alias targets while
                    // env.ml:1516-1518 scrapes aliases before component-table
                    // construction. env.ml:867-870 first checks `env.modules`;
                    // only env.ml:872-875's `Not_found` branch forces
                    // `ps_sig = Subst.signature identity sign` from
                    // env.ml:719-721. ctype expression expansion can reach
                    // direct opened components without carrying PersistentEnv;
                    // detect that through the opened Env binding from
                    // compiler/ml/env.ml:1874-1877. The TypeContext guard is
                    // set while compiler/ml/typemod.ml:1710-1719's package
                    // `wrap_constraint` equivalent walks inclusion types in a
                    // Rust-only probe, where no OCaml lookup has yet forced
                    // this alias target.
                    ctx.trigger_module_sig_rename(id.name());
                }
            }
            PathView::Pident(_) => {}
            PathView::Papply(_, _) => {}
        }
    }
    let (raw_sig, resolved_name) =
        if let Some(resolved) = env.resolve_module_type(&md.md_type, pers_env, ctx, cache_mode) {
            resolved
        } else {
            let alias_target = match &md.md_type {
                super::decl::ModuleType::MtyAlias(_, target) => Some(target.as_ref()),
                _ => None,
            };
            (match alias_target.map(|p| p.view()) {
                Some(PathView::Pident(alias_id)) if alias_id.is_persistent() =>
                {
                    // OCaml compiler/ml/env.ml:1517 calls `scrape_alias` before
                    // building component tables; env.ml:1440-1446 resolves
                    // `Mty_alias (_, path)` with `find_module`, whose `Pident`
                    // case at env.ml:865-875 checks the persistent table
                    // directly and forces `ps_sig` at env.ml:872-875.
                    let renamed_sig = if let Some(pers) = pers_env.as_mut() {
                        pers.get_renamed_sig_shared(alias_id.name(), ctx)
                    } else {
                        ctx.trigger_module_sig_rename(alias_id.name());
                        ctx.renamed_module_sig(alias_id.name())
                    };
                    renamed_sig.map(|renamed_sig| {
                        (
                            crate::types::typecore::copy_lookup_signature_for_subst(
                                renamed_sig.as_ref(),
                                ctx,
                            ),
                            Some(alias_id.name().to_string()),
                        )
                    })
                }
                _ => None,
            })?
        };
    let pident_sibling_alias_name =
        parent_substitution_context
            .as_ref()
            .and_then(|(_, parent_sig)| {
                let super::decl::ModuleType::MtyAlias(_, target) = &md.md_type else {
                    return None;
                };
                let PathView::Pident(alias_id) = &target.view() else {
                    return None;
                };
                parent_sig
                    .iter()
                    .any(|item| {
                        matches!(
                            item,
                            SignatureItem::SigModule(id, _, _) if id.same(alias_id)
                        )
                    })
                    .then(|| alias_id.name().to_string())
            });
    let shared_access_path = Arc::new(*access_path);
    let mut qualified_sig = crate::types::typecore::qualify_resolved_signature_for_local_components(
        access_path,
        &md.md_type,
        &raw_sig,
        resolved_name.as_deref(),
        pers_env,
        ctx,
    );
    if let Some((parent_access_path, parent_sig)) = parent_substitution_context {
        // OCaml compiler/ml/env.ml:1513-1518 stores the parent substitution inside
        // the lazy component thunk. When env.ml:1517 scrapes a child alias, the
        // scraped signature is still processed with env.ml:1530-1538
        // `prefix_idents`, and compiler/ml/subst.ml:303-309 rewrites value types
        // that mention sibling modules such as `DocumentClient.t`.
        crate::cmi::persistent_env::substitute_type_paths_in_child_sig(
            &qualified_sig,
            parent_sig,
            parent_access_path,
            ctx,
        );
        if let Some(alias_name) = pident_sibling_alias_name {
            // OCaml compiler/ml/subst.ml:69-76 rewrites the sibling alias
            // binder through the parent component substitution, and
            // compiler/ml/env.ml:1530-1538 then prefixes the scraped signature
            // with the selected child path. Rust may resolve the sibling
            // signature through the working env without forcing the sibling
            // module declaration, so apply that same parent-prefix-to-selected
            // substitution to the copied signature without consuming extra
            // component-thunk stamps.
            let target_prefix = Path::pdot(*parent_access_path, alias_name);
            crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                &qualified_sig,
                &target_prefix,
                &shared_access_path,
                ctx,
            );
            crate::cmi::persistent_env::rewrite_sig_paths_by_path_prefix(
                &mut qualified_sig,
                &target_prefix,
                &shared_access_path,
                ctx,
            );
        }
        crate::cmi::persistent_env::substitute_module_alias_paths_in_child_sig(
            &mut qualified_sig,
            parent_sig,
            parent_access_path,
            ctx,
        );
    }
    if raw_sig.len() != qualified_sig.len() {
        return None;
    }
    let shared_source_prefix = source_prefix.map(|source| Arc::new(*source));
    if let Some(source) = shared_source_prefix.as_ref()
        && !source.same(access_path)
    {
        // A child of an in-process unit's components: its items name each
        // other through the unit (`Unit.Sub.u`); `prefix_idents`
        // (env.ml:1454-1481, 1530-1538) puts them at the access path.
        crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
            &qualified_sig,
            source,
            &shared_access_path,
            ctx,
        );
        crate::cmi::persistent_env::rewrite_sig_paths_by_path_prefix(
            &mut qualified_sig,
            source,
            &shared_access_path,
            ctx,
        );
        strengthen_view_types(&mut qualified_sig, source, ctx);
    }

    let qualified_sig = Arc::new(qualified_sig);
    // OCaml compiler/ml/env.ml:1548-1578 closes child `comp_components`
    // thunks over the evolving `env` that is extended while walking the parent
    // signature. Every child `comp_components` thunk should capture that
    // evolving environment, independent of typedtree output mode; env.ml:1579
    // stores the raw child module only after creating the thunk.
    let mut working_env = Some(env.clone());
    let use_qualified_items_for_env = matches!(md.md_type, super::decl::ModuleType::MtyAlias(..));
    let qualified_sig_for_children = qualified_sig.clone();
    let mut child_components = HashMap::new();
    let mut runtime_pos = 0usize;

    // Match OCaml `components_of_module_maker`: component tables use the
    // qualified view, but the evolving local env is extended from the raw
    // signature items in left-to-right order.
    for (raw_item, qualified_item) in raw_sig.iter().zip(qualified_sig.iter()) {
        match (raw_item, qualified_item) {
            (SignatureItem::SigValue(_, _), SignatureItem::SigValue(_, desc)) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    runtime_pos += 1;
                }
            }
            (SignatureItem::SigType(id, decl, _), SignatureItem::SigType(_, qualified_decl, _)) => {
                if let Some(working_env) = working_env.as_mut() {
                    let env_decl = if use_qualified_items_for_env {
                        qualified_decl.clone()
                    } else {
                        decl.clone()
                    };
                    working_env.add_type(*id, env_decl);
                }
            }
            (SignatureItem::SigTypext(_, _, _), SignatureItem::SigTypext(_, _, _))
            | (SignatureItem::SigClass, SignatureItem::SigClass) => {
                runtime_pos += 1;
            }
            (SignatureItem::SigModule(id, child_md, _), SignatureItem::SigModule(_, qmd, _)) => {
                if let Some(working_env) = working_env.as_mut() {
                    let child_access_path =
                        ctx.dotted_from_ident(shared_access_path.clone(), *id, runtime_pos as i32);
                    let env_decl = strengthened_child_env_decl(
                        if use_qualified_items_for_env {
                            qmd
                        } else {
                            child_md
                        },
                        *id,
                        shared_source_prefix
                            .as_ref()
                            .filter(|source| !source.same(access_path)),
                        runtime_pos,
                        ctx,
                    );
                    // OCaml compiler/ml/env.ml:1573-1578 stores the child
                    // component thunk with the final substitution built by
                    // env.ml:1530-1531/1454-1486 `prefix_idents`. Rust
                    // materializes that substituted child module declaration in
                    // the qualified signature item.
                    let component_decl = if use_qualified_items_for_env {
                        qmd.clone()
                    } else {
                        child_md.clone()
                    };
                    working_env.add_module_with_component_context(
                        *id,
                        env_decl,
                        component_decl,
                        child_access_path,
                        Some((*access_path, qualified_sig_for_children.clone())),
                    );
                }
                if let Some(working_env) = working_env.as_ref()
                    && let Some(stored) =
                        working_env.local_module_components_shared(&Path::pident(*id))
                {
                    child_components.insert(id.name().to_string(), (runtime_pos, stored));
                }
                runtime_pos += 1;
            }
            (SignatureItem::SigModtype(id, mtd), SignatureItem::SigModtype(_, _)) => {
                if let Some(working_env) = working_env.as_mut() {
                    let env_mtd = if use_qualified_items_for_env {
                        match qualified_item {
                            SignatureItem::SigModtype(_, qualified_mtd) => qualified_mtd.clone(),
                            _ => return None,
                        }
                    } else {
                        mtd.clone()
                    };
                    working_env.add_modtype(*id, env_mtd);
                }
            }
            (SignatureItem::SigClassType, SignatureItem::SigClassType) => {}
            _ => return None,
        }
    }

    Some(
        QualifiedModuleComponents::new_with_complete_child_components_arc(
            *access_path,
            qualified_sig,
            child_components,
            ctx,
        ),
    )
}

#[derive(Debug, Clone)]
pub(crate) struct StoredModuleComponents {
    seed_env: Box<super::env::Env>,
    access_path: Path,
    module_decl: ModuleDeclaration,
    parent_context: Option<(Path, Arc<Signature>)>,
    /// For a child of components whose signature names its items through an
    /// in-process unit (`Unit.Sub.t`), that unit-rooted path of this child.
    source_prefix: OnceCell<Path>,
    cached: OnceCell<Rc<QualifiedModuleComponents>>,
    /// The world view this module is a child of, and its ordinal there,
    /// when the module's own path is a view key
    /// (`ModuleView::structure_child`): its components are that view.
    world_child: OnceCell<(Arc<super::module_view::ModuleView>, u32)>,
    /// A child of a world view, kept by the worker for every compilation
    /// that adopts the view (`ViewTables`). Nothing a compilation builds is
    /// cached in it: its tables, when its path has no world view (a functor,
    /// a module type declared in another unit), are built for the
    /// compilation that asks and kept by that compilation.
    of_view: std::cell::Cell<bool>,
    /// Built during a store build (see `StructureComponentTables::in_store`).
    in_store: bool,
    /// Key of this module's compilation-private components (see
    /// `TypeContext::local_stored_components`).
    local_id: u64,
    cached_piece: OnceCell<Rc<super::context::StorePiece>>,
    functor_component_result: OnceCell<ModuleType>,
    functor_component_piece: OnceCell<Rc<super::context::StorePiece>>,
    functor_result_subst_cache: OnceCell<RefCell<HashMap<Path, FunctorResultSubst>>>,
}

impl StoredModuleComponents {
    pub(crate) fn new(
        seed_env: super::env::Env,
        access_path: Path,
        module_decl: ModuleDeclaration,
    ) -> Self {
        Self::new_with_parent_context(seed_env, access_path, module_decl, None)
    }

    pub(crate) fn new_with_parent_context(
        seed_env: super::env::Env,
        access_path: Path,
        module_decl: ModuleDeclaration,
        parent_context: Option<(Path, Arc<Signature>)>,
    ) -> Self {
        Self {
            seed_env: Box::new(seed_env),
            access_path,
            module_decl,
            parent_context,
            source_prefix: OnceCell::new(),
            cached: OnceCell::new(),
            world_child: OnceCell::new(),
            of_view: std::cell::Cell::new(false),
            in_store: super::thread_store::store_build_active(),
            local_id: {
                static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
                NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            },
            cached_piece: OnceCell::new(),
            functor_component_result: OnceCell::new(),
            functor_component_piece: OnceCell::new(),
            functor_result_subst_cache: OnceCell::new(),
        }
    }

    /// The components of this module: the world's view of its path when it
    /// has one (one load of the child's cell and one probe of the
    /// compilation's component cache once the view is built), else the
    /// tables built for this compilation or worker.
    pub(crate) fn with_components<R>(
        &self,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &super::context::TypeContext,
        cache_mode: super::typecore::ComponentLookupApi,
        f: impl FnOnce(Components<'_>) -> R,
    ) -> Option<R> {
        if let Some((parent, ordinal)) = self.world_child.get()
            && let Some(view) = super::typecore::adopt_child_view(parent, *ordinal, pers_env, ctx)
        {
            return Some(f(Components::World(&view)));
        }
        self.with_local_components(pers_env, ctx, cache_mode, |components| {
            f(Components::Local(components))
        })
    }

    /// The seed environment of this module's tables: what the scan of its
    /// parent had installed when it reached the module.
    pub(crate) fn seed_env(&self) -> &super::env::Env {
        &self.seed_env
    }

    /// The tables built for this compilation or worker, whatever view the
    /// world has of the module's path.
    pub(crate) fn with_local_components<R>(
        &self,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &super::context::TypeContext,
        cache_mode: super::typecore::ComponentLookupApi,
        f: impl FnOnce(&QualifiedModuleComponents) -> R,
    ) -> Option<R> {
        if self.of_view.get() {
            // One probe of the compilation's table; the build is once per
            // compilation.
            if let Some(components) = ctx.local_stored_components(self.local_id) {
                return Some(f(components.as_ref()));
            }
            let components = Rc::new(self.build_components(pers_env, ctx, cache_mode)?);
            ctx.set_local_stored_components(self.local_id, components.clone());
            return Some(f(components.as_ref()));
        }
        if let Some(components) = self.cached.get().cloned() {
            // A shared result is valid for this compilation only when it
            // answers the build's guarded reads the same way.
            let piece = self.cached_piece.get();
            if piece.is_none_or(|piece| ctx.store_guards_hold(piece)) {
                if ctx.compiler_counters_enabled() {
                    crate::perf_counters::record_stored_component_cached(ctx);
                }
                if let Some(piece) = piece {
                    ctx.touch_store_piece(piece);
                }
                return Some(f(components.as_ref()));
            }
            if super::context::store_debug_enabled() {
                eprintln!("[store-guard-miss] {}", self.access_path.name());
            }
        }

        if self.in_store {
            if let Some(components) = ctx.local_stored_components(self.local_id) {
                // Compilation-private, like the build that produced it.
                ctx.poison_store_build_for("local-stored-components");
                return Some(f(components.as_ref()));
            }
            let (components, piece) =
                ctx.build_in_store_guarded(|| self.build_components(pers_env, ctx, cache_mode));
            let components = Rc::new(components?);
            match piece {
                Some(piece) => {
                    if self.cached.set(components.clone()).is_ok() {
                        let _ = self.cached_piece.set(piece);
                    } else {
                        // The shared result failed this compilation's guards:
                        // keep this build for the rest of the compilation.
                        ctx.set_local_stored_components(self.local_id, components.clone());
                    }
                }
                // Built from this compilation's private state (such as a
                // renamed persistent signature): keep it for this compilation
                // only.
                None => ctx.set_local_stored_components(self.local_id, components.clone()),
            }
            return Some(f(components.as_ref()));
        }

        let components = Rc::new(self.build_components(pers_env, ctx, cache_mode)?);
        if self.cached.set(components.clone()).is_err()
            && let Some(cached) = self.cached.get().cloned()
        {
            return Some(f(cached.as_ref()));
        }
        Some(f(components.as_ref()))
    }

    fn build_components(
        &self,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &super::context::TypeContext,
        cache_mode: super::typecore::ComponentLookupApi,
    ) -> Option<QualifiedModuleComponents> {
        let components = build_local_module_components(self, pers_env, ctx, cache_mode)?;
        if ctx.compiler_counters_enabled() {
            crate::perf_counters::record_stored_component_build(ctx, cache_mode);
        }
        Some(components)
    }

    pub(crate) fn instantiate_functor_result_for_application(
        &self,
        arg_path: &Path,
        ctx: &super::context::TypeContext,
    ) -> Option<ModuleType> {
        let ModuleType::MtyFunctor { param, result, .. } = &self.module_decl.md_type else {
            return None;
        };
        // A store-resident component is shared with later compilations: its
        // cached results must be store builds, and a result for an argument
        // path local to this compilation is not cached at all.
        let shareable_arg = path_non_apply_root_is_persistent_or_global(arg_path);
        if let Some(cache) = self.functor_result_subst_cache.get()
            && let Some((cached, piece)) = cache.borrow().get(arg_path).cloned()
        {
            if let Some(piece) = piece {
                ctx.touch_store_piece(&piece);
            }
            return Some(cached);
        }
        let parent_context = self
            .parent_context
            .as_ref()
            .map(|(path, sig)| (path, sig.as_ref().as_slice()));
        let compute_component_result = || {
            // OCaml compiler/ml/env.ml:1595-1602 stores `fcomp_res =
            // Subst.modtype sub ty_res` in `Functor_comps` when the functor
            // component table is forced. compiler/ml/env.ml:1744-1756 then
            // reuses that cached result for each `components_of_functor_appl`
            // argument before applying `Subst.add_module fcomp_param p2`.
            crate::cmi::persistent_env::freshen_functor_component_module_type(
                result.as_ref(),
                parent_context,
                ctx,
            )
        };
        let component_result = if self.of_view.get() {
            // Instantiated for the compilation: the result's nodes are its
            // own, and the compilation caches the applied path's components.
            compute_component_result()
        } else if let Some(cached) = self.functor_component_result.get() {
            if let Some(piece) = self.functor_component_piece.get() {
                ctx.touch_store_piece(piece);
            }
            cached.clone()
        } else if self.in_store {
            let (computed, piece) = ctx.build_in_store(compute_component_result);
            if let Some(piece) = piece
                && self.functor_component_result.set(computed.clone()).is_ok()
            {
                let _ = self.functor_component_piece.set(piece);
            }
            computed
        } else {
            self.functor_component_result
                .get_or_init(compute_component_result)
                .clone()
        };
        let substitute = || {
            crate::cmi::persistent_env::substitute_functor_result_module_path(
                &component_result,
                param,
                arg_path,
                ctx,
            )
        };
        let (substituted, piece, cacheable) = if self.of_view.get() {
            (substitute(), None, false)
        } else if self.in_store {
            if shareable_arg {
                let (substituted, piece) = ctx.build_in_store(substitute);
                let cacheable = piece.is_some();
                (substituted, piece, cacheable)
            } else {
                (substitute(), None, false)
            }
        } else {
            (substitute(), None, true)
        };
        if cacheable {
            self.functor_result_subst_cache
                .get_or_init(|| RefCell::new(HashMap::new()))
                .borrow_mut()
                .insert(*arg_path, (substituted.clone(), piece));
        }
        Some(substituted)
    }
}

/// What one worker derives from a world view: the layer tables `open`
/// installs, and one `StoredModuleComponents` per child module, which names
/// the child's world view when its path has one and otherwise holds what a
/// compilation needs to build the child's tables for itself. No type node
/// and no store build.
pub(crate) struct ViewTables {
    access_path: Arc<Path>,
    opened: OnceCell<Rc<super::env::OpenedLayers>>,
    children: RefCell<HashMap<String, Option<ChildComponents>>>,
    scan: RefCell<ChildComponentScanState>,
}

impl ViewTables {
    pub(crate) fn new(view: &super::module_view::ModuleView) -> Self {
        ViewTables {
            access_path: Arc::new(*view.access_path()),
            opened: OnceCell::new(),
            children: RefCell::new(HashMap::new()),
            scan: RefCell::new(ChildComponentScanState::Pending(ChildScanCursor::default())),
        }
    }

    /// `comp_components` of child `name` (env.ml:1573-1578). One probe when
    /// the scan has passed the child; else the scan continues from where it
    /// stopped, so all lookups together visit each signature item once.
    pub(crate) fn child_components(
        &self,
        view: &Arc<super::module_view::ModuleView>,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Rc<StoredModuleComponents>)> {
        if let Some(cached) = self.children.borrow().get(name) {
            return cached.clone();
        }
        if matches!(*self.scan.borrow(), ChildComponentScanState::Complete) {
            self.children.borrow_mut().insert(name.to_string(), None);
            return None;
        }
        // env.ml:1548-1578: the thunks of a child view's children close over
        // the environment the scan of its ancestors had built when it
        // reached the child. This worker's scan of the parent holds it.
        let unseeded = matches!(
            &*self.scan.borrow(),
            ChildComponentScanState::Pending(cursor)
                if cursor.next_index == 0 && cursor.working_env.is_none()
        );
        if unseeded
            && let Some((parent, own_name)) = view.seed_parent()
            && let Some((_, stored)) = ctx
                .thread_store()
                .view_tables(&parent)
                .child_components(&parent, own_name, ctx)
            && let ChildComponentScanState::Pending(cursor) = &mut *self.scan.borrow_mut()
        {
            cursor.working_env = Some(stored.seed_env().clone());
        }
        // The scan's results are kept by the worker for every compilation
        // that adopts the view, so it must create nothing a compilation
        // owns: it installs the view's frozen declarations in the evolving
        // environment and creates no type node.
        let nodes_before = ctx.type_expr_count();
        let (found, _scanned) = scan_child_component_from_signature(
            &self.access_path,
            view.value_source(),
            view.signature_ref(),
            view.raw_signature(),
            Some(view),
            &mut self.children.borrow_mut(),
            &mut self.scan.borrow_mut(),
            name,
            ctx,
        );
        debug_assert_eq!(
            nodes_before,
            ctx.type_expr_count(),
            "the child scan of a view created a type node"
        );
        #[cfg(test)]
        CHILD_SCAN_STEPS.with(|steps| steps.set(steps.get() + _scanned as u64));
        found
    }

    /// The layer tables `open` adds for the view (env.ml:1841-1877), built
    /// once per worker: one hash insert per opened item, no type node.
    pub(crate) fn opened_layers(
        &self,
        view: &Arc<super::module_view::ModuleView>,
        ctx: &super::context::TypeContext,
    ) -> Rc<super::env::OpenedLayers> {
        self.opened
            .get_or_init(|| {
                let items = view.opened_items();
                let mut module_components = Vec::with_capacity(items.modules.len());
                for module in &items.modules {
                    let stored = if module.direct_persistent_alias {
                        // env.ml:1516-1518: the components of an alias
                        // of a persistent unit are that unit's.
                        let stored = StoredModuleComponents::new(
                            super::env::Env::empty(),
                            module.decl.md_path.expect("an opened module has its path"),
                            module.decl.as_ref().clone(),
                        );
                        stored.of_view.set(true);
                        if let Some((ordinal, _)) = view.world_child(module.id.name()) {
                            let _ = stored.world_child.set((view.clone(), ordinal));
                        }
                        Some(Rc::new(stored))
                    } else {
                        self.child_components(view, module.id.name(), ctx)
                            .map(|(_, stored)| stored)
                    };
                    if let Some(stored) = stored {
                        module_components.push((module.id, stored, module.pos));
                    }
                }
                Rc::new(super::env::OpenedLayers::from_view(items, module_components))
            })
            .clone()
    }
}

/// What a lookup through a module path receives: the world's view of the
/// path, or the tables one compilation (or one worker's store) built for a
/// path the world has no view of.
#[derive(Clone, Copy)]
pub(crate) enum Components<'a> {
    World(&'a Arc<super::module_view::ModuleView>),
    Local(&'a QualifiedModuleComponents),
}

// Passed by value down every lookup: a tag and a pointer.
const _: () = assert!(std::mem::size_of::<Components<'static>>() <= 16);

impl<'a> Components<'a> {
    /// An owned hold on the same components, for a caller that keeps them
    /// across another lookup. One reference-count increment.
    pub(crate) fn to_held(self) -> HeldComponents {
        match self {
            Components::World(view) => HeldComponents::World(view.clone()),
            Components::Local(components) => HeldComponents::Local(Rc::new(components.clone())),
        }
    }

    #[inline]
    pub(crate) fn access_path(self) -> &'a Path {
        match self {
            Components::World(view) => view.access_path(),
            Components::Local(components) => components.access_path(),
        }
    }

    #[inline]
    pub(crate) fn signature(self) -> &'a [SignatureItem] {
        match self {
            Components::World(view) => view.signature(),
            Components::Local(components) => components.signature(),
        }
    }

    #[inline]
    pub(crate) fn signature_arc(self) -> Arc<Signature> {
        match self {
            Components::World(view) => view.signature_arc(),
            Components::Local(components) => components.signature_arc(),
        }
    }

    /// See `QualifiedModuleComponents::rerooted_value_source`; a view's
    /// values are substituted when it is built.
    #[inline]
    pub(crate) fn rerooted_value_source(self) -> Option<&'a Path> {
        match self {
            Components::World(view) => view.value_source().map(|source| source.as_ref()),
            Components::Local(components) => components.rerooted_value_source(),
        }
    }

    pub(crate) fn lookup_value_for_access(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, ValueDescription)> {
        match self {
            Components::World(view) => view.lookup_value_for_access(name),
            Components::Local(components) => components.lookup_value_for_access(name, ctx),
        }
    }

    pub(crate) fn lookup_constructors(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Arc<Vec<ConstructorDescription>> {
        match self {
            Components::World(view) => view.lookup_constructors(name),
            Components::Local(components) => components.lookup_constructors(name, ctx),
        }
    }

    pub(crate) fn lookup_labels(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Arc<Vec<LabelDescription>> {
        match self {
            Components::World(view) => view.lookup_labels(name),
            Components::Local(components) => components.lookup_labels(name, ctx),
        }
    }

    pub(crate) fn type_label_family(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<super::decl::LabelArrayRef> {
        match self {
            Components::World(view) => view.type_label_family(name),
            Components::Local(components) => components.type_label_family(name, ctx),
        }
    }

    pub(crate) fn lookup_type(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(&'a Ident, &'a Arc<TypeDeclaration>)> {
        match self {
            Components::World(view) => view.lookup_type(name),
            Components::Local(components) => components.lookup_type(name, ctx),
        }
    }

    pub(crate) fn lookup_module(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, &'a Ident, &'a ModuleDeclaration)> {
        match self {
            Components::World(view) => view.lookup_module(name),
            Components::Local(components) => components.lookup_module(name, ctx),
        }
    }

    pub(crate) fn lookup_module_alias_target(
        self,
        name: &str,
        include_ident: bool,
        ctx: &super::context::TypeContext,
    ) -> Option<Arc<Path>> {
        match self {
            Components::World(view) => view.lookup_module_alias_target(name, include_ident),
            Components::Local(components) => {
                components.lookup_module_alias_target(name, include_ident, ctx)
            }
        }
    }

    /// The component tables of child `name`, for a child whose path the
    /// world has no view of: a worker keeps them per view.
    pub(crate) fn lookup_child_components(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Rc<StoredModuleComponents>)> {
        match self {
            Components::World(view) => ctx
                .thread_store()
                .view_tables(view)
                .child_components(view, name, ctx),
            Components::Local(components) => components.lookup_child_components(name, ctx),
        }
    }

    /// `find_module` of child `name`. A view's forced declaration is also
    /// registered with the compilation, where the tables of an alias path
    /// to the same module look for it.
    pub(crate) fn lookup_qualified_module_shared(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, Arc<ModuleDeclaration>)> {
        match self {
            Components::World(view) => {
                let (item, runtime_pos, forced) = view.lookup_forced_module(ctx.world(), name)?;
                if let Some((id, md)) = forced {
                    ctx.note_forced_view_module(view, item, name, id, &md);
                    return Some((runtime_pos, id, md));
                }
                // The pool had no room for the declaration: this
                // compilation forces its own, once (the force registers it).
                if let Some((id, md)) = ctx.find_qualified_module_decl(view.access_path(), name) {
                    return Some((runtime_pos, id, md));
                }
                let SignatureItem::SigModule(id, md, _) = &view.signature()[item] else {
                    return None;
                };
                let (id, md) = force_component_module_declaration_thunk(
                    view.access_path(),
                    name,
                    view.access_path(),
                    view.signature(),
                    *id,
                    md.clone(),
                    ctx,
                );
                Some((runtime_pos, id, md))
            }
            Components::Local(components) => components.lookup_qualified_module_shared(name, ctx),
        }
    }

    pub(crate) fn lookup_qualified_module(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, ModuleDeclaration)> {
        self.lookup_qualified_module_shared(name, ctx)
            .map(|(runtime_pos, id, md)| (runtime_pos, id, md.as_ref().clone()))
    }

    pub(crate) fn lookup_modtype(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(Ident, ModtypeDeclaration)> {
        match self {
            Components::World(view) => view.lookup_modtype(name),
            Components::Local(components) => components.lookup_modtype(name, ctx),
        }
    }

    pub(crate) fn lookup_qualified_modtype(
        self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(Ident, ModtypeDeclaration)> {
        match self {
            Components::World(view) => view.lookup_modtype(name),
            Components::Local(components) => components.lookup_qualified_modtype(name, ctx),
        }
    }
}

/// A compilation's hold on the components of one path: what its component
/// cache stores.
#[derive(Clone)]
pub(crate) enum HeldComponents {
    World(Arc<super::module_view::ModuleView>),
    Local(Rc<QualifiedModuleComponents>),
}

impl HeldComponents {
    #[inline]
    pub(crate) fn components(&self) -> Components<'_> {
        match self {
            HeldComponents::World(view) => Components::World(view),
            HeldComponents::Local(components) => Components::Local(components),
        }
    }
}

impl std::fmt::Debug for HeldComponents {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HeldComponents::World(view) => write!(f, "World({})", view.access_path().name()),
            HeldComponents::Local(components) => {
                write!(f, "Local({})", components.access_path().name())
            }
        }
    }
}

#[cfg(test)]
mod provenance_tests {
    use super::*;

    #[test]
    fn scanned_child_paths_share_the_component_root_and_keep_cached_allocations() {
        let ctx =
            super::super::context::TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let root = Path::pident(ctx.create_ident("Root"));
        let first = ctx.create_ident("First");
        let second = ctx.create_ident("Second");
        let module = |id| {
            SignatureItem::SigModule(
                id,
                ModuleDeclaration {
                    md_type: ModuleType::MtySignature(Arc::new(vec![])),
                    md_attributes: vec![],
                    md_loc: Default::default(),
                    md_path: None,
                },
                super::super::decl::RecStatus::TrecNot,
            )
        };
        let components =
            QualifiedModuleComponents::new(root, vec![module(first), module(second)], &ctx);
        let (first_pos, a) = components.lookup_child_components("First", &ctx).unwrap();
        let (second_pos, b) = components.lookup_child_components("Second", &ctx).unwrap();
        assert_eq!((first_pos, second_pos), (0, 1));
        assert_eq!(a.access_path, Path::pdot_pos(root, first.name_atom(), 0));
        assert_eq!(b.access_path, Path::pdot_pos(root, second.name_atom(), 1));
        let (_, again) = components.lookup_child_components("First", &ctx).unwrap();
        assert_eq!(again.access_path, a.access_path);
    }

    #[test]
    fn strengthened_children_and_modtypes_share_source_prefix_and_names() {
        let ctx =
            super::super::context::TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let mut arena = crate::parse_arena::ParseArena::new();
        let name = arena.push_string("Shared");
        let module_id = ctx.create_ast_ident(&arena, name);
        let modtype_id = ctx.create_ast_ident(&arena, name);
        let source = Arc::new(Path::pident(ctx.create_ident("Source")));
        let mut sig = vec![SignatureItem::SigModtype(
            modtype_id,
            super::super::decl::ModtypeDeclaration {
                mtd_type: None,
                mtd_attributes: vec![],
                mtd_loc: Default::default(),
            },
        )];
        strengthen_view_types(&mut sig, &source, &ctx);
        let md = ModuleDeclaration {
            md_type: ModuleType::MtySignature(Arc::new(vec![])),
            md_attributes: vec![],
            md_loc: Default::default(),
            md_path: None,
        };
        let child = strengthened_child_env_decl(&md, module_id, Some(&source), 3, &ctx);
        let ModuleType::MtyAlias(_, path) = &child.md_type else {
            panic!("alias")
        };
        assert_eq!(**path, Path::pdot_pos(*source, module_id.name_atom(), 3));
        let SignatureItem::SigModtype(_, mtd) = &sig[0] else {
            panic!("modtype")
        };
        let Some(ModuleType::MtyIdent(path)) = &mtd.mtd_type else {
            panic!("ident")
        };
        assert!(path.same(&Path::pdot(*source, modtype_id.name_atom())));
        for source in [&source, &Arc::new(*source)] {
            let unchanged = strengthened_child_env_decl(&child, module_id, Some(source), 3, &ctx);
            let ModuleType::MtyAlias(_, path) = &unchanged.md_type else {
                panic!("alias")
            };
            assert_eq!(**path, Path::pdot_pos(**source, module_id.name_atom(), 3));
        }
    }
}
