//! Lazy qualified module components, matching OCaml's EnvLazy backbone.
//!
//! OCaml memoizes `components_of_module_maker (env, sub, path, mty)` and then
//! answers repeated type/module/value lookups from that cached view. Rust used
//! to cache only copied signatures and still re-scan or re-copy declarations on
//! each lookup. This module provides the cached qualified view that the hot
//! module-resolution paths use as their source of truth.

use crate::fast_hash::AHashMap as HashMap;
use std::cell::{OnceCell, RefCell};
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
    modules: HashMap<smol_str::SmolStr, (usize, usize)>,
    /// Alias/ident module items, as (item index, runtime position), in order.
    alias_modules: Vec<(usize, usize)>,
    /// Module type items, in order.
    modtypes: Vec<usize>,
}

impl SignatureIndex {
    pub(crate) fn build(signature: &Signature) -> Self {
        let mut index = SignatureIndex::default();
        let mut runtime_pos = 0usize;
        for (idx, item) in signature.iter().enumerate() {
            match item {
                SignatureItem::SigValue(id, desc) => {
                    index.values.insert(smol_str::SmolStr::new_static(id.name()), (idx, runtime_pos));
                    if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                        runtime_pos += 1;
                    }
                }
                SignatureItem::SigType(id, _, _) => {
                    index.types.insert(smol_str::SmolStr::new_static(id.name()), idx);
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
                    index.modules.insert(smol_str::SmolStr::new_static(id.name()), (idx, runtime_pos));
                    runtime_pos += 1;
                }
                SignatureItem::SigModtype(_, _) => index.modtypes.push(idx),
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
    let mut seen = crate::fast_hash::AHashSet::new();
    while let Some(ty) = stack.pop() {
        if !ty.is_store() {
            ctx.poison_store_build_for("unit-signature");
            return;
        }
        if seen.insert(ty) {
            super::btype::iter_type_expr(ctx, ty, |child| stack.push(child));
        }
    }
}

fn path_non_apply_root_is_persistent_or_global(path: &Path) -> bool {
    fn root_ident(path: &Path) -> Option<&Ident> {
        match path {
            Path::Pident(id) => Some(id),
            Path::Pdot(prefix, _, _) => root_ident(prefix),
            Path::Papply(_, _) => None,
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
    let map_path = |p: &Path| crate::cmi::persistent_env::reroot_path(p, &prefixes);
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

/// Label counterpart of [`reroot_constructor_descriptions`] (env.ml:1548-1559).
fn reroot_label_descriptions(
    descs: &mut [LabelDescription],
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
    let map_path = |p: &Path| crate::cmi::persistent_env::reroot_path(p, &prefixes);
    for desc in descs.iter_mut() {
        if !(mentions(desc.lbl_arg) || mentions(desc.lbl_res)) {
            continue;
        }
        let mut cache = super::type_expr::TypeExprRefMap::new();
        let mut copy = |ty: super::type_expr::TypeExprRef| {
            super::typecore::copy_type_expr_mapping_paths(ctx, ty, &mut cache, &map_path)
        };
        desc.lbl_res = copy(desc.lbl_res);
        desc.lbl_arg = copy(desc.lbl_arg);
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
    let type_path = Path::pdot(access_path.clone(), type_name);
    build_type_constructors(out, &type_path, decl, Some(constructor_name), ctx);
}

/// `fst (Env.find_type_descrs path env)` for a variant declaration whose
/// descriptors live at `type_path` (compiler/ml/datarepr.ml:111-172 via
/// compiler/ml/env.ml:1542-1547), in declaration order.
pub(crate) fn constructors_of_type_path(
    type_path: &Path,
    decl: &TypeDeclaration,
    ctx: &super::context::TypeContext,
) -> Vec<ConstructorDescription> {
    let mut out = Vec::new();
    build_type_constructors(&mut out, type_path, decl, None, ctx);
    out.reverse();
    if let Some(access_path) = type_path.parent() {
        reroot_constructor_descriptions(&mut out, &[], &access_path, ctx);
    }
    out
}

/// `snd (Env.find_type_descrs path env)` for a record declaration, in label
/// position order (compiler/ml/datarepr.ml:174-188).
pub(crate) fn labels_of_type_path(
    type_path: &Path,
    decl: &TypeDeclaration,
    ctx: &super::context::TypeContext,
) -> Vec<LabelDescription> {
    let super::decl::TypeKind::TypeRecord(labels, repr) = &decl.type_kind else {
        return Vec::new();
    };
    let res_ty = ctx.new_generic_constr(type_path.clone(), decl.type_params.clone());
    let mut descs: Vec<LabelDescription> = labels
        .iter()
        .enumerate()
        .map(|(pos, ld)| LabelDescription {
            lbl_name: ld.ld_id.name().to_string(),
            lbl_runtime_name: ld.declaration_name(),
            lbl_res: res_ty,
            lbl_arg: super::ctype::remap_label_type_to_params(ctx, ld.ld_type, &decl.type_params),
            lbl_mut: ld.ld_mutable,
            lbl_optional: ld.ld_optional,
            lbl_pos: pos as i32,
            lbl_all: super::decl::LabelArrayRef(0),
            lbl_repres: repr.clone(),
            lbl_private: decl.type_private,
            lbl_loc: ld.ld_loc,
            lbl_attributes: ld.ld_attributes.clone(),
        })
        .collect();
    if let Some(access_path) = type_path.parent() {
        reroot_label_descriptions(&mut descs, &[], &access_path, ctx);
    }
    descs
}

fn build_type_constructors(
    out: &mut Vec<ConstructorDescription>,
    type_path: &Path,
    decl: &TypeDeclaration,
    constructor_name: Option<&str>,
    ctx: &super::context::TypeContext,
) {
    let super::decl::TypeKind::TypeVariant(cstrs, layout) = &decl.type_kind else {
        return;
    };

    let type_path = type_path.clone();
    for (position, cd) in cstrs.iter().enumerate() {
        if constructor_name.is_some_and(|name| cd.cd_id.name() != name) {
            continue;
        }

        let (cstr_args, cstr_arity, cstr_inlined) = match &cd.cd_args {
            super::decl::ConstructorArguments::CstrTuple(args) => {
                (args.clone(), args.len() as i32, None)
            }
            super::decl::ConstructorArguments::CstrRecord(labels) => {
                let inline_params =
                    super::typecore::inline_record_type_params(ctx, &decl.type_params, labels);
                let inline_path = Path::pdot(type_path.clone(), cd.cd_id.name());
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
                    let args = args.clone();
                    drop(desc);
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
                            for arg in &args {
                                crate::cmi::persistent_env::rewrite_type_expr_by_path_prefix_pub(
                                    *arg,
                                    &old_prefix,
                                    &new_prefix,
                                    ctx,
                                );
                            }
                        }
                    }
                    ctx.new_generic_constr(type_path.clone(), args.to_vec())
                }
                _ => {
                    drop(desc);
                    res_ty
                }
            }
        } else {
            ctx.new_generic_constr(type_path.clone(), decl.type_params.clone())
        };
        out.insert(
            0,
            ConstructorDescription {
                cstr_name: cd.cd_id.name().to_string(),
                cstr_res,
                // datarepr.ml:62-75: the variables of the arguments that the
                // GADT result type does not mention.
                cstr_existentials: super::env::constructor_existentials(
                    ctx,
                    &cstr_args,
                    cd.cd_res.map(|_| cstr_res),
                ),
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

fn build_matching_type_labels(
    out: &mut Vec<LabelDescription>,
    access_path: &Path,
    type_name: &str,
    decl: &TypeDeclaration,
    label_name: &str,
    ctx: &super::context::TypeContext,
) {
    let super::decl::TypeKind::TypeRecord(labels, repr) = &decl.type_kind else {
        return;
    };

    let mut res_ty = None;
    for (pos, ld) in labels.iter().enumerate() {
        if ld.ld_id.name() != label_name {
            continue;
        }
        let res_ty = *res_ty.get_or_insert_with(|| {
            let type_path = Path::pdot(access_path.clone(), type_name);
            ctx.new_generic_constr(type_path, decl.type_params.clone())
        });
        let label_desc = LabelDescription {
            lbl_name: ld.ld_id.name().to_string(),
            lbl_runtime_name: ld.declaration_name(),
            lbl_res: res_ty,
            lbl_arg: super::ctype::remap_label_type_to_params(ctx, ld.ld_type, &decl.type_params),
            lbl_mut: ld.ld_mutable,
            lbl_optional: ld.ld_optional,
            lbl_pos: pos as i32,
            lbl_all: super::decl::LabelArrayRef(0),
            lbl_repres: repr.clone(),
            lbl_private: decl.type_private,
            lbl_loc: ld.ld_loc,
            lbl_attributes: ld.ld_attributes.clone(),
        };
        out.insert(0, label_desc);
    }
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
                let ext_path = Path::pdot_pos(access_path.clone(), id.name(), ext_slot);
                let (cstr_args, cstr_arity, cstr_inlined) = match &ext.ext_args {
                    super::decl::ConstructorArguments::CstrTuple(args) => {
                        (args.clone(), args.len() as i32, None)
                    }
                    super::decl::ConstructorArguments::CstrRecord(labels) => {
                        let inline_params = super::typecore::inline_record_type_params(
                            ctx,
                            &ext.ext_type_params,
                            labels,
                        );
                        let inline_path = ext_path.clone();
                        let inline_constr =
                            ctx.new_generic_constr(inline_path.clone(), inline_params.clone());
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
                            type_inlined_types: vec![],
                            type_path: None,
                        };
                        (vec![inline_constr], 1, Some(Box::new(inline_decl)))
                    }
                };
                let ext_type_path = crate::cmi::persistent_env::substitute_sig_path(
                    &ext.ext_type_path,
                    signature,
                    access_path,
                );
                let cstr_res = ctx.new_generic_constr(ext_type_path, ext.ext_type_params.clone());
                constructors.insert(
                    0,
                    ConstructorDescription {
                        cstr_name: id.name().to_string(),
                        cstr_res,
                        // datarepr.ml:62-75, extension_descr.
                        cstr_existentials: super::env::constructor_existentials(
                            ctx,
                            &cstr_args,
                            ext.ext_ret_type,
                        ),
                        cstr_args,
                        cstr_arity,
                        cstr_kind: ConstructorKind::Extension(ext_path.clone()),
                        cstr_generalized: ext.ext_ret_type.is_some(),
                        cstr_private: ext.ext_private,
                        cstr_loc: ext.ext_loc,
                        cstr_attributes: ext.ext_attributes.clone(),
                        cstr_inlined,
                    },
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

fn build_labels_for_name(
    access_path: &Path,
    signature: &[SignatureItem],
    label_name: &str,
    ctx: &super::context::TypeContext,
) -> Vec<LabelDescription> {
    let mut labels = Vec::new();

    for item in signature {
        if let SignatureItem::SigType(id, decl, _) = item {
            build_matching_type_labels(&mut labels, access_path, id.name(), decl, label_name, ctx);
        }
    }

    labels
}

#[derive(Debug, Clone)]
struct ChildComponentScanState {
    working_env: Option<super::env::Env>,
    next_index: usize,
    runtime_pos: usize,
    complete: bool,
}

impl ChildComponentScanState {
    fn new() -> Self {
        Self {
            working_env: None,
            next_index: 0,
            runtime_pos: 0,
            complete: false,
        }
    }

    fn complete() -> Self {
        Self {
            working_env: None,
            next_index: 0,
            runtime_pos: 0,
            complete: true,
        }
    }

    fn working_env_mut(&mut self) -> &mut super::env::Env {
        self.working_env.get_or_insert_with(super::env::Env::empty)
    }
}

#[derive(Debug, Clone)]
struct StructureComponentTables {
    index: Arc<SignatureIndex>,
    component_values: RefCell<HashMap<String, Option<(usize, Ident, ValueDescription)>>>,
    constructors: RefCell<HashMap<String, Arc<Vec<ConstructorDescription>>>>,
    labels: RefCell<HashMap<String, Arc<Vec<LabelDescription>>>>,
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
    child_components: RefCell<HashMap<String, Option<(usize, Arc<StoredModuleComponents>)>>>,
    child_component_scan: RefCell<ChildComponentScanState>,
    // The component substitution for value lookups depends only on the
    // signature and access path; build it once per component table.
    value_subst_maps: RefCell<Option<Arc<crate::cmi::persistent_env::ValueSubstMaps>>>,
    /// Built during a store build: the tables may be shared with later
    /// compilations on this worker, so entries are forced as store builds and
    /// carry the replay record of their forcing.
    in_store: std::cell::Cell<bool>,
    store_pieces: RefCell<HashMap<(ForcedKind, String), Arc<super::context::StorePiece>>>,
    /// The layer tables `open` adds for this view, built on first open.
    opened_layers: OnceCell<(Arc<super::env::OpenedLayers>, Option<Arc<super::context::StorePiece>>)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ForcedKind {
    Value,
    Constructors,
    Labels,
    ChildComponents,
    QualifiedModule,
}

#[derive(Debug, Clone)]
pub(crate) struct QualifiedModuleComponents {
    access_path: Arc<Path>,
    signature: Arc<Signature>,
    tables: Arc<StructureComponentTables>,
    compiler_counters_enabled: bool,
    value_source_prefix: Option<Arc<Path>>,
}

fn scan_child_component_from_signature(
    access_path: &Path,
    source_prefix: Option<&Path>,
    signature: &Arc<Signature>,
    child_components: &mut HashMap<String, Option<(usize, Arc<StoredModuleComponents>)>>,
    state: &mut ChildComponentScanState,
    child_name: &str,
) -> (Option<(usize, Arc<StoredModuleComponents>)>, usize) {
    let start_index = state.next_index;
    let mut found = None;

    // OCaml compiler/ml/env.ml:1530-1578 computes component paths once,
    // stores module declarations in `comp_modules` at env.ml:1568-1569, and
    // separately stores child component thunks in `comp_components` at
    // env.ml:1573-1578. Persistent signatures need the same split so
    // qualified value lookup can descend through child components without
    // forcing `Subst.modtype` on the module declaration thunk.
    while state.next_index < signature.len() {
        let item = &signature[state.next_index];
        state.next_index += 1;
        match item {
            SignatureItem::SigValue(_, desc) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    state.runtime_pos += 1;
                }
            }
            SignatureItem::SigType(id, decl, _) => {
                state.working_env_mut().add_type(id.clone(), decl.clone());
            }
            SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                state.runtime_pos += 1;
            }
            SignatureItem::SigModule(id, md, _) => {
                let runtime_pos = state.runtime_pos;
                let child_access_path =
                    qualified_submodule_access_path(access_path, id.name(), runtime_pos, md);
                let stored = {
                    let working_env = state.working_env_mut();
                    working_env.add_module_with_component_context(
                        id.clone(),
                        md.clone(),
                        md.clone(),
                        child_access_path,
                        Some((access_path.clone(), signature.clone())),
                    );
                    working_env
                        .local_module_components_arc(&Path::pident(id.clone()))
                        .map(|stored| (runtime_pos, stored))
                };
                if let (Some(source), Some((_, stored))) = (source_prefix, &stored) {
                    let _ = stored
                        .source_prefix
                        .set(Path::pdot(source.clone(), id.name()));
                }
                // OCaml `Tbl.add` shadows earlier entries with the same name
                // (compiler/ml/env.ml:1577-1578), so keep the latest scanned
                // child component for this name.
                child_components.insert(id.name().to_string(), stored.clone());
                if id.name() == child_name {
                    found = stored;
                    state.runtime_pos += 1;
                    break;
                }
                state.runtime_pos += 1;
            }
            SignatureItem::SigModtype(id, mtd) => {
                state.working_env_mut().add_modtype(id.clone(), mtd.clone());
            }
            SignatureItem::SigClassType => {}
        }
    }

    if state.next_index >= signature.len() {
        state.complete = true;
        state.working_env = None;
        child_components
            .entry(child_name.to_string())
            .or_insert(None);
    }

    (found, state.next_index - start_index)
}

impl QualifiedModuleComponents {
    pub(crate) fn new(
        access_path: Path,
        signature: Signature,
        ctx: &super::context::TypeContext,
    ) -> Self {
        Self::new_with_child_components_arc(access_path, Arc::new(signature), HashMap::new(), ctx)
    }

    pub(crate) fn new_with_child_components(
        access_path: Path,
        signature: Signature,
        child_components: HashMap<String, (usize, Arc<StoredModuleComponents>)>,
        ctx: &super::context::TypeContext,
    ) -> Self {
        Self::new_with_child_components_arc(access_path, Arc::new(signature), child_components, ctx)
    }

    pub(crate) fn new_with_child_components_arc(
        access_path: Path,
        signature: Arc<Signature>,
        child_components: HashMap<String, (usize, Arc<StoredModuleComponents>)>,
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
        child_components: HashMap<String, (usize, Arc<StoredModuleComponents>)>,
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
        child_components: HashMap<String, (usize, Arc<StoredModuleComponents>)>,
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
        child_components: HashMap<String, (usize, Arc<StoredModuleComponents>)>,
        value_source_prefix: Option<Path>,
        child_component_scan_complete: bool,
        ctx: &super::context::TypeContext,
    ) -> Self {
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
                            Path::pdot(source.clone(), id.name()),
                            Path::pdot(access_path.clone(), id.name()),
                        ),
                        _ => (source.clone(), access_path.clone()),
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
                    &access_path,
                );
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
                    && let super::decl::ModuleType::MtyAlias(_, alias_source)
                    | super::decl::ModuleType::MtyIdent(alias_source) = &md.md_type
                {
                    let component_path =
                        Path::pdot_pos(access_path.clone(), id.name(), runtime_pos as i32);
                    // OCaml compiler/ml/env.ml:1517 `scrape_alias` follows
                    // the module declaration's alias path through
                    // env.ml:865-882 `find_module`, then env.ml:1530-1578
                    // stores thunks under the selected component path.
                    // Preserve the actual source path from the declaration
                    // instead of recovering it from flattened spelling.
                    ctx.register_component_alias_source(component_path, alias_source.clone());
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
                    component_modtypes.insert(id.name().to_string(), (id.clone(), component_mtd));
                }
            }
        }

        let child_components = child_components
            .into_iter()
            .map(|(name, component)| (name, Some(component)))
            .collect();

        Self {
            access_path: Arc::new(access_path),
            signature,
            tables: Arc::new(StructureComponentTables {
                index,
                component_values: RefCell::new(HashMap::new()),
                constructors: RefCell::new(HashMap::new()),
                labels: RefCell::new(HashMap::new()),
                modtypes: component_modtypes,
                qualified_modules: RefCell::new(HashMap::new()),
                qualified_modtypes: RefCell::new(HashMap::new()),
                child_components: RefCell::new(child_components),
                child_component_scan: RefCell::new(if child_component_scan_complete {
                    ChildComponentScanState::complete()
                } else {
                    ChildComponentScanState::new()
                }),
                value_subst_maps: RefCell::new(None),
                in_store: std::cell::Cell::new(super::thread_store::store_build_active()),
                store_pieces: RefCell::new(HashMap::new()),
                opened_layers: OnceCell::new(),
            }),
            compiler_counters_enabled: ctx.compiler_counters_enabled(),
            value_source_prefix: value_source_prefix.map(Arc::new),
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
        let known = self
            .tables
            .store_pieces
            .borrow()
            .get(&(kind, name.to_string()))
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
                self.tables
                    .store_pieces
                    .borrow_mut()
                    .insert((kind, name.to_string()), piece);
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
    ) -> Arc<super::env::OpenedLayers> {
        if let Some((layers, piece)) = self.tables.opened_layers.get() {
            if let Some(piece) = piece {
                ctx.touch_store_piece(piece);
            }
            return layers.clone();
        }
        if self.tables.in_store.get() {
            let (layers, piece) = ctx.build_in_store(build);
            let layers = Arc::new(layers);
            if let Some(piece) = piece {
                let _ = self.tables.opened_layers.set((layers.clone(), Some(piece)));
            }
            return layers;
        }
        let layers = Arc::new(build());
        let _ = self.tables.opened_layers.set((layers.clone(), None));
        layers
    }

    /// Keep these tables private to this compilation (their build read
    /// compilation-local state): later entries are forced locally.
    pub(crate) fn make_private(&self) {
        self.tables.in_store.set(false);
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
            ForcedKind::Labels => {
                self.tables.labels.borrow_mut().remove(name);
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

    pub(crate) fn cloned_signature(&self) -> Signature {
        self.signature.as_ref().clone()
    }

    fn cached_value_index(&self, name: &str) -> Option<(usize, usize)> {
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Value);
        }
        self.tables.index.values.get(name).copied()
    }


    fn cached_type_index(&self, name: &str) -> Option<usize> {
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Type);
        }
        self.tables.index.types.get(name).copied()
    }

    fn cached_module_index(&self, name: &str) -> Option<(usize, usize)> {
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Module);
        }
        self.tables.index.modules.get(name).copied()
    }

    pub(crate) fn lookup_value(&self, name: &str) -> Option<(usize, &Ident, &ValueDescription)> {
        let (idx, runtime_pos) = self.cached_value_index(name)?;
        match &self.signature[idx] {
            SignatureItem::SigValue(id, desc) => Some((runtime_pos, id, desc)),
            _ => None,
        }
    }

    pub(crate) fn lookup_value_for_access(&self, name: &str, ctx: &super::context::TypeContext) -> Option<(usize, Ident, ValueDescription)> {
        self.force_entry(ForcedKind::Value, name, ctx, || self.lookup_value_for_access_inner(name, ctx))
    }

    fn lookup_value_for_access_inner(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, ValueDescription)> {
        if let Some(cached) = self.tables.component_values.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Value);
            }
            return cached;
        }

        let (runtime_pos, id, desc) = self.lookup_value(name)?;
        let mut desc = super::typecore::copy_lookup_value_description_for_subst(desc, ctx);
        // Re-root the copy like the component's other items (see
        // `new_with_child_components_arc_and_value_source_prefix_inner`).
        if let Some(source) = self.rerooted_value_source() {
            crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                &[SignatureItem::SigValue(id.clone(), desc.clone())],
                source,
                self.access_path(),
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
        let result = Some((runtime_pos, id.clone(), desc));
        self.tables
            .component_values
            .borrow_mut()
            .insert(name.to_string(), result.clone());
        result
    }

    pub(crate) fn lookup_constructors(&self, name: &str, ctx: &super::context::TypeContext) -> Arc<Vec<ConstructorDescription>> {
        self.force_entry(ForcedKind::Constructors, name, ctx, || self.lookup_constructors_inner(name, ctx))
    }

    fn lookup_constructors_inner(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Arc<Vec<ConstructorDescription>> {
        if let Some(cached) = self.tables.constructors.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(
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
        let mut built = build_constructors_for_name(
            self.access_path(),
            self.signature.as_ref(),
            name,
            ctx,
        );
        reroot_constructor_descriptions(
            &mut built,
            self.signature.as_ref(),
            self.access_path(),
            ctx,
        );
        let built = Arc::new(built);
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
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

    pub(crate) fn lookup_labels(&self, name: &str, ctx: &super::context::TypeContext) -> Arc<Vec<LabelDescription>> {
        self.force_entry(ForcedKind::Labels, name, ctx, || self.lookup_labels_inner(name, ctx))
    }

    fn lookup_labels_inner(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Arc<Vec<LabelDescription>> {
        if let Some(cached) = self.tables.labels.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Label);
            }
            return cached;
        }

        // OCaml compiler/ml/env.ml:1548-1559 computes `comp_labels` from the
        // selected component path. For normal compilation, force just the label
        // bucket requested by typecore.ml:1107-1126-style qualified lookup; this
        // avoids constructing hundreds of unused JSX record labels per module view.
        let mut built = build_labels_for_name(
            self.access_path(),
            self.signature.as_ref(),
            name,
            ctx,
        );
        reroot_label_descriptions(&mut built, self.signature.as_ref(), self.access_path(), ctx);
        let built = Arc::new(built);
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
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

    pub(crate) fn lookup_type(&self, name: &str) -> Option<(&Ident, &Arc<TypeDeclaration>)> {
        let idx = self.cached_type_index(name)?;
        match &self.signature[idx] {
            SignatureItem::SigType(id, decl, _) => Some((id, decl)),
            _ => None,
        }
    }

    pub(crate) fn lookup_module(&self, name: &str) -> Option<(usize, &Ident, &ModuleDeclaration)> {
        let (idx, runtime_pos) = self.cached_module_index(name)?;
        match &self.signature[idx] {
            SignatureItem::SigModule(id, md, _) => Some((runtime_pos, id, md)),
            _ => None,
        }
    }

    pub(crate) fn lookup_child_components(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Arc<StoredModuleComponents>)> {
        self.force_entry(ForcedKind::ChildComponents, name, ctx, || {
            self.lookup_child_components_inner(name)
        })
    }

    fn lookup_child_components_inner(
        &self,
        name: &str,
    ) -> Option<(usize, Arc<StoredModuleComponents>)> {
        if let Some(cached) = self.tables.child_components.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(
                    crate::perf_counters::LazyLookupKind::ChildComponent,
                );
            }
            return cached;
        }

        let mut scan = self.tables.child_component_scan.borrow_mut();
        if scan.complete {
            self.tables
                .child_components
                .borrow_mut()
                .insert(name.to_string(), None);
            return None;
        }

        let mut child_components = self.tables.child_components.borrow_mut();
        let (built, scanned_items) = scan_child_component_from_signature(
            self.access_path(),
            self.value_source_prefix.as_deref(),
            &self.signature,
            &mut child_components,
            &mut scan,
            name,
        );
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
                crate::perf_counters::LazyLookupKind::ChildComponent,
                scanned_items,
                usize::from(built.is_some()),
            );
        }
        built
    }

    pub(crate) fn lookup_qualified_module_shared(&self, name: &str, ctx: &super::context::TypeContext) -> Option<(usize, Ident, Arc<ModuleDeclaration>)> {
        self.force_entry(ForcedKind::QualifiedModule, name, ctx, || self.lookup_qualified_module_shared_inner(name, ctx))
    }

    fn lookup_qualified_module_shared_inner(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, Arc<ModuleDeclaration>)> {
        let (idx, runtime_pos) = self.cached_module_index(name)?;
        if let Some((id, md)) = self.tables.qualified_modules.borrow().get(name).cloned() {
            let selected_path =
                qualified_submodule_access_path(self.access_path.as_ref(), name, runtime_pos, &md);
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
            if let Some((id, md)) = ctx.find_qualified_module_decl(self.access_path.as_ref(), name) {
                let selected_path =
                    qualified_submodule_access_path(self.access_path.as_ref(), name, runtime_pos, &md);
                if !module_decl_is_self_alias_for_access_path(&md, &selected_path) {
                    self.tables
                        .qualified_modules
                        .borrow_mut()
                        .insert(name.to_string(), (id.clone(), md.clone()));
                    return Some((runtime_pos, id, md));
                }
                // Same OCaml env.ml:865-882 / subst.ml:351-364 force boundary as
                // above: do not let a TypeContext-level self-alias placeholder hide
                // the raw component module-declaration thunk.
            }
            for source_prefix in ctx.alias_sources_for_component_path(self.access_path.as_ref()) {
                if let Some((id, md)) = ctx.find_qualified_module_decl(&source_prefix, name) {
                    let selected_path = qualified_submodule_access_path(
                        self.access_path.as_ref(),
                        name,
                        runtime_pos,
                        &md,
                    );
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
                        .insert(name.to_string(), (id.clone(), md.clone()));
                    ctx.register_qualified_module_decl(
                        self.access_path.as_ref(),
                        name,
                        id.clone(),
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
                    qualified_submodule_access_path(self.access_path.as_ref(), name, runtime_pos, &md);
                if !module_decl_is_self_alias_for_access_path(&md, &selected_path) {
                    // Same sharing as above, but reached from the flattened backing
                    // component view after the selected path forced the declaration.
                    self.tables
                        .qualified_modules
                        .borrow_mut()
                        .insert(name.to_string(), (id.clone(), md.clone()));
                    ctx.register_qualified_module_decl(
                        self.access_path.as_ref(),
                        name,
                        id.clone(),
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
            SignatureItem::SigModule(id, md, _) => (id.clone(), md.clone()),
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
                .insert(name.to_string(), (raw_id.clone(), md.clone()));
            // OCaml compiler/ml/env.ml:1568 stores one lazy module-declaration
            // thunk for the raw component item, and env.ml:1517-1519 can reach
            // that same thunk through a strengthened alias path after
            // env.ml:1435-1449 `scrape_alias`. Rust has separate component
            // views for paths such as `Webapi.Fetch` and `Webapi__Fetch`; cache
            // the forced declaration under the raw parent too so a later direct
            // raw lookup observes the already-forced OCaml thunk instead of
            // running compiler/ml/subst.ml:351-400 a second time.
            if !raw_parent_path.same(self.access_path.as_ref()) {
                ctx.register_qualified_module_decl(
                    &raw_parent_path,
                    name,
                    raw_id.clone(),
                    md.clone(),
                );
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
            .insert(name.to_string(), (id.clone(), md.clone()));
        Some((runtime_pos, id, md))
    }

    pub(crate) fn lookup_qualified_module(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, ModuleDeclaration)> {
        self.lookup_qualified_module_shared(name, ctx)
            .map(|(runtime_pos, id, md)| (runtime_pos, id, md.as_ref().clone()))
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
            .insert(name.to_string(), (id.clone(), mtd.clone()));
        Some((id, mtd))
    }
}

fn qualified_submodule_access_path(
    parent_access_path: &Path,
    module_name: &str,
    runtime_pos: usize,
    _md: &ModuleDeclaration,
) -> Path {
    if path_non_apply_root_is_persistent_or_global(parent_access_path) {
        // OCaml compiler/ml/env.ml:1454-1481 `prefix_idents` creates
        // component paths as `Pdot(root, name, pos)`, and env.ml:1573-1578
        // stores child component thunks under that prefixed path. Do not let an
        // alias module's own `md_path` replace the selected component path.
        Path::pdot_pos(
            parent_access_path.clone(),
            module_name.to_string(),
            runtime_pos as i32,
        )
    } else {
        Path::pdot_pos(
            parent_access_path.clone(),
            module_name.to_string(),
            runtime_pos as i32,
        )
    }
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
    ctx.register_qualified_module_decl(cache_parent_path, child_name, id.clone(), md.clone());
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
    push_path_unique(&mut candidates, Path::pident(head.clone()));
    candidates
}

fn self_alias_raw_parent_module_item(
    access_path: &Path,
    module_name: &str,
    runtime_pos: usize,
    md: &ModuleDeclaration,
    ctx: &super::context::TypeContext,
) -> Option<(Ident, ModuleDeclaration, Signature, Path)> {
    let selected_path = qualified_submodule_access_path(access_path, module_name, runtime_pos, md);
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
            let Path::Pident(id) = &raw_parent_path else {
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
                    id.clone(),
                    raw_md.clone(),
                    raw_parent_sig.clone(),
                    raw_parent_path.clone(),
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
    matches!(access_path.parent(), Some(Path::Pident(_)))
        && env.path_starts_with_opened_component(access_path)
}

fn build_local_module_components<'a>(
    env: &super::env::Env,
    access_path: &Path,
    md: &ModuleDeclaration,
    parent_substitution_context: Option<(&Path, &[SignatureItem])>,
    source_prefix: Option<&Path>,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a super::context::TypeContext,
    cache_mode: super::typecore::ComponentLookupApi,
) -> Option<QualifiedModuleComponents> {
    if ctx.persistent_env_is_in_process()
        && let super::decl::ModuleType::MtyAlias(_, Path::Pident(alias_id))
        | super::decl::ModuleType::MtyIdent(Path::Pident(alias_id)) = &md.md_type
        && alias_id.is_persistent()
        && cache_mode.forces_alias_sig()
    {
        let ps = {
            let pers = pers_env.as_mut()?;
            pers.find_pers_struct(alias_id.name(), ctx)
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
            // instead of renaming and copying the unit's signature. This skips
            // the rename's stamp consumption, so in-process ident stamps can
            // differ from OCaml's; in-process builds write no `.cmt` files.
            return Some(
                QualifiedModuleComponents::new_with_child_components_arc_and_value_source_prefix(
                    access_path.clone(),
                    ps.ps_sig.clone(),
                    HashMap::new(),
                    Some(source_prefix),
                    ctx,
                ),
            );
        }
    }

    if let super::decl::ModuleType::MtyAlias(_, alias_path) = &md.md_type {
        // OCaml compiler/ml/env.ml:1517 calls `scrape_alias` before building
        // component tables. `scrape_alias` at env.ml:1440-1446 resolves an
        // alias with `find_module`, and env.ml:865-882 forces the final
        // env.ml:1568 `comp_modules` thunk for that target before returning
        // the module type whose signature is used below.
        match alias_path {
            Path::Pdot(parent, name, _) => {
                if cache_mode.forces_alias_sig() {
                    // OCaml compiler/ml/env.ml:1517 calls `scrape_alias` for
                    // real component-table construction, and scrape_alias
                    // reaches env.ml:865-882 `find_module`, which forces
                    // env.ml:1568's module-declaration thunk. Rust-only probe
                    // callers skip this branch because they are existence
                    // checks with no corresponding OCaml lookup step.
                    let _ = crate::types::typecore::lookup_module_in_resolved_path(
                        parent,
                        name.as_str(),
                        env,
                        pers_env,
                        ctx,
                    );
                }
            }
            Path::Pident(id) if id.is_persistent() => {
                // OCaml compiler/ml/env.ml:1516-1518 scrapes aliases while
                // building real component tables, which can force
                // env.ml:719-721 `ps_sig` through env.ml:865-875. Rust-only
                // existence probes suppress that force because no OCaml lookup
                // reaches this alias at that point.
                if cache_mode.forces_alias_sig()
                    && let Some(pers) = pers_env.as_mut()
                {
                    let _ = pers.force_lazy_signature_rename(id.name(), ctx);
                } else if access_path_is_direct_opened_component(env, access_path)
                    && cache_mode.forces_alias_sig()
                    && env.find_module(id.name()).is_err()
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
            Path::Pident(_) => {}
            Path::Papply(_, _) => {}
        }
    }
    let (raw_sig, resolved_name) =
        if let Some(resolved) = env.resolve_module_type(&md.md_type, pers_env, ctx, cache_mode) {
            resolved
        } else {
            let Some((raw_sig, resolved_name)) = (match &md.md_type {
                super::decl::ModuleType::MtyAlias(_, Path::Pident(alias_id))
                    if alias_id.is_persistent() && cache_mode.forces_alias_sig() =>
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
            }) else {
                return None;
            };
            (raw_sig, resolved_name)
        };
    let pident_sibling_alias_name =
        parent_substitution_context
            .as_ref()
            .and_then(|(_, parent_sig)| match &md.md_type {
                super::decl::ModuleType::MtyAlias(_, Path::Pident(alias_id))
                    if parent_sig.iter().any(|item| {
                        matches!(
                            item,
                            SignatureItem::SigModule(id, _, _) if id.same(alias_id)
                        )
                    }) =>
                {
                    Some(alias_id.name().to_string())
                }
                _ => None,
            });
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
            let target_prefix = Path::pdot(parent_access_path.clone(), alias_name);
            crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                &qualified_sig,
                &target_prefix,
                access_path,
                ctx,
            );
            crate::cmi::persistent_env::rewrite_sig_paths_by_path_prefix(
                &mut qualified_sig,
                &target_prefix,
                access_path,
            );
        }
        crate::cmi::persistent_env::substitute_module_alias_paths_in_child_sig(
            &mut qualified_sig,
            parent_sig,
            parent_access_path,
        );
    }
    if raw_sig.len() != qualified_sig.len() {
        return None;
    }
    if let Some(source) = source_prefix
        && !source.same(access_path)
    {
        // A child of an in-process unit's components: its items name each
        // other through the unit (`Unit.Sub.u`); `prefix_idents`
        // (env.ml:1454-1481, 1530-1538) puts them at the access path.
        crate::cmi::persistent_env::rewrite_sig_by_path_prefix(&qualified_sig, source, access_path, ctx);
        crate::cmi::persistent_env::rewrite_sig_paths_by_path_prefix(
            &mut qualified_sig,
            source,
            access_path,
        );
    }

    let qualified_sig = Arc::new(qualified_sig);
    // OCaml compiler/ml/env.ml:1548-1578 closes child `comp_components`
    // thunks over the evolving `env` that is extended while walking the parent
    // signature. Every child `comp_components` thunk should capture that
    // evolving environment, independent of typedtree output mode; env.ml:1579
    // stores the raw child module only after creating the thunk.
    let mut working_env = Some(env.clone_preserve_id());
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
            (
                SignatureItem::SigType(id, decl, _),
                SignatureItem::SigType(qualified_id, qualified_decl, _),
            ) => {
                if let Some(working_env) = working_env.as_mut() {
                    let env_decl = if use_qualified_items_for_env {
                        qualified_decl.clone()
                    } else {
                        decl.clone()
                    };
                    working_env.add_type(id.clone(), env_decl);
                }
                ctx.register_type_decl(qualified_id.name(), qualified_decl.clone());
                if qualified_id.stamp() != 0 {
                    ctx.register_type_decl_by_stamp(qualified_id.stamp(), qualified_decl.clone());
                }
            }
            (SignatureItem::SigTypext(_, _, _), SignatureItem::SigTypext(_, _, _))
            | (SignatureItem::SigClass, SignatureItem::SigClass) => {
                runtime_pos += 1;
            }
            (SignatureItem::SigModule(id, child_md, _), SignatureItem::SigModule(_, qmd, _)) => {
                if let Some(working_env) = working_env.as_mut() {
                    let child_access_path =
                        qualified_submodule_access_path(access_path, id.name(), runtime_pos, qmd);
                    let env_decl = if use_qualified_items_for_env {
                        qmd.clone()
                    } else {
                        child_md.clone()
                    };
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
                        id.clone(),
                        env_decl,
                        component_decl,
                        child_access_path,
                        Some((access_path.clone(), qualified_sig_for_children.clone())),
                    );
                }
                crate::cmi::persistent_env::register_types_by_stamp_recursive(&qmd.md_type, ctx);
                if let Some(working_env) = working_env.as_ref()
                    && let Some(stored) =
                        working_env.local_module_components_arc(&Path::pident(id.clone()))
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
                    working_env.add_modtype(id.clone(), env_mtd);
                }
            }
            (SignatureItem::SigClassType, SignatureItem::SigClassType) => {}
            _ => return None,
        }
    }

    Some(
        QualifiedModuleComponents::new_with_complete_child_components_arc(
            access_path.clone(),
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
    cached: OnceCell<Arc<QualifiedModuleComponents>>,
    /// Built during a store build (see `StructureComponentTables::in_store`).
    in_store: bool,
    /// Key of this module's compilation-private components (see
    /// `TypeContext::local_stored_components`).
    local_id: u64,
    cached_piece: OnceCell<Arc<super::context::StorePiece>>,
    functor_component_result: OnceCell<ModuleType>,
    functor_component_piece: OnceCell<Arc<super::context::StorePiece>>,
    functor_result_subst_cache:
        OnceCell<RefCell<HashMap<Path, (ModuleType, Option<Arc<super::context::StorePiece>>)>>>,
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

    pub(crate) fn with_components<'a, R>(
        &self,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'a super::context::TypeContext,
        cache_mode: super::typecore::ComponentLookupApi,
        f: impl FnOnce(&QualifiedModuleComponents) -> R,
    ) -> Option<R> {
        if let Some(components) = self.cached.get().cloned() {
            if ctx.compiler_counters_enabled() {
                crate::perf_counters::record_stored_component_cached();
            }
            if let Some(piece) = self.cached_piece.get() {
                ctx.touch_store_piece(piece);
            }
            return Some(f(components.as_ref()));
        }

        if self.in_store {
            if let Some(components) = ctx.local_stored_components(self.local_id) {
                // Compilation-private, like the build that produced it.
                ctx.poison_store_build_for("local-stored-components");
                return Some(f(components.as_ref()));
            }
            let (components, piece) = ctx.build_in_store(|| self.build_components(pers_env, ctx, cache_mode));
            let components = Arc::new(components?);
            if cache_mode.publishes() {
                match piece {
                    Some(piece) => {
                        if self.cached.set(components.clone()).is_ok() {
                            let _ = self.cached_piece.set(piece);
                        }
                    }
                    // Built from this compilation's private state (such as
                    // a renamed persistent signature): keep it for this
                    // compilation only.
                    None => ctx.set_local_stored_components(self.local_id, components.clone()),
                }
            }
            return Some(f(components.as_ref()));
        }

        let components = Arc::new(self.build_components(pers_env, ctx, cache_mode)?);
        if cache_mode.publishes() {
            if self.cached.set(components.clone()).is_err()
                && let Some(cached) = self.cached.get().cloned()
            {
                return Some(f(cached.as_ref()));
            }
        }
        Some(f(components.as_ref()))
    }

    fn build_components(
        &self,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &super::context::TypeContext,
        cache_mode: super::typecore::ComponentLookupApi,
    ) -> Option<QualifiedModuleComponents> {
        let parent_substitution_context =
            self.parent_context
                .as_ref()
                .map(|(parent_access_path, parent_sig)| {
                    (parent_access_path, parent_sig.as_ref().as_slice())
                });
        let components = build_local_module_components(
            self.seed_env.as_ref(),
            &self.access_path,
            &self.module_decl,
            parent_substitution_context,
            self.source_prefix.get(),
            pers_env,
            ctx,
            cache_mode,
        )?;
        if ctx.compiler_counters_enabled() {
            crate::perf_counters::record_stored_component_build(
                cache_mode.counter_name(),
                cache_mode.publishes(),
            );
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
        let component_result = if let Some(cached) = self.functor_component_result.get() {
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
        let (substituted, piece, cacheable) = if self.in_store {
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
                .insert(arg_path.clone(), (substituted.clone(), piece));
        }
        Some(substituted)
    }
}
