//! Lazy qualified module components, matching OCaml's EnvLazy backbone.
//!
//! OCaml memoizes `components_of_module_maker (env, sub, path, mty)` and then
//! answers repeated type/module/value lookups from that cached view. Rust used
//! to cache only copied signatures and still re-scan or re-copy declarations on
//! each lookup. This module provides the cached qualified view that the hot
//! module-resolution paths use as their source of truth.

use ahash::AHashMap as HashMap;
use std::cell::{Cell, RefCell};
use std::sync::Arc;

use crate::ident::Ident;

use super::decl::{
    ConstructorDescription, ConstructorTag, LabelDescription, ModtypeDeclaration,
    ModuleDeclaration, ModuleType, Signature, SignatureItem, TypeDeclaration, ValueDescription,
    ValueKind,
};
use super::path::Path;

const ADAPTIVE_VALUE_INDEX_MIN_SIGNATURE_ITEMS: usize = 32;
const ADAPTIVE_VALUE_INDEX_MIN_CACHED_NAMES: usize = 2;

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

fn flattened_component_head(path: &Path) -> Option<&Ident> {
    // OCaml compiler/ml/path.ml:63-69 refuses to flatten `Papply`; flattened
    // alias sharing only applies to paths with a stable selected module head.
    path.flatten().ok().map(|(head, _)| head)
}

fn build_matching_type_constructors(
    out: &mut Vec<ConstructorDescription>,
    access_path: &Path,
    type_name: &str,
    decl: &TypeDeclaration,
    constructor_name: &str,
    ctx: &super::context::TypeContext,
) {
    let super::decl::TypeKind::TypeVariant(cstrs) = &decl.type_kind else {
        return;
    };

    let type_path = Path::pdot(access_path.clone(), type_name);
    let num_consts = cstrs
        .iter()
        .filter(|c| {
            matches!(
                c.cd_args,
                super::decl::ConstructorArguments::CstrTuple(ref args) if args.is_empty()
            )
        })
        .count() as i32;
    let num_nonconsts = cstrs.len() as i32 - num_consts;
    let mut const_idx = 0i32;
    let mut block_idx = 0i32;

    for cd in cstrs {
        let is_constant = matches!(
            cd.cd_args,
            super::decl::ConstructorArguments::CstrTuple(ref args) if args.is_empty()
        );
        let tag = if decl.type_unboxed.unboxed {
            ConstructorTag::CstrUnboxed
        } else if is_constant {
            ConstructorTag::CstrConstant(const_idx)
        } else {
            ConstructorTag::CstrBlock(block_idx)
        };

        if cd.cd_id.name() != constructor_name {
            if is_constant {
                const_idx += 1;
            } else {
                block_idx += 1;
            }
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
                        labels.clone(),
                        if decl.type_unboxed.unboxed {
                            super::decl::RecordRepresentation::RecordUnboxed(false)
                        } else {
                            super::decl::RecordRepresentation::RecordInlined {
                                tag: block_idx,
                                name: cd.cd_id.name().to_string(),
                                num_nonconsts,
                                attrs: cd.cd_attributes.clone(),
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
                    type_unboxed: super::decl::UnboxedStatus::default(),
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
                    ctx.new_generic_constr(type_path.clone(), args)
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
                cstr_existentials: vec![],
                cstr_args,
                cstr_arity,
                cstr_tag: tag,
                cstr_consts: num_consts,
                cstr_nonconsts: num_nonconsts,
                cstr_generalized: cd.cd_res.is_some(),
                cstr_private: decl.type_private,
                cstr_loc: cd.cd_loc,
                cstr_attributes: super::decl::constructor_description_attrs_for_variant(cstrs, cd),
                cstr_inlined,
            },
        );
        if is_constant {
            const_idx += 1;
        } else {
            block_idx += 1;
        }
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
                                labels.clone(),
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
                            type_unboxed: super::decl::UnboxedStatus::default(),
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
                        cstr_existentials: vec![],
                        cstr_args,
                        cstr_arity,
                        cstr_tag: ConstructorTag::CstrExtension(ext_path),
                        cstr_consts: -1,
                        cstr_nonconsts: -1,
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
pub(crate) struct QualifiedModuleComponents {
    access_path: Arc<Path>,
    signature: Arc<Signature>,
    values: Arc<RefCell<HashMap<String, Option<(usize, usize)>>>>,
    values_indexed: Arc<Cell<bool>>,
    constructors: Arc<RefCell<HashMap<String, Arc<Vec<ConstructorDescription>>>>>,
    labels: Arc<RefCell<HashMap<String, Arc<Vec<LabelDescription>>>>>,
    types: Arc<RefCell<HashMap<String, Option<usize>>>>,
    modules: Arc<RefCell<HashMap<String, Option<(usize, usize)>>>>,
    compiler_counters_enabled: bool,
    component_modtypes: Arc<HashMap<String, (Ident, ModtypeDeclaration)>>,
    // OCaml compiler/ml/env.ml:1568-1578 stores `comp_modules` and
    // `comp_modtypes` declarations in EnvLazy-backed component tables, and
    // env.ml:568-571/865-882 forces those thunks at most once per component
    // table. Rust clones component views out of the global cache before
    // running callbacks, so the forced-declaration memo must be shared by
    // those clones to preserve the same lazy identifier-renaming order.
    qualified_modules: Arc<RefCell<HashMap<String, (Ident, Arc<ModuleDeclaration>)>>>,
    qualified_modtypes: Arc<RefCell<HashMap<String, (Ident, ModtypeDeclaration)>>>,
    // OCaml keeps `comp_components` lazy (compiler/ml/env.ml:1573-1578).
    // Cache forced child component thunks by name, including misses, so a
    // lookup for one child does not materialize every sibling in the parent
    // signature.
    child_components: Arc<RefCell<HashMap<String, Option<(usize, Arc<StoredModuleComponents>)>>>>,
    value_source_prefix: Option<Arc<Path>>,
}

fn build_child_component_from_signature(
    access_path: &Path,
    signature: &Arc<Signature>,
    child_name: &str,
) -> Option<(usize, Arc<StoredModuleComponents>)> {
    let mut working_env = super::env::Env::empty();
    let mut runtime_pos = 0usize;

    // OCaml compiler/ml/env.ml:1530-1578 computes component paths once,
    // stores module declarations in `comp_modules` at env.ml:1568-1569, and
    // separately stores child component thunks in `comp_components` at
    // env.ml:1573-1578. Persistent signatures need the same split so
    // qualified value lookup can descend through child components without
    // forcing `Subst.modtype` on the module declaration thunk.
    for item in signature.iter() {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    runtime_pos += 1;
                }
            }
            SignatureItem::SigType(id, decl, _) => {
                working_env.add_type(id.clone(), decl.clone());
            }
            SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                runtime_pos += 1;
            }
            SignatureItem::SigModule(id, md, _) => {
                let child_access_path =
                    qualified_submodule_access_path(access_path, id.name(), runtime_pos, md);
                working_env.add_module_with_component_context(
                    id.clone(),
                    md.clone(),
                    md.clone(),
                    child_access_path,
                    Some((access_path.clone(), signature.clone())),
                );
                if id.name() == child_name {
                    if let Some(stored) =
                        working_env.local_module_components_arc(&Path::pident(id.clone()))
                    {
                        return Some((runtime_pos, stored));
                    }
                    return None;
                }
                runtime_pos += 1;
            }
            SignatureItem::SigModtype(id, mtd) => {
                working_env.add_modtype(id.clone(), mtd.clone());
            }
            SignatureItem::SigClassType => {}
        }
    }

    None
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

    pub(crate) fn new_with_child_components_arc_and_value_source_prefix(
        access_path: Path,
        signature: Arc<Signature>,
        child_components: HashMap<String, (usize, Arc<StoredModuleComponents>)>,
        value_source_prefix: Option<Path>,
        ctx: &super::context::TypeContext,
    ) -> Self {
        // OCaml compiler/ml/env.ml:1513-1519 builds one component table after
        // `scrape_alias`, so aliases like `Webapi.Dom` and their flattened
        // backing unit can reach the same env.ml:1581-1585 modtype force.
        let mut source_prefixes = Vec::new();
        if let Some(source_prefix) = value_source_prefix.as_ref() {
            source_prefixes.push(source_prefix.clone());
        }
        let one_hop_selected_alias = matches!(
            &access_path,
            Path::Pdot(parent, _, _) if matches!(parent.as_ref(), Path::Pident(_))
        );
        if one_hop_selected_alias {
            for flat_head in ctx.flattened_alias_heads_for_component_path(&access_path) {
                let source_prefix = Path::pident(Ident::create_persistent(&flat_head));
                if !source_prefix.same(&access_path)
                    && !source_prefixes
                        .iter()
                        .any(|existing| existing.same(&source_prefix))
                {
                    source_prefixes.push(source_prefix);
                }
            }
        }
        // OCaml compiler/ml/env.ml:781-813 can later select the flattened
        // persistent unit directly (`Pident Webapi__Dom`) after an earlier
        // selected alias force (`Webapi.Dom`). That direct persistent path uses
        // its own env.ml:1513-1519 component table, so env.ml:1581-1585 freshens
        // module-type declarations again. Preserve that per-table stamp stream
        // for typedtree output; keep the cross-path sharing only for normal
        // compilation.
        let share_modtype_force = !ctx.preserve_canonical_typedtree()
            && (!source_prefixes.is_empty()
                || flattened_component_head(&access_path).is_some_and(|head| {
                    head.is_persistent()
                        && ctx
                            .find_flattened_alias_component_path(head.name())
                            .is_some()
                }));

        let mut component_modtypes = HashMap::new();
        let mut runtime_pos = 0usize;

        for item in signature.iter() {
            match item {
                SignatureItem::SigValue(_, desc) => {
                    if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                        runtime_pos += 1;
                    }
                }
                SignatureItem::SigType(_, _, _) => {}
                SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                    runtime_pos += 1;
                }
                SignatureItem::SigModule(id, _, _) => {
                    if let SignatureItem::SigModule(_, md, _) = item {
                        if let super::decl::ModuleType::MtyAlias(_, Path::Pident(alias_id))
                        | super::decl::ModuleType::MtyIdent(Path::Pident(alias_id)) = &md.md_type
                        {
                            let component_path =
                                Path::pdot_pos(access_path.clone(), id.name(), runtime_pos as i32);
                            // OCaml compiler/ml/env.ml:1530 prefixes child
                            // identifiers with the selected component path,
                            // then env.ml:1573-1578 stores that same path in
                            // `comp_components`. Remember flattened backing
                            // units here so later Rust-only paths like
                            // `Js_types` can return to `Js.Types`.
                            ctx.register_flattened_alias_component_path(
                                alias_id.name(),
                                component_path,
                            );
                        }
                    }
                    runtime_pos += 1;
                }
                SignatureItem::SigModtype(id, mtd) => {
                    let (component_id, component_mtd) = if !share_modtype_force {
                        let mut component_mtd = mtd.clone();
                        // OCaml compiler/ml/env.ml:1513-1514 memoizes a
                        // component table per force point, then env.ml:1581-1585
                        // applies `Subst.modtype_declaration` for that table.
                        // With no scraped alias source, this Rust component
                        // construction is the force point, so freshen locally.
                        crate::cmi::persistent_env::freshen_component_modtype_declaration_bound_idents(
                            &mut component_mtd,
                            &signature,
                            &access_path,
                            ctx,
                        );
                        (id.clone(), component_mtd)
                    } else {
                        ctx.find_qualified_modtype_decl(&access_path, id.name())
                            .or_else(|| {
                                source_prefixes.iter().find_map(|source_prefix| {
                                    ctx.find_qualified_modtype_decl(source_prefix, id.name())
                                })
                            })
                            .unwrap_or_else(|| {
                                let mut component_mtd = mtd.clone();
                                // OCaml compiler/ml/env.ml:1513-1514 memoizes the
                                // component table, then env.ml:1581-1585 applies
                                // `Subst.modtype_declaration` once for each
                                // module type in that table. Cache the forced
                                // declaration by selected access path so Rust
                                // component views reached through type-path probes
                                // reuse the same OCaml force point instead of
                                // freshening the module type again.
                                crate::cmi::persistent_env::freshen_component_modtype_declaration_bound_idents(
                                    &mut component_mtd,
                                    &signature,
                                    &access_path,
                                    ctx,
                                );
                                let result = (id.clone(), component_mtd);
                                ctx.register_qualified_modtype_decl(
                                    &access_path,
                                    id.name(),
                                    result.0.clone(),
                                    result.1.clone(),
                                );
                                for source_prefix in source_prefixes.iter() {
                                    if source_prefix.same(&access_path) {
                                        continue;
                                    }
                                    // OCaml compiler/ml/env.ml:1513-1519 keeps
                                    // one component-table force result reachable
                                    // through both the selected path and the
                                    // scraped alias source. Rust has separate
                                    // views for paths such as `Webapi.Dom` and
                                    // `Webapi__Dom`, so share the
                                    // env.ml:1581-1585 modtype declaration force
                                    // across both keys.
                                    ctx.register_qualified_modtype_decl(
                                        source_prefix,
                                        id.name(),
                                        result.0.clone(),
                                        result.1.clone(),
                                    );
                                }
                                result
                            })
                    };
                    component_modtypes.insert(id.name().to_string(), (component_id, component_mtd));
                }
                SignatureItem::SigClassType => {}
            }
        }

        let child_components = child_components
            .into_iter()
            .map(|(name, component)| (name, Some(component)))
            .collect();

        Self {
            access_path: Arc::new(access_path),
            signature,
            values: Arc::new(RefCell::new(HashMap::new())),
            values_indexed: Arc::new(Cell::new(false)),
            constructors: Arc::new(RefCell::new(HashMap::new())),
            labels: Arc::new(RefCell::new(HashMap::new())),
            types: Arc::new(RefCell::new(HashMap::new())),
            modules: Arc::new(RefCell::new(HashMap::new())),
            compiler_counters_enabled: ctx.compiler_counters_enabled(),
            component_modtypes: Arc::new(component_modtypes),
            qualified_modules: Arc::new(RefCell::new(HashMap::new())),
            qualified_modtypes: Arc::new(RefCell::new(HashMap::new())),
            child_components: Arc::new(RefCell::new(child_components)),
            value_source_prefix: value_source_prefix.map(Arc::new),
        }
    }

    pub(crate) fn access_path(&self) -> &Path {
        self.access_path.as_ref()
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
        if let Some(cached) = self.values.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Value);
            }
            return cached;
        }
        if self.values_indexed.get() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Value);
            }
            return None;
        }

        if self.signature.len() >= ADAPTIVE_VALUE_INDEX_MIN_SIGNATURE_ITEMS
            && self.values.borrow().len() >= ADAPTIVE_VALUE_INDEX_MIN_CACHED_NAMES
        {
            return self.build_value_index_and_get(name);
        }

        // OCaml compiler/ml/env.ml:1513-1514 stores component tables lazily.
        // Keep the canonical signature immutable and force only this env.ml:1132
        // value lookup bucket instead of allocating indexes for every sibling.
        let mut found = None;
        let mut runtime_pos = 0usize;
        for (idx, item) in self.signature.iter().enumerate() {
            match item {
                SignatureItem::SigValue(id, desc) => {
                    if id.name() == name {
                        found = Some((idx, runtime_pos));
                    }
                    if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                        runtime_pos += 1;
                    }
                }
                SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                    runtime_pos += 1;
                }
                SignatureItem::SigModule(_, _, _) => {
                    runtime_pos += 1;
                }
                SignatureItem::SigType(_, _, _)
                | SignatureItem::SigModtype(_, _)
                | SignatureItem::SigClassType => {}
            }
        }
        self.values.borrow_mut().insert(name.to_string(), found);
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
                crate::perf_counters::LazyLookupKind::Value,
                self.signature.len(),
                usize::from(found.is_some()),
            );
        }
        found
    }

    fn build_value_index_and_get(&self, name: &str) -> Option<(usize, usize)> {
        let mut values = self.values.borrow_mut();
        if !self.values_indexed.get() {
            let mut runtime_pos = 0usize;
            let mut result_items = 0usize;
            for (idx, item) in self.signature.iter().enumerate() {
                match item {
                    SignatureItem::SigValue(id, desc) => {
                        values.insert(id.name().to_string(), Some((idx, runtime_pos)));
                        result_items += 1;
                        if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                            runtime_pos += 1;
                        }
                    }
                    SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                        runtime_pos += 1;
                    }
                    SignatureItem::SigModule(_, _, _) => {
                        runtime_pos += 1;
                    }
                    SignatureItem::SigType(_, _, _)
                    | SignatureItem::SigModtype(_, _)
                    | SignatureItem::SigClassType => {}
                }
            }
            self.values_indexed.set(true);
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_scan(
                    crate::perf_counters::LazyLookupKind::Value,
                    self.signature.len(),
                    result_items,
                );
            }
        }
        values.get(name).cloned().unwrap_or(None)
    }

    fn cached_type_index(&self, name: &str) -> Option<usize> {
        if let Some(cached) = self.types.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Type);
            }
            return cached;
        }

        // OCaml compiler/ml/env.ml:1542 stores type declarations in the
        // component table, but the table itself is behind EnvLazy. Defer this
        // per-name index until a type lookup actually asks for it.
        let mut found = None;
        for (idx, item) in self.signature.iter().enumerate() {
            if let SignatureItem::SigType(id, _, _) = item
                && id.name() == name
            {
                found = Some(idx);
            }
        }
        self.types.borrow_mut().insert(name.to_string(), found);
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
                crate::perf_counters::LazyLookupKind::Type,
                self.signature.len(),
                usize::from(found.is_some()),
            );
        }
        found
    }

    fn cached_module_index(&self, name: &str) -> Option<(usize, usize)> {
        if let Some(cached) = self.modules.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Module);
            }
            return cached;
        }

        // OCaml compiler/ml/env.ml:1568 and 1573-1578 expose module
        // declarations/components through separate lazy thunks. Force only the
        // requested child name here; the full shared signature stays untouched.
        let mut found = None;
        let mut runtime_pos = 0usize;
        for (idx, item) in self.signature.iter().enumerate() {
            match item {
                SignatureItem::SigValue(_, desc) => {
                    if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                        runtime_pos += 1;
                    }
                }
                SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                    runtime_pos += 1;
                }
                SignatureItem::SigModule(id, _, _) => {
                    if id.name() == name {
                        found = Some((idx, runtime_pos));
                    }
                    runtime_pos += 1;
                }
                SignatureItem::SigType(_, _, _)
                | SignatureItem::SigModtype(_, _)
                | SignatureItem::SigClassType => {}
            }
        }
        self.modules.borrow_mut().insert(name.to_string(), found);
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
                crate::perf_counters::LazyLookupKind::Module,
                self.signature.len(),
                usize::from(found.is_some()),
            );
        }
        found
    }

    pub(crate) fn lookup_value(&self, name: &str) -> Option<(usize, &Ident, &ValueDescription)> {
        let (idx, runtime_pos) = self.cached_value_index(name)?;
        match &self.signature[idx] {
            SignatureItem::SigValue(id, desc) => Some((runtime_pos, id, desc)),
            _ => None,
        }
    }

    fn value_mentions_local_component_type(
        &self,
        desc: &ValueDescription,
        ctx: &super::context::TypeContext,
    ) -> bool {
        // OCaml compiler/ml/env.ml:1530-1538 builds component substitutions
        // before compiler/ml/subst.ml:303-309 rewrites value descriptions.
        // Keep the optimized Rust value lookup lazy by detecting the rare
        // signatures that still need that substitution.
        // OCaml compiler/ml/env.ml:1530-1538 builds a substitution for both
        // type and module binders in the selected component signature, and
        // compiler/ml/subst.ml:305 applies it to value descriptions. Include
        // module binders here because subst.ml:226-235 also rewrites
        // polymorphic-variant row_name paths such as `Types.Color.value`.
        let component_types = self
            .signature
            .iter()
            .filter_map(|item| match item {
                SignatureItem::SigType(id, _, _) => Some((id.stamp(), id.name())),
                _ => None,
            })
            .collect::<Vec<_>>();
        let component_modules = self
            .signature
            .iter()
            .filter_map(|item| match item {
                SignatureItem::SigModule(id, _, _) => Some((id.stamp(), id.name())),
                _ => None,
            })
            .collect::<Vec<_>>();
        if component_types.is_empty() && component_modules.is_empty() {
            return false;
        }

        fn path_mentions_component_module(path: &Path, component_modules: &[(i32, &str)]) -> bool {
            match path {
                Path::Pident(id) => component_modules.iter().any(|(stamp, name)| {
                    if id.stamp() != 0 && *stamp != 0 {
                        id.stamp() == *stamp
                    } else {
                        id.name() == *name
                    }
                }),
                Path::Pdot(parent, _, _) | Path::Papply(parent, _) => {
                    path_mentions_component_module(parent, component_modules)
                }
            }
        }

        fn visit(
            ty: super::type_expr::TypeExprRef,
            component_types: &[(i32, &str)],
            component_modules: &[(i32, &str)],
            ctx: &super::context::TypeContext,
            seen: &mut std::collections::HashSet<usize>,
        ) -> bool {
            let ty = ctx.repr(ty);
            if !seen.insert(ty.index()) {
                return false;
            }

            let desc = ctx.get_desc(ty);
            match &*desc {
                super::type_expr::TypeDesc::Tconstr { path, args, .. } => {
                    if path_mentions_component_module(path, component_modules) {
                        return true;
                    }
                    if let Path::Pident(id) = path {
                        let mentions_component_type =
                            component_types.iter().any(|(stamp, name)| {
                                if id.stamp() != 0 && *stamp != 0 {
                                    id.stamp() == *stamp
                                } else {
                                    id.name() == *name
                                }
                            });
                        if mentions_component_type {
                            return true;
                        }
                    }
                    args.iter()
                        .any(|arg| visit(*arg, component_types, component_modules, ctx, seen))
                }
                super::type_expr::TypeDesc::Tarrow { arg, ret, .. } => {
                    visit(arg.typ, component_types, component_modules, ctx, seen)
                        || visit(*ret, component_types, component_modules, ctx, seen)
                }
                super::type_expr::TypeDesc::Ttuple(args) => args
                    .iter()
                    .any(|arg| visit(*arg, component_types, component_modules, ctx, seen)),
                super::type_expr::TypeDesc::Tobject { fields, name } => {
                    visit(*fields, component_types, component_modules, ctx, seen)
                        || name.as_ref().is_some_and(|(_, args)| {
                            args.iter().any(|arg| {
                                visit(*arg, component_types, component_modules, ctx, seen)
                            })
                        })
                }
                super::type_expr::TypeDesc::Tfield { typ, rest, .. } => {
                    visit(*typ, component_types, component_modules, ctx, seen)
                        || visit(*rest, component_types, component_modules, ctx, seen)
                }
                super::type_expr::TypeDesc::Tlink(inner)
                | super::type_expr::TypeDesc::Tsubst(inner) => {
                    visit(*inner, component_types, component_modules, ctx, seen)
                }
                super::type_expr::TypeDesc::Tvariant(row) => {
                    visit(row.row_more, component_types, component_modules, ctx, seen)
                        || row.row_name.as_ref().is_some_and(|(path, args)| {
                            path_mentions_component_module(path, component_modules)
                                || args.iter().any(|arg| {
                                    visit(*arg, component_types, component_modules, ctx, seen)
                                })
                        })
                        || row.row_fields.iter().any(|(_, field)| match field {
                            super::type_expr::RowField::Rpresent(Some(arg)) => {
                                visit(*arg, component_types, component_modules, ctx, seen)
                            }
                            super::type_expr::RowField::Reither { types, .. } => {
                                types.iter().any(|arg| {
                                    visit(*arg, component_types, component_modules, ctx, seen)
                                })
                            }
                            super::type_expr::RowField::Rpresent(None)
                            | super::type_expr::RowField::Rabsent => false,
                        })
                }
                super::type_expr::TypeDesc::Tpoly { body, vars } => {
                    visit(*body, component_types, component_modules, ctx, seen)
                        || vars
                            .iter()
                            .any(|var| visit(*var, component_types, component_modules, ctx, seen))
                }
                super::type_expr::TypeDesc::Tpackage { args, .. } => args
                    .iter()
                    .any(|arg| visit(*arg, component_types, component_modules, ctx, seen)),
                super::type_expr::TypeDesc::Tvar(_)
                | super::type_expr::TypeDesc::Tunivar(_)
                | super::type_expr::TypeDesc::Tnil => false,
            }
        }

        visit(
            desc.val_type,
            component_types.as_slice(),
            component_modules.as_slice(),
            ctx,
            &mut std::collections::HashSet::new(),
        )
    }

    pub(crate) fn lookup_value_for_access(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, ValueDescription)> {
        let (runtime_pos, id, desc) = self.lookup_value(name)?;
        let needs_component_subst = self.value_mentions_local_component_type(desc, ctx);
        let desc = if needs_component_subst {
            let mut desc = super::typecore::copy_lookup_value_description_for_subst(desc, ctx);
            // OCaml compiler/ml/env.ml:1435-1444 follows module aliases with
            // `scrape_alias`, then compiler/ml/env.ml:1530-1538 applies
            // `Subst.value_description` using only the substitution produced
            // by `prefix_idents`. compiler/ml/mtype.ml:41-49 deliberately
            // leaves value descriptions unchanged while strengthening the
            // alias target, so do not rewrite every path under
            // `value_source_prefix` to this selected access path.
            if needs_component_subst {
                crate::cmi::persistent_env::substitute_type_paths_in_value_from_sig(
                    &mut desc,
                    self.signature.as_ref(),
                    self.access_path(),
                    ctx,
                );
            }
            desc
        } else {
            desc.clone()
        };
        Some((runtime_pos, id.clone(), desc))
    }

    pub(crate) fn lookup_constructors(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Arc<Vec<ConstructorDescription>> {
        if let Some(cached) = self.constructors.borrow().get(name).cloned() {
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
        let built = Arc::new(build_constructors_for_name(
            self.access_path(),
            self.signature.as_ref(),
            name,
            ctx,
        ));
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
                crate::perf_counters::LazyLookupKind::Constructor,
                self.signature.len(),
                built.len(),
            );
        }
        self.constructors
            .borrow_mut()
            .insert(name.to_string(), built.clone());
        built
    }

    pub(crate) fn lookup_labels(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Arc<Vec<LabelDescription>> {
        if let Some(cached) = self.labels.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Label);
            }
            return cached;
        }

        // OCaml compiler/ml/env.ml:1548-1559 computes `comp_labels` from the
        // selected component path. For normal compilation, force just the label
        // bucket requested by typecore.ml:1107-1126-style qualified lookup; this
        // avoids constructing hundreds of unused JSX record labels per module view.
        let built = Arc::new(build_labels_for_name(
            self.access_path(),
            self.signature.as_ref(),
            name,
            ctx,
        ));
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
                crate::perf_counters::LazyLookupKind::Label,
                self.signature.len(),
                built.len(),
            );
        }
        self.labels
            .borrow_mut()
            .insert(name.to_string(), built.clone());
        built
    }

    pub(crate) fn lookup_type(&self, name: &str) -> Option<(&Ident, &TypeDeclaration)> {
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
    ) -> Option<(usize, Arc<StoredModuleComponents>)> {
        if let Some(cached) = self.child_components.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(
                    crate::perf_counters::LazyLookupKind::ChildComponent,
                );
            }
            return cached;
        }

        let built = build_child_component_from_signature(self.access_path(), &self.signature, name);
        if self.compiler_counters_enabled {
            crate::perf_counters::record_lazy_scan(
                crate::perf_counters::LazyLookupKind::ChildComponent,
                self.signature.len(),
                usize::from(built.is_some()),
            );
        }
        self.child_components
            .borrow_mut()
            .insert(name.to_string(), built.clone());
        built
    }

    pub(crate) fn lookup_qualified_module_shared(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, Arc<ModuleDeclaration>)> {
        let (idx, runtime_pos) = self.cached_module_index(name)?;
        if let Some((id, md)) = self.qualified_modules.borrow().get(name).cloned() {
            return Some((runtime_pos, id, md));
        }
        // OCaml compiler/ml/env.ml:1513-1514 stores component tables as lazy
        // values, and env.ml:568-571/865-882 reuses the forced module-decl thunk
        // for the selected parent path. Rust can reach the same parent through
        // separate component views (`Stdlib.JSON` and `Stdlib_JSON`), so share the
        // forced declaration at the TypeContext level to preserve the same stamp
        // consumption.
        if let Some((id, md)) = ctx.find_qualified_module_decl(self.access_path.as_ref(), name) {
            self.qualified_modules
                .borrow_mut()
                .insert(name.to_string(), (id.clone(), md.clone()));
            return Some((runtime_pos, id, md));
        }
        for flat_head in ctx.flattened_alias_heads_for_component_path(self.access_path.as_ref()) {
            let source_prefix = Path::pident(Ident::create_persistent(&flat_head));
            if let Some((id, md)) = ctx.find_qualified_module_decl(&source_prefix, name) {
                // OCaml compiler/ml/env.ml:1513-1519 creates one component
                // table after `scrape_alias`; env.ml:1568-1578 stores both
                // `comp_modules` and `comp_components` thunks under that table.
                // A selected namespace path such as `Layout.Types` and its
                // flattened backing unit `Layout__Types` therefore share the
                // same forced env.ml:1568 module-declaration thunk. Rust has
                // separate component views, so reuse the backing declaration
                // instead of running compiler/ml/subst.ml:351-364 again.
                self.qualified_modules
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
        if let Some(head) = flattened_component_head(self.access_path.as_ref())
            && head.is_persistent()
            && let Some(component_path) = ctx.find_flattened_alias_component_path(head.name())
            && let Some((id, md)) = ctx.find_qualified_module_decl(&component_path, name)
        {
            // Same sharing as above, but reached from the flattened backing
            // component view after the selected path forced the declaration.
            self.qualified_modules
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

        let (id, mut md) = match &self.signature[idx] {
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
            md = raw_md;
            crate::cmi::persistent_env::freshen_component_module_declaration_bound_idents(
                &mut md,
                &raw_parent_sig,
                &self.access_path,
                ctx,
            );
            let md = Arc::new(md);
            self.qualified_modules
                .borrow_mut()
                .insert(name.to_string(), (raw_id.clone(), md.clone()));
            ctx.register_qualified_module_decl(
                self.access_path.as_ref(),
                name,
                raw_id.clone(),
                md.clone(),
            );
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
        crate::cmi::persistent_env::freshen_component_module_declaration_bound_idents(
            &mut md,
            &self.signature,
            &self.access_path,
            ctx,
        );
        let md = Arc::new(md);
        self.qualified_modules
            .borrow_mut()
            .insert(name.to_string(), (id.clone(), md.clone()));
        ctx.register_qualified_module_decl(self.access_path.as_ref(), name, id.clone(), md.clone());
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
        self.component_modtypes.get(name).cloned()
    }

    pub(crate) fn lookup_qualified_modtype(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(Ident, ModtypeDeclaration)> {
        if let Some((id, mtd)) = self.qualified_modtypes.borrow().get(name).cloned() {
            return Some((id, mtd));
        }

        // OCaml compiler/ml/env.ml:1581-1585 computes the component-table
        // modtype declaration once with `Subst.modtype_declaration` and later
        // lookup reads that cached declaration. Do not run the child-module
        // substitution pass again here; it would double-substitute package
        // identities that were already handled while building the component.
        let (id, mtd) = self.lookup_modtype(name, ctx)?;
        self.qualified_modtypes
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

fn raw_sig_candidate_names_for_access_path(access_path: &Path) -> Vec<String> {
    let Ok((head, components)) = access_path.flatten() else {
        return Vec::new();
    };
    if !(head.is_persistent() || head.stamp() == 0) {
        return Vec::new();
    }

    let mut candidates = Vec::new();
    if !components.is_empty() {
        // OCaml compiler/ml/env.ml:1517 scrapes a module alias before
        // env.ml:1530 prefixes component identifiers, so `Webapi.Fetch`
        // component forcing starts from the aliased backing signature
        // (`Webapi__Fetch`) before the outer namespace (`Webapi`).
        candidates.push(format!("{}__{}", head.name(), components.join("__")));
        candidates.push(format!("{}_{}", head.name(), components.join("_")));
    }
    candidates.push(head.name().to_string());
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
                || alias_target_matches_raw_parent_child(target, access_path, module_name)
    );
    if !is_self_alias {
        return None;
    }

    raw_sig_candidate_names_for_access_path(access_path)
        .into_iter()
        .filter_map(|name| {
            let raw_parent_sig = ctx.find_raw_module_sig(&name)?;
            let raw_parent_path = Path::pident(Ident::create_persistent(&name));
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

    raw_sig_candidate_names_for_access_path(access_path)
        .into_iter()
        .any(|candidate| {
            matches!(
                &parent,
                Path::Pident(id)
                    if (id.is_persistent() || id.stamp() == 0) && id.name() == candidate
            )
        })
}

fn access_path_is_direct_implicit_open_child(access_path: &Path) -> bool {
    matches!(
        access_path.parent(),
        Some(Path::Pident(parent))
            if (parent.is_persistent() || parent.stamp() == 0)
                && matches!(parent.name(), "Stdlib" | "Pervasives")
    )
}

fn signature_has_child_modules(signature: &Signature) -> bool {
    signature
        .iter()
        .any(|item| matches!(item, SignatureItem::SigModule(..)))
}

fn build_local_module_components<'a>(
    env: &super::env::Env,
    access_path: &Path,
    md: &ModuleDeclaration,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a super::context::TypeContext,
) -> Option<QualifiedModuleComponents> {
    if !ctx.preserve_canonical_typedtree()
        && ctx.persistent_env_is_in_process()
        && let super::decl::ModuleType::MtyAlias(_, Path::Pident(alias_id))
        | super::decl::ModuleType::MtyIdent(Path::Pident(alias_id)) = &md.md_type
        && alias_id.is_persistent()
    {
        let renamed_sig = {
            let pers = pers_env.as_mut()?;
            pers.get_renamed_sig_shared(alias_id.name(), ctx)
        };
        if let Some(renamed_sig) = renamed_sig {
            let source_prefix = Path::pident(Ident::create_persistent(alias_id.name()));
            // OCaml compiler/ml/env.ml:1516-1518 calls `scrape_alias` before
            // component-table construction; scrape_alias at env.ml:1435-1446
            // reaches `find_module`, whose persistent Pident branch at
            // env.ml:872-875 forces `ps_sig = Subst.signature identity sign`
            // from env.ml:677. mtype.ml:30-80 then strengthens the alias target
            // path, and mtype.ml:98-102 keeps child modules as aliases to that
            // target before env.ml:1530-1578 builds the selected component
            // table. Run the same qualification here instead of reusing the
            // raw Rust component signature directly.
            let qualified_sig = super::typecore::qualify_resolved_signature_for_local_components(
                access_path,
                &md.md_type,
                renamed_sig.as_ref(),
                Some(alias_id.name()),
                pers_env,
                ctx,
            );
            return Some(
                QualifiedModuleComponents::new_with_child_components_arc_and_value_source_prefix(
                    access_path.clone(),
                    Arc::new(qualified_sig),
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
                if !ctx.suppresses_component_alias_sig_force() {
                    // OCaml compiler/ml/env.ml:1517 calls `scrape_alias` for
                    // real component-table construction, and scrape_alias
                    // reaches env.ml:865-882 `find_module`, which forces
                    // env.ml:1568's module-declaration thunk. Callers under
                    // the probe guard mirror env.ml:781-793
                    // `find_module_descr`/env.ml:800-813 type lookup: they
                    // read component descriptors without forcing the alias
                    // target module declaration.
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
                // OCaml compiler/ml/env.ml:800-813 can read qualified type
                // components without forcing env.ml:719-721 `ps_sig`; callers
                // that are only probing typedecl.ml:767-779 constraints use
                // this guard to keep the alias target lazy.
                if ctx.preserve_canonical_typedtree()
                    && !ctx.suppresses_component_alias_sig_force()
                    && let Some(pers) = pers_env.as_mut()
                {
                    let _ = pers.force_lazy_signature_rename(id.name(), ctx);
                } else if ctx.preserve_canonical_typedtree()
                    && access_path_is_direct_implicit_open_child(access_path)
                    && !ctx.suppresses_component_alias_sig_force()
                    && env.find_module_with_origin(id.name()).is_err()
                {
                    // OCaml compiler/ml/env.ml:1440-1446 reaches
                    // env.ml:865-875 for persistent alias targets while
                    // env.ml:1516-1518 scrapes aliases before component-table
                    // construction. env.ml:867-870 first checks `env.modules`;
                    // only env.ml:872-875's `Not_found` branch forces
                    // `ps_sig = Subst.signature identity sign` from
                    // env.ml:719-721. ctype expression expansion can reach
                    // direct children of the implicit Stdlib/Pervasives roots
                    // from compiler/core/res_compmisc.ml:61-62 without carrying
                    // PersistentEnv. The TypeContext guard is set while
                    // compiler/ml/typemod.ml:1710-1719's package
                    // `wrap_constraint` equivalent walks inclusion types, where
                    // OCaml keeps env.ml:800-813/1573-1578 component-table
                    // laziness instead of forcing this alias target.
                    ctx.trigger_module_sig_rename(id.name());
                }
            }
            Path::Pident(_) => {}
            Path::Papply(_, _) => {}
        }
    }
    let (raw_sig, resolved_name) =
        if let Some(resolved) = env.resolve_module_type(&md.md_type, pers_env, ctx) {
            resolved
        } else {
            let Some((raw_sig, resolved_name)) = (match &md.md_type {
                super::decl::ModuleType::MtyAlias(_, Path::Pident(alias_id))
                    if alias_id.is_persistent() && !ctx.suppresses_component_alias_sig_force() =>
                {
                    // OCaml compiler/ml/env.ml:1517 calls `scrape_alias` before
                    // building component tables; env.ml:1440-1446 resolves
                    // `Mty_alias (_, path)` with `find_module`, whose `Pident`
                    // case at env.ml:865-875 checks the persistent table
                    // directly and forces `ps_sig` at env.ml:872-875. Rust's
                    // normal resolver can hit its cycle guard for selected alias
                    // paths with child component tables such as
                    // `Js.TypedArray2`; fall back to the OCaml persistent-table
                    // path only for module-bearing signatures, matching
                    // env.ml:1573-1578 child `comp_components` construction
                    // without eagerly forcing value/type-only aliases.
                    let has_child_modules = if let Some(pers) = pers_env.as_mut() {
                        pers.read_raw_sig_shared(alias_id.name(), ctx)
                            .is_some_and(|sig| signature_has_child_modules(sig.as_ref()))
                    } else {
                        ctx.with_raw_module_sig(alias_id.name(), signature_has_child_modules)
                            .unwrap_or(false)
                    };
                    if !has_child_modules {
                        None
                    } else {
                        let renamed_sig = if let Some(pers) = pers_env.as_mut() {
                            pers.get_renamed_sig_shared(alias_id.name(), ctx)
                        } else {
                            ctx.trigger_module_sig_rename(alias_id.name());
                            ctx.renamed_module_sigs
                                .borrow()
                                .get(alias_id.name())
                                .cloned()
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
                }
                _ => None,
            }) else {
                return None;
            };
            (raw_sig, resolved_name)
        };
    let qualified_sig = crate::types::typecore::qualify_resolved_signature_for_local_components(
        access_path,
        &md.md_type,
        &raw_sig,
        resolved_name.as_deref(),
        pers_env,
        ctx,
    );
    if raw_sig.len() != qualified_sig.len() {
        return None;
    }

    let qualified_sig = Arc::new(qualified_sig);
    // OCaml compiler/ml/env.ml:1548-1578 closes child `comp_components`
    // thunks over the evolving `env` that is extended while walking the parent
    // signature. Alias parents need the same captured env even when the child
    // component itself stays lazy; otherwise a later scrape of aliases such as
    // `Js.Json.Kind` resolves from an empty environment.
    let eager_child_components = ctx.preserve_canonical_typedtree()
        || matches!(
            md.md_type,
            super::decl::ModuleType::MtyAlias(..) | super::decl::ModuleType::MtyIdent(..)
        );
    let mut working_env = eager_child_components.then(|| env.clone_preserve_id());
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
                    let component_decl =
                        if use_qualified_items_for_env && !ctx.preserve_canonical_typedtree() {
                            // OCaml compiler/ml/env.ml:1573-1578 builds
                            // `comp_components` from the child md.md_type
                            // while env.ml:1568 stores the substituted
                            // module-declaration thunk. Normal compilation
                            // needs that raw child component to scrape aliases
                            // like `Js.Json.Kind`; strict typedtree mode keeps
                            // the existing substituted shape until the broader
                            // sharing model is fully unified.
                            child_md.clone()
                        } else if use_qualified_items_for_env {
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

    Some(QualifiedModuleComponents::new_with_child_components_arc(
        access_path.clone(),
        qualified_sig,
        child_components,
        ctx,
    ))
}

#[derive(Debug, Clone)]
pub(crate) struct StoredModuleComponents {
    seed_env: Box<super::env::Env>,
    access_path: Path,
    module_decl: ModuleDeclaration,
    parent_context: Option<(Path, Arc<Signature>)>,
    cached: RefCell<Option<QualifiedModuleComponents>>,
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
            cached: RefCell::new(None),
        }
    }

    pub(crate) fn with_components<'a, R>(
        &self,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'a super::context::TypeContext,
        f: impl FnOnce(&QualifiedModuleComponents) -> R,
    ) -> Option<R> {
        if self.cached.borrow().is_none() {
            let mut module_decl = self.module_decl.clone();
            if let Some((parent_access_path, parent_sig)) = &self.parent_context {
                let sibling_alias = match &module_decl.md_type {
                    super::decl::ModuleType::MtyAlias(_, Path::Pdot(parent, name, _))
                        if parent_matches_component_context(parent, parent_access_path, ctx) =>
                    {
                        raw_component_module_type(parent_access_path, name.as_str(), ctx).or_else(
                            || {
                                parent_sig.iter().find_map(|item| match item {
                                    SignatureItem::SigModule(id, md, _)
                                        if id.name() == name.as_str() =>
                                    {
                                        Some(md.md_type.clone())
                                    }
                                    _ => None,
                                })
                            },
                        )
                    }
                    _ => None,
                };
                if let Some(md_type) = sibling_alias {
                    // OCaml compiler/ml/env.ml:1516-1578 runs
                    // `scrape_alias` on child module types before `prefix_idents`
                    // applies the selected component path.
                    // Resolve sibling aliases from the parent signature here
                    // instead of substituting the alias path first. The same
                    // env.ml:1573-1578 `comp_components` path is used for
                    // persistent parents; otherwise Rust forces env.ml:1568's
                    // `Subst.modtype` thunk and freshens child binders before
                    // OCaml does.
                    module_decl.md_type = md_type;
                } else {
                    let keep_alias_target_for_scrape = matches!(
                        &module_decl.md_type,
                        super::decl::ModuleType::MtyAlias(_, Path::Pident(id))
                            if id.is_persistent()
                    ) || matches!(
                        &module_decl.md_type,
                        super::decl::ModuleType::MtyAlias(_, Path::Pdot(parent, _, _))
                            if !parent.same(parent_access_path)
                    );
                    if !keep_alias_target_for_scrape {
                        // OCaml compiler/ml/env.ml:1573-1578 stores child
                        // component thunks with the child module type, and
                        // env.ml:1517 scrapes aliases before env.ml:1530-1538
                        // prefixes the selected component path. Only rewrite
                        // aliases that still point through the selected parent;
                        // persistent aliases such as `Js_typed_array2` and
                        // already-qualified aliases such as `Stdlib_Date.UTC`/
                        // `Js.Json.Kind` must remain available to `scrape_alias`.
                        crate::cmi::persistent_env::substitute_type_paths_in_child_module_type(
                            &mut module_decl.md_type,
                            parent_sig,
                            parent_access_path,
                            ctx,
                        );
                    }
                }
            }
            let components = build_local_module_components(
                self.seed_env.as_ref(),
                &self.access_path,
                &module_decl,
                pers_env,
                ctx,
            )?;
            *self.cached.borrow_mut() = Some(components);
        }

        let cached = self.cached.borrow();
        let components = cached.as_ref()?;
        Some(f(components))
    }

    pub(crate) fn instantiate_functor_result_for_application(
        &self,
        arg_path: &Path,
        ctx: &super::context::TypeContext,
    ) -> Option<ModuleType> {
        let ModuleType::MtyFunctor { param, result, .. } = &self.module_decl.md_type else {
            return None;
        };
        let parent_context = self
            .parent_context
            .as_ref()
            .map(|(path, sig)| (path, sig.as_ref().as_slice()));
        let component_result = crate::cmi::persistent_env::freshen_functor_component_module_type(
            result.as_ref(),
            parent_context,
            ctx,
        );
        Some(
            crate::cmi::persistent_env::substitute_functor_result_module_path(
                &component_result,
                param,
                arg_path,
                ctx,
            ),
        )
    }
}

fn parent_matches_component_context(
    parent: &Path,
    parent_access_path: &Path,
    ctx: &super::context::TypeContext,
) -> bool {
    if parent.same(parent_access_path) {
        return true;
    }
    if let Some(head) = flattened_component_head(parent_access_path)
        && (head.is_persistent() || head.stamp() == 0)
        && let Some(alias_path) = ctx.find_flattened_alias_component_path(head.name())
    {
        return parent.same(&alias_path);
    }
    if let Path::Pident(access_id) = parent_access_path
        && (access_id.is_persistent() || access_id.stamp() == 0)
        && let Ok((parent_head, parent_components)) = parent.flatten()
        && !parent_components.is_empty()
    {
        // OCaml compiler/ml/env.ml:1573-1578 stores child `comp_components`
        // under the selected component table. Rust can see the same table via a
        // ReScript flattened backing unit (`Webapi__Fetch`) while the alias
        // still names the source parent (`Webapi.Fetch`).
        let double_underscore = format!("{}__{}", parent_head.name(), parent_components.join("__"));
        let single_underscore = format!("{}_{}", parent_head.name(), parent_components.join("_"));
        if access_id.name() == double_underscore || access_id.name() == single_underscore {
            return true;
        }
    }
    false
}

fn raw_component_module_type(
    parent_access_path: &Path,
    module_name: &str,
    ctx: &super::context::TypeContext,
) -> Option<super::decl::ModuleType> {
    raw_sig_candidate_names_for_access_path(parent_access_path)
        .into_iter()
        .find_map(|name| {
            let raw_parent_sig = ctx.find_raw_module_sig(&name)?;
            raw_parent_sig.iter().find_map(|item| match item {
                SignatureItem::SigModule(id, md, _) if id.name() == module_name => {
                    Some(md.md_type.clone())
                }
                _ => None,
            })
        })
}
