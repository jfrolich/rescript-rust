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
        self.working_env
            .get_or_insert_with(super::env::Env::empty)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct QualifiedModuleComponents {
    access_path: Arc<Path>,
    signature: Arc<Signature>,
    values: Arc<RefCell<HashMap<String, Option<(usize, usize)>>>>,
    component_values: Arc<RefCell<HashMap<String, Option<(usize, Ident, ValueDescription)>>>>,
    values_indexed: Arc<Cell<bool>>,
    constructors: Arc<RefCell<HashMap<String, Arc<Vec<ConstructorDescription>>>>>,
    labels: Arc<RefCell<HashMap<String, Arc<Vec<LabelDescription>>>>>,
    types: Arc<RefCell<HashMap<String, Option<usize>>>>,
    types_indexed: Arc<Cell<bool>>,
    modules: Arc<RefCell<HashMap<String, Option<(usize, usize)>>>>,
    modules_indexed: Arc<Cell<bool>>,
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
    child_component_scan: Arc<RefCell<ChildComponentScanState>>,
    value_source_prefix: Option<Arc<Path>>,
}

fn scan_child_component_from_signature(
    access_path: &Path,
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
                state
                    .working_env_mut()
                    .add_modtype(id.clone(), mtd.clone());
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
        let mut values = HashMap::new();
        let mut types = HashMap::new();
        let mut modules = HashMap::new();
        let mut component_modtypes = HashMap::new();
        let mut runtime_pos = 0usize;

        for (idx, item) in signature.iter().enumerate() {
            match item {
                SignatureItem::SigValue(id, desc) => {
                    values.insert(id.name().to_string(), Some((idx, runtime_pos)));
                    if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                        runtime_pos += 1;
                    }
                }
                SignatureItem::SigType(id, _, _) => {
                    types.insert(id.name().to_string(), Some(idx));
                }
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
                            // `comp_components`. Remember the scraped backing
                            // unit so later raw child-thunk recovery uses the
                            // same alias relation instead of path spelling.
                            ctx.register_flattened_alias_component_path(
                                alias_id.name(),
                                component_path,
                            );
                        }
                    }
                    modules.insert(id.name().to_string(), Some((idx, runtime_pos)));
                    runtime_pos += 1;
                }
                SignatureItem::SigModtype(id, mtd) => {
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
                    let component_id = id.clone();
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
            values: Arc::new(RefCell::new(values)),
            component_values: Arc::new(RefCell::new(HashMap::new())),
            values_indexed: Arc::new(Cell::new(true)),
            constructors: Arc::new(RefCell::new(HashMap::new())),
            labels: Arc::new(RefCell::new(HashMap::new())),
            types: Arc::new(RefCell::new(types)),
            types_indexed: Arc::new(Cell::new(true)),
            modules: Arc::new(RefCell::new(modules)),
            modules_indexed: Arc::new(Cell::new(true)),
            compiler_counters_enabled: ctx.compiler_counters_enabled(),
            component_modtypes: Arc::new(component_modtypes),
            qualified_modules: Arc::new(RefCell::new(HashMap::new())),
            qualified_modtypes: Arc::new(RefCell::new(HashMap::new())),
            child_components: Arc::new(RefCell::new(child_components)),
            child_component_scan: Arc::new(RefCell::new(if child_component_scan_complete {
                ChildComponentScanState::complete()
            } else {
                ChildComponentScanState::new()
            })),
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
        if self.types_indexed.get() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Type);
            }
            return None;
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
        if self.modules_indexed.get() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Module);
            }
            return None;
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

    pub(crate) fn lookup_value_for_access(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, ValueDescription)> {
        if let Some(cached) = self.component_values.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(crate::perf_counters::LazyLookupKind::Value);
            }
            return cached;
        }

        let (runtime_pos, id, desc) = self.lookup_value(name)?;
        let mut desc = super::typecore::copy_lookup_value_description_for_subst(desc, ctx);
        // OCaml compiler/ml/env.ml:1530-1538 builds `prefix_idents` for the
        // selected component path, then env.ml:1537 always applies
        // compiler/ml/subst.ml:303-309 `Subst.value_description` to component
        // values before typecore.ml:2421-2457 instances `desc.val_type`.
        // Keep the alias-strengthening boundary from compiler/ml/mtype.ml:41-49:
        // only the component substitution is applied here; alias target value
        // descriptions are not rewritten wholesale.
        crate::cmi::persistent_env::substitute_type_paths_in_value_from_sig(
            &mut desc,
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
        self.component_values
            .borrow_mut()
            .insert(name.to_string(), result.clone());
        result
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
        _ctx: &super::context::TypeContext,
    ) -> Option<(usize, Arc<StoredModuleComponents>)> {
        if let Some(cached) = self.child_components.borrow().get(name).cloned() {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_lazy_hit(
                    crate::perf_counters::LazyLookupKind::ChildComponent,
                );
            }
            return cached;
        }

        let mut scan = self.child_component_scan.borrow_mut();
        if scan.complete {
            self.child_components
                .borrow_mut()
                .insert(name.to_string(), None);
            return None;
        }

        let mut child_components = self.child_components.borrow_mut();
        let (built, scanned_items) = scan_child_component_from_signature(
            self.access_path(),
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

    pub(crate) fn lookup_qualified_module_shared(
        &self,
        name: &str,
        ctx: &super::context::TypeContext,
    ) -> Option<(usize, Ident, Arc<ModuleDeclaration>)> {
        let (idx, runtime_pos) = self.cached_module_index(name)?;
        if let Some((id, md)) = self.qualified_modules.borrow().get(name).cloned() {
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
                self.qualified_modules
                    .borrow_mut()
                    .insert(name.to_string(), (id.clone(), md.clone()));
                return Some((runtime_pos, id, md));
            }
            // Same OCaml env.ml:865-882 / subst.ml:351-364 force boundary as
            // above: do not let a TypeContext-level self-alias placeholder hide
            // the raw component module-declaration thunk.
        }
        for flat_head in ctx.flattened_alias_heads_for_component_path(self.access_path.as_ref()) {
            let source_prefix = Path::pident(Ident::create_persistent(&flat_head));
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
            let selected_path =
                qualified_submodule_access_path(self.access_path.as_ref(), name, runtime_pos, &md);
            if !module_decl_is_self_alias_for_access_path(&md, &selected_path) {
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
            // OCaml compiler/ml/env.ml:1568 stores the module-declaration thunk
            // from the raw component item. A cached self alias can be produced by
            // compiler/ml/mtype.ml:98-102 strengthening, but env.ml:865-882
            // `find_module` still forces the raw thunk and applies
            // compiler/ml/subst.ml:351-364 before returning it.
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

fn module_decl_is_self_alias_for_access_path(md: &ModuleDeclaration, access_path: &Path) -> bool {
    matches!(&md.md_type, ModuleType::MtyAlias(_, target) if target.same(access_path))
}

fn raw_sig_candidate_names_for_access_path(
    access_path: &Path,
    ctx: &super::context::TypeContext,
) -> Vec<String> {
    let Ok((head, _components)) = access_path.flatten() else {
        return Vec::new();
    };
    if !(head.is_persistent() || head.stamp() == 0) {
        return Vec::new();
    }

    let mut candidates = Vec::new();
    let mut push_candidate = |candidate: String| {
        if !candidates.iter().any(|existing| existing == &candidate) {
            candidates.push(candidate);
        }
    };
    // OCaml compiler/ml/env.ml:1517 scrapes the alias target before
    // env.ml:1530 `prefix_idents`; env.ml:1567-1578 then stores child
    // declaration/component thunks from that raw signature item. Rust records
    // the same alias-to-selected-component relation when building the component
    // table, so raw backing signatures come from the captured alias relation
    // rather than flattened path spelling.
    for flat_head in ctx.flattened_alias_heads_for_component_path(access_path) {
        push_candidate(flat_head);
    }
    push_candidate(head.name().to_string());
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

    raw_sig_candidate_names_for_access_path(access_path, ctx)
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

    raw_sig_candidate_names_for_access_path(access_path, ctx)
        .into_iter()
        .any(|candidate| {
            matches!(
                &parent,
                Path::Pident(id)
                    if (id.is_persistent() || id.stamp() == 0) && id.name() == candidate
            )
        })
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
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a super::context::TypeContext,
    cache_mode: super::typecore::ComponentLookupCacheMode,
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
            // this TypeContext, so share that component signature and let the
            // view apply the selected access path lazily to forced items.
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
                    // env.ml:1568's module-declaration thunk. Callers under
                    // probe mode mirror env.ml:781-793 `find_module_descr`
                    // and env.ml:800-813 type lookup: they read component
                    // descriptors without forcing the alias target module
                    // declaration.
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
                // probe mode to keep the alias target lazy.
                if cache_mode.forces_alias_sig()
                    && let Some(pers) = pers_env.as_mut()
                {
                    let _ = pers.force_lazy_signature_rename(id.name(), ctx);
                } else if access_path_is_direct_opened_component(env, access_path)
                    && cache_mode.forces_alias_sig()
                    && env.find_module_with_origin(id.name()).is_err()
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
                    // `wrap_constraint` equivalent walks inclusion types in
                    // probe mode, where OCaml keeps env.ml:800-813/1573-1578
                    // component-table laziness instead of forcing this alias
                    // target.
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
    }
    if raw_sig.len() != qualified_sig.len() {
        return None;
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

    Some(QualifiedModuleComponents::new_with_complete_child_components_arc(
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
        cache_mode: super::typecore::ComponentLookupCacheMode,
        f: impl FnOnce(&QualifiedModuleComponents) -> R,
    ) -> Option<R> {
        {
            let cached = self.cached.borrow();
            if let Some(components) = cached.as_ref() {
                if ctx.compiler_counters_enabled() {
                    crate::perf_counters::record_stored_component_cached();
                }
                return Some(f(components));
            }
        }

        let mut module_decl = self.module_decl.clone();
        let mut parent_substitution_context = None;
        if let Some((parent_access_path, parent_sig)) = &self.parent_context {
            let pident_sibling_alias = match &module_decl.md_type {
                super::decl::ModuleType::MtyAlias(_, Path::Pident(alias_id))
                    if parent_sig.iter().any(|item| {
                        matches!(
                            item,
                            SignatureItem::SigModule(id, _, _) if id.same(alias_id)
                        )
                    }) =>
                {
                    true
                }
                _ => false,
            };
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
            if pident_sibling_alias {
                // OCaml compiler/ml/env.ml:1568 forces child module
                // declarations by applying `Subst.modtype sub` with the
                // parent component substitution from env.ml:1530. For an alias
                // that still points to a sibling binder by `Pident`,
                // compiler/ml/subst.ml:69-76 `module_path` maps that binder
                // through the parent component substitution. Keep the alias
                // module type itself intact here so env.ml:1516-1518 can still
                // scrape it without forcing the sibling declaration early; the
                // copied signature is rewritten after scraping below.
                parent_substitution_context =
                    Some((parent_access_path, parent_sig.as_ref().as_slice()));
            } else if sibling_alias.is_some() {
                // OCaml compiler/ml/env.ml:1516-1578 runs
                // `scrape_alias` on child module types before `prefix_idents`
                // applies the selected component path.
                // Keep the child module type as the alias, rather than
                // replacing it with the sibling's raw module type: after
                // env.ml:1435-1446 `scrape_alias` obtains that raw signature,
                // env.ml:1530-1538 `prefix_idents` still prefixes value and
                // type paths with the selected alias path. Replacing the alias
                // here would qualify component value types through the target
                // sibling path instead.
                parent_substitution_context =
                    Some((parent_access_path, parent_sig.as_ref().as_slice()));
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
                if keep_alias_target_for_scrape {
                    // OCaml compiler/ml/env.ml:1517 scrapes the raw alias
                    // target first, then env.ml:1530 applies the parent
                    // substitution captured in the component thunk. Defer the
                    // substitution instead of rewriting the alias path before
                    // it is resolved.
                    parent_substitution_context =
                        Some((parent_access_path, parent_sig.as_ref().as_slice()));
                } else {
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
            parent_substitution_context,
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
        if cache_mode.publishes() {
            *self.cached.borrow_mut() = Some(components);
            let cached = self.cached.borrow();
            let components = cached.as_ref()?;
            Some(f(components))
        } else {
            Some(f(&components))
        }
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
    false
}

fn raw_component_module_type(
    parent_access_path: &Path,
    module_name: &str,
    ctx: &super::context::TypeContext,
) -> Option<super::decl::ModuleType> {
    raw_sig_candidate_names_for_access_path(parent_access_path, ctx)
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
