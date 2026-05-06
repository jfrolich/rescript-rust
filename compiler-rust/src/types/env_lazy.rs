//! Lazy qualified module components, matching OCaml's EnvLazy backbone.
//!
//! OCaml memoizes `components_of_module_maker (env, sub, path, mty)` and then
//! answers repeated type/module/value lookups from that cached view. Rust used
//! to cache only copied signatures and still re-scan or re-copy declarations on
//! each lookup. This module provides the cached qualified view that the hot
//! module-resolution paths use as their source of truth.

use ahash::AHashMap as HashMap;
use std::cell::RefCell;
use std::sync::Arc;

use crate::ident::Ident;

use super::decl::{
    ConstructorDescription, ConstructorTag, LabelDescription, ModtypeDeclaration,
    ModuleDeclaration, Signature, SignatureItem, TypeDeclaration, ValueDescription, ValueKind,
};
use super::path::Path;

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

fn add_type_constructors(
    constructors: &mut HashMap<String, Vec<ConstructorDescription>>,
    access_path: &Path,
    type_name: &str,
    decl: &TypeDeclaration,
    ctx: &super::context::TypeContext<'_>,
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
        constructors
            .entry(cd.cd_id.name().to_string())
            .or_insert_with(Vec::new)
            .insert(
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
                    cstr_attributes: super::decl::constructor_description_attrs_for_variant(
                        cstrs, cd,
                    ),
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

fn add_type_labels(
    labels_by_name: &mut HashMap<String, Vec<LabelDescription>>,
    access_path: &Path,
    type_name: &str,
    decl: &TypeDeclaration,
    ctx: &super::context::TypeContext<'_>,
) {
    let super::decl::TypeKind::TypeRecord(labels, repr) = &decl.type_kind else {
        return;
    };

    let type_path = Path::pdot(access_path.clone(), type_name);
    let res_ty = ctx.new_generic_constr(type_path, decl.type_params.clone());
    for (pos, ld) in labels.iter().enumerate() {
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
        labels_by_name
            .entry(ld.ld_id.name().to_string())
            .or_insert_with(Vec::new)
            .insert(0, label_desc);
    }
}

#[derive(Debug, Clone)]
pub(crate) struct QualifiedModuleComponents {
    access_path: Arc<Path>,
    signature: Arc<Signature>,
    values: Arc<HashMap<String, (usize, usize)>>,
    constructors: Arc<HashMap<String, Vec<ConstructorDescription>>>,
    labels: Arc<HashMap<String, Vec<LabelDescription>>>,
    types: Arc<HashMap<String, usize>>,
    modules: Arc<HashMap<String, (usize, usize)>>,
    modtypes: Arc<HashMap<String, usize>>,
    component_modtypes: Arc<HashMap<String, (Ident, ModtypeDeclaration)>>,
    // OCaml compiler/ml/env.ml:1568-1578 stores `comp_modules` and
    // `comp_modtypes` declarations in EnvLazy-backed component tables, and
    // env.ml:568-571/865-882 forces those thunks at most once per component
    // table. Rust clones component views out of the global cache before
    // running callbacks, so the forced-declaration memo must be shared by
    // those clones to preserve the same lazy identifier-renaming order.
    qualified_modules: Arc<RefCell<HashMap<String, (Ident, ModuleDeclaration)>>>,
    qualified_modtypes: Arc<RefCell<HashMap<String, (Ident, ModtypeDeclaration)>>>,
    child_components: Arc<HashMap<String, (usize, Arc<StoredModuleComponents>)>>,
}

fn build_child_components_from_signature(
    access_path: &Path,
    signature: &Signature,
) -> HashMap<String, (usize, Arc<StoredModuleComponents>)> {
    let mut child_components = HashMap::new();
    let mut working_env = super::env::Env::empty();
    let parent_sig = Arc::new(signature.clone());
    let mut runtime_pos = 0usize;

    // OCaml compiler/ml/env.ml:1530-1578 computes component paths once,
    // stores module declarations in `comp_modules` at env.ml:1568-1569, and
    // separately stores child component thunks in `comp_components` at
    // env.ml:1573-1578. Persistent signatures need the same split so
    // qualified value lookup can descend through child components without
    // forcing `Subst.modtype` on the module declaration thunk.
    for item in signature {
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
                    Some((access_path.clone(), parent_sig.clone())),
                );
                if let Some(stored) = working_env
                    .with_local_module_components(&Path::pident(id.clone()), |stored| {
                        Arc::new(stored.clone())
                    })
                {
                    child_components.insert(id.name().to_string(), (runtime_pos, stored));
                }
                runtime_pos += 1;
            }
            SignatureItem::SigModtype(id, mtd) => {
                working_env.add_modtype(id.clone(), mtd.clone());
            }
            SignatureItem::SigClassType => {}
        }
    }

    child_components
}

impl QualifiedModuleComponents {
    pub(crate) fn new(
        access_path: Path,
        signature: Signature,
        ctx: &super::context::TypeContext<'_>,
    ) -> Self {
        Self::new_with_child_components(access_path, signature, HashMap::new(), ctx)
    }

    pub(crate) fn new_with_child_components(
        access_path: Path,
        signature: Signature,
        child_components: HashMap<String, (usize, Arc<StoredModuleComponents>)>,
        ctx: &super::context::TypeContext<'_>,
    ) -> Self {
        let child_components = if child_components.is_empty() {
            build_child_components_from_signature(&access_path, &signature)
        } else {
            child_components
        };
        let mut values = HashMap::new();
        let mut constructors = HashMap::new();
        let mut labels = HashMap::new();
        let mut types = HashMap::new();
        let mut modules = HashMap::new();
        let mut modtypes = HashMap::new();
        let mut component_modtypes = HashMap::new();
        let mut runtime_pos = 0usize;

        for (idx, item) in signature.iter().enumerate() {
            match item {
                SignatureItem::SigValue(id, desc) => {
                    values.insert(id.name().to_string(), (idx, runtime_pos));
                    if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                        runtime_pos += 1;
                    }
                }
                SignatureItem::SigType(id, _, _) => {
                    types.insert(id.name().to_string(), idx);
                }
                SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                    runtime_pos += 1;
                }
                SignatureItem::SigModule(id, _, _) => {
                    modules.insert(id.name().to_string(), (idx, runtime_pos));
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
                    modtypes.insert(id.name().to_string(), idx);
                    let mut component_mtd = mtd.clone();
                    // OCaml compiler/ml/env.ml:1530 and 1581-1585 apply the
                    // `prefix_idents` substitution to component modtypes while
                    // keeping the original declaration in the evolving env.
                    // Keep that split so forced components consume the same
                    // fresh identifiers without changing the raw signature used
                    // by package/include checks.
                    crate::cmi::persistent_env::freshen_component_modtype_declaration_bound_idents(
                        &mut component_mtd,
                        &signature,
                        &access_path,
                        ctx,
                    );
                    component_modtypes.insert(id.name().to_string(), (id.clone(), component_mtd));
                }
                SignatureItem::SigClassType => {}
            }
        }

        // OCaml compiler/ml/env.ml:1542-1556 builds `comp_constrs`
        // while forcing module components, using the selected component
        // path from env.ml:1530-1538. Later env.ml:1132-1137 reads this
        // table directly for qualified constructor lookup.
        let mut runtime_pos = 0i32;
        for item in &signature {
            match item {
                SignatureItem::SigValue(_, desc) => {
                    if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                        runtime_pos += 1;
                    }
                }
                SignatureItem::SigType(id, decl, _) => {
                    add_type_constructors(&mut constructors, &access_path, id.name(), decl, ctx);
                    add_type_labels(&mut labels, &access_path, id.name(), decl, ctx);
                }
                SignatureItem::SigTypext(id, ext, _) => {
                    let ext_slot = runtime_pos;
                    runtime_pos += 1;
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
                            let inline_constr =
                                ctx.new_generic_constr(ext_path.clone(), inline_params.clone());
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
                        &signature,
                        &access_path,
                    );
                    let cstr_res =
                        ctx.new_generic_constr(ext_type_path, ext.ext_type_params.clone());
                    constructors
                        .entry(id.name().to_string())
                        .or_insert_with(Vec::new)
                        .insert(
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
                SignatureItem::SigModule(_, _, _) => {
                    runtime_pos += 1;
                }
                SignatureItem::SigModtype(_, _) | SignatureItem::SigClassType => {}
                SignatureItem::SigClass => {
                    runtime_pos += 1;
                }
            }
        }

        Self {
            access_path: Arc::new(access_path),
            signature: Arc::new(signature),
            values: Arc::new(values),
            constructors: Arc::new(constructors),
            labels: Arc::new(labels),
            types: Arc::new(types),
            modules: Arc::new(modules),
            modtypes: Arc::new(modtypes),
            component_modtypes: Arc::new(component_modtypes),
            qualified_modules: Arc::new(RefCell::new(HashMap::new())),
            qualified_modtypes: Arc::new(RefCell::new(HashMap::new())),
            child_components: Arc::new(child_components),
        }
    }

    pub(crate) fn access_path(&self) -> &Path {
        self.access_path.as_ref()
    }

    pub(crate) fn signature(&self) -> &[SignatureItem] {
        self.signature.as_slice()
    }

    pub(crate) fn cloned_signature(&self) -> Signature {
        self.signature.as_ref().clone()
    }

    pub(crate) fn lookup_value(&self, name: &str) -> Option<(usize, &Ident, &ValueDescription)> {
        let (idx, runtime_pos) = *self.values.get(name)?;
        match &self.signature[idx] {
            SignatureItem::SigValue(id, desc) => Some((runtime_pos, id, desc)),
            _ => None,
        }
    }

    pub(crate) fn lookup_constructors(&self, name: &str) -> Option<&[ConstructorDescription]> {
        self.constructors.get(name).map(Vec::as_slice)
    }

    pub(crate) fn lookup_labels(&self, name: &str) -> Option<&[LabelDescription]> {
        self.labels.get(name).map(Vec::as_slice)
    }

    pub(crate) fn lookup_type(&self, name: &str) -> Option<(&Ident, &TypeDeclaration)> {
        let idx = *self.types.get(name)?;
        match &self.signature[idx] {
            SignatureItem::SigType(id, decl, _) => Some((id, decl)),
            _ => None,
        }
    }

    pub(crate) fn lookup_module(&self, name: &str) -> Option<(usize, &Ident, &ModuleDeclaration)> {
        let (idx, runtime_pos) = *self.modules.get(name)?;
        match &self.signature[idx] {
            SignatureItem::SigModule(id, md, _) => Some((runtime_pos, id, md)),
            _ => None,
        }
    }

    pub(crate) fn lookup_child_components(
        &self,
        name: &str,
    ) -> Option<(usize, Arc<StoredModuleComponents>)> {
        self.child_components
            .get(name)
            .map(|(runtime_pos, stored)| (*runtime_pos, stored.clone()))
    }

    pub(crate) fn lookup_qualified_module(
        &self,
        name: &str,
        ctx: &super::context::TypeContext<'_>,
    ) -> Option<(usize, Ident, ModuleDeclaration)> {
        let (idx, runtime_pos) = *self.modules.get(name)?;
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

        let (id, mut md) = match &self.signature[idx] {
            SignatureItem::SigModule(id, md, _) => (id.clone(), md.clone()),
            _ => return None,
        };
        if let Some((raw_id, raw_md, raw_parent_sig)) =
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
            self.qualified_modules
                .borrow_mut()
                .insert(name.to_string(), (raw_id.clone(), md.clone()));
            ctx.register_qualified_module_decl(
                self.access_path.as_ref(),
                name,
                raw_id.clone(),
                md.clone(),
            );
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
        self.qualified_modules
            .borrow_mut()
            .insert(name.to_string(), (id.clone(), md.clone()));
        ctx.register_qualified_module_decl(self.access_path.as_ref(), name, id.clone(), md.clone());
        Some((runtime_pos, id, md))
    }

    pub(crate) fn lookup_modtype(&self, name: &str) -> Option<(&Ident, &ModtypeDeclaration)> {
        self.component_modtypes.get(name).map(|(id, mtd)| (id, mtd))
    }

    pub(crate) fn lookup_qualified_modtype(
        &self,
        name: &str,
        _ctx: &super::context::TypeContext<'_>,
    ) -> Option<(Ident, ModtypeDeclaration)> {
        if let Some((id, mtd)) = self.qualified_modtypes.borrow().get(name).cloned() {
            return Some((id, mtd));
        }

        // OCaml compiler/ml/env.ml:1581-1585 computes the component-table
        // modtype declaration once with `Subst.modtype_declaration` and later
        // lookup reads that cached declaration. Do not run the child-module
        // substitution pass again here; it would double-substitute package
        // identities that were already handled while building the component.
        let (id, mtd) = self.component_modtypes.get(name).cloned()?;
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
    ctx: &super::context::TypeContext<'_>,
) -> Option<(Ident, ModuleDeclaration, Signature)> {
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
        .filter_map(|name| ctx.find_raw_module_sig(&name))
        .find_map(|raw_parent_sig| {
            raw_parent_sig.iter().find_map(|item| match item {
                SignatureItem::SigModule(id, raw_md, _) if id.name() == module_name => {
                    Some((id.clone(), raw_md.clone(), raw_parent_sig.clone()))
                }
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

fn build_local_module_components<'a>(
    env: &super::env::Env,
    access_path: &Path,
    md: &ModuleDeclaration,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a super::context::TypeContext<'a>,
) -> Option<QualifiedModuleComponents> {
    if let super::decl::ModuleType::MtyAlias(_, alias_path) = &md.md_type {
        // OCaml compiler/ml/env.ml:1517 calls `scrape_alias` before building
        // component tables. `scrape_alias` at env.ml:1440-1446 resolves an
        // alias with `find_module`, and env.ml:865-882 forces the final
        // env.ml:1568 `comp_modules` thunk for that target before returning
        // the module type whose signature is used below.
        match alias_path {
            Path::Pdot(parent, name, _) => {
                let _ = crate::types::typecore::lookup_module_in_resolved_path(
                    parent,
                    name.as_str(),
                    env,
                    pers_env,
                    ctx,
                );
            }
            Path::Pident(id) if id.is_persistent() => {
                if let Some(pers) = pers_env.as_mut() {
                    let _ = pers.get_renamed_sig(id.name(), ctx);
                } else if access_path_is_direct_implicit_open_child(access_path)
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
    let (raw_sig, resolved_name) = env.resolve_module_type(&md.md_type, pers_env, ctx)?;
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

    let mut working_env = env.clone_preserve_id();
    let use_qualified_items_for_env = matches!(md.md_type, super::decl::ModuleType::MtyAlias(..));
    let qualified_sig_for_children = Arc::new(qualified_sig.clone());
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
                let env_decl = if use_qualified_items_for_env {
                    qualified_decl.clone()
                } else {
                    decl.clone()
                };
                working_env.add_type(id.clone(), env_decl);
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
                let child_access_path =
                    qualified_submodule_access_path(access_path, id.name(), runtime_pos, qmd);
                // OCaml compiler/ml/env.ml:1573-1575 builds child
                // `comp_components` from the same `md` item that
                // env.ml:1517 got after `scrape_alias`. For alias parents,
                // compiler/ml/mtype.ml:76-102 has already strengthened child
                // modules to `Mty_alias` declarations; using the raw child
                // declaration would skip the later scrape/find_module force.
                let component_decl = if use_qualified_items_for_env {
                    qmd.clone()
                } else {
                    child_md.clone()
                };
                working_env.add_module_with_component_context(
                    id.clone(),
                    component_decl.clone(),
                    // OCaml compiler/ml/env.ml:1573-1578 stores
                    // `comp_components` as its own lazy over the child module
                    // declaration. It shares the persistent-alias force point
                    // above, but otherwise keeps the child declaration separate
                    // from env.ml:1568's `comp_modules` thunk.
                    component_decl,
                    child_access_path,
                    Some((access_path.clone(), qualified_sig_for_children.clone())),
                );
                crate::cmi::persistent_env::register_types_by_stamp_recursive(&qmd.md_type, ctx);
                if let Some(stored) = working_env
                    .with_local_module_components(&Path::pident(id.clone()), |stored| {
                        Arc::new(stored.clone())
                    })
                {
                    child_components.insert(id.name().to_string(), (runtime_pos, stored));
                }
                runtime_pos += 1;
            }
            (SignatureItem::SigModtype(id, mtd), SignatureItem::SigModtype(_, _)) => {
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
            (SignatureItem::SigClassType, SignatureItem::SigClassType) => {}
            _ => return None,
        }
    }

    Some(QualifiedModuleComponents::new_with_child_components(
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
        ctx: &'a super::context::TypeContext<'a>,
        f: impl FnOnce(&QualifiedModuleComponents) -> R,
    ) -> Option<R> {
        if self.cached.borrow().is_none() {
            let mut module_decl = self.module_decl.clone();
            if let Some((parent_access_path, parent_sig)) = &self.parent_context {
                let sibling_alias = match &module_decl.md_type {
                    super::decl::ModuleType::MtyAlias(_, Path::Pdot(parent, name, _))
                        if !parent_access_path.head().is_persistent()
                            && parent_access_path.head().stamp() != 0
                            && parent.same(parent_access_path) =>
                    {
                        parent_sig.iter().find_map(|item| match item {
                            SignatureItem::SigModule(id, md, _) if id.name() == name.as_str() => {
                                Some(md.md_type.clone())
                            }
                            _ => None,
                        })
                    }
                    _ => None,
                };
                if let Some(md_type) = sibling_alias {
                    // OCaml compiler/ml/env.ml:1516-1578 runs
                    // `scrape_alias` on local child module types before
                    // `prefix_idents` applies the selected component path.
                    // Resolve local sibling aliases from the parent signature
                    // here instead of substituting the alias path first;
                    // otherwise Rust forces env.ml:1568's `Subst.modtype`
                    // thunk and freshens child binders before OCaml does.
                    module_decl.md_type = md_type;
                } else {
                    let keep_alias_target_for_scrape = matches!(
                        &module_decl.md_type,
                        super::decl::ModuleType::MtyAlias(_, Path::Pdot(parent, _, _))
                            if !parent.same(parent_access_path)
                    );
                    if !keep_alias_target_for_scrape {
                        // OCaml compiler/ml/env.ml:1573-1578 stores child
                        // component thunks with the child module type, and
                        // env.ml:1517 scrapes aliases before env.ml:1530-1538
                        // prefixes the selected component path. Preserve
                        // already-qualified alias targets such as
                        // `Stdlib_Date.UTC`/`Js.Json.Kind` until scraping;
                        // substituting them to the selected path first turns
                        // the alias into a self-reference and skips the
                        // component-forcing side effects OCaml observes.
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
}
