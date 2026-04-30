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
    ModtypeDeclaration, ModuleDeclaration, Signature, SignatureItem, TypeDeclaration,
    ValueDescription, ValueKind,
};
use super::path::Path;

#[derive(Debug, Clone)]
pub(crate) struct QualifiedModuleComponents {
    access_path: Arc<Path>,
    signature: Arc<Signature>,
    values: Arc<HashMap<String, (usize, usize)>>,
    types: Arc<HashMap<String, usize>>,
    modules: Arc<HashMap<String, (usize, usize)>>,
    modtypes: Arc<HashMap<String, usize>>,
    qualified_modules: RefCell<HashMap<String, (Ident, ModuleDeclaration)>>,
    qualified_modtypes: RefCell<HashMap<String, (Ident, ModtypeDeclaration)>>,
    child_components: Arc<HashMap<String, (usize, Arc<StoredModuleComponents>)>>,
}

impl QualifiedModuleComponents {
    pub(crate) fn new(access_path: Path, signature: Signature) -> Self {
        Self::new_with_child_components(access_path, signature, HashMap::new())
    }

    pub(crate) fn new_with_child_components(
        access_path: Path,
        signature: Signature,
        child_components: HashMap<String, (usize, Arc<StoredModuleComponents>)>,
    ) -> Self {
        let mut values = HashMap::new();
        let mut types = HashMap::new();
        let mut modules = HashMap::new();
        let mut modtypes = HashMap::new();
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
                    runtime_pos += 1;
                }
                SignatureItem::SigModtype(id, _) => {
                    modtypes.insert(id.name().to_string(), idx);
                }
                SignatureItem::SigClassType => {}
            }
        }

        Self {
            access_path: Arc::new(access_path),
            signature: Arc::new(signature),
            values: Arc::new(values),
            types: Arc::new(types),
            modules: Arc::new(modules),
            modtypes: Arc::new(modtypes),
            qualified_modules: RefCell::new(HashMap::new()),
            qualified_modtypes: RefCell::new(HashMap::new()),
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

        let (id, mut md) = match &self.signature[idx] {
            SignatureItem::SigModule(id, md, _) => (id.clone(), md.clone()),
            _ => return None,
        };
        crate::cmi::persistent_env::substitute_type_paths_in_child_module_type(
            &mut md.md_type,
            &self.signature,
            &self.access_path,
            ctx,
        );
        self.qualified_modules
            .borrow_mut()
            .insert(name.to_string(), (id.clone(), md.clone()));
        Some((runtime_pos, id, md))
    }

    pub(crate) fn lookup_modtype(&self, name: &str) -> Option<(&Ident, &ModtypeDeclaration)> {
        let idx = *self.modtypes.get(name)?;
        match &self.signature[idx] {
            SignatureItem::SigModtype(id, mtd) => Some((id, mtd)),
            _ => None,
        }
    }

    pub(crate) fn lookup_qualified_modtype(
        &self,
        name: &str,
        ctx: &super::context::TypeContext<'_>,
    ) -> Option<(Ident, ModtypeDeclaration)> {
        let idx = *self.modtypes.get(name)?;
        if let Some((id, mtd)) = self.qualified_modtypes.borrow().get(name).cloned() {
            return Some((id, mtd));
        }

        let (id, mut mtd) = match &self.signature[idx] {
            SignatureItem::SigModtype(id, mtd) => (id.clone(), mtd.clone()),
            _ => return None,
        };
        if let Some(mty) = mtd.mtd_type.as_mut() {
            crate::cmi::persistent_env::substitute_type_paths_in_child_module_type(
                mty,
                &self.signature,
                &self.access_path,
                ctx,
            );
        }
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
    md: &ModuleDeclaration,
) -> Path {
    if parent_access_path.head().is_persistent() || parent_access_path.head().stamp() == 0 {
        md.md_path
            .clone()
            .unwrap_or_else(|| Path::pdot(parent_access_path.clone(), module_name.to_string()))
    } else {
        Path::pdot_pos(
            parent_access_path.clone(),
            module_name.to_string(),
            runtime_pos as i32,
        )
    }
}

fn build_local_module_components<'a>(
    env: &super::env::Env,
    access_path: &Path,
    md: &ModuleDeclaration,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a super::context::TypeContext<'a>,
) -> Option<QualifiedModuleComponents> {
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
                working_env.add_type(id.clone(), decl.clone());
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
                working_env.add_module_with_component_context(
                    id.clone(),
                    child_md.clone(),
                    qmd.clone(),
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
                working_env.add_modtype(id.clone(), mtd.clone());
            }
            (SignatureItem::SigClassType, SignatureItem::SigClassType) => {}
            _ => return None,
        }
    }

    Some(QualifiedModuleComponents::new_with_child_components(
        access_path.clone(),
        qualified_sig,
        child_components,
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
                crate::cmi::persistent_env::substitute_type_paths_in_child_module_type(
                    &mut module_decl.md_type,
                    parent_sig,
                    parent_access_path,
                    ctx,
                );
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
