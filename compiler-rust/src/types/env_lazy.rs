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
    access_path: Path,
    signature: Signature,
    values: HashMap<String, (usize, usize)>,
    types: HashMap<String, usize>,
    modules: HashMap<String, (usize, usize)>,
    modtypes: HashMap<String, usize>,
    qualified_modules: RefCell<HashMap<String, (Ident, ModuleDeclaration)>>,
    qualified_modtypes: RefCell<HashMap<String, (Ident, ModtypeDeclaration)>>,
    child_components: HashMap<String, (usize, Arc<StoredModuleComponents>)>,
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
            access_path,
            signature,
            values,
            types,
            modules,
            modtypes,
            qualified_modules: RefCell::new(HashMap::new()),
            qualified_modtypes: RefCell::new(HashMap::new()),
            child_components,
        }
    }

    pub(crate) fn access_path(&self) -> &Path {
        &self.access_path
    }

    pub(crate) fn signature(&self) -> &[SignatureItem] {
        &self.signature
    }

    pub(crate) fn cloned_signature(&self) -> Signature {
        self.signature.clone()
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
    let sig = crate::types::typecore::build_qualified_signature_for_access_path(
        env,
        access_path,
        &md.md_type,
        pers_env,
        ctx,
    )?;
    let mut working_env = env.clone_preserve_id();
    let mut child_components = HashMap::new();
    let mut runtime_pos = 0usize;

    for item in &sig {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    runtime_pos += 1;
                }
            }
            SignatureItem::SigType(id, decl, rec_status) => {
                let item = SignatureItem::SigType(id.clone(), decl.clone(), *rec_status);
                crate::cmi::persistent_env::add_signature_to_env(
                    std::slice::from_ref(&item),
                    access_path,
                    &mut working_env,
                    ctx,
                    false,
                );
            }
            SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                runtime_pos += 1;
            }
            SignatureItem::SigModule(id, child_md, _) => {
                let child_access_path =
                    qualified_submodule_access_path(access_path, id.name(), runtime_pos, child_md);
                let mut child_md = child_md.clone();
                child_md.md_path = Some(child_access_path.clone());
                working_env.add_module_with_component_path(
                    id.clone(),
                    child_md.clone(),
                    child_access_path,
                );
                crate::cmi::persistent_env::register_types_by_stamp_recursive(&child_md.md_type, ctx);
                if let Some(stored) = working_env.with_local_module_components(
                    &Path::pident(id.clone()),
                    |stored| Arc::new(stored.clone()),
                ) {
                    child_components.insert(id.name().to_string(), (runtime_pos, stored));
                }
                runtime_pos += 1;
            }
            SignatureItem::SigModtype(id, mtd) => {
                let item = SignatureItem::SigModtype(id.clone(), mtd.clone());
                crate::cmi::persistent_env::add_signature_to_env(
                    std::slice::from_ref(&item),
                    access_path,
                    &mut working_env,
                    ctx,
                    false,
                );
            }
            SignatureItem::SigClassType => {}
        }
    }

    Some(QualifiedModuleComponents::new_with_child_components(
        access_path.clone(),
        sig,
        child_components,
    ))
}

#[derive(Debug, Clone)]
pub(crate) struct StoredModuleComponents {
    seed_env: Box<super::env::Env>,
    access_path: Path,
    module_decl: ModuleDeclaration,
    cached: RefCell<Option<QualifiedModuleComponents>>,
}

impl StoredModuleComponents {
    pub(crate) fn new(
        seed_env: super::env::Env,
        access_path: Path,
        module_decl: ModuleDeclaration,
    ) -> Self {
        Self {
            seed_env: Box::new(seed_env),
            access_path,
            module_decl,
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
            let components = build_local_module_components(
                self.seed_env.as_ref(),
                &self.access_path,
                &self.module_decl,
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
