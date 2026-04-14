//! Lazy qualified module components, matching OCaml's EnvLazy backbone.
//!
//! OCaml memoizes `components_of_module_maker (env, sub, path, mty)` and then
//! answers repeated type/module/value lookups from that cached view. Rust used
//! to cache only copied signatures and still re-scan or re-copy declarations on
//! each lookup. This module provides the cached qualified view that the hot
//! module-resolution paths use as their source of truth.

use ahash::AHashMap as HashMap;
use std::cell::RefCell;

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
}

impl QualifiedModuleComponents {
    pub(crate) fn new(access_path: Path, signature: Signature) -> Self {
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
