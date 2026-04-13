//! Lazy qualified module components, matching OCaml's EnvLazy backbone.
//!
//! OCaml memoizes `components_of_module_maker (env, sub, path, mty)` and then
//! answers repeated type/module/value lookups from that cached view. Rust used
//! to cache only copied signatures and still re-scan or re-copy declarations on
//! each lookup. This module provides the cached qualified view that the hot
//! module-resolution paths use as their source of truth.

use ahash::AHashMap as HashMap;

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

    pub(crate) fn lookup_modtype(&self, name: &str) -> Option<(&Ident, &ModtypeDeclaration)> {
        let idx = *self.modtypes.get(name)?;
        match &self.signature[idx] {
            SignatureItem::SigModtype(id, mtd) => Some((id, mtd)),
            _ => None,
        }
    }
}
