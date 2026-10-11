//! A module's published interface as an incremental build stores it: its
//! portable signature, the JS metadata other modules' code generation reads,
//! the alias rewrites it registered, and the GenType type declarations of its
//! typed artifacts (GenType translates imported types with them). Loading one stands in for compiling
//! an unchanged dependency.

use ahash::AHashMap as HashMap;

use super::persistent_env::InMemoryModuleInfo;
use super::portable_types::PortablePersStruct;
use crate::types::path::Path;

/// Borrowed form, for encoding straight from the registry.
#[derive(serde::Serialize)]
pub struct StoredModuleRef<'a> {
    pub pers_struct: Option<&'a PortablePersStruct>,
    pub info: &'a InMemoryModuleInfo,
    pub alias_rewrites: &'a [(String, Path)],
    pub gentype_declarations: &'a [(String, GentypeDeclarations)],
}

/// GenType type declarations of one typed artifact, by `.cmt` path.
pub type GentypeDeclarations = std::sync::Arc<Vec<crate::gentype::code_item::TypeDeclaration>>;

/// A decoded stored module.
#[derive(serde::Deserialize)]
pub struct StoredModule {
    pub pers_struct: Option<PortablePersStruct>,
    pub info: InMemoryModuleInfo,
    pub alias_rewrites: Vec<(String, Path)>,
    pub gentype_declarations: Vec<(String, Vec<crate::gentype::code_item::TypeDeclaration>)>,
}

impl StoredModule {
    pub fn alias_rewrite_map(&self) -> HashMap<String, Path> {
        self.alias_rewrites.iter().cloned().collect()
    }
}

pub fn encode(module: &StoredModuleRef<'_>) -> Vec<u8> {
    crate::binser::to_vec(module).expect("encoding to memory cannot fail")
}

/// `None` for data that does not decode (written by another compiler
/// version: the build record is discarded on compiler changes, but be safe).
pub fn decode(bytes: &[u8]) -> Option<StoredModule> {
    crate::binser::from_slice(bytes).ok()
}
