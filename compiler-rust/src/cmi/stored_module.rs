//! A module's published interface as an incremental build stores it: its
//! portable signature, the JS metadata other modules' code generation reads,
//! and the GenType type declarations of its typed artifacts (GenType
//! translates imported types with them). Loading one stands in for compiling
//! an unchanged dependency.
//!
//! The encoding has two parts, so a build can register a stored module
//! without decoding all of it (see `ModuleRegistry::register_stored_lazily`):
//!
//! - the extras: the GenType declarations, which other modules' compiles
//!   look up by typed-artifact path and so must be registered up front;
//! - the core: the signature and JS metadata, which a compile only reads
//!   through the module's name, decoded the first time it is looked up.
//!
//! An encoded module is the extras' length (4 bytes, little endian), the
//! extras, then the core.

use super::persistent_env::InMemoryModuleInfo;
use super::portable_types::PortablePersStruct;

/// Borrowed form, for encoding straight from the registry.
pub struct StoredModuleRef<'a> {
    pub pers_struct: Option<&'a PortablePersStruct>,
    pub info: &'a InMemoryModuleInfo,
    pub gentype_declarations: &'a [(String, GentypeDeclarations)],
}

#[derive(serde::Serialize)]
struct ExtrasRef<'a> {
    gentype_declarations: &'a [(String, GentypeDeclarations)],
}

#[derive(serde::Serialize)]
struct CoreRef<'a> {
    pers_struct: Option<&'a PortablePersStruct>,
    info: &'a InMemoryModuleInfo,
}

/// GenType type declarations of one typed artifact, by `.cmt` path.
pub type GentypeDeclarations = crate::gentype::main::EncodedTypeDeclarations;

/// The part of a stored module registered up front.
#[derive(serde::Deserialize, Default)]
pub struct StoredExtras {
    /// The GenType declarations of the module's typed artifacts.
    pub gentype_declarations: Vec<(String, GentypeDeclarations)>,
}

/// The part of a stored module decoded when the module is first looked up.
#[derive(serde::Deserialize)]
pub struct StoredCore {
    /// The module's signature, `None` for a module registered without one.
    pub pers_struct: Option<PortablePersStruct>,
    /// The module's JS metadata.
    pub info: InMemoryModuleInfo,
}

/// Encode a module as the build stores it (see the module documentation).
pub fn encode(module: &StoredModuleRef<'_>) -> Vec<u8> {
    let extras = encode_extras(module);
    let core = encode_core(module);
    let mut out = Vec::with_capacity(4 + extras.len() + core.len());
    out.extend_from_slice(&(extras.len() as u32).to_le_bytes());
    out.extend_from_slice(&extras);
    out.extend_from_slice(&core);
    out
}

fn encode_extras(module: &StoredModuleRef<'_>) -> Vec<u8> {
    crate::binser::to_vec(&ExtrasRef {
        gentype_declarations: module.gentype_declarations,
    })
    .expect("encoding to memory cannot fail")
}

fn encode_core(module: &StoredModuleRef<'_>) -> Vec<u8> {
    crate::binser::to_vec(&CoreRef {
        pers_struct: module.pers_struct,
        info: module.info,
    })
    .expect("encoding to memory cannot fail")
}

/// A module's extras, `None` when it has none, and core, encoded
/// separately so a build can store the core where it reads it only on demand.
pub fn encode_parts(module: &StoredModuleRef<'_>) -> (Option<Vec<u8>>, Vec<u8>) {
    let extras = (!module.gentype_declarations.is_empty()).then(|| encode_extras(module));
    (extras, encode_core(module))
}

/// The encoded extras and core of a stored module, `None` when `bytes` is
/// too short to hold them.
pub fn split(bytes: &[u8]) -> Option<(&[u8], &[u8])> {
    let len = u32::from_le_bytes(bytes.get(..4)?.try_into().ok()?) as usize;
    let extras = bytes.get(4..4 + len)?;
    Some((extras, &bytes[4 + len..]))
}

/// `None` for data that does not decode (written by another compiler
/// version: the build record is discarded on compiler changes, but be safe).
pub fn decode_extras(bytes: &[u8]) -> Option<StoredExtras> {
    crate::binser::from_slice(bytes).ok()
}

/// See [`decode_extras`].
pub fn decode_core(bytes: &[u8]) -> Option<StoredCore> {
    crate::binser::from_slice(bytes).ok()
}
