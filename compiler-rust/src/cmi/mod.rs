//! CMI file loading infrastructure.
//!
//! This module implements reading OCaml's compiled module interface (CMI) files,
//! which contain type signatures for external modules. This enables the Rust
//! compiler to type-check code that references external modules like Belt, Js, etc.
//!
//! # Architecture
//!
//! - `marshal_reader`: Generic OCaml Marshal binary format reader
//! - `cmi_format`: CMI file format parser (magic number, header, signature)
//! - `sig_reader`: Converts generic marshal values into Rust `Types` structures
//! - `persistent_env`: Caches loaded modules and provides lookup functions

pub mod cmi_format;
pub mod ffi_decode;
pub mod item_deps;
pub mod stored_module;
pub mod marshal_reader;
pub mod persistent_env;
pub mod portable_types;
pub mod sig_reader;

pub use cmi_format::CmiInfos;
pub use persistent_env::PersistentEnv;
