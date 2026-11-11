//! Binary AST file generation
//!
//! This module implements generation of binary AST files (.ast, .iast) that are
//! byte-identical to those produced by the OCaml compiler. These files are used for:
//!
//! 1. **Incremental compilation**: Cached parsed ASTs avoid re-parsing unchanged files
//! 2. **Conversion tools**: Frozen v0 AST compatibility remains for tools and tests
//! 3. **Build system integration**: `rewatch` uses binary ASTs for dependency tracking
//!
//! # Binary AST File Format
//!
//! The binary AST file has three sections:
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │ SECTION 1: Header                                                   │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ Offset 0-3: Dependency section size (4 bytes, big-endian u32)       │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ SECTION 2: Dependencies + Source Path                               │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ Byte 4: '\n' (0x0A) - separator                                     │
//! │ "ModuleName1\n"                                                     │
//! │ "ModuleName2\n"                                                     │
//! │ ...                                                                 │
//! │ "/" - terminates deps AND starts absolute path                      │
//! │ "Users/path/to/source.res\n" - rest of path + newline               │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ SECTION 3: OCaml Marshal Data                                       │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │ Magic: 0x84 0x95 0xA6 0xBE (4 bytes)                                │
//! │ Header: data_len(4) + obj_count(4) + size_32(4) + size_64(4)        │
//! │ Payload: Encoded AST (current parsetree for -bs-ast,                │
//! │          frozen parsetree0 for the external PPX protocol)           │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Module Structure
//!
//! - [`marshal`] - OCaml Marshal format writer
//! - [`serialize`] - Marshal trait and implementations for basic types
//! - [`current_marshal`] - Marshal implementations for the current parsetree (`-bs-ast`)
//! - [`parsetree0`] - Frozen PPX-compatible AST type definitions
//! - [`parsetree0_marshal`] - Marshal implementations for parsetree0
//! - [`parsetree0_unmarshal`] - Decoder for parsetree0 values returned by external PPXs
//! - [`mapper_to0`] - Current parsetree → parsetree0 conversion
//! - [`mapper_from0`] - parsetree0 → current parsetree conversion
//! - [`ppx`] - Built-in PPX rewrites applied before marshalling
//! - [`mod@derive`] - Single seam for removable built-in derives
//! - [`spice_ppx`] - Built-in spice PPX
//! - [`ast_iter`] - Port of OCaml `Ast_iterator` for the current parsetree
//! - [`ffi_types`] - Marshalling of digested externals (`External_ffi_types`)
//! - [`types`] - Marshal implementations for core types (Position, Location, Longident)
//! - [`deps`] - Module dependency extraction
//! - [`header`] - Binary AST header reader (`Binary_ast.read_header`)
//! - [`writer`] - Binary AST file writer

pub mod ast_dict;
pub mod ast_iter;
pub mod current_marshal;
pub mod deps;
pub mod derive;
pub mod ffi_types;
pub mod header;
pub mod mapper_from0;
pub mod mapper_to0;
pub mod marshal;
pub mod parsetree0;
pub mod parsetree0_marshal;
pub mod parsetree0_unmarshal;
pub mod ppx;
pub mod serialize;
pub mod spice_ppx;
pub mod types;
pub mod writer;

// Re-exports
pub use deps::{Dependencies, extract_signature_deps, extract_structure_deps};
pub use mapper_to0::{map_signature, map_structure};
pub use marshal::MarshalWriter;
pub use parsetree0::*;
pub use serialize::Marshal;
pub use writer::{
    write_external_ppx_signature_input, write_external_ppx_structure_input,
    write_signature_ast_current_with_extra_deps_and_builtin_ppx,
    write_structure_ast_current_with_extra_deps_and_builtin_ppx,
};
