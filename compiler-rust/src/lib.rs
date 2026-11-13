//! ReScript Compiler - Rust Implementation
//!
//! This crate provides the ReScript compiler implementation in Rust,
//! designed for concurrent compilation with no global mutable state.
//!
//! # Architecture
//!
//! Each compilation owns its mutable state in explicit context objects:
//!
//! - [`IdGenerator`] - identifier stamps and type-node ids for one compilation
//! - [`TypeContext`] - the type checker's state, including the type-node arena
//!
//! # Concurrency Model
//!
//! Multiple files can be compiled in parallel because there is no global
//! mutable state: compiler data inside a compilation lives in
//! per-compilation arenas addressed by indices, not `Rc`/`Arc`, and only
//! configuration is shared between compilations.

#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![allow(clippy::uninlined_format_args)] // Style preference, not a correctness issue

pub mod analysis;
pub mod arena;
pub mod ast_fixed_arg;
pub mod ast_helper_type;
pub mod ast_jsx_component;
pub mod ast_payload;
pub mod ast_raw;
pub mod ast_todo;
pub mod binary_ast;
pub mod binser;
pub mod bir;
#[cfg(feature = "native")]
pub mod cli;
/// CMI file loading infrastructure.
pub mod cmi;
pub mod context;
/// Cached debug environment flags.
pub mod debug_flags;
pub mod diagnostics;
pub mod driver;
#[doc(hidden)]
pub mod tc;
pub mod emit;
pub mod fast_hash;
/// GenType TypeScript emitter port.
pub mod gentype;
pub mod hash_seed;
pub mod ident;
pub mod intern;
pub mod js_ir;
pub mod lambda;
pub mod location;
pub mod misc;
pub mod name;
pub mod ocaml_float;
pub mod parse_arena;
pub mod parser;
/// Optional aggregate compiler performance counters.
pub mod perf_counters;
pub mod process_cwd;
pub mod raw_lambda;
/// Source text decoding helpers.
pub mod source_text;
pub mod string_literal;
/// Optional aggregate compiler phase timings.
pub mod timing;
pub mod types;
pub mod verify;
#[cfg(target_arch = "wasm32")]
pub mod wasm_vfs;

// Re-exports for convenience
pub use context::IdGenerator;
pub use ident::Ident;
pub use lambda::Lambda;
pub use location::Location;
pub use types::{Path, TypeContext, TypeExpr, Variance};

// Binary AST exports
pub use binary_ast::{Marshal, MarshalWriter};

/// Generic cost accounting for generated items, implemented behind the derive seam.
pub use binary_ast::derive::census as derived_census;
