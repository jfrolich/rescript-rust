//! ReScript Compiler - Rust Implementation
//!
//! This crate provides the ReScript compiler implementation in Rust,
//! designed for concurrent compilation with no global mutable state.
//!
//! # Architecture
//!
//! The compiler is organized around explicit context objects that are
//! passed through the compilation pipeline:
//!
//! - [`CompilerConfig`] - Immutable configuration shared across compilations
//! - [`CompilationContext`] - Per-compilation context with ID generation and diagnostics
//! - [`TypeContext`] - Per-type-checking context with type arena (future)
//! - [`ModuleCache`] - Thread-safe cache for compiled module interfaces
//!
//! # Concurrency Model
//!
//! Multiple files can be compiled in parallel because:
//! 1. No global mutable state - all state is in explicit contexts
//! 2. Each compilation gets its own `CompilationContext`
//! 3. Shared data uses thread-safe structures (`Arc`, `DashMap`)
//!
//! ```rust,ignore
//! use rescript_compiler::{CompilationContext, CompilerConfig, ModuleCache};
//! use rayon::prelude::*;
//!
//! let config = Arc::new(CompilerConfig::default());
//! let cache = Arc::new(ModuleCache::new());
//!
//! modules.par_iter().map(|module| {
//!     let ctx = CompilationContext::new(config.clone(), cache.clone());
//!     ctx.compile_module(module)
//! }).collect()
//! ```

#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![allow(clippy::uninlined_format_args)] // Style preference, not a correctness issue

pub mod arena;
pub mod binary_ast;
pub mod cache;
/// CMI file loading infrastructure.
pub mod cmi;
pub mod config;
pub mod context;
/// Cached debug environment flags.
pub mod debug_flags;
pub mod diagnostics;
pub mod driver;
/// GenType TypeScript emitter port.
pub mod gentype;
pub mod ident;
pub mod intern;
pub mod js_ir;
pub mod lambda;
pub mod location;
pub mod parse_arena;
pub mod parser;
/// Optional aggregate compiler performance counters.
pub mod perf_counters;
pub mod process_cwd;
pub mod raw_lambda;
/// Source text decoding helpers.
pub mod source_text;
/// Optional aggregate compiler phase timings.
pub mod timing;
pub mod types;
#[cfg(target_arch = "wasm32")]
pub mod wasm_vfs;

// Re-exports for convenience
#[cfg(feature = "native")]
pub use cache::ModuleCache;
pub use config::CompilerConfig;
#[cfg(feature = "native")]
pub use context::CompilationContext;
pub use context::IdGenerator;
pub use diagnostics::DiagnosticsContext;
pub use ident::Ident;
pub use lambda::Lambda;
pub use location::Location;
pub use types::{Path, TypeContext, TypeExpr, Variance};

// Binary AST exports
pub use binary_ast::{Marshal, MarshalWriter};
