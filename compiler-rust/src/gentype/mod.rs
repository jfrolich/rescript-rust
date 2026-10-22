//! GenType TypeScript emitter port.
//!
//! This module is a staged Rust port of `compiler/gentype/*.ml`. The files are
//! kept close to the OCaml implementation and wired incrementally.

pub mod annotation;
pub mod code_item;
pub mod config;
pub mod converter;
pub mod debug;
pub mod dependencies;
pub mod emit_js;
pub mod emit_text;
pub mod emit_type;
pub mod emitters;
pub mod export_module;
pub mod gen_ident;
pub mod gen_type_common;
pub mod generated_files;
pub mod import_path;
pub mod indent;
pub mod log_;
pub mod main;
pub mod module_extension;
pub mod module_name;
pub mod module_resolver;
pub mod named_args;
pub mod paths;
pub mod resolved_name;
pub mod runtime;
pub mod translate_core_type;
pub mod translate_signature;
pub mod translate_signature_from_types;
pub mod translate_structure;
pub mod translate_type_declarations;
pub mod translate_type_expr_from_types;
pub mod translation;
pub mod type_env;
pub mod type_vars;
