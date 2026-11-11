//! GenType TypeScript emitter port.
//!
//! This module is a staged Rust port of `compiler/gentype/*.ml`. The files are
//! kept close to the OCaml implementation and wired incrementally.

/// `@genType` and related attributes: reading them and their payloads (`Annotation.ml`).
pub mod annotation;
/// The items a translation produces: value exports and imports, and type declarations (`CodeItem.ml`).
pub mod code_item;
/// The gentype configuration a compilation runs with (`GenTypeConfig.ml`).
pub mod config;
/// Inlining of exported types into the types that mention them (`Converter.ml`).
pub mod converter;
/// Switches for gentype's debug logging (`Debug.ml`).
pub mod debug;
/// Resolution of type paths to the dependencies of translated types
/// (`Dependencies.ml`).
pub mod dependencies;
/// Emission of a translation as a generated TypeScript file (`EmitJs.ml`).
pub mod emit_js;
/// Small helpers for emitted text (`EmitText.ml`).
pub mod emit_text;
/// Rendering of types, exports and imports as TypeScript (`EmitType.ml`).
pub mod emit_type;
/// The sections a generated file is assembled from (`Emitters.ml`).
pub mod emitters;
/// Grouping of the values exported from submodules into nested objects (`ExportModule.ml`).
pub mod export_module;
/// Generation of fresh type variable names (`GenIdent.ml`).
pub mod gen_ident;
/// The types gentype translates into, and helpers shared by the whole emitter (`GenTypeCommon.ml`).
pub mod gen_type_common;
/// Writing generated files only when their contents change (`GeneratedFiles.ml`).
pub mod generated_files;
/// Paths that generated files import from (`ImportPath.ml`).
pub mod import_path;
/// Indentation of emitted text (`Indent.ml`).
pub mod indent;
/// Gentype's logging and its colored diagnostics (`Log_.ml`).
pub mod log_;
/// The entry point: translating a typed artifact and writing its generated file (`GenTypeMain.ml`).
pub mod main;
/// The file extensions of generated and shim modules (`ModuleExtension.ml`).
pub mod module_extension;
/// Module names as gentype handles them (`ModuleName.ml`).
pub mod module_name;
/// Resolution of imported modules to the files gentype imports them from
/// (`ModuleResolver.ml`).
pub mod module_resolver;
/// The arguments of translated function types (`NamedArgs.ml`).
pub mod named_args;
/// The paths of source, output and `.cmt` files (`Paths.ml`).
pub mod paths;
/// Names qualified by the submodules they are declared in (`ResolvedName.ml`).
pub mod resolved_name;
/// The runtime representations gentype refers to: how values are reached in
/// compiled modules, and the fields of variants (`Runtime.ml`).
pub mod runtime;
/// Translation of type expressions written in the source (`TranslateCoreType.ml`).
pub mod translate_core_type;
/// Translation of typed signatures, from `.resi` files (`TranslateSignature.ml`).
pub mod translate_signature;
/// Translation of signatures that exist only as types, such as those of
/// included or aliased modules (`TranslateSignatureFromTypes.ml`).
pub mod translate_signature_from_types;
/// Translation of typed structures, from `.res` files (`TranslateStructure.ml`).
pub mod translate_structure;
/// Translation of type declarations (`TranslateTypeDeclarations.ml`).
pub mod translate_type_declarations;
/// Translation of inferred type expressions (`TranslateTypeExprFromTypes.ml`).
pub mod translate_type_expr_from_types;
/// The result of translating an artifact, and the translation of values
/// (`Translation.ml`).
pub mod translation;
/// The environment of types and modules a translation resolves names in
/// (`TypeEnv.ml`).
pub mod type_env;
/// Type variables of translated types: collecting and substituting them
/// (`TypeVars.ml`).
pub mod type_vars;
