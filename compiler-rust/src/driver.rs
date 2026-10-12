//! Compiler driver utilities.
//!
//! This module wires together parsing, type-checking, Lambda conversion, and
//! JS IR codegen to produce JavaScript output.

mod type_clash;

use std::borrow::Cow;
use std::ffi::OsString;
use std::fmt;
use std::path::{Component, Path as FsPath, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use ahash::AHashSet;
use anyhow::{Context, Result, anyhow};
use tracing::info_span;

use crate::binary_ast::{
    ppx, write_external_ppx_signature_input, write_external_ppx_structure_input,
};
use crate::cmi::persistent_env::{
    CmjExportArity, CmjExportConstant, ModuleRegistry, PersistentEnv, PersistentEnvError,
};
use crate::cmi::portable_types::PortablePersStruct;
use crate::context::IdGenerator;
use crate::diagnostics::WarningConfig;
use crate::ident::Ident;
use crate::js_ir::{
    DepsProgram, Kind, ModuleFormat, ModuleId, ModulePathResolutionError, ModulePathResolver,
    print_deps_program_with_directives_and_options, print_deps_program_with_source_map,
};
use crate::lambda::lam_compile::LambdaCompiler;
use crate::location::Location;
use crate::parse_arena::{ExprIdx, LocIdx, ModExprIdx, ParseArena, StrIdx};
use crate::parser::ast::{
    ArgLabel as ParserArgLabel, Attribute, Attributes, Constant, Expression, ExpressionDesc,
    ModuleExpr, ModuleExprDesc, PatternDesc, Payload, Signature, SignatureItemDesc, Structure,
    StructureItemDesc,
};
use crate::parser::{Longident, Parser, code_frame, jsx_ppx, module};
use crate::types::sexp_typedtree::{
    print_typed_signature, print_typed_signature_with_locs, print_typed_structure,
    print_typed_structure_with_locs,
};
use crate::types::typecore::{BuiltinExtensionError, JsxPropKind, TypeCoreError, TypeCoreWarning};
use crate::types::typemod::{TypeExtensionMismatch, TypeModError, UnboundTypeVarDetail};
use crate::types::{
    ArgLabel as TypeArgLabel, TypeCheckContext, TypeClashContext, TypeContext, TypeDesc,
    TypeExprRef, initial_env, transl_signature, type_structure,
};

// OCaml's Predef sets `Ident.set_current_time 999`. OCaml's Parmatch.extra_pat
// then eagerly creates Ident.create "+" consuming stamp 1000.
// We match this by starting at 999 and consuming one stamp.
const OCAML_NON_PREDEF_STAMP_START: i32 = 999;
const LET_UNWRAP_FEATURE_NOT_ENABLED_MSG: &str = "Experimental feature not enabled: LetUnwrap. Enable it by setting \"LetUnwrap\" to true under \"experimental-features\" in rescript.json.";
const LET_UNWRAP_TOPLEVEL_MSG: &str = "`let?` is not allowed for top-level bindings.";
const LET_UNWRAP_UNSUPPORTED_TYPE_MSG: &str =
    "`let?` is only supported in let bindings targeting the `result` or `option` type.";
static SKIP_CLI_CLEANUP: AtomicBool = AtomicBool::new(false);
static EXTERNAL_PPX_TEMP_COUNTER: AtomicUsize = AtomicUsize::new(0);
const AST_IMPL_MAGIC_NUMBER: &[u8] = b"Caml1999M022";
const AST_INTF_MAGIC_NUMBER: &[u8] = b"Caml1999N022";

#[derive(Debug)]
pub struct UserDiagnostic {
    output: String,
    exit_code: i32,
}

impl UserDiagnostic {
    pub fn new(output: String, exit_code: i32) -> Self {
        let output = match crate::source_text::decode_internal_utf8_runs(&output) {
            std::borrow::Cow::Borrowed(_) => output,
            std::borrow::Cow::Owned(decoded) => decoded,
        };
        Self { output, exit_code }
    }

    pub fn output(&self) -> &str {
        &self.output
    }

    pub fn exit_code(&self) -> i32 {
        self.exit_code
    }
}

impl fmt::Display for UserDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.output)
    }
}

impl std::error::Error for UserDiagnostic {}

pub fn enable_cli_cleanup_skip() {
    SKIP_CLI_CLEANUP.store(true, Ordering::Relaxed);
}

pub fn module_name_from_source_filename(path: &str) -> String {
    let basename = std::path::Path::new(path)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(path);
    let name = basename.split('.').next().unwrap_or(basename);
    let mut chars = name.chars();
    match chars.next() {
        None => String::new(),
        Some(ch) => ch.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

pub fn max_lambda_input_stamp(typed_structure: &crate::types::typedtree::Structure) -> i32 {
    use crate::ident::Ident;
    use crate::types::decl::{
        ConstructorArguments as DeclConstructorArguments, ModuleType as DeclModuleType,
        SignatureItem as DeclSignatureItem, TypeKind as DeclTypeKind,
    };
    use crate::types::path::Path as TypePath;
    use crate::types::typedtree::{
        Case, ConstructorArgument, ExpExtra, Expression, ExpressionDesc, ExtensionConstructor,
        ExtensionConstructorKind, FunctionParam, IncludeDescription, ModuleBinding, ModuleCoercion,
        ModuleExpr, ModuleExprDesc, ModuleType, ModuleTypeConstraint, ModuleTypeDeclaration,
        ModuleTypeDesc, OpenDeclaration, PatExtra, Pattern, PatternDesc, RowFieldDesc, Structure,
        StructureItemDesc, TypedConstructorArguments, TypedCoreType, TypedCoreTypeDesc,
        TypedSignature, TypedSignatureItemDesc, TypedTypeDeclaration, TypedTypeKind,
        TypedValueDescription, ValueBinding, WithConstraint,
    };

    fn visit_ident(max_stamp: &mut i32, id: &Ident) {
        *max_stamp = (*max_stamp).max(id.stamp());
    }

    fn visit_path(max_stamp: &mut i32, path: &TypePath) {
        match path {
            TypePath::Pident(id) => visit_ident(max_stamp, id),
            TypePath::Pdot(prefix, _, _) => visit_path(max_stamp, prefix),
            TypePath::Papply(functor, arg) => {
                visit_path(max_stamp, functor);
                visit_path(max_stamp, arg);
            }
        }
    }

    fn visit_typed_core_type(max_stamp: &mut i32, core_type: &TypedCoreType) {
        match &core_type.ctyp_desc {
            TypedCoreTypeDesc::Ttyp_var(_) => {}
            TypedCoreTypeDesc::Ttyp_arrow(args, ret) => {
                for arg in args {
                    visit_typed_core_type(max_stamp, &arg.typ);
                }
                visit_typed_core_type(max_stamp, ret);
            }
            TypedCoreTypeDesc::Ttyp_tuple(items) => {
                for item in items {
                    visit_typed_core_type(max_stamp, item);
                }
            }
            TypedCoreTypeDesc::Ttyp_constr(path, _, args) => {
                visit_path(max_stamp, path);
                for arg in args {
                    visit_typed_core_type(max_stamp, arg);
                }
            }
            TypedCoreTypeDesc::Ttyp_object(fields, _) => {
                for field in fields {
                    match &field.of_desc {
                        crate::types::typedtree::ObjectFieldDesc::OTtag(_, ty)
                        | crate::types::typedtree::ObjectFieldDesc::OTinherit(ty) => {
                            visit_typed_core_type(max_stamp, ty);
                        }
                    }
                }
            }
            TypedCoreTypeDesc::Ttyp_poly(_, inner) | TypedCoreTypeDesc::Ttyp_alias(inner, _) => {
                visit_typed_core_type(max_stamp, inner);
            }
            TypedCoreTypeDesc::Ttyp_variant(fields, _, _) => {
                for field in fields {
                    match &field.rf_desc {
                        RowFieldDesc::Rtag(_, _, tys) => {
                            for ty in tys {
                                visit_typed_core_type(max_stamp, ty);
                            }
                        }
                        RowFieldDesc::Rinherit(ty) => visit_typed_core_type(max_stamp, ty),
                    }
                }
            }
            TypedCoreTypeDesc::Ttyp_package(pkg) => {
                visit_path(max_stamp, &pkg.pack_path);
                for (_, ty) in &pkg.pack_fields {
                    visit_typed_core_type(max_stamp, ty);
                }
            }
        }
    }

    fn visit_pattern(max_stamp: &mut i32, pattern: &Pattern) {
        match &pattern.pat_desc {
            PatternDesc::Tpat_any | PatternDesc::Tpat_constant(_) => {}
            PatternDesc::Tpat_var(id, _) => visit_ident(max_stamp, id),
            PatternDesc::Tpat_alias(inner, id, _) => {
                visit_pattern(max_stamp, inner);
                visit_ident(max_stamp, id);
            }
            PatternDesc::Tpat_tuple(items)
            | PatternDesc::Tpat_construct(_, _, items)
            | PatternDesc::Tpat_array(items) => {
                for item in items {
                    visit_pattern(max_stamp, item);
                }
            }
            PatternDesc::Tpat_variant(_, inner, _) => {
                if let Some(inner) = inner {
                    visit_pattern(max_stamp, inner);
                }
            }
            PatternDesc::Tpat_record(fields, _, _) => {
                for (_, _, pattern, _) in fields {
                    visit_pattern(max_stamp, pattern);
                }
            }
            PatternDesc::Tpat_or(left, right, _) => {
                visit_pattern(max_stamp, left);
                visit_pattern(max_stamp, right);
            }
        }

        for (extra, _, _) in &pattern.pat_extra {
            match extra {
                PatExtra::Tpat_constraint(core_type) => {
                    visit_typed_core_type(max_stamp, core_type);
                }
                PatExtra::Tpat_type(path, _) => {
                    visit_path(max_stamp, path);
                }
                PatExtra::Tpat_unpack => {}
            }
        }
    }

    fn visit_case(max_stamp: &mut i32, case: &Case) {
        visit_pattern(max_stamp, &case.c_lhs);
        if let Some(guard) = &case.c_guard {
            visit_expression(max_stamp, guard);
        }
        visit_expression(max_stamp, &case.c_rhs);
    }

    fn visit_function_param(max_stamp: &mut i32, param: &FunctionParam) {
        visit_ident(max_stamp, &param.fp_param);
        visit_pattern(max_stamp, &param.fp_pat);
    }

    fn visit_expression(max_stamp: &mut i32, expr: &Expression) {
        match &expr.exp_desc {
            ExpressionDesc::Texp_ident(path, _, _) => visit_path(max_stamp, path),
            ExpressionDesc::Texp_constant(_)
            | ExpressionDesc::Texp_break
            | ExpressionDesc::Texp_continue => {}
            ExpressionDesc::Texp_let(_, bindings, body) => {
                for binding in bindings {
                    visit_value_binding(max_stamp, binding);
                }
                visit_expression(max_stamp, body);
            }
            ExpressionDesc::Texp_function { params, body, .. } => {
                for param in params {
                    visit_function_param(max_stamp, param);
                }
                visit_expression(max_stamp, body);
            }
            ExpressionDesc::Texp_apply { funct, args, .. } => {
                visit_expression(max_stamp, funct);
                for arg in args {
                    if let Some(expr) = &arg.expression {
                        visit_expression(max_stamp, expr);
                    }
                }
            }
            ExpressionDesc::Texp_match(scrutinee, cases, exn_cases, _) => {
                visit_expression(max_stamp, scrutinee);
                for case in cases {
                    visit_case(max_stamp, case);
                }
                for case in exn_cases {
                    visit_case(max_stamp, case);
                }
            }
            ExpressionDesc::Texp_try(body, cases) => {
                visit_expression(max_stamp, body);
                for case in cases {
                    visit_case(max_stamp, case);
                }
            }
            ExpressionDesc::Texp_tuple(items)
            | ExpressionDesc::Texp_construct(_, _, items)
            | ExpressionDesc::Texp_array(items) => {
                for item in items {
                    visit_expression(max_stamp, item);
                }
            }
            ExpressionDesc::Texp_variant(_, arg) => {
                if let Some(arg) = arg {
                    visit_expression(max_stamp, arg);
                }
            }
            ExpressionDesc::Texp_record {
                fields,
                extended_expression,
                ..
            } => {
                for (_, _, field, _) in fields {
                    match field {
                        crate::types::typedtree::RecordLabelDefinition::Kept(_) => {}
                        crate::types::typedtree::RecordLabelDefinition::Overridden(_, expr) => {
                            visit_expression(max_stamp, expr);
                        }
                        crate::types::typedtree::RecordLabelDefinition::OmittedOptionalNone(
                            _,
                            _,
                        ) => {}
                    }
                }
                if let Some(base) = extended_expression {
                    visit_expression(max_stamp, base);
                }
            }
            ExpressionDesc::Texp_record_sparse {
                fields,
                extended_expression,
                ..
            } => {
                // Intentional Rust performance representation: omitted
                // optional fields are synthetic, so traversal only visits
                // explicit overridden expressions and the optional base.
                for (_, _, field, _) in fields {
                    if let crate::types::typedtree::RecordLabelDefinition::Overridden(_, expr) =
                        field
                    {
                        visit_expression(max_stamp, expr);
                    }
                }
                if let Some(base) = extended_expression {
                    visit_expression(max_stamp, base);
                }
            }
            ExpressionDesc::Texp_field(expr, _, _) | ExpressionDesc::Texp_assert(expr) => {
                visit_expression(max_stamp, expr);
            }
            ExpressionDesc::Texp_setfield(lhs, _, _, rhs)
            | ExpressionDesc::Texp_sequence(lhs, rhs) => {
                visit_expression(max_stamp, lhs);
                visit_expression(max_stamp, rhs);
            }
            ExpressionDesc::Texp_ifthenelse(cond, then_, else_) => {
                visit_expression(max_stamp, cond);
                visit_expression(max_stamp, then_);
                if let Some(else_) = else_ {
                    visit_expression(max_stamp, else_);
                }
            }
            ExpressionDesc::Texp_while(cond, body) => {
                visit_expression(max_stamp, cond);
                visit_expression(max_stamp, body);
            }
            ExpressionDesc::Texp_for(id, pattern, lo, hi, _, body) => {
                visit_ident(max_stamp, id);
                visit_pattern(max_stamp, pattern);
                visit_expression(max_stamp, lo);
                visit_expression(max_stamp, hi);
                visit_expression(max_stamp, body);
            }
            ExpressionDesc::Texp_for_of(id, _pat, iterable, body)
            | ExpressionDesc::Texp_for_await_of(id, _pat, iterable, body) => {
                visit_ident(max_stamp, id);
                visit_expression(max_stamp, iterable);
                visit_expression(max_stamp, body);
            }
            ExpressionDesc::Texp_tagged_template { tag, values, .. } => {
                visit_expression(max_stamp, tag);
                for value in values {
                    visit_expression(max_stamp, value);
                }
            }
            ExpressionDesc::Texp_template { values, .. } => {
                for value in values {
                    visit_expression(max_stamp, value);
                }
            }
            ExpressionDesc::Texp_object_get(expr, _) => visit_expression(max_stamp, expr),
            ExpressionDesc::Texp_object_set(expr, _, value) => {
                visit_expression(max_stamp, expr);
                visit_expression(max_stamp, value);
            }
            ExpressionDesc::Texp_object_literal(fields) => {
                for (_, field) in fields {
                    visit_expression(max_stamp, field);
                }
            }
            ExpressionDesc::Texp_letmodule(id, _, module_expr, body) => {
                visit_ident(max_stamp, id);
                visit_module_expr(max_stamp, module_expr);
                visit_expression(max_stamp, body);
            }
            ExpressionDesc::Texp_letexception(ext, body) => {
                visit_extension_constructor(max_stamp, ext);
                visit_expression(max_stamp, body);
            }
            ExpressionDesc::Texp_pack(module_expr) => visit_module_expr(max_stamp, module_expr),
            ExpressionDesc::Texp_extension_constructor(_, path) => visit_path(max_stamp, path),
        }

        for (extra, _, _) in &expr.exp_extra {
            match extra {
                ExpExtra::Texp_constraint(core_type)
                | ExpExtra::Texp_coerce {
                    target: core_type, ..
                } => {
                    visit_typed_core_type(max_stamp, core_type);
                }
                ExpExtra::Texp_open(_, path, _, _) => visit_path(max_stamp, path),
                ExpExtra::Texp_newtype(_) => {}
            }
        }
    }

    fn visit_extension_constructor(max_stamp: &mut i32, ext: &ExtensionConstructor) {
        visit_ident(max_stamp, &ext.ext_id);
        match &ext.ext_kind {
            ExtensionConstructorKind::Text_decl(args, result) => {
                match args {
                    ConstructorArgument::Cstr_tuple(types) => {
                        for ty in types {
                            visit_typed_core_type(max_stamp, ty);
                        }
                    }
                    ConstructorArgument::Cstr_record(labels) => {
                        for label in labels {
                            visit_ident(max_stamp, &label.ld_id);
                            visit_typed_core_type(max_stamp, &label.ld_type);
                        }
                    }
                }
                if let Some(result) = result {
                    visit_typed_core_type(max_stamp, result);
                }
            }
            ExtensionConstructorKind::Text_rebind(path, _) => visit_path(max_stamp, path),
        }
    }

    fn visit_typed_type_decl(max_stamp: &mut i32, decl: &TypedTypeDeclaration) {
        visit_ident(max_stamp, &decl.typ_id);
        for (param, _) in &decl.typ_params {
            visit_typed_core_type(max_stamp, param);
        }
        for (lhs, rhs, _) in &decl.typ_cstrs {
            visit_typed_core_type(max_stamp, lhs);
            visit_typed_core_type(max_stamp, rhs);
        }
        if let Some(manifest) = &decl.typ_manifest {
            visit_typed_core_type(max_stamp, manifest);
        }
        match &decl.typ_kind {
            TypedTypeKind::Ttype_abstract | TypedTypeKind::Ttype_open => {}
            TypedTypeKind::Ttype_variant(constructors) => {
                for constructor in constructors {
                    visit_ident(max_stamp, &constructor.cd_id);
                    match &constructor.cd_args {
                        TypedConstructorArguments::Cstr_tuple(types) => {
                            for ty in types {
                                visit_typed_core_type(max_stamp, ty);
                            }
                        }
                        TypedConstructorArguments::Cstr_record(labels) => {
                            for label in labels {
                                visit_ident(max_stamp, &label.ld_id);
                                visit_typed_core_type(max_stamp, &label.ld_type);
                            }
                        }
                    }
                    if let Some(result) = &constructor.cd_res {
                        visit_typed_core_type(max_stamp, result);
                    }
                }
            }
            TypedTypeKind::Ttype_record(labels) => {
                for label in labels {
                    visit_ident(max_stamp, &label.ld_id);
                    visit_typed_core_type(max_stamp, &label.ld_type);
                }
            }
        }
    }

    fn visit_open_decl(max_stamp: &mut i32, open_decl: &OpenDeclaration) {
        visit_path(max_stamp, &open_decl.open_path);
    }

    fn visit_typed_value_desc(max_stamp: &mut i32, value_desc: &TypedValueDescription) {
        visit_ident(max_stamp, &value_desc.val_id);
        visit_typed_core_type(max_stamp, &value_desc.val_desc);
    }

    fn visit_module_type_constraint(max_stamp: &mut i32, constraint_: &ModuleTypeConstraint) {
        match constraint_ {
            ModuleTypeConstraint::Tmodtype_explicit(module_type) => {
                visit_module_type(max_stamp, module_type);
            }
            ModuleTypeConstraint::Tmodtype_implicit => {}
        }
    }

    fn visit_module_coercion(max_stamp: &mut i32, coercion: &ModuleCoercion) {
        match coercion {
            ModuleCoercion::Tcoerce_none => {}
            ModuleCoercion::Tcoerce_structure(pos_cc_list, id_pos_list, _) => {
                for (_, coercion) in pos_cc_list {
                    visit_module_coercion(max_stamp, coercion);
                }
                for (id, _, coercion) in id_pos_list {
                    visit_ident(max_stamp, id);
                    visit_module_coercion(max_stamp, coercion);
                }
            }
            ModuleCoercion::Tcoerce_functor(arg, result) => {
                visit_module_coercion(max_stamp, arg);
                visit_module_coercion(max_stamp, result);
            }
            ModuleCoercion::Tcoerce_primitive(primitive) => {
                visit_ident(max_stamp, &primitive.pc_id);
            }
            ModuleCoercion::Tcoerce_alias(_, path, coercion) => {
                visit_path(max_stamp, path);
                visit_module_coercion(max_stamp, coercion);
            }
        }
    }

    fn visit_module_type(max_stamp: &mut i32, module_type: &ModuleType) {
        match &module_type.mty_desc {
            ModuleTypeDesc::Tmty_ident(path, _) | ModuleTypeDesc::Tmty_alias(path, _) => {
                visit_path(max_stamp, path);
            }
            ModuleTypeDesc::Tmty_signature(signature) => {
                visit_typed_signature(max_stamp, signature);
            }
            ModuleTypeDesc::Tmty_functor(param, _, param_type, result) => {
                visit_ident(max_stamp, param);
                if let Some(param_type) = param_type {
                    visit_module_type(max_stamp, param_type);
                }
                visit_module_type(max_stamp, result);
            }
            ModuleTypeDesc::Tmty_with(module_type, constraints) => {
                visit_module_type(max_stamp, module_type);
                for (path, _, constraint_) in constraints {
                    visit_path(max_stamp, path);
                    match constraint_ {
                        WithConstraint::Twith_type(type_decl)
                        | WithConstraint::Twith_typesubst(type_decl) => {
                            visit_typed_type_decl(max_stamp, type_decl);
                        }
                        WithConstraint::Twith_module(path, _)
                        | WithConstraint::Twith_modsubst(path, _) => {
                            visit_path(max_stamp, path);
                        }
                    }
                }
            }
            ModuleTypeDesc::Tmty_typeof(module_expr) => visit_module_expr(max_stamp, module_expr),
            ModuleTypeDesc::Tmty_placeholder => {}
        }
    }

    fn visit_typed_module_decl(
        max_stamp: &mut i32,
        module_decl: &crate::types::typedtree::TypedModuleDeclaration,
    ) {
        visit_ident(max_stamp, &module_decl.md_id);
        visit_module_type(max_stamp, &module_decl.md_type);
    }

    fn visit_module_binding(max_stamp: &mut i32, binding: &ModuleBinding) {
        visit_ident(max_stamp, &binding.mb_id);
        visit_module_expr(max_stamp, &binding.mb_expr);
    }

    fn visit_include_description(max_stamp: &mut i32, include_desc: &IncludeDescription) {
        visit_module_type(max_stamp, &include_desc.incl_mod);
        visit_decl_signature(max_stamp, &include_desc.incl_type);
    }

    fn visit_module_type_decl(max_stamp: &mut i32, module_type_decl: &ModuleTypeDeclaration) {
        visit_ident(max_stamp, &module_type_decl.mtd_id);
        if let Some(module_type) = &module_type_decl.mtd_type {
            visit_module_type(max_stamp, module_type);
        }
    }

    fn visit_typed_signature(max_stamp: &mut i32, signature: &TypedSignature) {
        for item in &signature.sig_items {
            match &item.sig_desc {
                TypedSignatureItemDesc::Tsig_value(value_desc) => {
                    visit_typed_value_desc(max_stamp, value_desc);
                }
                TypedSignatureItemDesc::Tsig_type(_, decls) => {
                    for decl in decls {
                        visit_typed_type_decl(max_stamp, decl);
                    }
                }
                TypedSignatureItemDesc::Tsig_typext(type_ext) => {
                    visit_path(max_stamp, &type_ext.tyext_path);
                    for (param, _) in &type_ext.tyext_params {
                        visit_typed_core_type(max_stamp, param);
                    }
                    for ext in &type_ext.tyext_constructors {
                        visit_extension_constructor(max_stamp, ext);
                    }
                }
                TypedSignatureItemDesc::Tsig_exception(ext) => {
                    visit_extension_constructor(max_stamp, ext);
                }
                TypedSignatureItemDesc::Tsig_module(module_decl) => {
                    visit_typed_module_decl(max_stamp, module_decl);
                }
                TypedSignatureItemDesc::Tsig_recmodule(module_decls) => {
                    for module_decl in module_decls {
                        visit_typed_module_decl(max_stamp, module_decl);
                    }
                }
                TypedSignatureItemDesc::Tsig_modtype(module_type_decl) => {
                    visit_module_type_decl(max_stamp, module_type_decl);
                }
                TypedSignatureItemDesc::Tsig_open(open_decl) => {
                    visit_open_decl(max_stamp, open_decl)
                }
                TypedSignatureItemDesc::Tsig_include(include_desc) => {
                    visit_include_description(max_stamp, include_desc);
                }
                TypedSignatureItemDesc::Tsig_attribute(_) => {}
            }
        }
    }

    fn visit_module_expr(max_stamp: &mut i32, module_expr: &ModuleExpr) {
        visit_decl_module_type(max_stamp, &module_expr.mod_type);
        match &module_expr.mod_desc {
            ModuleExprDesc::Tmod_ident(path, _) => visit_path(max_stamp, path),
            ModuleExprDesc::Tmod_structure(structure) => visit_structure(max_stamp, structure),
            ModuleExprDesc::Tmod_apply(functor, arg, coercion) => {
                visit_module_expr(max_stamp, functor);
                visit_module_expr(max_stamp, arg);
                visit_module_coercion(max_stamp, coercion);
            }
            ModuleExprDesc::Tmod_functor(param, _, param_type, body) => {
                visit_ident(max_stamp, param);
                if let Some(param_type) = param_type {
                    visit_module_type(max_stamp, param_type);
                }
                visit_module_expr(max_stamp, body);
            }
            ModuleExprDesc::Tmod_constraint(module_expr, module_type, constraint_, coercion) => {
                visit_module_expr(max_stamp, module_expr);
                visit_decl_module_type(max_stamp, module_type);
                visit_module_type_constraint(max_stamp, constraint_);
                visit_module_coercion(max_stamp, coercion);
            }
            ModuleExprDesc::Tmod_unpack(expr, module_type) => {
                visit_expression(max_stamp, expr);
                visit_decl_module_type(max_stamp, module_type);
            }
        }
    }

    fn visit_value_binding(max_stamp: &mut i32, binding: &ValueBinding) {
        visit_pattern(max_stamp, &binding.vb_pat);
        visit_expression(max_stamp, &binding.vb_expr);
    }

    fn visit_decl_module_type(max_stamp: &mut i32, module_type: &DeclModuleType) {
        match module_type {
            DeclModuleType::MtyIdent(path) | DeclModuleType::MtyAlias(_, path) => {
                visit_path(max_stamp, path);
            }
            DeclModuleType::MtySignature(signature) => visit_decl_signature(max_stamp, signature),
            DeclModuleType::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                visit_ident(max_stamp, param);
                if let Some(param_type) = param_type {
                    visit_decl_module_type(max_stamp, param_type);
                }
                visit_decl_module_type(max_stamp, result);
            }
        }
    }

    fn visit_decl_type_decl(max_stamp: &mut i32, type_decl: &crate::types::decl::TypeDeclaration) {
        if let Some(path) = &type_decl.type_path {
            visit_path(max_stamp, path);
        }
        match &type_decl.type_kind {
            DeclTypeKind::TypeAbstract | DeclTypeKind::TypeOpen => {}
            DeclTypeKind::TypeRecord(labels, _) => {
                for label in labels {
                    visit_ident(max_stamp, &label.ld_id);
                }
            }
            DeclTypeKind::TypeVariant(constructors, _) => {
                for constructor in constructors {
                    visit_ident(max_stamp, &constructor.cd_id);
                    if let DeclConstructorArguments::CstrRecord(labels) = &constructor.cd_args {
                        for label in labels {
                            visit_ident(max_stamp, &label.ld_id);
                        }
                    }
                }
            }
        }
    }

    fn visit_decl_extension_constructor(
        max_stamp: &mut i32,
        ext: &crate::types::decl::ExtensionConstructor,
    ) {
        visit_path(max_stamp, &ext.ext_type_path);
        if let DeclConstructorArguments::CstrRecord(labels) = &ext.ext_args {
            for label in labels {
                visit_ident(max_stamp, &label.ld_id);
            }
        }
    }

    fn visit_decl_signature(max_stamp: &mut i32, signature: &[DeclSignatureItem]) {
        for item in signature {
            match item {
                DeclSignatureItem::SigValue(id, value_desc) => {
                    visit_ident(max_stamp, id);
                    if let Some(path) = &value_desc.val_path {
                        visit_path(max_stamp, path);
                    }
                }
                DeclSignatureItem::SigType(id, type_decl, _) => {
                    visit_ident(max_stamp, id);
                    visit_decl_type_decl(max_stamp, type_decl);
                }
                DeclSignatureItem::SigTypext(id, ext, _) => {
                    visit_ident(max_stamp, id);
                    visit_decl_extension_constructor(max_stamp, ext);
                }
                DeclSignatureItem::SigModule(id, module_decl, _) => {
                    visit_ident(max_stamp, id);
                    if let Some(path) = &module_decl.md_path {
                        visit_path(max_stamp, path);
                    }
                    visit_decl_module_type(max_stamp, &module_decl.md_type);
                }
                DeclSignatureItem::SigModtype(id, module_type_decl) => {
                    visit_ident(max_stamp, id);
                    if let Some(module_type) = &module_type_decl.mtd_type {
                        visit_decl_module_type(max_stamp, module_type);
                    }
                }
                DeclSignatureItem::SigClass | DeclSignatureItem::SigClassType => {}
            }
        }
    }

    fn visit_structure(max_stamp: &mut i32, structure: &Structure) {
        for item in &structure.str_items {
            match &item.str_desc {
                StructureItemDesc::Tstr_eval(expr, _) => visit_expression(max_stamp, expr),
                StructureItemDesc::Tstr_value(_, bindings) => {
                    for binding in bindings {
                        visit_value_binding(max_stamp, binding);
                    }
                }
                StructureItemDesc::Tstr_primitive(value_desc) => {
                    visit_typed_value_desc(max_stamp, value_desc);
                }
                StructureItemDesc::Tstr_type(_, decls) => {
                    for decl in decls {
                        visit_typed_type_decl(max_stamp, decl);
                    }
                }
                StructureItemDesc::Tstr_typext(type_ext) => {
                    visit_path(max_stamp, &type_ext.tyext_path);
                    for (param, _) in &type_ext.tyext_params {
                        visit_typed_core_type(max_stamp, param);
                    }
                    for ext in &type_ext.tyext_constructors {
                        visit_extension_constructor(max_stamp, ext);
                    }
                }
                StructureItemDesc::Tstr_exception(ext) => {
                    visit_extension_constructor(max_stamp, ext)
                }
                StructureItemDesc::Tstr_module(binding) => visit_module_binding(max_stamp, binding),
                StructureItemDesc::Tstr_recmodule(bindings) => {
                    for binding in bindings {
                        visit_module_binding(max_stamp, binding);
                    }
                }
                StructureItemDesc::Tstr_modtype(module_type_decl) => {
                    visit_module_type_decl(max_stamp, module_type_decl);
                }
                StructureItemDesc::Tstr_open(open_decl) => visit_open_decl(max_stamp, open_decl),
                StructureItemDesc::Tstr_include(include_decl) => {
                    visit_module_expr(max_stamp, &include_decl.incl_mod);
                    visit_decl_signature(max_stamp, &include_decl.incl_type);
                }
                StructureItemDesc::Tstr_attribute(_) => {}
            }
        }

        visit_decl_signature(max_stamp, &structure.str_type);
    }

    let mut max_stamp = 0;
    visit_structure(&mut max_stamp, typed_structure);
    max_stamp
}

fn expression_has_string_literal(
    expr: &Expression,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    use crate::parser::ast::ExpressionDesc as ED;

    match &*expr.pexp_desc {
        ED::Pexp_constant(c) => matches!(&**c, Constant::String(s) if s.semantic() == value),
        ED::Pexp_template(template) => template
            .values
            .iter()
            .any(|e| expression_has_string_literal(arena.get_expr(*e), value, arena)),
        ED::Pexp_tagged_template(template) => {
            expression_has_string_literal(arena.get_expr(template.tag), value, arena)
                || template
                    .values
                    .iter()
                    .any(|e| expression_has_string_literal(arena.get_expr(*e), value, arena))
        }
        ED::Pexp_let(inner) => {
            let (_, bindings, body) = &**inner;
            bindings
                .iter()
                .any(|vb| expression_has_string_literal(arena.get_expr(vb.pvb_expr), value, arena))
                || expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_fun(inner) => {
            let crate::parser::ast::PexpFun { default, rhs, .. } = &**inner;
            default
                .as_ref()
                .is_some_and(|e| expression_has_string_literal(arena.get_expr(*e), value, arena))
                || expression_has_string_literal(arena.get_expr(*rhs), value, arena)
        }
        ED::Pexp_apply(inner) => {
            let crate::parser::ast::PexpApply { funct, args, .. } = &**inner;
            expression_has_string_literal(arena.get_expr(*funct), value, arena)
                || args.iter().any(|(_, arg)| {
                    expression_has_string_literal(arena.get_expr(*arg), value, arena)
                })
        }
        ED::Pexp_match(inner) | ED::Pexp_try(inner) => {
            let (scrutinee, cases) = &**inner;
            expression_has_string_literal(arena.get_expr(*scrutinee), value, arena)
                || cases.iter().any(|case| {
                    case.pc_guard.as_ref().is_some_and(|g| {
                        expression_has_string_literal(arena.get_expr(*g), value, arena)
                    }) || expression_has_string_literal(arena.get_expr(case.pc_rhs), value, arena)
                })
        }
        ED::Pexp_tuple(items) | ED::Pexp_array(items) => items
            .iter()
            .any(|item| expression_has_string_literal(arena.get_expr(*item), value, arena)),
        ED::Pexp_construct(_, args) => args
            .txt
            .iter()
            .any(|arg| expression_has_string_literal(arena.get_expr(*arg), value, arena)),
        ED::Pexp_variant(inner) => {
            let (_, args) = &**inner;
            args.txt
                .iter()
                .any(|arg| expression_has_string_literal(arena.get_expr(*arg), value, arena))
        }
        ED::Pexp_record(inner) => {
            let (fields, base) = &**inner;
            fields.iter().any(|field| {
                expression_has_string_literal(arena.get_expr(field.expr), value, arena)
            }) || base.as_ref().is_some_and(|base| {
                expression_has_string_literal(arena.get_expr(*base), value, arena)
            })
        }
        ED::Pexp_field(expr, _) | ED::Pexp_assert(expr) | ED::Pexp_await(expr) => {
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        ED::Pexp_newtype(inner) => {
            let (_, expr) = &**inner;
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        ED::Pexp_constraint(inner) => {
            let (expr, _) = &**inner;
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        ED::Pexp_coerce(inner) => {
            let (expr, _, _) = &**inner;
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        ED::Pexp_object_get(inner) => {
            let (expr, _) = &**inner;
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        ED::Pexp_object_set(inner) => {
            let (lhs, _, rhs) = &**inner;
            expression_has_string_literal(arena.get_expr(*lhs), value, arena)
                || expression_has_string_literal(arena.get_expr(*rhs), value, arena)
        }
        ED::Pexp_object_literal(fields) => fields
            .iter()
            .any(|(_, e)| expression_has_string_literal(arena.get_expr(*e), value, arena)),
        ED::Pexp_setfield(inner) => {
            let (lhs, _, rhs) = &**inner;
            expression_has_string_literal(arena.get_expr(*lhs), value, arena)
                || expression_has_string_literal(arena.get_expr(*rhs), value, arena)
        }
        ED::Pexp_sequence(lhs, rhs) | ED::Pexp_while(lhs, rhs) => {
            expression_has_string_literal(arena.get_expr(*lhs), value, arena)
                || expression_has_string_literal(arena.get_expr(*rhs), value, arena)
        }
        ED::Pexp_braces(braces) => {
            expression_has_string_literal(arena.get_expr(braces.expr), value, arena)
        }
        ED::Pexp_regexp(_) => false,
        ED::Pexp_ternary(inner) => {
            let (cond, consequent, alternate) = **inner;
            expression_has_string_literal(arena.get_expr(cond), value, arena)
                || expression_has_string_literal(arena.get_expr(consequent), value, arena)
                || expression_has_string_literal(arena.get_expr(alternate), value, arena)
        }
        ED::Pexp_ifthenelse(inner) => {
            let (cond, then_expr, else_expr) = &**inner;
            expression_has_string_literal(arena.get_expr(*cond), value, arena)
                || expression_has_string_literal(arena.get_expr(*then_expr), value, arena)
                || else_expr.as_ref().is_some_and(|else_expr| {
                    expression_has_string_literal(arena.get_expr(*else_expr), value, arena)
                })
        }
        ED::Pexp_for(inner) => {
            let (_, start, end, _, body) = &**inner;
            expression_has_string_literal(arena.get_expr(*start), value, arena)
                || expression_has_string_literal(arena.get_expr(*end), value, arena)
                || expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_for_of(inner) | ED::Pexp_for_await_of(inner) => {
            let (_, iterable, body) = &**inner;
            expression_has_string_literal(arena.get_expr(*iterable), value, arena)
                || expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_letmodule(inner) => {
            let (_, module_expr, body) = &**inner;
            module_expr_has_config_string(arena.get_mod_expr(*module_expr), value, arena)
                || expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_pack(module_expr) => {
            module_expr_has_config_string(arena.get_mod_expr(*module_expr), value, arena)
        }
        ED::Pexp_letexception(inner) => {
            let (_, body) = &**inner;
            expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_open(inner) => {
            let (_, _, body) = &**inner;
            expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_extension(inner) => {
            let (_, payload) = &**inner;
            payload_has_string_literal(payload, value, arena)
        }
        ED::Pexp_ident(_) | ED::Pexp_break | ED::Pexp_continue | ED::Pexp_jsx_element(_) => false,
    }
}

fn payload_has_string_literal(
    payload: &Payload,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    match payload {
        Payload::PStr(items) => items.iter().any(|item| match &*item.pstr_desc {
            StructureItemDesc::Pstr_eval(inner) => {
                let (expr, _) = &**inner;
                expression_has_string_literal(arena.get_expr(*expr), value, arena)
            }
            StructureItemDesc::Pstr_attribute(attr) => {
                payload_has_string_literal(&attr.1, value, arena)
            }
            _ => false,
        }),
        Payload::PPat(inner) => {
            let (pat, guard) = &**inner;
            pattern_has_string_literal(arena.get_pat(*pat), value, arena)
                || guard.as_ref().is_some_and(|guard| {
                    expression_has_string_literal(arena.get_expr(*guard), value, arena)
                })
        }
        Payload::PTyp(_) | Payload::PSig(_) => false,
    }
}

fn pattern_has_string_literal(
    pat: &crate::parser::ast::Pattern,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    use crate::parser::ast::PatternDesc as PD;

    match &*pat.ppat_desc {
        PD::Ppat_constant(c) => matches!(&**c, Constant::String(s) if s.semantic() == value),
        PD::Ppat_alias(inner, _) | PD::Ppat_exception(inner) => {
            pattern_has_string_literal(arena.get_pat(*inner), value, arena)
        }
        PD::Ppat_constraint(inner) => {
            let (inner_pat, _) = &**inner;
            pattern_has_string_literal(arena.get_pat(*inner_pat), value, arena)
        }
        PD::Ppat_tuple(items) | PD::Ppat_array(items) => items
            .iter()
            .any(|item| pattern_has_string_literal(arena.get_pat(*item), value, arena)),
        PD::Ppat_construct(_, args) => args
            .txt
            .iter()
            .any(|arg| pattern_has_string_literal(arena.get_pat(*arg), value, arena)),
        PD::Ppat_variant(inner) => {
            let (_, args) = &**inner;
            args.txt
                .iter()
                .any(|arg| pattern_has_string_literal(arena.get_pat(*arg), value, arena))
        }
        PD::Ppat_or(lhs, rhs) => {
            pattern_has_string_literal(arena.get_pat(*lhs), value, arena)
                || pattern_has_string_literal(arena.get_pat(*rhs), value, arena)
        }
        PD::Ppat_record(inner) => {
            let (rows, _, _) = &**inner;
            rows.iter()
                .any(|row| pattern_has_string_literal(arena.get_pat(row.pat), value, arena))
        }
        PD::Ppat_extension(inner) => {
            let (_, payload) = &**inner;
            payload_has_string_literal(payload, value, arena)
        }
        _ => false,
    }
}

fn module_expr_has_config_string(
    module_expr: &ModuleExpr,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    match &*module_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(structure) => {
            structure_has_config_string(structure, value, arena)
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_, param, body) = &**inner;
            param.as_ref().is_some_and(|param| {
                module_type_has_config_string(arena.get_mod_type(*param), value, arena)
            }) || module_expr_has_config_string(arena.get_mod_expr(*body), value, arena)
        }
        ModuleExprDesc::Pmod_apply(lhs, rhs) => {
            module_expr_has_config_string(arena.get_mod_expr(*lhs), value, arena)
                || module_expr_has_config_string(arena.get_mod_expr(*rhs), value, arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, module_type) => {
            module_expr_has_config_string(arena.get_mod_expr(*inner), value, arena)
                || module_type_has_config_string(arena.get_mod_type(*module_type), value, arena)
        }
        ModuleExprDesc::Pmod_unpack(expr) => {
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        _ => false,
    }
}

fn module_type_has_config_string(
    module_type: &crate::parser::ast::ModuleType,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    use crate::parser::ast::ModuleTypeDesc as MTD;

    match &*module_type.pmty_desc {
        MTD::Pmty_signature(sig_items) => sig_items.iter().any(|item| match &*item.psig_desc {
            crate::parser::ast::SignatureItemDesc::Psig_attribute(attr) => {
                payload_has_string_literal(&attr.1, value, arena)
            }
            _ => false,
        }),
        MTD::Pmty_functor(inner) => {
            let (_, param, body) = &**inner;
            param.as_ref().is_some_and(|param| {
                module_type_has_config_string(arena.get_mod_type(*param), value, arena)
            }) || module_type_has_config_string(arena.get_mod_type(*body), value, arena)
        }
        MTD::Pmty_with(inner) => {
            let (inner_mty, _) = &**inner;
            module_type_has_config_string(arena.get_mod_type(*inner_mty), value, arena)
        }
        MTD::Pmty_typeof(module_expr) => {
            module_expr_has_config_string(arena.get_mod_expr(*module_expr), value, arena)
        }
        _ => false,
    }
}

fn structure_has_config_string(
    structure: &Structure,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    structure.iter().any(|item| match &*item.pstr_desc {
        StructureItemDesc::Pstr_attribute(attr) => {
            payload_has_string_literal(&attr.1, value, arena)
        }
        StructureItemDesc::Pstr_module(mb) => {
            module_expr_has_config_string(arena.get_mod_expr(mb.pmb_expr), value, arena)
        }
        StructureItemDesc::Pstr_recmodule(mbs) => mbs
            .iter()
            .any(|mb| module_expr_has_config_string(arena.get_mod_expr(mb.pmb_expr), value, arena)),
        StructureItemDesc::Pstr_include(incl) => {
            module_expr_has_config_string(arena.get_mod_expr(incl.pincl_mod), value, arena)
        }
        _ => false,
    })
}

/// A concrete JavaScript output target for one compile.
#[derive(Clone)]
pub struct JsOutputTarget {
    pub path: PathBuf,
    pub module_format: ModuleFormat,
}

/// Rendered JavaScript for one concrete output path.
pub struct JsOutput {
    pub path: PathBuf,
    pub code: String,
    /// External source map contents for linked/hidden modes.
    pub source_map: Option<String>,
}

/// An intermediate representation an in-process compile can capture, printed
/// as the matching `bsc` flag prints it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DumpKind {
    /// `-dtyped-sexp`
    TypedTree,
    /// `-dtyped-sexp-locs`
    TypedTreeLocs,
    /// `-drawlambda`
    RawLambda,
    /// `-dlambda-sexp`
    Lambda,
    /// `-dlambda-sexp-locs`
    LambdaLocs,
}

impl DumpKind {
    pub const ALL: [DumpKind; 5] = [
        DumpKind::TypedTree,
        DumpKind::TypedTreeLocs,
        DumpKind::RawLambda,
        DumpKind::Lambda,
        DumpKind::LambdaLocs,
    ];

    /// The name used on the command line and as the dump file extension.
    pub fn name(self) -> &'static str {
        match self {
            DumpKind::TypedTree => "typedtree",
            DumpKind::TypedTreeLocs => "typedtree-locs",
            DumpKind::RawLambda => "rawlambda",
            DumpKind::Lambda => "lambda",
            DumpKind::LambdaLocs => "lambda-locs",
        }
    }

    pub fn from_name(name: &str) -> Option<DumpKind> {
        DumpKind::ALL.into_iter().find(|kind| kind.name() == name)
    }

    fn is_lambda(self) -> bool {
        matches!(
            self,
            DumpKind::RawLambda | DumpKind::Lambda | DumpKind::LambdaLocs
        )
    }
}

/// The dump's bytes, one `char` per byte. Dump printers write source text
/// byte for byte, so the bytes need not be UTF-8; writers turn each `char`
/// back into its byte.
fn latin1_dump(bytes: Vec<u8>) -> String {
    bytes.into_iter().map(char::from).collect()
}

/// Compiler options that can be passed to the driver.
#[derive(Clone)]
pub struct CompilerOptions {
    /// Print the Lambda IR to stderr (like OCaml's -drawlambda)
    pub dump_lambda: bool,
    /// Print the typed tree as sexp to stderr (like OCaml's -dtyped-sexp)
    pub dump_typed_sexp: bool,
    /// Print the typed tree as sexp with locations to stderr (like OCaml's -dtyped-sexp-locs)
    pub dump_typed_sexp_locs: bool,
    /// Print the Lambda IR as sexp to stderr (like OCaml's -dlambda-sexp)
    pub dump_lambda_sexp: bool,
    /// Print the Lambda IR as sexp with locations to stderr (like OCaml's -dlambda-sexp-locs)
    pub dump_lambda_sexp_locs: bool,
    /// Include paths for finding .cmi files (from -I flags)
    pub include_paths: Vec<PathBuf>,
    /// Runtime package path (from -runtime-path flag)
    /// Used to locate stdlib CMIs at {runtime_path}/lib/ocaml/
    pub runtime_path: Option<PathBuf>,
    /// Additional modules opened implicitly from `-open` flags.
    pub open_modules: Vec<String>,
    /// Record what an in-process compile read of other units
    /// (`unit_reads` of the results), for incremental builds.
    pub collect_unit_reads: bool,
    /// Warning enable/disable specs from `-w` flags.
    pub warning_specs: Vec<String>,
    /// Warning-as-error specs from `-warn-error` flags.
    pub warning_error_specs: Vec<String>,
    /// Source filename for interface constraint propagation.
    /// When set, after type_structure, checks for a matching .cmi and
    /// unifies implementation value types with interface types.
    pub source_filename: Option<String>,
    /// Output path used for module-format and relative-import resolution.
    pub output_path: Option<PathBuf>,
    /// Output module format from the build config. When absent, legacy callers
    /// infer it from `output_path`.
    pub output_module_format: Option<crate::js_ir::ModuleFormat>,
    /// Extra concrete JS outputs for in-process callers that need the same
    /// typed/lambda result rendered for multiple package specs.
    pub js_output_targets: Vec<JsOutputTarget>,
    /// The package's `-bs-package-output` specs, which import paths follow
    /// (see `js_ir::JsPackageSpec`).
    pub js_package_specs: Vec<crate::js_ir::JsPackageSpec>,
    /// Source map output mode.
    pub source_map: crate::js_ir::source_map::SourceMapMode,
    /// Include original source text in generated source maps.
    pub source_map_sources_content: bool,
    /// Optional sourceRoot emitted in generated source maps.
    pub source_map_root: String,
    /// JSX version from CLI `-bs-jsx` (e.g. 4). When set, enables JSX PPX rewrite.
    pub jsx_version: Option<i32>,
    /// JSX module from CLI `-bs-jsx-module` (`Js_config.jsx_module`); `None`
    /// is OCaml's default `React`.
    pub jsx_module: Option<String>,
    /// Experimental LetUnwrap feature from `-enable-experimental LetUnwrap`.
    pub experimental_let_unwrap: bool,
    /// Preserve transformed JSX syntax in the final JS dumper.
    pub jsx_preserve: bool,
    /// Enable debug-mode JS emission (like OCaml's -bs-g / Js_config.debug).
    pub debug: bool,
    /// Suppress the generated version/header comment (`-bs-no-version-header`).
    pub no_version_header: bool,
    /// Mirror `Js_config.check_div_by_zero` for checked integer/bigint lowering.
    pub check_div_by_zero: bool,
    /// Mirror `Js_config.cross_module_inline` / `-bs-cross-module-opt`.
    pub cross_module_inline: bool,
    /// Mirror `Clflags.no_assert_false` / `-bs-noassertfalse`.
    pub no_assert_false: bool,
    /// Mirror `Clflags.noassert` / `-noassert`.
    pub noassert: bool,
    /// Mirror `Clflags.transparent_modules` / `-no-alias-deps`.
    pub transparent_modules: bool,
    /// Mirror `Js_config.no_builtin_ppx` / `-bs-no-builtin-ppx`.
    pub no_builtin_ppx: bool,
    /// Run the builtin Spice mapper in place of a configured spice PPX
    /// (set by the in-process build, which then omits it from `external_ppxs`).
    pub spice_ppx: bool,
    /// External `-ppx` rewriters, in command-line order.
    pub external_ppxs: Vec<String>,
    /// When true, do not implicitly open Pervasives and Stdlib.
    pub nopervasives: bool,
    /// The module name being compiled. Used to filter self-opens.
    pub module_name: Option<String>,
    /// Current npm package name from `-bs-package-name`.
    pub package_name: Option<String>,
    /// Compile the runtime package (`-make-runtime`).
    pub make_runtime: bool,
    /// Mirror `Clflags.assume_no_mli := Mli_exists` from `-bs-read-cmi`.
    pub assume_compiled_interface: bool,
    /// Where the file compile finds the interface's `.cmi`, spelled as its
    /// `-I` entry (`find_in_path_uncap`, typemod.ml:1742-1749), for the
    /// interface-mismatch report: a build's is `../ocaml`, its package's
    /// `lib/ocaml` seen from `lib/bs`. `None`: next to the source, where
    /// `bsc` writes it.
    pub interface_cmi_dir: Option<PathBuf>,
    /// GenType configuration derived from `-bs-gentype-*` flags.
    pub gentype_config: Option<std::sync::Arc<crate::gentype::config::T>>,
    /// Build-scoped GenType module resolver shared by in-process compilations.
    pub gentype_resolver: Option<std::sync::Arc<crate::gentype::module_resolver::Resolver>>,
    /// Run GenType only to register the module's type declarations (for the
    /// modules that import its types), without generating output.
    pub gentype_declarations_only: bool,
    /// When true, `compile_source_in_process` captures the typed tree,
    /// raw lambda, and lambda sexps for display (used by the playground).
    pub capture_intermediates: bool,
    /// Intermediate representations an in-process compile captures into its
    /// result's `dumps`, in this order.
    pub dumps: Vec<DumpKind>,
    /// Build typed/lambda/JS IR metadata but skip rendering JavaScript text.
    /// Used by runtime seeding, which only needs signatures, purity, and
    /// closed constants in memory.
    pub skip_js_render: bool,
    /// Publish a portable in-process signature for downstream module lookup.
    /// Rewatch can disable this for implementations whose interface already
    /// supplies the published signature. OCaml still saves before Lambda translation
    /// (`compiler/ml/typemod.ml:1779-1788`; `compiler/ml/translmod.ml:267`);
    /// this only skips the Rust-only portable registry extraction when no
    /// downstream lookup can observe it.
    pub publish_in_process_signature: bool,
    /// The input is a `.ast`/`.iast` written by `bsc -bs-ast`. OCaml reads the
    /// already-preprocessed tree (compiler/core/js_implementation.ml:189-196),
    /// so frontend warnings were reported by the `-bs-ast` run and are not
    /// repeated. Rust re-runs the frontend from source, silently.
    pub frontend_already_reported: bool,
    /// Package roots whose in-process units are on the load path (the `-I`
    /// directories of a file build). `None` makes every registered unit visible.
    pub visible_package_roots: Option<Vec<PathBuf>>,
    /// `Clflags.keep_locs` (`-keep-locs`/`-no-keep-locs`): whether saved
    /// signatures keep source locations (subst.ml:57-67 `Subst.for_saving`).
    pub keep_locs: bool,
}

/// `Subst.signature (Subst.for_saving ...)` with `Clflags.keep_locs = false`
/// (subst.ml:57-67): saved signatures replace every location, including the
/// attributes', with `Location.none`.
fn strip_saved_signature_locations(sig: &mut [crate::types::decl::SignatureItem]) {
    use crate::types::decl::{Attribute, SignatureLocationVisitor};
    // `Subst.loc` and `Subst.attrs` (compiler/ml/subst.ml:57-67).
    struct Strip;
    impl SignatureLocationVisitor for Strip {
        fn location(&mut self, loc: &mut crate::location::Location) {
            *loc = crate::location::Location::none();
        }
        fn attribute(&mut self, attr: &mut Attribute) {
            self.location(&mut attr.attr_loc);
            self.location(&mut attr.attr_name.loc);
        }
    }
    crate::types::decl::walk_signature_locations(sig, &mut Strip);
}

/// `Subst.extension_constructor` for saving drops `ext_loc` whatever
/// `keep_locs` says (subst.ml:314-322).
fn strip_saved_extension_locations(sig: &mut [crate::types::decl::SignatureItem]) {
    use crate::types::decl::{ModuleType, SignatureItem};
    fn module_type(mty: &mut ModuleType) {
        match mty {
            ModuleType::MtySignature(sig) => {
                strip_saved_extension_locations(&mut std::sync::Arc::make_mut(sig)[..])
            }
            ModuleType::MtyFunctor {
                param_type, result, ..
            } => {
                if let Some(param) = param_type {
                    module_type(param);
                }
                module_type(result);
            }
            ModuleType::MtyIdent(_) | ModuleType::MtyAlias(..) => {}
        }
    }
    for item in sig {
        match item {
            SignatureItem::SigTypext(_, ext, _) => ext.ext_loc = crate::location::Location::none(),
            SignatureItem::SigModule(_, md, _) => module_type(&mut md.md_type),
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(mty) = &mut mtd.mtd_type {
                    module_type(mty);
                }
            }
            _ => {}
        }
    }
}

/// `bsc -format` (rescript_compiler_main.ml:168-182 via
/// res_multi_printer.ml:1-30): parse `.res`/`.resi` source in printer mode and
/// print it back with its comments. Sources are Latin-1 byte strings like the
/// parser's input; the result keeps the original byte encoding. A file with
/// parse errors fails with the diagnostic report (`Res_diagnostics.print_report`).
pub fn format_source(source: &[u8], filename: &str) -> std::result::Result<Vec<u8>, String> {
    let (report, output) = format_source_with(source, filename, false);
    output.ok_or(report)
}

/// `Res_multi_printer.print ~ignore_parse_errors`: the parse diagnostics
/// report (empty without errors) and the formatted source, which is `None`
/// when parse errors are not ignored.
pub fn format_source_with(
    source: &[u8],
    filename: &str,
    ignore_parse_errors: bool,
) -> (String, Option<Vec<u8>>) {
    let source = crate::source_text::latin1_bytes_to_string(source.to_vec());
    let is_interface = filename.ends_with(".resi");
    let mut parser = Parser::new(filename, &source);
    let (report, output) = if is_interface {
        let signature = module::parse_signature(&mut parser);
        let report = parse_diagnostics_report(&parser, &source, filename);
        if parser.has_errors() && !ignore_parse_errors {
            return (report, None);
        }
        let comments = parser.comments().to_vec();
        let output = crate::parser::printer::print_signature_with_comments(
            &signature,
            comments,
            parser.arena_mut(),
        );
        (report, output)
    } else {
        let structure = module::parse_structure(&mut parser);
        let report = parse_diagnostics_report(&parser, &source, filename);
        if parser.has_errors() && !ignore_parse_errors {
            return (report, None);
        }
        let comments = parser.comments().to_vec();
        let output = crate::parser::printer::print_structure_with_comments(
            &structure,
            comments,
            parser.arena_mut(),
        );
        (report, output)
    };
    (report, Some(output.chars().map(|c| c as u8).collect()))
}

fn parse_diagnostics_report(parser: &Parser<'_>, source: &str, filename: &str) -> String {
    let report: String = parser
        .diagnostics()
        .iter()
        .map(|diag| {
            code_frame::format_error(
                filename,
                source,
                &diag.start_pos,
                &diag.end_pos,
                &diag.explain_with_source(Some(source)),
            )
        })
        .collect();
    // Source text is Latin-1 chars standing for bytes; the frame adds real
    // Unicode (box drawing). Write each back as the bytes OCaml prints.
    let mut bytes = Vec::with_capacity(report.len());
    for c in report.chars() {
        if (c as u32) <= 0xFF {
            bytes.push(c as u8);
        } else {
            let mut buf = [0u8; 4];
            bytes.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        }
    }
    String::from_utf8_lossy(&bytes).into_owned()
}

impl Default for CompilerOptions {
    fn default() -> Self {
        Self {
            dump_lambda: false,
            dump_typed_sexp: false,
            dump_typed_sexp_locs: false,
            dump_lambda_sexp: false,
            dump_lambda_sexp_locs: false,
            include_paths: Vec::new(),
            runtime_path: None,
            open_modules: Vec::new(),
            collect_unit_reads: false,
            warning_specs: Vec::new(),
            warning_error_specs: Vec::new(),
            source_filename: None,
            output_path: None,
            output_module_format: None,
            js_output_targets: Vec::new(),
            js_package_specs: Vec::new(),
            source_map: crate::js_ir::source_map::SourceMapMode::None,
            source_map_sources_content: false,
            source_map_root: String::new(),
            jsx_version: None,
            jsx_module: None,
            experimental_let_unwrap: false,
            jsx_preserve: false,
            debug: false,
            no_version_header: false,
            check_div_by_zero: true,
            cross_module_inline: false,
            no_assert_false: false,
            noassert: false,
            transparent_modules: false,
            no_builtin_ppx: false,
            spice_ppx: false,
            external_ppxs: Vec::new(),
            nopervasives: false,
            module_name: None,
            package_name: None,
            make_runtime: false,
            assume_compiled_interface: false,
            interface_cmi_dir: None,
            gentype_config: None,
            gentype_resolver: None,
            gentype_declarations_only: false,
            capture_intermediates: false,
            dumps: Vec::new(),
            skip_js_render: false,
            publish_in_process_signature: true,
            frontend_already_reported: false,
            visible_package_roots: None,
            keep_locs: true,
        }
    }
}

impl CompilerOptions {
    /// `Env.get_unit_name ()`: js_implementation.ml:142-145 sets it to
    /// `Ext_filename.module_name outputprefix` (ext_filename.ml:71-79), the
    /// basename up to its last dot, so `hello.foo.res` is unit `Hello` even
    /// though the build registers it under its full module name.
    fn current_unit_name(&self) -> Option<String> {
        self.module_name
            .as_deref()
            .map(|name| {
                name.rsplit_once('.')
                    .map_or(name, |(unit, _)| unit)
                    .to_string()
            })
            .or_else(|| {
                self.source_filename
                    .as_deref()
                    .map(module_name_from_source_filename)
                    .filter(|name| !name.is_empty())
            })
    }
}

fn apply_warning_options(tctx: &mut TypeCheckContext<'_>, options: &CompilerOptions) {
    for spec in &options.warning_specs {
        tctx.apply_warning_spec(spec);
    }
    for spec in &options.warning_error_specs {
        tctx.apply_warning_error_spec(spec);
    }
}

fn apply_warning_specs_to_config(
    config: &mut WarningConfig,
    warning_specs: &[String],
    warning_error_specs: &[String],
) {
    for spec in warning_specs {
        let _ = config.parse(spec);
    }
    for spec in warning_error_specs {
        let _ = config.parse_as_error(spec);
    }
}

fn apply_file_config_warning_options(
    tctx: &mut TypeCheckContext<'_>,
    config: &FileConfigOverrides,
) {
    for (as_error, spec) in &config.warning_ops {
        if *as_error {
            tctx.apply_warning_error_spec(spec);
        } else {
            tctx.apply_warning_spec(spec);
        }
    }
}

fn apply_leading_warning_attribute_options(
    tctx: &mut TypeCheckContext<'_>,
    specs: &[ppx::WarningAttributeSpec],
) {
    for spec in specs {
        if spec.as_error {
            tctx.apply_warning_error_spec(&spec.spec);
        } else {
            tctx.apply_warning_spec(&spec.spec);
        }
    }
}

fn warning_config_for_options(options: &CompilerOptions) -> WarningConfig {
    let mut config = WarningConfig::new();
    apply_warning_specs_to_config(
        &mut config,
        &options.warning_specs,
        &options.warning_error_specs,
    );
    config
}

/// The warning state when `Ast_config.process_str` first runs: command-line
/// options plus the leading `@@warning` attributes applied by
/// `Bs_ast_invariant.iter_warnings_on_stru` (compiler/frontend/ppx_entry.ml:46-48).
fn warning_config_for_options_and_leading_attrs(
    options: &CompilerOptions,
    leading_specs: &[ppx::WarningAttributeSpec],
) -> WarningConfig {
    let mut config = warning_config_for_options(options);
    for spec in leading_specs {
        if spec.as_error {
            let _ = config.parse_as_error(&spec.spec);
        } else {
            let _ = config.parse(&spec.spec);
        }
    }
    config
}

fn warning_config_for_options_file_config_and_leading_attrs(
    options: &CompilerOptions,
    file_config: &FileConfigOverrides,
    leading_specs: &[ppx::WarningAttributeSpec],
) -> WarningConfig {
    let mut config = warning_config_for_options(options);
    // OCaml compiler/frontend/ppx_entry.ml:28-47 calls
    // Bs_ast_invariant.iter_warnings_on_stru/sigi before builtin PPX
    // rewriting; those leading attributes mutate Warnings.current before
    // @deriving and external warnings are emitted.
    for spec in leading_specs {
        if spec.as_error {
            let _ = config.parse_as_error(&spec.spec);
        } else {
            let _ = config.parse(&spec.spec);
        }
    }
    apply_file_config_warning_ops(&mut config, file_config);
    config
}

fn apply_file_config_warning_ops(config: &mut WarningConfig, file_config: &FileConfigOverrides) {
    for (as_error, spec) in &file_config.warning_ops {
        if *as_error {
            let _ = config.parse_as_error(spec);
        } else {
            let _ = config.parse(spec);
        }
    }
}

fn shell_quote_path(path: &std::path::Path) -> String {
    let value = path.to_string_lossy();
    let mut quoted = String::with_capacity(value.len() + 2);
    quoted.push('\'');
    for ch in value.chars() {
        if ch == '\'' {
            quoted.push_str("'\\''");
        } else {
            quoted.push(ch);
        }
    }
    quoted.push('\'');
    quoted
}

fn temp_ppx_file(input_name: &str) -> Result<PathBuf> {
    let basename = FsPath::new(input_name)
        .file_name()
        .and_then(|name| name.to_str())
        .filter(|name| !name.is_empty())
        .unwrap_or("input");
    let pid = std::process::id();
    for _ in 0..1000 {
        let counter = EXTERNAL_PPX_TEMP_COUNTER.fetch_add(1, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!("ppx{pid:x}{counter:x}{basename}"));
        match std::fs::OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&path)
        {
            Ok(_) => return Ok(path),
            Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(err) => {
                return Err(err).with_context(|| format!("Failed to create {}", path.display()));
            }
        }
    }
    Err(anyhow!(
        "Failed to create external preprocessor temporary file"
    ))
}

fn format_external_ppx_cannot_run_report(filename: &str, command: &str) -> String {
    format!(
        "\n  We've found a bug for you!\n  {filename}\n\n  Error while running external preprocessor\nCommand line: {command}\n\n\n"
    )
}

fn format_external_ppx_wrong_magic_report(filename: &str, magic: &str) -> String {
    format!(
        "\n  We've found a bug for you!\n  {filename}\n\n  External preprocessor does not produce a valid file\nCommand line: {magic}\n\n\n"
    )
}

fn external_ppx_cannot_run(filename: &str, command: &str) -> anyhow::Error {
    UserDiagnostic::new(format_external_ppx_cannot_run_report(filename, command), 2).into()
}

fn external_ppx_wrong_magic(filename: &str, magic: &str) -> anyhow::Error {
    UserDiagnostic::new(format_external_ppx_wrong_magic_report(filename, magic), 2).into()
}

fn check_external_ppx_output_magic(
    output_path: &std::path::Path,
    magic: &[u8],
    filename: &str,
) -> Result<()> {
    let bytes = std::fs::read(output_path).unwrap_or_default();
    let buffer = if bytes.len() < magic.len() {
        String::new()
    } else {
        String::from_utf8_lossy(&bytes[..magic.len()]).into_owned()
    };
    if buffer.as_bytes() != magic {
        return Err(external_ppx_wrong_magic(filename, &buffer));
    }
    Ok(())
}

/// `Cmd_ppx_apply.rewrite` (cmd_ppx_apply.ml:78-95): write the Parsetree0
/// input, run each rewriter on the previous one's output, and return the
/// last output file's contents.
fn run_external_ppxs(
    ppxs: &[String],
    filename: &str,
    write_input: impl FnOnce(&std::path::Path) -> std::io::Result<()>,
    magic: &[u8],
) -> Result<Vec<u8>> {
    let input_path = temp_ppx_file(filename)?;
    write_input(&input_path)
        .with_context(|| format!("Failed to write {}", input_path.display()))?;
    let mut temp_files = vec![input_path.clone()];
    let mut current = input_path;
    let result = (|| {
        for ppx in ppxs {
            let output_path = temp_ppx_file(filename)?;
            temp_files.push(output_path.clone());
            let command = format!(
                "{} {} {}",
                ppx,
                shell_quote_path(&current),
                shell_quote_path(&output_path)
            );
            let status = std::process::Command::new("sh")
                .arg("-c")
                .arg(&command)
                .status();
            if !status.as_ref().is_ok_and(|status| status.success()) || !output_path.exists() {
                return Err(external_ppx_cannot_run(filename, &command));
            }
            check_external_ppx_output_magic(&output_path, magic, filename)?;
            current = output_path;
        }
        std::fs::read(&current).with_context(|| format!("Failed to read {}", current.display()))
    })();
    for path in temp_files {
        let _ = std::fs::remove_file(path);
    }
    result
}

/// External PPXs the compiler implements itself: `@rescript/ppx-spice` style
/// rewriters are covered by the builtin spice mapper (`binary_ast::spice_ppx`),
/// which runs as part of the builtin PPX.
impl CompilerOptions {
    /// Whether the builtin spice mapper rewrites the AST. The `bsc` CLI runs
    /// every configured `-ppx` executable as OCaml does (cmd_ppx_apply.ml:97-110);
    /// the in-process build sets `spice_ppx` instead of passing a configured
    /// spice PPX, so the builtin mapper replaces a per-module subprocess.
    pub fn builtin_spice(&self) -> bool {
        self.spice_ppx
    }
}

fn external_ppxs_to_run(options: &CompilerOptions) -> Vec<String> {
    options.external_ppxs.clone()
}

/// `Ast_mapper.ppx_context` (ast_mapper.ml:571-640): the
/// `[@@@ocaml.ppx.context]` record the rewriters receive.
fn ppx_context_attribute(
    arena: &mut ParseArena,
    options: &CompilerOptions,
) -> crate::binary_ast::parsetree0::Attribute {
    use crate::binary_ast::parsetree0 as pt0;
    use crate::location::Located as OldLocated;
    let none = arena.to_location(arena.none_loc());
    let mk = |desc: pt0::ExpressionDesc| pt0::Expression {
        pexp_desc: desc,
        pexp_loc: none.clone(),
        pexp_attributes: vec![],
    };
    let mut lid = |arena: &mut ParseArena, name: &str| {
        OldLocated::new(Longident::Lident(arena.intern(name)), none.clone())
    };
    let string = |s: &str| {
        mk(pt0::ExpressionDesc::Constant(pt0::Constant::String(
            crate::string_literal::normalize_semantic(s).into_owned(),
            None,
        )))
    };
    let list = |arena: &mut ParseArena, items: Vec<pt0::Expression>| {
        let mut tail = mk(pt0::ExpressionDesc::Construct(lid(arena, "[]"), None));
        for item in items.into_iter().rev() {
            tail = mk(pt0::ExpressionDesc::Construct(
                lid(arena, "::"),
                Some(Box::new(mk(pt0::ExpressionDesc::Tuple(vec![item, tail])))),
            ));
        }
        tail
    };
    let path_string = |p: &PathBuf| p.to_string_lossy().into_owned();
    // `-I` prepends to `Clflags.include_dirs`; `Res_compmisc.init_path` puts
    // them back in command-line order ahead of the stdlib directory.
    let include_dirs: Vec<_> = options
        .include_paths
        .iter()
        .rev()
        .map(path_string)
        .collect();
    let mut load_path: Vec<_> = options.include_paths.iter().map(path_string).collect();
    if let Some(runtime) = &options.runtime_path {
        load_path.push(path_string(&runtime.join("lib").join("ocaml")));
    }
    let include_dirs = include_dirs.iter().map(|s| string(s)).collect();
    let load_path = load_path.iter().map(|s| string(s)).collect();
    let open_modules = options
        .open_modules
        .iter()
        .rev()
        .map(|s| string(s))
        .collect();
    let fields = vec![
        (lid(arena, "tool_name"), string("ReScript")),
        (lid(arena, "include_dirs"), list(arena, include_dirs)),
        (lid(arena, "load_path"), list(arena, load_path)),
        (lid(arena, "open_modules"), list(arena, open_modules)),
        (
            lid(arena, "debug"),
            mk(pt0::ExpressionDesc::Construct(
                lid(arena, if options.debug { "true" } else { "false" }),
                None,
            )),
        ),
        (lid(arena, "cookies"), list(arena, Vec::new())),
    ];
    let record = mk(pt0::ExpressionDesc::Record(fields, None));
    (
        OldLocated::new("ocaml.ppx.context".to_string(), none.clone()),
        pt0::Payload::PStr(vec![pt0::StructureItem {
            pstr_desc: pt0::StructureItemDesc::Eval(record, vec![]),
            pstr_loc: none,
        }]),
    )
}

fn ppx_output_error(filename: &str, error: impl std::fmt::Display) -> anyhow::Error {
    anyhow!("External preprocessor output for {filename} could not be read: {error}")
}

/// `Cmd_ppx_apply.apply_rewriters_str` (cmd_ppx_apply.ml:97-110) with
/// `~restore:false`: add the ppx context, run the rewriters over the
/// Parsetree0 form, read the result back and drop the context again.
pub fn apply_external_structure_ppxs(
    options: &CompilerOptions,
    filename: &str,
    arena: &mut ParseArena,
    structure: Structure,
) -> Result<Structure> {
    use crate::binary_ast::parsetree0 as pt0;
    arena.set_builtin_spice(options.builtin_spice());
    let ppxs = external_ppxs_to_run(options);
    if ppxs.is_empty() {
        // The builtin spice mapper stands in for a configured spice PPX, and
        // OCaml hands that PPX the Parsetree0 form and reads it back
        // (cmd_ppx_apply.ml:97-110), so the AST still takes that round trip.
        if options.builtin_spice() {
            let ast0 = crate::binary_ast::mapper_to0::map_structure(arena, &structure);
            return Ok(crate::binary_ast::mapper_from0::map_structure(
                arena, &ast0,
            )?);
        }
        return Ok(structure);
    }
    let context = ppx_context_attribute(arena, options);
    let none = arena.to_location(arena.none_loc());
    let mut ast0 = crate::binary_ast::mapper_to0::map_structure(arena, &structure);
    ast0.insert(
        0,
        pt0::StructureItem {
            pstr_desc: pt0::StructureItemDesc::Attribute(context),
            pstr_loc: none,
        },
    );
    let output = run_external_ppxs(
        &ppxs,
        filename,
        |path| {
            crate::binary_ast::writer::write_external_ppx_input0(
                path,
                filename,
                arena,
                AST_IMPL_MAGIC_NUMBER,
                &ast0,
            )
        },
        AST_IMPL_MAGIC_NUMBER,
    )?;
    let output =
        crate::binary_ast::parsetree0_unmarshal::read_ppx_output(&output, AST_IMPL_MAGIC_NUMBER)
            .map_err(|e| ppx_output_error(filename, e.0))?;
    let mut ast0 = crate::binary_ast::parsetree0_unmarshal::Decoder::new(arena)
        .structure(&output.ast)
        .map_err(|e| ppx_output_error(filename, e.0))?;
    if matches!(
        ast0.first().map(|item| &item.pstr_desc),
        Some(pt0::StructureItemDesc::Attribute((name, _))) if name.txt == "ocaml.ppx.context"
    ) {
        ast0.remove(0);
    }
    Ok(crate::binary_ast::mapper_from0::map_structure(
        arena, &ast0,
    )?)
}

/// `Cmd_ppx_apply.apply_rewriters_sig` (cmd_ppx_apply.ml:112-125).
pub fn apply_external_signature_ppxs(
    options: &CompilerOptions,
    filename: &str,
    arena: &mut ParseArena,
    signature: Signature,
) -> Result<Signature> {
    use crate::binary_ast::parsetree0 as pt0;
    arena.set_builtin_spice(options.builtin_spice());
    let ppxs = external_ppxs_to_run(options);
    if ppxs.is_empty() {
        // See `apply_external_structure_ppxs` (cmd_ppx_apply.ml:112-125).
        if options.builtin_spice() {
            let ast0 = crate::binary_ast::mapper_to0::map_signature(arena, &signature);
            return Ok(crate::binary_ast::mapper_from0::map_signature(
                arena, &ast0,
            )?);
        }
        return Ok(signature);
    }
    let context = ppx_context_attribute(arena, options);
    let none = arena.to_location(arena.none_loc());
    let mut ast0 = crate::binary_ast::mapper_to0::map_signature(arena, &signature);
    ast0.insert(
        0,
        pt0::SignatureItem {
            psig_desc: pt0::SignatureItemDesc::Attribute(context),
            psig_loc: none,
        },
    );
    let output = run_external_ppxs(
        &ppxs,
        filename,
        |path| {
            crate::binary_ast::writer::write_external_ppx_input0(
                path,
                filename,
                arena,
                AST_INTF_MAGIC_NUMBER,
                &ast0,
            )
        },
        AST_INTF_MAGIC_NUMBER,
    )?;
    let output =
        crate::binary_ast::parsetree0_unmarshal::read_ppx_output(&output, AST_INTF_MAGIC_NUMBER)
            .map_err(|e| ppx_output_error(filename, e.0))?;
    let mut ast0 = crate::binary_ast::parsetree0_unmarshal::Decoder::new(arena)
        .signature(&output.ast)
        .map_err(|e| ppx_output_error(filename, e.0))?;
    if matches!(
        ast0.first().map(|item| &item.psig_desc),
        Some(pt0::SignatureItemDesc::Attribute((name, _))) if name.txt == "ocaml.ppx.context"
    ) {
        ast0.remove(0);
    }
    Ok(crate::binary_ast::mapper_from0::map_signature(
        arena, &ast0,
    )?)
}

/// `Js_config.string_of_jsx_module !Js_config.jsx_module`
/// (compiler/common/js_config.ml:66-76): the module the JSX rewrite targets.
/// File-level `@@config` flags are parsed after the command line, so they win.
pub fn jsx_module_name<'a>(
    options: &'a CompilerOptions,
    file_config: Option<&'a FileConfigOverrides>,
) -> &'a str {
    let configured = file_config
        .and_then(|config| config.jsx_module.as_deref())
        .or(options.jsx_module.as_deref());
    match configured {
        Some(module) if !module.eq_ignore_ascii_case("react") => module,
        _ => "react",
    }
}

/// `-bs-jsx-module` (compiler/bsc/rescript_compiler_main.ml:267-276): set the
/// JSX module; any module but `react` is generic JSX, which implies JSX v4.
pub fn apply_jsx_module_flag(
    module: &str,
    jsx_module: &mut Option<String>,
    jsx_version: &mut Option<i32>,
) {
    *jsx_module = Some(module.to_string());
    if !module.eq_ignore_ascii_case("react") {
        *jsx_version = Some(4);
    }
}

pub fn jsx_version_for_structure(
    structure: &Structure,
    options: &CompilerOptions,
    arena: &crate::parse_arena::ParseArena,
) -> Option<i32> {
    options
        .jsx_version
        .or_else(|| structure_has_config_string(structure, "-bs-jsx", arena).then_some(4))
}

pub fn experimental_let_unwrap_for_structure(
    structure: &Structure,
    options: &CompilerOptions,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    options.experimental_let_unwrap
        || extract_file_config_from_structure(structure, arena).let_unwrap
}

fn experimental_let_unwrap_for_signature(
    signature: &Signature,
    options: &CompilerOptions,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    options.experimental_let_unwrap
        || extract_file_config_from_signature(signature, arena).let_unwrap
}

pub(crate) fn debug_for_structure(
    structure: &Structure,
    options: &CompilerOptions,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    options.debug || structure_has_config_string(structure, "-bs-g", arena)
}

pub(crate) fn jsx_preserve_for_structure(
    structure: &Structure,
    options: &CompilerOptions,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    options.jsx_preserve || structure_has_config_string(structure, "-bs-jsx-preserve", arena)
}

/// `builtin_ppx_warnings` receives the warnings the builtin mapper prints,
/// including those emitted before a mapper error.
fn preprocess_signature_for_typecheck_with_source(
    signature: Signature,
    options: &CompilerOptions,
    arena: &mut crate::parse_arena::ParseArena,
    source: &str,
    filename: &str,
    builtin_ppx_warnings: &mut Vec<ppx::PpxWarning>,
) -> Result<Signature> {
    let signature = if let Some(jsx_version) = options.jsx_version {
        jsx_ppx::transform_signature_result(
            signature,
            jsx_version,
            jsx_module_name(options, None),
            arena,
        )
        .map_err(|e| jsx_ppx_error_to_anyhow(e, arena, source, filename))?
    } else {
        signature
    };

    if options.no_builtin_ppx {
        Ok(signature)
    } else {
        arena.set_builtin_spice(options.builtin_spice());
        let (rewritten, warnings) = ppx::rewrite_signature_with_warnings(&signature, arena);
        builtin_ppx_warnings.extend(warnings);
        rewritten.map_err(|e| ppx_error_to_anyhow(e, arena, source, filename))
    }
}

fn ppx_error_to_anyhow(
    err: ppx::PpxError,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    let mut prefix = String::new();
    for warning in err.warnings() {
        prefix.push_str(&format_compiler_warning_report(
            arena,
            source,
            filename,
            &TypeCoreWarning {
                loc: warning.loc,
                warning: warning.warning.clone(),
                is_error: false,
            },
        ));
    }
    if err.loc().is_none() && err.message_text().starts_with("Fatal error: exception ") {
        return UserDiagnostic::new(format!("{prefix}{}", err.message_text()), 2).into();
    }
    if let Some(loc) = err.loc() {
        let message = err.message_text();
        let mut report = if message.contains('\n') {
            let mut raw_message = String::with_capacity(message.len() + 2);
            raw_message.push_str("  ");
            raw_message.push_str(message);
            format_compiler_error_report_raw_message(arena, source, filename, loc, &raw_message)
        } else {
            format_compiler_error_report(arena, source, filename, loc, message)
        };
        if !prefix.is_empty() {
            report.insert_str(0, &prefix);
        }
        UserDiagnostic::new(report, 2).into()
    } else {
        let mut report = format_compiler_error_report_for_file(filename, err.message_text());
        if !prefix.is_empty() {
            report.insert_str(0, &prefix);
        }
        UserDiagnostic::new(report, 2).into()
    }
}

fn jsx_ppx_error_to_anyhow(
    err: jsx_ppx::JsxPreprocessorError,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    let loc = arena.to_location(err.loc);
    // Location.print_loc (location.ml:75-92) prints the location's own
    // pos_fname; a range-less `Location.in_file file_name` (jsx_v4.ml
    // empty_loc) names the module rather than the source file.
    let loc_file = arena.get_string(loc.loc_start.file_name);
    let filename =
        if !code_frame::has_printable_range(&loc.loc_start, &loc.loc_end) && !loc_file.is_empty() {
            loc_file
        } else {
            filename
        };
    let output = match err.message_style {
        jsx_ppx::JsxPreprocessorMessageStyle::PrefixedLines => {
            format_compiler_error_report_from_location(source, filename, &loc, &err.message)
        }
        jsx_ppx::JsxPreprocessorMessageStyle::FirstLineOnlyPrefix => {
            let mut output = String::new();
            push_compiler_error_report_header_from_location(&mut output, source, filename, &loc);
            for (idx, line) in err.message.lines().enumerate() {
                if idx == 0 {
                    output.push_str("  ");
                }
                output.push_str(line);
                output.push('\n');
            }
            output.push('\n');
            output
        }
    };
    UserDiagnostic::new(output, 2).into()
}

fn jsx_preprocessor_warnings_to_ppx(
    arena: &mut ParseArena,
    warnings: Vec<jsx_ppx::JsxPreprocessorWarning>,
) -> Vec<ppx::PpxWarning> {
    warnings
        .into_iter()
        .map(|warning| ppx::PpxWarning {
            loc: arena.mk_loc_from_positions(&warning.start_pos, &warning.end_pos),
            warning: crate::diagnostics::Warning::Preprocessor {
                message: warning.message,
            },
        })
        .collect()
}

fn emit_ppx_warnings(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    warnings: &[ppx::PpxWarning],
) -> bool {
    let warning_config = warning_config_for_options(options);
    emit_ppx_warnings_with_config(arena, source, filename, &warning_config, warnings)
}

/// Parser warnings (e.g. the deprecated `(. ...)` syntax) are reported by OCaml
/// through `Location.prerr_warning` while parsing, under the command-line warning
/// settings (compiler/syntax/src/res_core.ml:291-298). Emit them before any syntax
/// errors and report whether one was configured as an error.
pub fn emit_parser_warnings(
    parser: &mut Parser<'_>,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> bool {
    let mut out = String::new();
    let has_error = format_parser_warnings(parser, source, filename, options, &mut out);
    write_stderr(&out);
    has_error
}

fn write_stderr(output: &str) {
    if !output.is_empty() {
        let output = crate::source_text::decode_internal_utf8_runs(output);
        let mut stderr = std::io::stderr();
        let _ = std::io::Write::write_all(&mut stderr, output.as_bytes());
        let _ = std::io::Write::flush(&mut stderr);
    }
}

/// Like [`emit_parser_warnings`], appending the reports to `out`.
fn format_parser_warnings(
    parser: &mut Parser<'_>,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    out: &mut String,
) -> bool {
    let parser_warnings = parser.warnings().to_vec();
    if parser_warnings.is_empty() {
        return false;
    }
    let mut warnings = Vec::with_capacity(parser_warnings.len());
    for warning in parser_warnings {
        let message = match warning.kind {
            crate::parser::ParserWarningKind::DeprecatedUncurriedDotSyntax => {
                "The `(. ...)` uncurried syntax is deprecated. Uncurried is now the default in ReScript — remove the leading dot.".to_string()
            }
        };
        let arena = parser.arena_mut();
        let start = arena.push_position(warning.start_pos);
        let end = arena.push_position(warning.end_pos);
        let loc = arena.mk_loc(start, end);
        let location = arena.to_location(loc);
        warnings.push(ppx::PpxWarning {
            loc,
            warning: crate::diagnostics::Warning::Deprecated {
                message,
                def_loc: location.clone(),
                use_loc: location,
                can_be_automigrated: false,
            },
        });
    }
    let warning_config = warning_config_for_options(options);
    format_ppx_warnings_with_config(
        parser.arena(),
        source,
        filename,
        &warning_config,
        &warnings,
        out,
    )
}

fn emit_ppx_warnings_with_config(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    warning_config: &WarningConfig,
    warnings: &[ppx::PpxWarning],
) -> bool {
    let mut out = String::new();
    let has_error = format_ppx_warnings_with_config(
        arena,
        source,
        filename,
        warning_config,
        warnings,
        &mut out,
    );
    write_stderr(&out);
    has_error
}

/// Append the active warnings' reports to `out`; returns whether one is an error.
fn format_ppx_warnings_with_config(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    warning_config: &WarningConfig,
    warnings: &[ppx::PpxWarning],
    out: &mut String,
) -> bool {
    let mut has_error = false;
    for warning in warnings {
        if !warning_config.is_active(&warning.warning) {
            continue;
        }
        let is_error = warning_config.is_error(&warning.warning);
        has_error |= is_error;
        out.push_str(&format_compiler_warning_report(
            arena,
            source,
            filename,
            &TypeCoreWarning {
                loc: warning.loc,
                warning: warning.warning.clone(),
                is_error,
            },
        ));
    }
    has_error
}

pub fn parser_error_to_anyhow(parser: &Parser<'_>, source: &str, filename: &str) -> anyhow::Error {
    let mut output = String::new();
    for diagnostic in parser.diagnostics().iter() {
        output.push_str(&code_frame::format_error(
            filename,
            source,
            &diagnostic.start_pos,
            &diagnostic.end_pos,
            &diagnostic.explain_with_source(Some(source)),
        ));
    }
    UserDiagnostic::new(output, 1).into()
}

fn directive_payload_error_to_anyhow(
    err: DirectivePayloadError,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    UserDiagnostic::new(
        format_compiler_error_report(arena, source, filename, err.loc, err.message),
        2,
    )
    .into()
}

fn let_unwrap_feature_error_to_anyhow(
    loc: LocIdx,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    UserDiagnostic::new(
        format_compiler_error_report(
            arena,
            source,
            filename,
            loc,
            LET_UNWRAP_FEATURE_NOT_ENABLED_MSG,
        ),
        2,
    )
    .into()
}

fn let_unwrap_position_error_to_anyhow(
    loc: LocIdx,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    message: &str,
) -> anyhow::Error {
    UserDiagnostic::new(
        format_compiler_error_report(arena, source, filename, loc, message),
        2,
    )
    .into()
}

fn attr_is_let_unwrap(attr: &Attribute, arena: &ParseArena) -> bool {
    arena.get_string(attr.0.txt) == "let.unwrap"
}

fn attrs_have_let_unwrap(attrs: &crate::parser::ast::Attributes, arena: &ParseArena) -> bool {
    attrs.iter().any(|attr| attr_is_let_unwrap(attr, arena))
}

fn reject_disabled_let_unwrap_in_structure(
    enabled: bool,
    structure: &Structure,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> Result<()> {
    if !enabled {
        if let Some(loc) = disabled_let_unwrap_loc_in_structure(structure, arena) {
            return Err(let_unwrap_feature_error_to_anyhow(
                loc, arena, source, filename,
            ));
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum LetUnwrapPositionError {
    Toplevel(LocIdx),
    UnsupportedType(LocIdx),
}

fn reject_enabled_invalid_let_unwrap_in_structure(
    enabled: bool,
    structure: &Structure,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> Result<()> {
    if !enabled {
        return Ok(());
    }
    if let Some(error) = invalid_enabled_let_unwrap_in_structure(structure, arena) {
        let (loc, message) = match error {
            LetUnwrapPositionError::Toplevel(loc) => (loc, LET_UNWRAP_TOPLEVEL_MSG),
            LetUnwrapPositionError::UnsupportedType(loc) => (loc, LET_UNWRAP_UNSUPPORTED_TYPE_MSG),
        };
        return Err(let_unwrap_position_error_to_anyhow(
            loc, arena, source, filename, message,
        ));
    }
    Ok(())
}

fn let_unwrap_binding_loc(
    bindings: &[crate::parser::ast::ValueBinding],
    arena: &ParseArena,
) -> Option<LocIdx> {
    bindings
        .iter()
        .find(|binding| attrs_have_let_unwrap(&binding.pvb_attributes, arena))
        .map(|binding| arena.get_pat(binding.pvb_pat).ppat_loc)
}

fn is_supported_let_unwrap_pattern(pat: &crate::parser::ast::Pattern, arena: &ParseArena) -> bool {
    let PatternDesc::Ppat_construct(ctor_lid, payload) = &*pat.ppat_desc else {
        return false;
    };
    let Longident::Lident(ctor_name_idx) = arena.get_longident(ctor_lid.txt) else {
        return false;
    };
    match (arena.get_string(*ctor_name_idx), !payload.txt.is_empty()) {
        ("Ok", true) | ("Error", true) | ("Some", true) | ("None", false) => true,
        _ => false,
    }
}

fn invalid_enabled_let_unwrap_in_bindings(
    bindings: &[crate::parser::ast::ValueBinding],
    arena: &ParseArena,
) -> Option<LetUnwrapPositionError> {
    for binding in bindings {
        if let Some(error) = invalid_enabled_let_unwrap_in_expr(binding.pvb_expr, arena) {
            return Some(error);
        }
    }
    None
}

fn invalid_enabled_let_unwrap_in_structure(
    structure: &Structure,
    arena: &ParseArena,
) -> Option<LetUnwrapPositionError> {
    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_eval(eval) => {
                if let Some(error) = invalid_enabled_let_unwrap_in_expr(eval.0, arena) {
                    return Some(error);
                }
            }
            StructureItemDesc::Pstr_value(value) => {
                if let Some(loc) = let_unwrap_binding_loc(&value.1, arena) {
                    return Some(LetUnwrapPositionError::Toplevel(loc));
                }
                if let Some(error) = invalid_enabled_let_unwrap_in_bindings(&value.1, arena) {
                    return Some(error);
                }
            }
            StructureItemDesc::Pstr_module(module_binding) => {
                if let Some(error) =
                    invalid_enabled_let_unwrap_in_mod_expr(module_binding.pmb_expr, arena)
                {
                    return Some(error);
                }
            }
            StructureItemDesc::Pstr_recmodule(module_bindings) => {
                for module_binding in module_bindings.iter() {
                    if let Some(error) =
                        invalid_enabled_let_unwrap_in_mod_expr(module_binding.pmb_expr, arena)
                    {
                        return Some(error);
                    }
                }
            }
            StructureItemDesc::Pstr_include(include_decl) => {
                if let Some(error) =
                    invalid_enabled_let_unwrap_in_mod_expr(include_decl.pincl_mod, arena)
                {
                    return Some(error);
                }
            }
            _ => {}
        }
    }
    None
}

fn invalid_enabled_let_unwrap_in_mod_expr(
    mod_expr: ModExprIdx,
    arena: &ParseArena,
) -> Option<LetUnwrapPositionError> {
    let mod_expr = arena.get_mod_expr(mod_expr);
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => {
            invalid_enabled_let_unwrap_in_structure(items, arena)
        }
        ModuleExprDesc::Pmod_functor(functor) => {
            invalid_enabled_let_unwrap_in_mod_expr(functor.2, arena)
        }
        ModuleExprDesc::Pmod_apply(lhs, rhs) => invalid_enabled_let_unwrap_in_mod_expr(*lhs, arena)
            .or_else(|| invalid_enabled_let_unwrap_in_mod_expr(*rhs, arena)),
        ModuleExprDesc::Pmod_constraint(inner, _) => {
            invalid_enabled_let_unwrap_in_mod_expr(*inner, arena)
        }
        ModuleExprDesc::Pmod_unpack(expr) => invalid_enabled_let_unwrap_in_expr(*expr, arena),
        _ => None,
    }
}

fn invalid_enabled_let_unwrap_in_expr(
    expr: ExprIdx,
    arena: &ParseArena,
) -> Option<LetUnwrapPositionError> {
    let expr = arena.get_expr(expr);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_let(inner) => {
            let (_rec_flag, bindings, body) = &**inner;
            if let [binding] = bindings.as_slice()
                && attrs_have_let_unwrap(&binding.pvb_attributes, arena)
                && !is_supported_let_unwrap_pattern(arena.get_pat(binding.pvb_pat), arena)
            {
                return Some(LetUnwrapPositionError::UnsupportedType(
                    arena.get_pat(binding.pvb_pat).ppat_loc,
                ));
            }
            invalid_enabled_let_unwrap_in_bindings(bindings, arena)
                .or_else(|| invalid_enabled_let_unwrap_in_expr(*body, arena))
        }
        ExpressionDesc::Pexp_fun(fun) => fun
            .default
            .and_then(|expr| invalid_enabled_let_unwrap_in_expr(expr, arena))
            .or_else(|| invalid_enabled_let_unwrap_in_expr(fun.rhs, arena)),
        ExpressionDesc::Pexp_apply(apply) => invalid_enabled_let_unwrap_in_expr(apply.funct, arena)
            .or_else(|| {
                apply
                    .args
                    .iter()
                    .find_map(|(_, arg)| invalid_enabled_let_unwrap_in_expr(*arg, arena))
            }),
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            invalid_enabled_let_unwrap_in_expr(inner.0, arena).or_else(|| {
                inner.1.iter().find_map(|case| {
                    case.pc_guard
                        .and_then(|guard| invalid_enabled_let_unwrap_in_expr(guard, arena))
                        .or_else(|| invalid_enabled_let_unwrap_in_expr(case.pc_rhs, arena))
                })
            })
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => items
            .iter()
            .find_map(|item| invalid_enabled_let_unwrap_in_expr(*item, arena)),
        ExpressionDesc::Pexp_construct(_, payload) => payload
            .txt
            .iter()
            .find_map(|expr| invalid_enabled_let_unwrap_in_expr(*expr, arena)),
        ExpressionDesc::Pexp_variant(inner) => inner
            .1
            .txt
            .iter()
            .find_map(|expr| invalid_enabled_let_unwrap_in_expr(*expr, arena)),
        ExpressionDesc::Pexp_record(record) => record
            .0
            .iter()
            .find_map(|field| invalid_enabled_let_unwrap_in_expr(field.expr, arena))
            .or_else(|| {
                record
                    .1
                    .and_then(|base| invalid_enabled_let_unwrap_in_expr(base, arena))
            }),
        ExpressionDesc::Pexp_field(owner, _)
        | ExpressionDesc::Pexp_assert(owner)
        | ExpressionDesc::Pexp_await(owner) => invalid_enabled_let_unwrap_in_expr(*owner, arena),
        ExpressionDesc::Pexp_object_get(inner) => {
            invalid_enabled_let_unwrap_in_expr(inner.0, arena)
        }
        ExpressionDesc::Pexp_setfield(inner) => invalid_enabled_let_unwrap_in_expr(inner.0, arena)
            .or_else(|| invalid_enabled_let_unwrap_in_expr(inner.2, arena)),
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            invalid_enabled_let_unwrap_in_expr(inner.0, arena)
                .or_else(|| invalid_enabled_let_unwrap_in_expr(inner.1, arena))
                .or_else(|| {
                    inner
                        .2
                        .and_then(|else_expr| invalid_enabled_let_unwrap_in_expr(else_expr, arena))
                })
        }
        ExpressionDesc::Pexp_braces(braces) => {
            invalid_enabled_let_unwrap_in_expr(braces.expr, arena)
        }
        ExpressionDesc::Pexp_ternary(inner) => invalid_enabled_let_unwrap_in_expr(inner.0, arena)
            .or_else(|| invalid_enabled_let_unwrap_in_expr(inner.1, arena))
            .or_else(|| invalid_enabled_let_unwrap_in_expr(inner.2, arena)),
        ExpressionDesc::Pexp_sequence(lhs, rhs) => invalid_enabled_let_unwrap_in_expr(*lhs, arena)
            .or_else(|| invalid_enabled_let_unwrap_in_expr(*rhs, arena)),
        ExpressionDesc::Pexp_while(cond, body) => invalid_enabled_let_unwrap_in_expr(*cond, arena)
            .or_else(|| invalid_enabled_let_unwrap_in_expr(*body, arena)),
        ExpressionDesc::Pexp_for(inner) => invalid_enabled_let_unwrap_in_expr(inner.1, arena)
            .or_else(|| invalid_enabled_let_unwrap_in_expr(inner.2, arena))
            .or_else(|| invalid_enabled_let_unwrap_in_expr(inner.4, arena)),
        ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
            invalid_enabled_let_unwrap_in_expr(inner.1, arena)
                .or_else(|| invalid_enabled_let_unwrap_in_expr(inner.2, arena))
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            invalid_enabled_let_unwrap_in_expr(inner.0, arena)
        }
        ExpressionDesc::Pexp_coerce(inner) => invalid_enabled_let_unwrap_in_expr(inner.0, arena),
        ExpressionDesc::Pexp_letmodule(inner) => {
            invalid_enabled_let_unwrap_in_mod_expr(inner.1, arena)
                .or_else(|| invalid_enabled_let_unwrap_in_expr(inner.2, arena))
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            invalid_enabled_let_unwrap_in_expr(inner.1, arena)
        }
        ExpressionDesc::Pexp_newtype(inner) => invalid_enabled_let_unwrap_in_expr(inner.1, arena),
        ExpressionDesc::Pexp_pack(mod_expr) => {
            invalid_enabled_let_unwrap_in_mod_expr(*mod_expr, arena)
        }
        ExpressionDesc::Pexp_open(inner) => invalid_enabled_let_unwrap_in_expr(inner.2, arena),
        _ => None,
    }
}

fn disabled_let_unwrap_loc_in_bindings(
    bindings: &[crate::parser::ast::ValueBinding],
    arena: &ParseArena,
) -> Option<LocIdx> {
    for binding in bindings {
        if attrs_have_let_unwrap(&binding.pvb_attributes, arena) {
            return Some(arena.get_pat(binding.pvb_pat).ppat_loc);
        }
    }
    for binding in bindings {
        if let Some(loc) = disabled_let_unwrap_loc_in_expr(binding.pvb_expr, arena) {
            return Some(loc);
        }
    }
    None
}

fn disabled_let_unwrap_loc_in_structure(
    structure: &Structure,
    arena: &ParseArena,
) -> Option<LocIdx> {
    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_eval(eval) => {
                if let Some(loc) = disabled_let_unwrap_loc_in_expr(eval.0, arena) {
                    return Some(loc);
                }
            }
            StructureItemDesc::Pstr_value(value) => {
                if let Some(loc) = disabled_let_unwrap_loc_in_bindings(&value.1, arena) {
                    return Some(loc);
                }
            }
            StructureItemDesc::Pstr_module(module_binding) => {
                if let Some(loc) =
                    disabled_let_unwrap_loc_in_mod_expr(module_binding.pmb_expr, arena)
                {
                    return Some(loc);
                }
            }
            StructureItemDesc::Pstr_recmodule(module_bindings) => {
                for module_binding in module_bindings.iter() {
                    if let Some(loc) =
                        disabled_let_unwrap_loc_in_mod_expr(module_binding.pmb_expr, arena)
                    {
                        return Some(loc);
                    }
                }
            }
            StructureItemDesc::Pstr_include(include_decl) => {
                if let Some(loc) =
                    disabled_let_unwrap_loc_in_mod_expr(include_decl.pincl_mod, arena)
                {
                    return Some(loc);
                }
            }
            _ => {}
        }
    }
    None
}

fn disabled_let_unwrap_loc_in_mod_expr(mod_expr: ModExprIdx, arena: &ParseArena) -> Option<LocIdx> {
    let mod_expr = arena.get_mod_expr(mod_expr);
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => disabled_let_unwrap_loc_in_structure(items, arena),
        ModuleExprDesc::Pmod_functor(functor) => {
            disabled_let_unwrap_loc_in_mod_expr(functor.2, arena)
        }
        ModuleExprDesc::Pmod_apply(lhs, rhs) => disabled_let_unwrap_loc_in_mod_expr(*lhs, arena)
            .or_else(|| disabled_let_unwrap_loc_in_mod_expr(*rhs, arena)),
        ModuleExprDesc::Pmod_constraint(inner, _) => {
            disabled_let_unwrap_loc_in_mod_expr(*inner, arena)
        }
        ModuleExprDesc::Pmod_unpack(expr) => disabled_let_unwrap_loc_in_expr(*expr, arena),
        _ => None,
    }
}

fn disabled_let_unwrap_loc_in_expr(expr: ExprIdx, arena: &ParseArena) -> Option<LocIdx> {
    let expr = arena.get_expr(expr);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_let(inner) => disabled_let_unwrap_loc_in_bindings(&inner.1, arena)
            .or_else(|| disabled_let_unwrap_loc_in_expr(inner.2, arena)),
        ExpressionDesc::Pexp_fun(fun) => fun
            .default
            .and_then(|expr| disabled_let_unwrap_loc_in_expr(expr, arena))
            .or_else(|| disabled_let_unwrap_loc_in_expr(fun.rhs, arena)),
        ExpressionDesc::Pexp_apply(apply) => disabled_let_unwrap_loc_in_expr(apply.funct, arena)
            .or_else(|| {
                apply
                    .args
                    .iter()
                    .find_map(|(_, arg)| disabled_let_unwrap_loc_in_expr(*arg, arena))
            }),
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            disabled_let_unwrap_loc_in_expr(inner.0, arena).or_else(|| {
                inner.1.iter().find_map(|case| {
                    case.pc_guard
                        .and_then(|guard| disabled_let_unwrap_loc_in_expr(guard, arena))
                        .or_else(|| disabled_let_unwrap_loc_in_expr(case.pc_rhs, arena))
                })
            })
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => items
            .iter()
            .find_map(|item| disabled_let_unwrap_loc_in_expr(*item, arena)),
        ExpressionDesc::Pexp_construct(_, payload) => payload
            .txt
            .iter()
            .find_map(|expr| disabled_let_unwrap_loc_in_expr(*expr, arena)),
        ExpressionDesc::Pexp_variant(inner) => inner
            .1
            .txt
            .iter()
            .find_map(|expr| disabled_let_unwrap_loc_in_expr(*expr, arena)),
        ExpressionDesc::Pexp_record(record) => record
            .0
            .iter()
            .find_map(|field| disabled_let_unwrap_loc_in_expr(field.expr, arena))
            .or_else(|| {
                record
                    .1
                    .and_then(|base| disabled_let_unwrap_loc_in_expr(base, arena))
            }),
        ExpressionDesc::Pexp_field(owner, _)
        | ExpressionDesc::Pexp_assert(owner)
        | ExpressionDesc::Pexp_await(owner) => disabled_let_unwrap_loc_in_expr(*owner, arena),
        ExpressionDesc::Pexp_object_get(inner) => disabled_let_unwrap_loc_in_expr(inner.0, arena),
        ExpressionDesc::Pexp_setfield(inner) => disabled_let_unwrap_loc_in_expr(inner.0, arena)
            .or_else(|| disabled_let_unwrap_loc_in_expr(inner.2, arena)),
        ExpressionDesc::Pexp_ifthenelse(inner) => disabled_let_unwrap_loc_in_expr(inner.0, arena)
            .or_else(|| disabled_let_unwrap_loc_in_expr(inner.1, arena))
            .or_else(|| {
                inner
                    .2
                    .and_then(|else_expr| disabled_let_unwrap_loc_in_expr(else_expr, arena))
            }),
        ExpressionDesc::Pexp_braces(braces) => disabled_let_unwrap_loc_in_expr(braces.expr, arena),
        ExpressionDesc::Pexp_ternary(inner) => disabled_let_unwrap_loc_in_expr(inner.0, arena)
            .or_else(|| disabled_let_unwrap_loc_in_expr(inner.1, arena))
            .or_else(|| disabled_let_unwrap_loc_in_expr(inner.2, arena)),
        ExpressionDesc::Pexp_sequence(lhs, rhs) => disabled_let_unwrap_loc_in_expr(*lhs, arena)
            .or_else(|| disabled_let_unwrap_loc_in_expr(*rhs, arena)),
        ExpressionDesc::Pexp_while(cond, body) => disabled_let_unwrap_loc_in_expr(*cond, arena)
            .or_else(|| disabled_let_unwrap_loc_in_expr(*body, arena)),
        ExpressionDesc::Pexp_for(inner) => disabled_let_unwrap_loc_in_expr(inner.1, arena)
            .or_else(|| disabled_let_unwrap_loc_in_expr(inner.2, arena))
            .or_else(|| disabled_let_unwrap_loc_in_expr(inner.4, arena)),
        ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
            disabled_let_unwrap_loc_in_expr(inner.1, arena)
                .or_else(|| disabled_let_unwrap_loc_in_expr(inner.2, arena))
        }
        ExpressionDesc::Pexp_constraint(inner) => disabled_let_unwrap_loc_in_expr(inner.0, arena),
        ExpressionDesc::Pexp_coerce(inner) => disabled_let_unwrap_loc_in_expr(inner.0, arena),
        ExpressionDesc::Pexp_letmodule(inner) => {
            disabled_let_unwrap_loc_in_mod_expr(inner.1, arena)
                .or_else(|| disabled_let_unwrap_loc_in_expr(inner.2, arena))
        }
        ExpressionDesc::Pexp_letexception(inner) => disabled_let_unwrap_loc_in_expr(inner.1, arena),
        ExpressionDesc::Pexp_newtype(inner) => disabled_let_unwrap_loc_in_expr(inner.1, arena),
        ExpressionDesc::Pexp_pack(mod_expr) => {
            disabled_let_unwrap_loc_in_mod_expr(*mod_expr, arena)
        }
        ExpressionDesc::Pexp_open(inner) => disabled_let_unwrap_loc_in_expr(inner.2, arena),
        _ => None,
    }
}

/// Remove SGR style escapes (`ESC [ ... m`).
fn strip_style_escapes(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("\x1b[") {
        out.push_str(&rest[..start]);
        let after = &rest[start + 2..];
        match after.find('m') {
            Some(end)
                if after[..end]
                    .bytes()
                    .all(|b| b.is_ascii_digit() || b == b';') =>
            {
                rest = &after[end + 1..];
            }
            _ => {
                out.push_str("\x1b[");
                rest = after;
            }
        }
    }
    out.push_str(rest);
    out
}

fn type_mod_error_to_anyhow(
    err: TypeModError,
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    suppress_info_style: bool,
) -> anyhow::Error {
    let error = type_mod_error_to_anyhow_styled(
        err,
        type_ctx,
        arena,
        source,
        filename,
        suppress_info_style,
    );
    // The snippets the report re-parsed printed their parser warnings first
    // (`Error_message_utils.Parser.parse_source`, Location.prerr_warning).
    let reparse_warnings = format_reparse_warnings(type_ctx);
    let error = if reparse_warnings.is_empty() {
        error
    } else {
        match error.downcast::<UserDiagnostic>() {
            Ok(diagnostic) => UserDiagnostic {
                output: format!("{reparse_warnings}{}", diagnostic.output),
                exit_code: diagnostic.exit_code,
            }
            .into(),
            Err(error) => error,
        }
    };
    if !suppress_info_style {
        return error;
    }
    // OCaml compiler/ext/misc.ml:337-392: once a printed warning has run
    // `Location.setup_colors` with colors disabled, the style tags of later
    // error messages print nothing.
    match error.downcast::<UserDiagnostic>() {
        Ok(diagnostic) => UserDiagnostic {
            output: strip_style_escapes(&diagnostic.output),
            exit_code: diagnostic.exit_code,
        }
        .into(),
        Err(error) => error,
    }
}

/// The parser warnings of the snippets an error report re-parsed, at their
/// `<none>` locations (no code frame), as `Location.prerr_warning` prints
/// them.
fn format_reparse_warnings(type_ctx: &TypeContext) -> String {
    let warnings = type_ctx.take_reparse_warnings();
    if warnings.is_empty() {
        return String::new();
    }
    let config = type_ctx.report_warning_config();
    let mut output = String::new();
    for parser_warning in warnings {
        let warning = match parser_warning.kind {
            crate::parser::ParserWarningKind::DeprecatedUncurriedDotSyntax => {
                crate::diagnostics::Warning::Deprecated {
                    message: "The `(. ...)` uncurried syntax is deprecated. Uncurried is now the default in ReScript — remove the leading dot.".to_string(),
                    def_loc: crate::location::Location::none(),
                    use_loc: crate::location::Location::none(),
                    can_be_automigrated: false,
                }
            }
        };
        if !config.is_active(&warning) {
            continue;
        }
        let is_error = config.is_error(&warning);
        code_frame::mark_color_setup();
        output.push_str("\n  ");
        output.push_str(&code_frame::colorize_intro(
            &format!("Warning number {}", warning.number()),
            is_error,
        ));
        if is_error {
            output.push_str(" (configured as error) ");
        }
        output.push_str("\n  ");
        let location = code_frame::format_location(
            "<none>",
            &parser_warning.start_pos,
            &parser_warning.end_pos,
        );
        output.push_str(&code_frame::colorize_location(&location));
        output.push_str("\n\n  ");
        output.push_str(&warning.message());
        output.push_str("\n\n");
    }
    output
}

fn type_mod_error_to_anyhow_styled(
    err: TypeModError,
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    suppress_info_style: bool,
) -> anyhow::Error {
    match &err {
        TypeModError::CoreError(TypeCoreError::ModuleError(module_error)) => {
            type_mod_error_to_anyhow(
                (**module_error).clone(),
                type_ctx,
                arena,
                source,
                filename,
                suppress_info_style,
            )
        }
        TypeModError::CoreError(TypeCoreError::UncurriedArityMismatch {
            loc,
            function_type,
            expected_arity,
            provided_arity,
            provided_args,
            arity_suggestion,
            ..
        }) => UserDiagnostic::new(
            format_uncurried_arity_mismatch_report(
                type_ctx,
                arena,
                source,
                filename,
                *loc,
                *function_type,
                *expected_arity,
                *provided_arity,
                provided_args,
                arity_suggestion.as_deref(),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::ConstructorArityMismatch {
            loc,
            name,
            is_inline_record,
            expected,
            provided,
        }) => UserDiagnostic::new(
            format_constructor_arity_mismatch_report(
                arena,
                source,
                filename,
                *loc,
                name,
                *is_inline_record,
                *expected,
                *provided,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::MultiplyBoundVariable { loc, name }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!("Variable {name} is bound several times in this pattern"),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::IllegalValueName { loc, name }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!("'{name}' is not a valid value identifier."),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::OrpatVars {
            loc,
            id,
            valid_idents,
        }) => UserDiagnostic::new(
            format_orpat_vars_report(arena, source, filename, *loc, id, valid_idents),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::OrPatternTypeClash {
            loc,
            id,
            trace,
            env,
        }) => {
            let env = env
                .and_then(|env| type_ctx.get_typed_env(env))
                .map(|env| (*env).clone())
                .unwrap_or_else(crate::types::Env::empty);
            let message = type_clash::render_error_message(|ppf| {
                type_clash::print_or_pattern_type_clash(ppf, type_ctx, &env, id.name(), trace)
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::BreakOutsideLoop { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "`break` can only be used directly inside a loop body.",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::ContinueOutsideLoop { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "`continue` can only be used inside a loop body.",
                ),
                2,
            )
            .into()
        },
        TypeModError::CoreError(TypeCoreError::JsxNotEnabled { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Cannot compile JSX expression because JSX support is not enabled. Add \"jsx\" settings to rescript.json to enable JSX support.",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::ExtensionError(error)) => {
            UserDiagnostic::new(
                format_builtin_extension_error_report(arena, source, filename, error),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ExtensionAlreadyDisplayed) => {
            UserDiagnostic::new(String::new(), 2).into()
        }
        TypeModError::CoreError(TypeCoreError::InvalidForLoopIndex { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Invalid for-loop index: only variables and _ are allowed.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::InvalidForOfPattern { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Invalid for...of binding: only variables and _ are allowed.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::IllegalLetrecPat { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Only variables are allowed as left-hand side of `let rec`",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::IllegalLetrecExpr { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This kind of expression is not allowed as right-hand side of `let rec`",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::EmptyRecordLiteral { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Empty record literal {} should be type annotated or used in a record context.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::InvalidInterval { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Only character intervals are supported in patterns.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::NoValueClauses { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "None of the patterns in this switch match values.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ExceptionPatternBelowToplevel { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Exception patterns must be at the top level of a match case.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ModulesNotAllowed { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Modules are not allowed in this pattern.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::CannotInferSignature { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "The signature for this packaged module couldn't be inferred.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::NotAPackedModule { loc, ty }) => {
            UserDiagnostic::new(
                format_compiler_error_report_with_unindented_break(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This expression is packed module, but the expected type is",
                    &format_type_expr(type_ctx, *ty),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::InlinedRecordExpected { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This constructor expects an inlined record argument.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::InvalidExtensionConstructorPayload { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Invalid [%extension_constructor] payload, a constructor is expected.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::NotAnExtensionConstructor { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This constructor is not an extension constructor.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::CannotApplyModule { loc, mty, origin }) => {
            UserDiagnostic::new(
                format_cannot_apply_module_report(type_ctx, arena, source, filename, *loc, mty, origin.as_ref()),
                2,
            )
            .into()
        }
        TypeModError::NotAPackedModule { loc, ty } => {
            UserDiagnostic::new(
                format_compiler_error_report_with_unindented_break(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This expression is not a packed module. It has type",
                    &format_type_expr(type_ctx, *ty),
                ),
                2,
            )
            .into()
        }
        TypeModError::CannotApply { loc, mty, origin } => UserDiagnostic::new(
            format_cannot_apply_module_report(type_ctx, arena, source, filename, *loc, mty, origin.as_ref()),
            2,
        )
        .into(),
        TypeModError::MissingModule {
            loc,
            path,
            expanded,
        } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format_missing_module_message(path, expanded),
            ),
            2,
        )
        .into(),
        TypeModError::CannotScrapeAlias { loc, path } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("This is an alias for module {}, which is missing", path.name()),
            ),
            2,
        )
        .into(),
        TypeModError::IllegalValueName { loc, name } => UserDiagnostic::new(
            format_compiler_error_report_from_external_location(
                type_ctx,
                filename,
                loc,
                &format!("'{name}' is not a valid value identifier."),
            ),
            2,
        )
        .into(),
        TypeModError::CannotEliminateDependency { loc, mty } => UserDiagnostic::new(
            format_cannot_eliminate_dependency_report(
                type_ctx, arena, source, filename, *loc, mty,
            ),
            2,
        )
        .into(),
        TypeModError::RecursiveModuleRequiresExplicitType { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Recursive modules require an explicit module type.",
            ),
            2,
        )
        .into(),
        TypeModError::ApplyGenerative { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "This is a generative functor. It can only be applied to ()",
            ),
            2,
        )
        .into(),
        TypeModError::NotAllowedInFunctorBody { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "This expression creates fresh types.\nIt is not allowed inside applicative functors.",
            ),
            2,
        )
        .into(),
        TypeModError::IncompletePackedModule { loc, ty } => UserDiagnostic::new(
            format_compiler_error_report_with_unindented_break(
                arena,
                source,
                filename,
                *loc,
                "The type of this first-class module still contains type variables:",
                &format_package_type_expr_for_error(type_ctx, arena, *ty),
            ),
            2,
        )
        .into(),
        TypeModError::ScopingPack { loc, lid, ty } => UserDiagnostic::new(
            format_compiler_error_report_with_unindented_break(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "The type {} in this module cannot be exported.",
                    format_longident_for_report(arena, lid)
                ),
                &format!(
                    "Its type contains local dependencies:\n{}",
                    format_type_expr(type_ctx, *ty)
                ),
            ),
            2,
        )
        .into(),
        TypeModError::StructureExpected { loc, mty } => UserDiagnostic::new(
            format_structure_expected_report(type_ctx, arena, source, filename, *loc, mty),
            2,
        )
        .into(),
        TypeModError::WithNoComponent { loc, lid } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "The signature constrained by `with' has no component named {}",
                    format_longident_for_report(arena, lid)
                ),
            ),
            2,
        )
        .into(),
        TypeModError::WithMismatch { loc, lid, error } => UserDiagnostic::new(
            format_with_mismatch_report(type_ctx, arena, source, filename, *loc, lid, error),
            2,
        )
        .into(),
        TypeModError::WithChangesModuleAlias { loc, lid, id, path } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "This `with' constraint on {} changes {}, which is aliased \nin the constrained signature (as {}).",
                    format_longident_for_report(arena, lid),
                    path.name(),
                    id.name()
                ),
            ),
            2,
        )
        .into(),
        TypeModError::WithMakesApplicativeFunctorIllTyped {
            loc,
            lid,
            path,
            error,
        } => UserDiagnostic::new(
            format_with_makes_applicative_functor_ill_typed_report(
                type_ctx, arena, source, filename, *loc, lid, path, error,
            ),
            2,
        )
        .into(),
        TypeModError::WithCannotRemoveConstrainedType { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Destructive substitutions are not supported for constrained \ntypes (other than when replacing a type constructor with \na type constructor with the same arguments).",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::LiteralOverflow { loc, ty }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!(
                        "Integer literal exceeds the range of representable integers of type {ty}"
                    ),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::PolyvarLiteralOverflow { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Integer literal exceeds int32 range. Use float or BigInt if larger values are required.",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::InvalidStringEscapeSequence { loc }) => UserDiagnostic::new(
            format_compiler_error_report(arena, source, filename, *loc, "Invalid string escape sequence"),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::JsonLiteralOutsideExternal { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                crate::ast_payload::JSON_LITERAL_OUTSIDE_EXTERNAL_MESSAGE,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::UnknownLiteral {
            loc,
            literal,
            modifier,
        }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!("Unknown modifier '{modifier}' for literal {literal}{modifier}"),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ExprTypeClash {
            loc,
            trace,
            context,
            env,
        }) => {
            let env = env.and_then(|env| type_ctx.get_typed_env(env));
            let mut report = match env {
                Some(env) => format_expr_type_clash_report_ocaml(
                    type_ctx, arena, source, filename, *loc, trace, context, &env,
                ),
                None => format_expr_type_clash_report(
                    type_ctx, arena, source, filename, *loc, trace, context,
                ),
            };
            // Style escapes embedded in the message follow OCaml's
            // `Color.color_enabled`, which a printed warning switches to the
            // configured `-color` value (compiler/ext/misc.ml:337-392).
            if suppress_info_style {
                report = report
                    .replace("\x1b[1;31m", "")
                    .replace("\x1b[1;33m", "")
                    .replace("\x1b[0m", "");
            }
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::CoreError(TypeCoreError::PatternTypeClash {
            loc: Some(loc),
            trace,
            env,
        }) => {
            let env = env
                .and_then(|env| type_ctx.get_typed_env(env))
                .map(|env| (*env).clone())
                .unwrap_or_else(crate::types::Env::empty);
            let message = type_clash::render_error_message(|ppf| {
                type_clash::print_pattern_type_clash(ppf, type_ctx, &env, trace)
            });
            let mut report =
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message);
            if suppress_info_style {
                report = report
                    .replace("\x1b[1;31m", "")
                    .replace("\x1b[1;33m", "")
                    .replace("\x1b[2m", "")
                    .replace("\x1b[0m", "");
            }
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::CoreError(TypeCoreError::RecursiveLocalConstraint { loc, trace }) => {
            UserDiagnostic::new(
                format_recursive_local_constraint_report(
                    type_ctx, arena, source, filename, *loc, trace,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::PolymorphicLabel { loc, lid }) => {
            UserDiagnostic::new(
                format_polymorphic_label_report(arena, source, filename, *loc, lid),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::LabelMismatch {
            loc,
            lid,
            trace,
        }) => {
            UserDiagnostic::new(
                format_label_mismatch_report(
                    type_ctx,
                    arena,
                    source,
                    filename,
                    *loc,
                    lid,
                    trace,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::NotSubtype {
            loc,
            trace,
            trace2,
            context,
            env,
        }) => {
            let env = env
                .and_then(|env| type_ctx.get_typed_env(env))
                .map(|env| (*env).clone())
                .unwrap_or_else(crate::types::Env::empty);
            let message = type_clash::render_error_message(|ppf| {
                type_clash::print_not_subtype(ppf, type_ctx, &env, trace, trace2, context.as_ref())
            });
            let mut report =
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message);
            // See `ExprTypeClash`: style escapes follow `Color.color_enabled`.
            if suppress_info_style {
                report = report
                    .replace("\x1b[1;31m", "")
                    .replace("\x1b[1;33m", "")
                    .replace("\x1b[2m", "")
                    .replace("\x1b[0m", "");
            }
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::CoreError(TypeCoreError::LessGeneral {
            loc,
            kind,
            trace,
            env,
        }) => {
            let env = env
                .and_then(|env| type_ctx.get_typed_env(env))
                .map(|env| (*env).clone())
                .unwrap_or_else(crate::types::Env::empty);
            let message = type_clash::render_error_message(|ppf| {
                type_clash::print_less_general(ppf, type_ctx, &env, kind, trace)
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnqualifiedGadtPattern { loc, tpath, name }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!(
                        "The GADT constructor {} of type {}\nmust be written with its module prefix in this pattern.",
                        name,
                        format_type_path_for_report(tpath)
                    ),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnexpectedExistential { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This pattern introduces an existential type from a GADT constructor, which is not allowed here. Match on it inside a switch instead.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::NotAVariantType { loc, lid }) => {
            UserDiagnostic::new(
                format_not_a_variant_type_report(arena, source, filename, *loc, lid),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::TypeParamsNotSupported { loc, lid }) => {
            UserDiagnostic::new(
                format_type_params_not_supported_report(arena, source, filename, *loc, lid),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ApplyNonFunction { loc, typ }) => {
            UserDiagnostic::new(
                format_apply_non_function_report(type_ctx, arena, source, filename, *loc, *typ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::MisplacedLabelSyntax { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Label syntax is not supported in this position",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::TaggedTemplateNonTag { loc, typ }) => {
            UserDiagnostic::new(
                format_tagged_template_non_tag_report(
                    type_ctx, arena, source, filename, *loc, *typ,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::TooManyArguments {
            loc,
            in_function,
            ty,
        }) => UserDiagnostic::new(
            format_too_many_arguments_report(
                type_ctx,
                arena,
                source,
                filename,
                *loc,
                *in_function,
                *ty,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::AbstractWrongLabel { loc, label, ty }) => {
            UserDiagnostic::new(
                format_abstract_wrong_label_report(
                    type_ctx, source, filename, loc, label, *ty,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ApplyWrongLabel { loc, label, ty }) => {
            UserDiagnostic::new(
                format_apply_wrong_label_report(
                    type_ctx,
                    arena,
                    source,
                    filename,
                    *loc,
                    label,
                    *ty,
                    suppress_info_style,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::IncoherentLabelOrder { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report_with_unindented_break(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This labeled function is applied to arguments",
                    "in an order different from other calls.\nThis is only allowed when the real type is known.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::WrongName {
            loc,
            kind,
            ty,
            expected,
            path,
            name,
            alternatives,
            jsx_component_info,
            env,
        }) => UserDiagnostic::new(
            format_wrong_name_report(
                type_ctx,
                env.and_then(|env| type_ctx.get_typed_env(env)),
                arena,
                source,
                filename,
                *loc,
                kind,
                *ty,
                expected,
                path,
                name,
                alternatives,
                jsx_component_info.as_ref(),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::NameTypeMismatch {
            loc,
            kind,
            lid,
            expected,
            alternatives,
        }) => UserDiagnostic::new(
            format_name_type_mismatch_report(
                type_ctx,
                arena,
                source,
                filename,
                *loc,
                kind,
                lid,
                expected,
                alternatives,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::UndefinedMethod {
            loc: Some(loc),
            ty,
            method,
            alternatives,
        }) => UserDiagnostic::new(
            format_undefined_method_report(
                type_ctx,
                arena,
                source,
                filename,
                *loc,
                *ty,
                method,
                alternatives.as_deref(),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::ObjectFieldNotMutable { loc, ty, name }) => {
            let message = type_clash::render_error_message(|ppf| {
                type_clash::print_object_field_not_mutable(ppf, type_ctx, *ty, name)
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundValue {
            loc,
            name,
            qualifier,
            alternatives,
            module_suggestion,
        }) => {
            let mut report = format_unbound_value_report(
                arena,
                source,
                filename,
                *loc,
                name,
                qualifier.as_deref(),
                alternatives,
                module_suggestion.as_deref(),
            );
            // See `ExprTypeClash`: style escapes follow `Color.color_enabled`.
            if suppress_info_style {
                report = report
                    .replace("\x1b[1;33m", "")
                    .replace("\x1b[0m", "");
            }
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundModule {
            loc,
            name,
            alternatives,
        }) => UserDiagnostic::new(
            format_unbound_module_report(arena, source, filename, *loc, name, alternatives),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::UnboundModtype {
            loc,
            lid,
            alternatives,
        }) => UserDiagnostic::new(
            format_unbound_modtype_report(arena, source, filename, *loc, lid, alternatives),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::AccessFunctorAsStructure { loc, lid }) => {
            UserDiagnostic::new(
                format_access_functor_as_structure_report(arena, source, filename, *loc, lid),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::CannotScrapeAlias { loc, lid, path }) => {
            UserDiagnostic::new(
                format_cannot_scrape_alias_report(arena, source, filename, *loc, lid, path),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::IllegalReferenceToRecursiveModule { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Illegal recursive module reference",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundConstructor {
            loc,
            lid,
            alternatives,
        }) => {
            UserDiagnostic::new(
                format_unbound_constructor_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    lid,
                    alternatives,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundTypeConstructor {
            loc,
            lid,
            alternatives,
        }) => {
            UserDiagnostic::new(
                format_unbound_type_constructor_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    lid,
                    alternatives,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundTypeConstructorIncomplete {
            loc,
            path,
        }) => UserDiagnostic::new(
            format_unbound_type_constructor_incomplete_report(
                arena, source, filename, *loc, path,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::UnboundTypeVariable { loc, name }) => {
            UserDiagnostic::new(
                format_unbound_type_variable_report(arena, source, filename, *loc, name),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::InvalidVariableName { loc, name }) => {
            UserDiagnostic::new(
                format_invalid_variable_name_report(arena, source, filename, *loc, name),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::CannotQuantify { loc, name, ty }) => {
            UserDiagnostic::new(
                format_cannot_quantify_report(
                    type_ctx, arena, source, filename, *loc, name, *ty,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::MultipleConstraintsOnType { loc, lid }) => {
            UserDiagnostic::new(
                format_multiple_constraints_on_type_report(arena, source, filename, *loc, lid),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::SignatureExpected { loc }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "This module type is not a signature",
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::PresentHasConjunction { loc, label }) => {
            UserDiagnostic::new(
                format_present_has_conjunction_report(arena, source, filename, *loc, label),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::PresentHasNoType { loc, label }) => {
            UserDiagnostic::new(
                format_present_has_no_type_report(arena, source, filename, *loc, label),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::ConstructorMismatch {
            loc,
            actual,
            expected,
        }) => UserDiagnostic::new(
            format_constructor_mismatch_report(
                type_ctx, arena, source, filename, *loc, *actual, *expected,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::NotAVariant { loc, ty }) => UserDiagnostic::new(
            format_not_a_variant_report(type_ctx, arena, source, filename, *loc, *ty),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::MethodMismatch {
            loc,
            label,
            actual,
            expected,
        }) => UserDiagnostic::new(
            format_method_mismatch_report(
                type_ctx, arena, source, filename, *loc, label, *actual, *expected,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::TypeMismatch { loc, trace }) => {
            UserDiagnostic::new(
                format_type_mismatch_report(type_ctx, arena, source, filename, *loc, trace),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::AliasTypeMismatch { loc, trace }) => {
            UserDiagnostic::new(
                format_alias_type_mismatch_report(
                    type_ctx, arena, source, filename, *loc, trace,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::TypeArityMismatch {
            loc,
            lid,
            expected,
            provided,
        }) => UserDiagnostic::new(
            format_type_arity_mismatch_report(
                arena, source, filename, *loc, lid, *expected, *provided,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::LabelMultiplyDefined {
            loc,
            label,
            jsx_component_info,
        }) => UserDiagnostic::new(
            format_label_multiply_defined_report(
                arena,
                source,
                filename,
                *loc,
                label,
                jsx_component_info.as_ref(),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::LabelsMissing {
            loc,
            labels,
            jsx_component_info,
        }) => UserDiagnostic::new(
            format_labels_missing_report(
                arena,
                source,
                filename,
                *loc,
                labels,
                jsx_component_info.as_ref(),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::RecordRest { loc, error }) => {
            UserDiagnostic::new(
                format_compiler_error_report_with_unindented_continuation(
                    arena,
                    source,
                    filename,
                    *loc,
                    &error.message(arena),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::PrivateType { loc, ty }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!(
                        "Cannot create values of the private type {}",
                        format_type_expr(type_ctx, *ty)
                    ),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::LabelNotMutable { loc, lid }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!(
                        "The record field {} is not mutable",
                        format_longident_for_report(arena, lid)
                    ),
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::UnboundRecordField {
            loc,
            field_name,
            from_type,
            alternatives,
        }) => UserDiagnostic::new(
            format_unbound_record_field_report(
                type_ctx,
                arena,
                source,
                filename,
                *loc,
                field_name,
                *from_type,
                alternatives,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::FieldNotOptional { loc, name, typ }) => {
            UserDiagnostic::new(
                format_field_not_optional_report(
                    type_ctx, arena, source, filename, *loc, name, *typ,
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::FieldAccessOnDictType { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Direct field access on a dict is not supported. Use Dict.get instead.",
                ),
                2,
            )
            .into()
        }
        TypeModError::CoreError(TypeCoreError::NotAnObjectType { loc, ty }) => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("The type {} is not an object type", format_type_expr(type_ctx, *ty)),
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::OpenedObject { loc, path }) => {
            let report = match path {
                Some(path) => format_compiler_error_report_with_unindented_break(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Illegal open object type",
                    &path.name(),
                ),
                None => format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "Illegal open object type",
                ),
            };
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::SignatureMismatch { loc, error } => UserDiagnostic::new(
            format_compiler_error_report_raw_message(
                arena,
                source,
                filename,
                *loc,
                &crate::types::includemod::format_error(type_ctx, filename, error),
            ),
            2,
        )
        .into(),
        TypeModError::UnboundModtype {
            loc,
            lid,
            alternatives,
        } => UserDiagnostic::new(
            format_unbound_modtype_report(arena, source, filename, *loc, lid, alternatives),
            2,
        )
        .into(),
        TypeModError::TypeDeclTypeClash { loc, trace } => {
            // typedecl.ml:2176-2180.
            let message = type_clash::render_error_message(|ppf| {
                type_clash::print_report_unification_error(
                    ppf,
                    type_ctx,
                    trace,
                    "This type constructor expands to type",
                    "but is used here with type",
                )
            });
            UserDiagnostic::new(
                format_compiler_error_report_formatted(arena, source, filename, *loc, &message),
                2,
            )
            .into()
        }
        TypeModError::InconsistentConstraint { loc, trace } => UserDiagnostic::new(
            format_inconsistent_constraint_report(type_ctx, arena, source, filename, *loc, trace),
            2,
        )
        .into(),
        TypeModError::NullArityExternal { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "External identifiers must be functions",
            ),
            2,
        )
        .into(),
        TypeModError::FatalError { message } => UserDiagnostic::new(message.clone(), 2).into(),
        TypeModError::ConstraintFailed {
            loc,
            actual,
            expected,
        } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "Constraints are not satisfied in this type.\nType {} should be an instance of {}",
                    format_type_expr(type_ctx, *actual),
                    format_type_expr(type_ctx, *expected)
                ),
            ),
            2,
        )
        .into(),
        TypeModError::DefinitionMismatch { loc, ty, detail } => UserDiagnostic::new(
            format_definition_mismatch_report(
                type_ctx,
                arena,
                source,
                filename,
                *loc,
                *ty,
                detail.as_deref(),
            ),
            2,
        )
        .into(),
        TypeModError::BadFixedType { loc, reason } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("This fixed type {reason}"),
            ),
            2,
        )
        .into(),
        TypeModError::BadVariance {
            loc,
            param_index,
            actual,
            expected,
        } => UserDiagnostic::new(
            format_bad_variance_report(
                arena,
                source,
                filename,
                *loc,
                *param_index,
                *actual,
                *expected,
            ),
            2,
        )
        .into(),
        TypeModError::VaryingAnonymous { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "In this GADT definition, the variance of some parameter cannot be checked",
            ),
            2,
        )
        .into(),
        TypeModError::InvalidUntaggedVariantDefinition { loc, reason } => UserDiagnostic::new(
            format_compiler_error_report_from_location(
                source,
                filename,
                loc,
                &format!("This untagged variant definition is invalid: {reason}"),
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadCouldNotFindType { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "This type could not be found. It's only possible to spread variants that are known as the spread happens. This means for example that you can't spread variants in recursive definitions.",
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadInvalidType { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "This type is not a valid type to spread. It's only possible to spread other variants.",
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadHasTypeParams { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Type parameters are not supported in variant type spreads.",
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadDuplicateConstructor {
            loc,
            variant_name,
            constructor_name,
        } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "Variant {variant_name} has a constructor named {constructor_name}, but a constructor named {constructor_name} already exists in the variant it's spread into.\nYou cannot spread variants with overlapping constructors.",
                ),
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadUnboxedMismatch {
            loc,
            source_unboxed,
        } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "This variant is {}, but the variant where this is spread is not. Both variants unboxed configuration must match.",
                    if *source_unboxed {
                        "unboxed"
                    } else {
                        "not unboxed"
                    },
                ),
            ),
            2,
        )
        .into(),
        TypeModError::VariantSpreadTagMismatch { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "The @tag attribute does not match for this variant and the variant where this is spread. Both variants must have the same @tag attribute configuration, or no @tag attribute at all.",
            ),
            2,
        )
        .into(),
        TypeModError::RepeatedParameter { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "A type parameter occurs several times",
            ),
            2,
        )
        .into(),
        TypeModError::DuplicateConstructor { loc, name } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("Two constructors are named {name}"),
            ),
            2,
        )
        .into(),
        TypeModError::DuplicateLabel {
            loc,
            label,
            record_name,
        } => UserDiagnostic::new(
            format_duplicate_type_label_report(arena, source, filename, *loc, label, record_name),
            2,
        )
        .into(),
        TypeModError::RepeatedName {
            loc,
            kind,
            name,
            repeated_loc,
        } => UserDiagnostic::new(
            format_repeated_name_report(
                arena,
                source,
                filename,
                *loc,
                kind,
                name,
                *repeated_loc,
            ),
            2,
        )
        .into(),
        TypeModError::ObjectSpreadWithRecordField { loc, field_name } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "You cannot mix a record field with an object type spread.\nRemove the record field or change it to an object field (e.g. \"{field_name}\": ...)."
                ),
            ),
            2,
        )
        .into(),
        TypeModError::RecursiveAbbrev { loc, name } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("The type abbreviation {name} is cyclic"),
            ),
            2,
        )
        .into(),
        TypeModError::CycleInDef { loc, name, ty } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "The definition of {name} contains a cycle:\n{}",
                    format_type_expr(type_ctx, *ty)
                ),
            ),
            2,
        )
        .into(),
        TypeModError::ParametersDiffer {
            loc,
            path,
            actual,
            expected,
        } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "In the definition of {}, type {} should be {}",
                    path.name(),
                    format_type_expr(type_ctx, *actual),
                    format_type_expr(type_ctx, *expected)
                ),
            ),
            2,
        )
        .into(),
        TypeModError::InvalidAttribute { loc, message } => UserDiagnostic::new(
            format_compiler_error_report(arena, source, filename, *loc, message),
            2,
        )
        .into(),
        TypeModError::BadUnboxedAttribute { loc, message } => {
            let report = if message == "extensible variant types cannot be unboxed" {
                "This type cannot be unboxed because\nextensible variant types cannot be unboxed."
                    .to_string()
            } else {
                format!("This type cannot be unboxed because {message}.")
            };
            UserDiagnostic::new(
                format_compiler_error_report(arena, source, filename, *loc, &report),
                2,
            )
            .into()
        }
        TypeModError::BoxedAndUnboxed { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "A type cannot be boxed and unboxed at the same time.",
            ),
            2,
        )
        .into(),
        TypeModError::BadImmediateAttribute { loc } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                "Types marked with the immediate attribute must be\nnon-pointer types like int or bool",
            ),
            2,
        )
        .into(),
        TypeModError::CannotExtendPrivateType { loc, path } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("Cannot extend private type definition {}", path.name()),
            ),
            2,
        )
        .into(),
        TypeModError::NotExtensibleType { loc, path } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!("Type definition {} is not extensible", path.name()),
            ),
            2,
        )
        .into(),
        TypeModError::ExtensionMismatch {
            loc,
            path,
            mismatch,
        } => {
            let mismatch_message = match mismatch {
                TypeExtensionMismatch::Arity => "They have different arities.",
                TypeExtensionMismatch::Variance => "Their variances do not agree.",
            };
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    &format!(
                        "This extension does not match the definition of type {}\n{}",
                        path.name(),
                        mismatch_message
                    ),
                ),
                2,
            )
            .into()
        }
        TypeModError::RebindWrongType {
            loc,
            lid,
            actual,
            expected,
        } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "The constructor {} has type {} but was expected to be of type {}",
                    format_longident_for_report(arena, lid),
                    format_type_expr(type_ctx, *actual),
                    format_type_expr(type_ctx, *expected)
                ),
            ),
            2,
        )
        .into(),
        TypeModError::RebindPrivate { loc, lid } => UserDiagnostic::new(
            format_compiler_error_report(
                arena,
                source,
                filename,
                *loc,
                &format!(
                    "The constructor {} is private",
                    format_longident_for_report(arena, lid)
                ),
            ),
            2,
        )
        .into(),
        TypeModError::UnboundTypeVar {
            loc,
            name,
            detail: None,
            var: None,
        } => UserDiagnostic::new(
            format_unbound_type_variable_report(arena, source, filename, *loc, name),
            2,
        )
        .into(),
        TypeModError::UnboundTypeVar {
            loc,
            name,
            detail,
            var,
        } => UserDiagnostic::new(
            format_unbound_type_declaration_variable_report(
                type_ctx,
                arena,
                source,
                filename,
                *loc,
                name,
                detail.as_ref(),
                *var,
            ),
            2,
        )
        .into(),
        TypeModError::UnboundTypeVarInExtension { loc, var, args } => {
            // typedecl.ml:2202-2205: `tys_of_constr_args ext.ext_args`, then
            // `explain_unbound` over the first argument containing `var`.
            let tys: Vec<TypeExprRef> = match args {
                crate::types::ConstructorArguments::CstrTuple(tys) => tys.clone(),
                crate::types::ConstructorArguments::CstrRecord(labels) => {
                    labels.iter().map(|l| l.ld_type).collect()
                }
            };
            let first = "A type variable is unbound in this extension constructor";
            let report = match tys
                .iter()
                .find(|ti| crate::types::ctype::deep_occur(type_ctx, *var, **ti))
            {
                Some(ti) => {
                    let explanation = type_clash::render_error_message_at_column0(|ppf| {
                        type_clash::print_explain_unbound_type(ppf, type_ctx, *var, *ti)
                    });
                    format_compiler_error_report_with_unindented_break(
                        arena,
                        source,
                        filename,
                        *loc,
                        &format!("{first}."),
                        explanation.trim_end_matches('\n'),
                    )
                }
                None => format_compiler_error_report(arena, source, filename, *loc, first),
            };
            UserDiagnostic::new(report, 2).into()
        }
        TypeModError::UnboundTypeVarExt { loc, name } => UserDiagnostic::new(
            format_unbound_type_variable_report(arena, source, filename, *loc, name),
            2,
        )
        .into(),
        TypeModError::AstUntaggedVariantError { loc, error } => {
            let message = error.message_text();
            UserDiagnostic::new(
                format_compiler_error_report_from_location(source, filename, loc, &message),
                2,
            )
            .into()
        }
        TypeModError::NonrecursiveGadt { loc } => UserDiagnostic::new(
            format_compiler_error_report_raw_message(
                arena,
                source,
                filename,
                *loc,
                "  GADT case syntax cannot be used in a 'nonrec' block.",
            ),
            2,
        )
        .into(),
        TypeModError::NonGeneralizable { loc, typ } => UserDiagnostic::new(
            format_non_generalizable_report(source, filename, loc, type_ctx, *typ),
            2,
        )
        .into(),
        TypeModError::NonGeneralizableModule { loc, mty } => UserDiagnostic::new(
            format_non_generalizable_module_report(source, filename, loc, type_ctx, mty),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::InlinedRecordEscape { loc }) => {
            UserDiagnostic::new(
                format_compiler_error_report(
                    arena,
                    source,
                    filename,
                    *loc,
                    "This use of an inlined record is not allowed: its anonymous type would escape its constructor scope.\nPossible solutions: \n- Destructure the fields you're interested in from the inline record\n- Change the underlying type to use a defined record as payload instead of an inline record. That will let you use the payload without destructuring it first",
                ),
                2,
            )
            .into()
        }
        _ => anyhow!("Type checking failed: {err:?}"),
    }
}

fn persistent_env_error_to_anyhow(error: PersistentEnvError, filename: &str) -> anyhow::Error {
    if let PersistentEnvError::InterfaceRead { message } = error {
        let mut output = String::new();
        push_compiler_report_intro(&mut output, "We've found a bug for you!");
        push_compiler_report_location(&mut output, filename);
        output.push_str("  ");
        output.push_str(&message);
        output.push_str("\n\n");
        return UserDiagnostic::new(output, 2).into();
    }

    let message = match error {
        PersistentEnvError::InterfaceRead { .. } => unreachable!(),
        PersistentEnvError::IllegalRenaming {
            expected, actual, ..
        } => format!(
            "You referred to the module {expected}, but we've found one called {actual} instead.\nIs the name's casing right?"
        ),
        PersistentEnvError::InconsistentImport {
            name,
            source1,
            source2,
        } => {
            let source1 = format_persistent_env_path(&source1);
            let source2 = format_persistent_env_path(&source2);
            format!(
                "\x1b[1;33mIt's possible that your build is stale.\x1b[0m\nTry to clean the artifacts and build again?\n\n\x1b[1;33mHere's the original error message\x1b[0m\nThe files {source1}\nand {source2}\nmake inconsistent assumptions over interface {name}"
            )
        }
    };
    UserDiagnostic::new(format_compiler_error_report_for_file(filename, &message), 2).into()
}

fn module_path_resolution_error_to_anyhow(
    error: ModulePathResolutionError,
    filename: &str,
) -> anyhow::Error {
    let message = match error {
        ModulePathResolutionError::CmjNotFound { module_name } => format!(
            "{module_name} not found, it means either the module does not exist or it is a namespace"
        ),
        ModulePathResolutionError::JsNotFound { js_file } => {
            format!("{js_file} not found, needed in script mode ")
        }
        ModulePathResolutionError::MissingMlDependency { module_name } => {
            format!("Missing dependency {module_name} in search path")
        }
        ModulePathResolutionError::DependencyScriptModuleDependentNot { module_name } => {
            format!("{module_name} is compiled in script mode while its dependent is not")
        }
    };
    UserDiagnostic::new(format_compiler_error_report_for_file(filename, &message), 2).into()
}

fn check_module_path_resolution_errors(
    program: &DepsProgram,
    resolver: &ModulePathResolver,
    filename: &str,
) -> Result<()> {
    for module in &program.modules {
        if let Some(error) = resolver.module_path_resolution_error(module) {
            return Err(module_path_resolution_error_to_anyhow(error, filename));
        }
    }
    Ok(())
}

fn format_persistent_env_path(path: &str) -> String {
    // OCaml reports the stored persistent-structure filename directly through
    // `Location.print_filename` in compiler/ml/env.ml:2110-2119.
    path.to_string()
}

fn push_compiler_report_intro(output: &mut String, intro: &str) {
    // OCaml compiler/ml/location.ml:88-95 colors the diagnostic intro with
    // the `error`, `warning`, or `info` tag after bsc's color mode has been
    // installed by compiler/ml/location.ml:45-47.
    output.push_str("\n  ");
    output.push_str(&code_frame::colorize_intro(intro, true));
    output.push('\n');
}

fn push_compiler_report_location(output: &mut String, location: &str) {
    // OCaml compiler/ml/location.ml:65-85 prints filenames through the
    // `filename` tag and line/column ranges through the `dim` tag.
    output.push_str("  ");
    output.push_str(&code_frame::colorize_location(location));
    output.push_str("\n\n");
}

/// OCaml `Bs_exception.Bs_duplicate_exports` ("%s is exported twice",
/// compiler/depends/bs_exception.ml:50), reported without a location.
fn duplicate_export_error(filename: &str, name: &str) -> anyhow::Error {
    UserDiagnostic::new(
        format_compiler_error_report_for_file(filename, &format!("{name} is exported twice")),
        2,
    )
    .into()
}

fn format_compiler_error_report_for_file(filename: &str, message: &str) -> String {
    let mut output = String::new();
    push_compiler_report_intro(&mut output, "We've found a bug for you!");
    push_compiler_report_location(&mut output, filename);
    let message = code_frame::apply_message_styles(message);
    for line in message.lines() {
        output.push_str("  ");
        output.push_str(line);
        output.push('\n');
    }
    output.push('\n');
    output
}

fn format_duplicate_type_label_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &str,
    record_name: &Option<String>,
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let message = if let Some(record_name) = record_name {
        format!(
            "The field {INFO}{label}{RESET} is defined several times in the record {INFO}{record_name}{RESET}. Fields can only be added once to a record."
        )
    } else {
        format!(
            "The field {INFO}{label}{RESET} is defined several times in this record. Fields can only be added once to a record."
        )
    };
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_repeated_name_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    kind: &str,
    name: &str,
    repeated_loc: LocIdx,
) -> String {
    let repeated = code_frame::format_location(
        filename,
        arena.loc_start(repeated_loc),
        arena.loc_end(repeated_loc),
    );
    // OCaml compiler/ml/typemod.ml:1851-1855:
    // "@[Multiple definition of the %s name %s @ at @{<loc>%a@}@ @ Names must be
    //  unique in a given structure or signature.@]"
    let mut buf = Vec::new();
    {
        let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
        ppf.set_margin(76);
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.print(format_args!(
            "Multiple definition of the {kind} name {name} "
        ));
        ppf.space();
        ppf.str("at ");
        if code_frame::should_enable_color() {
            // `@{<loc>...@}` around `Location.print_loc`, which prints
            // `@{<filename>%s@}:@{<dim>%s@}` (compiler/ml/location.ml:75-93);
            // semantic tag markers take no width (compiler/ext/misc.ml:327-350).
            let (file, range) = repeated.split_once(':').unwrap_or((repeated.as_str(), ""));
            ppf.string_as(0, "\x1b[1m");
            ppf.string_as(0, "\x1b[36m");
            ppf.str(file);
            ppf.string_as(0, "\x1b[0m");
            if !range.is_empty() {
                ppf.str(":");
                ppf.string_as(0, "\x1b[2m");
                ppf.str(range);
                ppf.string_as(0, "\x1b[0m");
            }
            ppf.string_as(0, "\x1b[0m");
        } else {
            ppf.str(&repeated);
        }
        ppf.space();
        ppf.space();
        ppf.str("Names must be unique in a given structure or signature.");
        ppf.close_box();
        ppf.flush();
    }
    let message = String::from_utf8(buf).unwrap_or_default();
    format_compiler_error_report(arena, source, filename, loc, &message)
}

/// `non_generalizable_msg` (typemod.ml:1805-1812) around the fallback
/// message of `Non_generalizable` / `Non_generalizable_module`
/// (typemod.ml:1856-1874), inside `@[<v>...@]`.
fn render_non_generalizable_message(intro: &str, rendered_type: &str) -> String {
    use crate::types::printtyp::{TAG_ERROR, TAG_INFO, TAG_RESET};
    type_clash::render_error_message(|ppf| {
        ppf.open_vbox(0);
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.str(intro);
        ppf.cut();
        ppf.string_as(0, TAG_ERROR);
        ppf.str(rendered_type);
        ppf.string_as(0, TAG_RESET);
        ppf.close_box();
        ppf.cut();
        ppf.cut();
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.str("This happens when the type system senses there's a mutation/side-effect,");
        ppf.space();
        ppf.str("in combination with a polymorphic value.");
        ppf.cut();
        ppf.string_as(0, TAG_INFO);
        ppf.str("Using or annotating that value usually solves it.");
        ppf.string_as(0, TAG_RESET);
        ppf.close_box();
        ppf.close_box();
    })
}

fn format_compiler_error_report_formatted_from_location(
    source: &str,
    filename: &str,
    loc: &Location,
    message: &str,
) -> String {
    let mut output = String::new();
    push_compiler_error_report_header_from_location(&mut output, source, filename, loc);
    output.push_str(&code_frame::apply_message_styles(message));
    output.push_str("\n\n");
    output
}

fn format_non_generalizable_report(
    source: &str,
    filename: &str,
    loc: &Location,
    type_ctx: &TypeContext,
    typ: TypeExprRef,
) -> String {
    let rendered_type = format_non_generalizable_type_expr(type_ctx, typ);
    let message = render_non_generalizable_message(
        "This expression's type contains type variables that cannot be generalized:",
        &rendered_type,
    );
    format_compiler_error_report_formatted_from_location(source, filename, loc, &message)
}

fn format_non_generalizable_module_report(
    source: &str,
    filename: &str,
    loc: &Location,
    type_ctx: &TypeContext,
    mty: &crate::types::decl::ModuleType,
) -> String {
    let rendered_type = crate::types::includemod::format_module_type_show_weak(type_ctx, mty);
    let message = render_non_generalizable_message(
        "The type of this module contains type variables that cannot be generalized:",
        &rendered_type,
    );
    format_compiler_error_report_formatted_from_location(source, filename, loc, &message)
}

fn format_interface_not_compiled_report(
    source: &str,
    filename: &str,
    file_name_idx: StrIdx,
    interface_name: &str,
) -> String {
    let loc = Location::in_file(file_name_idx);
    let message = format!("Could not find the .cmi file for interface\n{interface_name}.");
    format_compiler_error_report_from_location(source, filename, &loc, &message)
}

fn interface_source_name(source_file: &str) -> String {
    let mut intf = std::path::PathBuf::from(source_file);
    intf.set_extension("resi");
    intf.to_string_lossy().into_owned()
}

fn parsed_signature_has_gentype_ignore_interface(
    arena: &ParseArena,
    signature: &Signature,
) -> bool {
    // OCaml compiler/gentype/GenTypeMain.ml:93-134 discovers
    // @@genType.ignoreInterface while scanning the interface CMT before
    // deciding whether the implementation artifact should own GenType output.
    signature.iter().any(|item| match item.psig_desc.as_ref() {
        SignatureItemDesc::Psig_attribute(attribute) => {
            let attributes = Attributes::from_vec(vec![attribute.as_ref().clone()]);
            crate::gentype::annotation::get_attribute_payload(
                arena,
                crate::gentype::annotation::tag_is_gentype_ignore_interface,
                &attributes,
            )
            .is_some()
        }
        _ => false,
    })
}

fn interface_source_has_gentype_ignore_interface(source_file: &str) -> bool {
    let intf_name = interface_source_name(source_file);
    let Ok(bytes) = std::fs::read(&intf_name) else {
        return false;
    };
    let source = crate::source_text::latin1_bytes_to_string(bytes);
    let mut parser = Parser::new(&intf_name, &source);
    let signature = module::parse_signature(&mut parser);
    if parser.has_errors() {
        return false;
    }
    parsed_signature_has_gentype_ignore_interface(parser.arena(), &signature)
}

fn source_has_interface(options: &CompilerOptions, source_file: &str) -> bool {
    options.assume_compiled_interface || std::path::Path::new(&format!("{source_file}i")).exists()
}

fn compiled_interface_file_exists(options: &CompilerOptions, source_file: &str) -> bool {
    let module_name = module_name_from_source_filename(source_file);
    let filename = format!("{module_name}.cmi");
    let uncapitalized = filename
        .chars()
        .next()
        .map(|ch| ch.to_lowercase().collect::<String>() + &filename[ch.len_utf8()..])
        .unwrap_or_else(|| filename.clone());

    build_load_path(options)
        .iter()
        .any(|dir| dir.join(&uncapitalized).exists() || dir.join(&filename).exists())
}

fn interface_cmi_name(source_file: &str) -> String {
    let mut intf = std::path::PathBuf::from(source_file);
    intf.set_extension("cmi");
    intf.to_string_lossy().into_owned()
}

fn push_compiler_error_report_header_from_location(
    output: &mut String,
    source: &str,
    filename: &str,
    loc: &Location,
) {
    push_compiler_report_intro(output, "We've found a bug for you!");
    if !code_frame::has_printable_range(&loc.loc_start, &loc.loc_end) {
        push_compiler_report_location(output, filename);
    } else {
        let location = code_frame::format_location(filename, &loc.loc_start, &loc.loc_end);
        push_compiler_report_location(output, &location);
        output.push_str(&code_frame::print(source, &loc.loc_start, &loc.loc_end));
        output.push('\n');
    }
}

fn push_compiler_error_report_header(
    output: &mut String,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
) {
    push_compiler_report_intro(output, "We've found a bug for you!");
    let start_pos = arena.loc_start(loc);
    let end_pos = arena.loc_end(loc);
    if !code_frame::has_printable_range(start_pos, end_pos) {
        // `Location.show_filename` (location.ml:38): the location's own file
        // name unless it is the `_none_` placeholder.
        let pos_fname = arena.get_string(start_pos.file_name);
        let shown = if pos_fname.is_empty() || pos_fname == "_none_" {
            filename
        } else {
            pos_fname
        };
        push_compiler_report_location(output, shown);
    } else {
        let location = code_frame::format_location(filename, start_pos, end_pos);
        push_compiler_report_location(output, &location);
        output.push_str(&code_frame::print(source, start_pos, end_pos));
        output.push('\n');
    }
}

fn format_compiler_error_report_from_location(
    source: &str,
    filename: &str,
    loc: &Location,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header_from_location(&mut output, source, filename, loc);

    let message = code_frame::apply_message_styles(message);
    for line in message.lines() {
        output.push_str("  ");
        output.push_str(line);
        output.push('\n');
    }
    output.push('\n');
    output
}

fn push_compiler_error_report_header_from_external_location(
    output: &mut String,
    source: Option<&str>,
    filename: &str,
    loc: &Location,
) {
    push_compiler_report_intro(output, "We've found a bug for you!");
    if !code_frame::has_printable_range(&loc.loc_start, &loc.loc_end) {
        push_compiler_report_location(output, filename);
    } else {
        let location = code_frame::format_location(filename, &loc.loc_start, &loc.loc_end);
        push_compiler_report_location(output, &location);
        if let Some(source) = source {
            output.push_str(&code_frame::print(source, &loc.loc_start, &loc.loc_end));
            output.push('\n');
        }
    }
}

fn format_compiler_error_report_from_external_location(
    type_ctx: &TypeContext,
    current_filename: &str,
    loc: &Location,
    message: &str,
) -> String {
    let loc_filename = type_ctx
        .resolve_cmi_longident_component(loc.loc_start.file_name)
        .filter(|name| !name.is_empty() && name != "_none_")
        .unwrap_or_else(|| current_filename.to_string());
    let loc_source = std::fs::read_to_string(&loc_filename).ok();
    let mut output = String::new();

    push_compiler_error_report_header_from_external_location(
        &mut output,
        loc_source.as_deref(),
        &loc_filename,
        loc,
    );

    for line in message.lines() {
        output.push_str("  ");
        output.push_str(line);
        output.push('\n');
    }
    output.push('\n');
    output
}

fn format_compiler_error_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);

    let message = code_frame::apply_message_styles(message);
    for line in message.lines() {
        output.push_str("  ");
        output.push_str(line);
        output.push('\n');
    }
    output.push('\n');
    output
}

/// The error OCaml raises when writing a binary AST reaches an `[%error]`
/// extension: `Location.Error (Builtin_attributes.error_of_extension ext)`
/// from `Depend.handle_extension` (depend.ml:92-96).
pub fn error_extension_to_anyhow(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    extension: &crate::parser::ast::Extension,
) -> anyhow::Error {
    match crate::types::typecore::builtin_extension_error(arena, extension) {
        TypeCoreError::ExtensionError(error) => UserDiagnostic::new(
            format_builtin_extension_error_report(arena, source, filename, &error),
            2,
        )
        .into(),
        _ => UserDiagnostic::new(String::new(), 2).into(),
    }
}

fn format_builtin_extension_error_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    error: &BuiltinExtensionError,
) -> String {
    let mut output =
        format_compiler_error_report(arena, source, filename, error.loc, &error.message);
    for sub in &error.sub {
        output.push_str(&format_builtin_extension_error_report(
            arena, source, filename, sub,
        ));
    }
    output
}

fn format_compiler_error_report_with_unindented_continuation(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);
    output.push_str("  ");
    output.push_str(message);
    if !message.ends_with('\n') {
        output.push('\n');
    }
    output.push('\n');
    output
}

fn format_compiler_error_report_with_unindented_break(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    first_line: &str,
    second_line: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);
    output.push_str("  ");
    output.push_str(first_line);
    output.push('\n');
    output.push_str(second_line);
    output.push_str("\n\n");
    output
}

fn format_cannot_apply_module_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    mty: &crate::types::decl::ModuleType,
    origin: Option<&crate::types::Path>,
) -> String {
    // typemod.ml:1816 "@[This module is not a functor; it has type@ %a@]".
    let rendered_module_type = match origin {
        Some(origin) => {
            crate::types::includemod::format_persistent_module_type(type_ctx, mty, origin)
        }
        None => format_typemod_module_type(type_ctx, mty),
    };
    let message = type_clash::render_error_message(|ppf| {
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.str("This module is not a functor; it has type");
        ppf.space();
        ppf.string_as(rendered_module_type.len(), &rendered_module_type);
        ppf.close_box();
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_missing_module_message(
    path: &crate::types::path::Path,
    expanded: &crate::types::path::Path,
) -> String {
    let head = expanded.head().name().to_string();
    if path.same(expanded) {
        format!(
            "Internal path {} is dangling.\nThe compiled interface for module {head} was not found.",
            path.name()
        )
    } else {
        format!(
            "Internal path {} expands to {} which is dangling.\nThe compiled interface for module {head} was not found.",
            path.name(),
            expanded.name()
        )
    }
}

fn format_cannot_eliminate_dependency_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    mty: &crate::types::decl::ModuleType,
) -> String {
    let rendered_module_type =
        crate::types::includemod::format_module_type_full_paths(type_ctx, mty);
    // typemod.ml:1819-1823: "@[This functor has type@ %a@ The parameter
    // cannot be eliminated in the result type.@  Bind the argument to a
    // module identifier.@]"; the outcome printer hands Format the module
    // type as one string (res_outcome_printer.ml:1063-1065).
    let message = type_clash::render_error_message(|ppf| {
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.str("This functor has type");
        ppf.space();
        ppf.string_as(rendered_module_type.len(), &rendered_module_type);
        ppf.space();
        ppf.str("The parameter cannot be eliminated in the result type.");
        ppf.space();
        ppf.str(" Bind the argument to a module identifier.");
        ppf.close_box();
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_structure_expected_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    mty: &crate::types::decl::ModuleType,
) -> String {
    // typemod.ml:1826 "@[This module is not a structure; it has type@ %a".
    let rendered_module_type = format_typemod_module_type(type_ctx, mty);
    let message = type_clash::render_error_message(|ppf| {
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        ppf.str("This module is not a structure; it has type");
        ppf.space();
        ppf.string_as(rendered_module_type.len(), &rendered_module_type);
        ppf.close_box();
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_typemod_module_type(
    type_ctx: &TypeContext,
    mty: &crate::types::decl::ModuleType,
) -> String {
    // `Printtyp.modtype` prints values with `tree_of_type_scheme`, which names
    // non-generalized variables `'_weakN` (printtyp.ml).
    crate::types::includemod::format_module_type_show_weak(type_ctx, mty)
}

fn format_with_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    error: &crate::types::includemod::IncludeModError,
) -> String {
    let mut message = String::new();
    message.push_str("  In this `with' constraint, the new definition of ");
    message.push_str(&format_longident_for_report(arena, lid));
    message.push('\n');
    message.push_str("  does not match its original definition in the constrained signature:\n");
    message.push_str(
        &crate::types::includemod::format_error_without_signature_header(type_ctx, filename, error),
    );
    format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
}

fn format_with_makes_applicative_functor_ill_typed_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    path: &crate::types::Path,
    error: &crate::types::includemod::IncludeModError,
) -> String {
    let mut message = String::new();
    let lid_text = format_longident_for_report(arena, lid);
    message.push_str("  This `with' constraint on ");
    message.push_str(&lid_text);
    message.push_str(" makes the applicative functor \n");
    message.push_str("  type ");
    message.push_str(&path.name());
    message.push_str(" ill-typed in the constrained signature:\n");
    let include_error =
        crate::types::includemod::format_error_without_signature_header(type_ctx, filename, error);
    message.push_str(&include_error);
    format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
}

fn format_not_a_variant_type_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
) -> String {
    format_compiler_error_report_with_unindented_break(
        arena,
        source,
        filename,
        loc,
        &format!("The type {}", format_longident_for_report(arena, lid)),
        "is not a variant type",
    )
}

fn format_type_params_not_supported_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
) -> String {
    format_compiler_error_report_with_unindented_break(
        arena,
        source,
        filename,
        loc,
        &format!("The type {}", format_longident_for_report(arena, lid)),
        "has type parameters, but type parameters are not supported here.",
    )
}

fn format_unbound_type_constructor_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    alternatives: &[String],
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let name = format_longident_for_report(arena, lid);
    let spellcheck_name = arena.get_string(lid.last_idx());
    if let Some(hint) = super_spellcheck_hint(spellcheck_name, alternatives) {
        return format_compiler_error_report(
            arena,
            source,
            filename,
            loc,
            &format!(
                "This type constructor, `{name}`, can't be found.\n\n\n{INFO}Hint: Did you mean {hint}?{RESET}"
            ),
        );
    }

    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!(
            "This type constructor, `{name}`, can't be found.\nIf you wanted to write a recursive type, don't forget the `rec` in `type rec`"
        ),
    )
}

fn format_unbound_type_constructor_incomplete_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    path: &crate::types::Path,
) -> String {
    let name = format_type_path_for_report(path);
    format_compiler_error_report_with_unindented_break(
        arena,
        source,
        filename,
        loc,
        &format!("The type constructor {name}"),
        "is not yet completely defined",
    )
}

fn format_unbound_type_variable_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
) -> String {
    let mut report = format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("Unbound type parameter {name}"),
    );
    report.push('\n');
    report
}

fn format_unbound_type_declaration_variable_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
    detail: Option<&UnboundTypeVarDetail>,
    var: Option<TypeExprRef>,
) -> String {
    // typedecl.ml:2182-2201: the period starts `explain_unbound_gen`'s
    // explanation (".@.@[In ...").
    let mut message = String::from("  A type variable is unbound in this type declaration");
    if let Some(detail) = detail {
        if let UnboundTypeVarDetail::Constructor {
            name: case_name,
            args,
        } = detail
        {
            // typedecl.ml:2185-2193: `typ ti` is a fresh tuple of the
            // argument types; the case prints `Printtyp.constructor_arguments`.
            let tys = match args {
                crate::types::ConstructorArguments::CstrTuple(tys) => tys.clone(),
                crate::types::ConstructorArguments::CstrRecord(labels) => {
                    labels.iter().map(|l| l.ld_type).collect()
                }
            };
            let typ_ti = type_ctx.new_generic_type(TypeDesc::Ttuple(tys.into()));
            let mut printer = TypeExprPrinter::new(type_ctx);
            printer.reset();
            printer.mark_loops(typ_ti);
            if let Some(var) = var {
                let ty0 = type_ctx.new_generic_type(TypeDesc::Tobject { fields: var });
                printer.mark_loops(ty0);
            }
            let args_text = printer.printtyp.constructor_arguments(args);
            let var_text = match var {
                Some(var) => printer.print(var),
                None => name.to_string(),
            };
            message.push_str(".\n");
            message.push_str(&format_explain_unbound_gen(
                "case",
                &format!("{case_name} of {args_text}"),
                &var_text,
            ));
            return format_compiler_error_report_raw_message(
                arena, source, filename, loc, &message,
            );
        }
        let (kwd, label, ty) = match detail {
            UnboundTypeVarDetail::Constructor { .. } => unreachable!(),
            UnboundTypeVarDetail::Type { ty } => ("type", String::new(), *ty),
            UnboundTypeVarDetail::Case {
                name: case_name,
                ty,
                polymorphic,
            } => (
                "case",
                if *polymorphic {
                    format!("`{case_name} of ")
                } else {
                    format!("{case_name} of ")
                },
                *ty,
            ),
            UnboundTypeVarDetail::Field {
                name: field_name,
                ty,
            } => ("field", format!("{field_name}: "), *ty),
            UnboundTypeVarDetail::Method {
                name: method_name,
                ty,
            } => ("field", format!("{method_name}: "), *ty),
        };
        // `Typedecl.explain_unbound_gen` (typedecl.ml:2080-2090):
        // `reset_and_mark_loops_list [typ ti; ty0]` with
        // `ty0 = newgenty (Tobject (tv, ref None))` to force aliasing, then
        // print `typ ti` and `tv` in that naming session.
        let mut printer = TypeExprPrinter::new(type_ctx);
        printer.reset();
        printer.mark_loops(ty);
        if let Some(var) = var {
            let ty0 = type_ctx.new_generic_type(TypeDesc::Tobject { fields: var });
            printer.mark_loops(ty0);
        }
        let ty_text = printer.format(ty);
        let var_text = match var {
            Some(var) => printer.print(var),
            None => name.to_string(),
        };
        message.push_str(".\n");
        message.push_str(&format_explain_unbound_gen(
            kwd,
            &format!("{label}{ty_text}"),
            &var_text,
        ));
    }
    format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
}

/// `explain_unbound_gen` (typedecl.ml:2080-2090) after the `.@.` flush:
/// `@[<hov2>In %s@ %a@;<1 -2>the variable %a is unbound@]` from column 0.
fn format_explain_unbound_gen(kwd: &str, item: &str, var: &str) -> String {
    type_clash::render_error_message_at_column0(|ppf| {
        ppf.open_hovbox(2);
        ppf.str(&format!("In {kwd}"));
        ppf.space();
        ppf.string_as(item.chars().count(), item);
        ppf.break_(1, -2);
        ppf.str("the variable ");
        ppf.string_as(var.chars().count(), var);
        ppf.str(" is unbound");
        ppf.close_box();
    })
}

fn format_unbound_modtype_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    alternatives: &[String],
) -> String {
    let name = format_longident_for_report(arena, lid);
    if let Some(hint) = spellcheck_hint(&name, alternatives) {
        let mut raw_message = String::new();
        raw_message.push_str("  Unbound module type ");
        raw_message.push_str(&name);
        raw_message.push('\n');
        raw_message.push_str("Hint: Did you mean ");
        raw_message.push_str(&hint);
        raw_message.push('?');
        format_compiler_error_report_raw_message(arena, source, filename, loc, &raw_message)
    } else {
        format_compiler_error_report(
            arena,
            source,
            filename,
            loc,
            &format!("Unbound module type {name}"),
        )
    }
}

fn format_invalid_variable_name_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
) -> String {
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!(
            "The type variable name {name} is not allowed; type variable names cannot start with an underscore."
        ),
    )
}

fn format_cannot_quantify_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
    ty: TypeExprRef,
) -> String {
    let reason = if crate::types::btype::is_tvar(type_ctx, ty) {
        "it escapes its scope"
    } else if crate::types::btype::is_tunivar(type_ctx, ty) {
        "it is already bound to another variable"
    } else {
        "it is not a variable"
    };
    let message = format_cannot_quantify_message(name, reason);
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_cannot_quantify_message(name: &str, reason: &str) -> String {
    let mut buf = Vec::new();
    {
        let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
        ppf.set_margin(76);
        ppf.open_hovbox(0);
        ppf.print(format_args!(
            "The universal type variable '{name} cannot be generalized:"
        ));
        ppf.space();
        ppf.print(format_args!("{reason}."));
        ppf.close_box();
        ppf.flush();
    }
    String::from_utf8(buf).unwrap_or_default()
}

fn format_multiple_constraints_on_type_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
) -> String {
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!(
            "Multiple constraints for type {}",
            format_longident_for_report(arena, lid)
        ),
    )
}

fn format_present_has_conjunction_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &str,
) -> String {
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("The present constructor {label} has a conjunctive type"),
    )
}

fn format_present_has_no_type_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &str,
) -> String {
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("The present constructor {label} has no type"),
    )
}

fn format_constructor_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_constructor_mismatch(ppf, type_ctx, actual, expected)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_not_a_variant_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    ty: TypeExprRef,
) -> String {
    let message =
        type_clash::render_error_message(|ppf| type_clash::print_not_a_variant(ppf, type_ctx, ty));
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_method_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &str,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_method_mismatch(ppf, type_ctx, label, actual, expected)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_type_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> String {
    // Typetexp `Type_mismatch` (typetexp.ml:790-794).
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_report_unification_error(
            ppf,
            type_ctx,
            trace,
            "This type",
            "should be an instance of type",
        )
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_alias_type_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> String {
    // Typetexp `Alias_type_mismatch` (typetexp.ml:795-799).
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_report_unification_error(
            ppf,
            type_ctx,
            trace,
            "This alias is bound to type",
            "but is used as an instance of type",
        )
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_type_arity_mismatch_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    expected: usize,
    provided: usize,
) -> String {
    let name = format_longident_for_report(arena, lid);
    let plural = |count: usize| if count == 1 { "" } else { "s" };
    // typetexp.ml:776-789: both messages are laid out in a Format box.
    let message = format_boxed_message(|ppf| {
        if expected == 0 {
            ppf.print(format_args!(
                "The type `{name}` is not generic so expects no arguments,"
            ));
            ppf.space();
            ppf.print(format_args!(
                "but is here given {provided} argument{}.",
                plural(provided)
            ));
            ppf.space();
            ppf.str("Have you tried removing the angular brackets `<` and `>` and the");
            ppf.space();
            ppf.print(format_args!(
                "arguments within them and just writing `{name}` instead? "
            ));
        } else {
            ppf.print(format_args!("The type constructor `{name}`"));
            ppf.space();
            ppf.print(format_args!(
                "expects {expected} type argument{},",
                plural(expected)
            ));
            ppf.space();
            ppf.print(format_args!("but is given {provided}"));
        }
    });
    format_compiler_error_report(arena, source, filename, loc, &message)
}

/// Lay out a report message printed as `@[...@]` by OCaml: a `Pp_box` in the
/// report body, whose two-column indent leaves a 76-column margin.
fn format_boxed_message(
    f: impl FnOnce(&mut crate::parser::formatter::Formatter<&mut Vec<u8>>),
) -> String {
    let mut buf = Vec::new();
    {
        let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
        ppf.set_margin(76);
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 0);
        f(&mut ppf);
        ppf.close_box();
        ppf.flush();
    }
    String::from_utf8(buf).unwrap_or_default()
}

fn format_inconsistent_constraint_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> String {
    if !trace.is_empty() {
        // typedecl.ml:2171-2175: "The type constraints are not consistent.@."
        // then `Printtyp.report_unification_error` from column 0.
        let unification = type_clash::render_error_message_at_column0(|ppf| {
            type_clash::print_report_unification_error(
                ppf,
                type_ctx,
                trace,
                "Type",
                "is not compatible with type",
            )
        });
        format_compiler_error_report_with_unindented_break(
            arena,
            source,
            filename,
            loc,
            "The type constraints are not consistent.",
            unification.trim_end_matches('\n'),
        )
    } else {
        format_compiler_error_report(
            arena,
            source,
            filename,
            loc,
            "The type constraints are not consistent.",
        )
    }
}

fn format_definition_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    ty: TypeExprRef,
    detail: Option<&str>,
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_definition_mismatch(ppf, type_ctx, ty, detail)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn variance_suffix(n: usize) -> &'static str {
    let is_teen = (n % 100) / 10 == 1;
    match n % 10 {
        1 if !is_teen => "st",
        2 if !is_teen => "nd",
        3 if !is_teen => "rd",
        _ => "th",
    }
}

fn format_variance((co, cn, inj): (bool, bool, bool)) -> String {
    let mut output = String::new();
    if inj {
        output.push_str("injective ");
    }
    match (co, cn) {
        (true, true) => output.push_str("invariant"),
        (true, false) => output.push_str("covariant"),
        (false, true) => output.push_str("contravariant"),
        (false, false) if inj => {}
        (false, false) => output.push_str("unrestricted"),
    }
    output
}

fn format_bad_variance_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    param_index: i32,
    actual: (bool, bool, bool),
    expected: (bool, bool, bool),
) -> String {
    let message = match param_index {
        -1 => format!(
            "In this definition, a type variable has a variance that\nis not reflected by its occurrence in type parameters.\nIt was expected to be {}, but it is {}.",
            format_variance(expected),
            format_variance(actual),
        ),
        -2 => "In this definition, a type variable cannot be deduced\nfrom the type parameters."
            .to_string(),
        -3 => format!(
            "In this definition, a type variable has a variance that\ncannot be deduced from the type parameters.\nIt was expected to be {}, but it is {}.",
            format_variance(expected),
            format_variance(actual),
        ),
        _ => {
            let param_index = param_index as usize;
            format!(
                "In this definition, expected parameter variances are not satisfied.\nThe {}{} type parameter was expected to be {},\nbut it is {}.",
                param_index,
                variance_suffix(param_index),
                format_variance(expected),
                format_variance(actual),
            )
        }
    };
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_compiler_error_report_with_bare_reset_lines(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    const RESET: &str = "\x1b[0m";

    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);

    for line in message.lines() {
        if line == RESET {
            output.push_str(line);
        } else {
            output.push_str("  ");
            output.push_str(line);
        }
        output.push('\n');
    }
    output.push('\n');
    output
}

fn format_compiler_warning_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    warning: &TypeCoreWarning,
) -> String {
    let start_pos = arena.loc_start(warning.loc);
    let end_pos = arena.loc_end(warning.loc);
    let mut output = String::new();
    code_frame::mark_color_setup();

    output.push_str("\n  ");
    output.push_str(&code_frame::colorize_intro(
        &format!("Warning number {}", warning.warning.number()),
        warning.is_error,
    ));
    if warning.is_error {
        output.push_str(" (configured as error) ");
    }
    output.push('\n');
    output.push_str("  ");
    if !code_frame::has_printable_range(start_pos, end_pos) {
        output.push_str(&code_frame::colorize_location(filename));
        output.push_str("\n\n");
    } else {
        let location = code_frame::format_location(filename, start_pos, end_pos);
        output.push_str(&code_frame::colorize_location(&location));
        output.push_str("\n\n");
        // OCaml `Location.print ~message_kind`: `Code_frame.print ~is_warning`
        // is false for a warning configured as an error (location.ml:143-155).
        output.push_str(&if warning.is_error {
            code_frame::print(source, start_pos, end_pos)
        } else {
            code_frame::print_warning(source, start_pos, end_pos)
        });
        output.push('\n');
    }

    let indent_after_blank = !matches!(
        warning.warning,
        crate::diagnostics::Warning::UnusedVariable { .. }
            | crate::diagnostics::Warning::UnusedVariableStrict { .. }
    );
    let mut after_blank = false;
    let message = warning.warning.message();
    // An empty message still prints its indented message line.
    if message.is_empty() {
        output.push_str("  \n");
    }
    for (idx, line) in message.lines().enumerate() {
        let indent_line = match warning.warning {
            crate::diagnostics::Warning::NonClosedRecordPattern { .. } => idx == 0,
            crate::diagnostics::Warning::AttributePayload { .. } => idx == 0,
            crate::diagnostics::Warning::BsUnusedAttribute { .. } => idx == 0,
            crate::diagnostics::Warning::AllClausesGuarded => idx == 0,
            crate::diagnostics::Warning::AmbiguousPattern { .. } => idx == 0,
            crate::diagnostics::Warning::AmbiguousName { .. } => idx == 0,
            crate::diagnostics::Warning::FragileMatch { .. } => idx == 0,
            // `Builtin_attributes.cat` and warnings.ml:263-278 carry the
            // indentation of every later line in the message itself.
            crate::diagnostics::Warning::Deprecated { .. } => idx == 0,
            crate::diagnostics::Warning::FragileLiteralPattern => idx == 0,
            crate::diagnostics::Warning::UnreachableCase => idx == 0,
            // warnings.ml:412-438 carries its own indentation after the
            // first line; the printed return type keeps Format's layout.
            crate::diagnostics::Warning::BsToplevelExpressionUnit { .. } => idx == 0,
            crate::diagnostics::Warning::BsRecordRestOptionalOverlap { .. } => idx == 0,
            crate::diagnostics::Warning::UnusedConstructor { .. }
            | crate::diagnostics::Warning::UnusedExtension { .. } => idx == 0,
            crate::diagnostics::Warning::PartialMatch { .. } => {
                idx < 2 || line.starts_with("Hint:")
            }
            _ => indent_after_blank || !after_blank,
        };
        if !line.is_empty() && indent_line {
            output.push_str("  ");
            output.push_str(line);
        } else if !line.is_empty() {
            output.push_str(line);
        }
        if line.is_empty() {
            after_blank = true;
        }
        output.push('\n');
    }
    if message.ends_with('\n') {
        output.push('\n');
    }
    output.push('\n');
    output
}

fn emit_type_warnings(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    warnings: &[TypeCoreWarning],
) {
    if warnings.is_empty() {
        return;
    }

    let mut stderr = std::io::stderr();
    let output = format_type_warnings(arena, source, filename, warnings);
    let _ = std::io::Write::write_all(&mut stderr, output.as_bytes());
    let _ = std::io::Write::flush(&mut stderr);
}

/// [`format_type_warnings`], reading the source only when there is a
/// warning to report.
fn format_type_warnings_lazy<'s>(
    arena: &ParseArena,
    source: &dyn Fn() -> &'s str,
    filename: &str,
    warnings: &[TypeCoreWarning],
) -> String {
    if warnings.is_empty() {
        return String::new();
    }
    format_type_warnings(arena, source(), filename, warnings)
}

/// The reports [`emit_type_warnings`] prints, as one string.
fn format_type_warnings(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    warnings: &[TypeCoreWarning],
) -> String {
    let mut output = String::new();
    for warning in warnings {
        let report = format_compiler_warning_report(arena, source, filename, warning);
        output.push_str(&crate::source_text::decode_internal_utf8_runs(&report));
    }
    output
}

/// The source text an in-process compile reports diagnostics against. Like
/// OCaml's code frames (location.ml), it is read back from the source file.
fn read_in_process_source(filename: &str) -> String {
    std::fs::read(filename)
        .map(crate::source_text::latin1_bytes_to_string)
        .unwrap_or_default()
}

/// An error report preceded by the warnings printed before it.
fn prefix_diagnostic(prefix: &str, err: anyhow::Error) -> anyhow::Error {
    if prefix.is_empty() {
        return err;
    }
    match err.downcast::<UserDiagnostic>() {
        Ok(diagnostic) => UserDiagnostic::new(
            format!("{prefix}{}", diagnostic.output()),
            diagnostic.exit_code(),
        )
        .into(),
        Err(err) => anyhow!("{prefix}{err}"),
    }
}

fn type_warnings_have_errors(warnings: &[TypeCoreWarning]) -> bool {
    warnings.iter().any(|warning| warning.is_error)
}

fn format_compiler_error_report_raw_message(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);
    let message = code_frame::apply_message_styles(message);
    output.push_str(&message);
    if !message.ends_with('\n') {
        output.push('\n');
    }
    output.push('\n');
    output
}

fn format_wrong_name_report(
    type_ctx: &TypeContext,
    env: Option<std::sync::Arc<crate::types::env::Env>>,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    kind: &str,
    ty: TypeExprRef,
    expected: &str,
    path: &crate::types::Path,
    name: &str,
    alternatives: &[String],
    jsx_component_info: Option<&crate::types::typecore::JsxPropErrorInfo>,
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";
    const RESET: &str = "\x1b[0m";

    if let Some(jsx_component_info) = jsx_component_info {
        let mut message = String::new();
        if name == "children" {
            message.push_str("This JSX component does not accept child elements. It has no ");
            message.push_str(ERROR);
            message.push_str("children");
            message.push_str(RESET);
            message.push_str(" prop ");
        } else {
            message.push_str("The prop ");
            message.push_str(ERROR);
            message.push_str(name);
            message.push_str(RESET);
            message.push_str(" does not belong to the JSX component ");
        }
        if let Some(component_name) = &jsx_component_info.component_name {
            message.push_str(INFO);
            message.push('<');
            message.push_str(component_name);
            message.push_str(" />");
            message.push_str(RESET);
            message.push(' ');
        }
        message.push_str("\n\n\n");
        if let Some(hint) = spellcheck_hint(name, alternatives) {
            let mut raw_message = format_message_with_compiler_indentation(&message);
            raw_message.push_str("Hint: Did you mean ");
            raw_message.push_str(&hint);
            raw_message.push_str("?\n");
            return format_compiler_error_report_raw_message(
                arena,
                source,
                filename,
                loc,
                &raw_message,
            );
        }
        return format_compiler_error_report(arena, source, filename, loc, &message);
    }

    if path.is_constructor_typath() {
        let hint = spellcheck_hint(name, alternatives);
        let message = type_clash::render_error_message(|ppf| {
            type_clash::print_wrong_name_inline_record_field(
                ppf,
                type_ctx,
                name,
                path,
                hint.as_deref(),
            )
        });
        return format_compiler_error_report_formatted(arena, source, filename, loc, &message);
    }

    let label = if kind == "record" { "field" } else { kind };
    let type_text = format_type_expr(type_ctx, ty);
    // `Printtyp.path` under `wrap_printing_env env` (typecore.ml:5253-5254).
    let mut printer = crate::types::printtyp::Printtyp::new(type_ctx);
    if let Some(env) = env {
        printer.set_printing_env(Box::new(move |name| {
            env.find_type_with_path(name).ok().map(|(p, _)| p)
        }));
    }
    // typecore.ml:4963-4971:
    //   @[<v>@[<2>The %s @{<error>%s@} does not belong to type @{<info>%a@}@]@,@,
    //   @[<2>%s type@ @{<info>%a@}@]@]
    // The type is one Format string, measured by its byte length even when
    // the outcome printer broke it over several lines.
    let path_text = printer.string_of_path(path);
    let message = {
        let mut buf = Vec::new();
        {
            use crate::parser::formatter::{BoxKind, Formatter};
            // The report body sits in a box two columns in; raw newlines of
            // the type string are not indented.
            let mut ppf = Formatter::new(&mut buf);
            ppf.set_margin(78);
            ppf.str("  ");
            ppf.open_box(BoxKind::V, 0);
            ppf.open_box(BoxKind::Box, 2);
            ppf.print(format_args!("The {label} "));
            ppf.string_as(0, ERROR);
            ppf.str(name);
            ppf.string_as(0, RESET);
            ppf.str(" does not belong to type ");
            ppf.string_as(0, INFO);
            ppf.str(&path_text);
            ppf.string_as(0, RESET);
            ppf.close_box();
            ppf.cut();
            ppf.cut();
            ppf.open_box(BoxKind::Box, 2);
            ppf.print(format_args!("{expected} type"));
            ppf.space();
            ppf.string_as(0, INFO);
            ppf.string_as(type_text.len(), &type_text);
            ppf.string_as(0, RESET);
            ppf.close_box();
            ppf.close_box();
            ppf.flush();
        }
        String::from_utf8(buf).unwrap_or_default()
    };
    let mut raw_message = message;
    raw_message.push('\n');
    if let Some(hint) = spellcheck_hint(name, alternatives) {
        raw_message.push_str("Hint: Did you mean ");
        raw_message.push_str(&hint);
        raw_message.push_str("?\n");
    }
    format_compiler_error_report_raw_message(arena, source, filename, loc, &raw_message)
}

fn format_name_type_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    kind: &str,
    lid: &Longident,
    expected: &(crate::types::Path, crate::types::Path),
    alternatives: &[(crate::types::Path, crate::types::Path)],
) -> String {
    let lid = format_longident_for_report(arena, lid);
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_name_type_mismatch(
            ppf,
            type_ctx,
            None,
            kind,
            &lid,
            expected,
            alternatives,
        )
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_undefined_method_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    ty: TypeExprRef,
    method: &str,
    alternatives: Option<&[String]>,
) -> String {
    let hint = alternatives.map(|alts| spellcheck_hint(method, alts));
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_undefined_method(
            ppf,
            type_ctx,
            ty,
            method,
            hint.as_ref().map(|h| h.as_deref()),
        )
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_type_path_for_report(path: &crate::types::Path) -> String {
    let name = path.name();
    name.strip_prefix("Stdlib.")
        .or_else(|| name.strip_prefix("Stdlib_"))
        .unwrap_or(&name)
        .to_string()
}

fn format_unbound_value_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
    qualifier: Option<&str>,
    alternatives: &[String],
    module_suggestion: Option<&str>,
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let mut message = String::new();
    if let Some(qualifier) = qualifier {
        message.push_str("The value ");
        message.push_str(name);
        message.push_str(" can't be found in ");
        message.push_str(qualifier);
    } else {
        message.push_str("The value ");
        message.push_str(name);
        message.push_str(" can't be found");
    }

    let spellcheck = super_spellcheck_hint(name, alternatives);
    if let Some(module_suggestion) = module_suggestion {
        let mut raw_message = String::new();
        raw_message.push_str("  ");
        raw_message.push_str(&message);
        raw_message.push('\n');

        if let Some(hint) = spellcheck {
            raw_message.push_str("  \n  ");
            raw_message.push_str(INFO);
            raw_message.push_str("Hint: Did you mean ");
            raw_message.push_str(&hint);
            raw_message.push('?');
            raw_message.push_str(RESET);
            raw_message.push_str("\n\n  Or did you mean");
        } else {
            raw_message.push_str("\n  Maybe you meant");
        }
        raw_message.push_str(" to use the module ");
        raw_message.push_str(INFO);
        raw_message.push_str(module_suggestion);
        raw_message.push_str(RESET);
        raw_message.push_str("?\n");

        return format_compiler_error_report_raw_message(
            arena,
            source,
            filename,
            loc,
            &raw_message,
        );
    }

    if let Some(hint) = spellcheck {
        message.push_str("\n\n");
        message.push_str(INFO);
        message.push_str("Hint: Did you mean ");
        message.push_str(&hint);
        message.push('?');
        message.push_str(RESET);
    }

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_unbound_module_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
    alternatives: &[String],
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let mut message = if name == "Str" {
        format!(
            "{INFO}The module or file Str can't be found.{RESET}\nAre you trying to use the standard library's Str?\nIf you're compiling to JavaScript, use {INFO}RegExp{RESET} instead.\nOtherwise, add str.cma to your ocamlc/ocamlopt command."
        )
    } else {
        format!(
            "{INFO}The module or file {name} can't be found.{RESET}\n- If it's a third-party dependency:\n  - Did you add it to the \"dependencies\" or \"dev-dependencies\" in rescript.json?\n- Did you include the file's directory to the \"sources\" in rescript.json?"
        )
    };
    // typetexp.ml:742-750 `spellcheck`: an `Ldot (r, s)` is checked by its
    // last component `s` against the modules of `r`.
    let last_component = name.rsplit('.').next().unwrap_or(name);
    if name != "Str"
        && let Some(hint) = super_spellcheck_hint(last_component, alternatives)
    {
        message.push_str("\n\n\n");
        message.push_str(INFO);
        message.push_str("Hint: Did you mean ");
        message.push_str(&hint);
        message.push('?');
        message.push_str(RESET);
    } else if name != "Str" {
        message.push_str("\n\n");
    }
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_access_functor_as_structure_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
) -> String {
    let name = format_longident_for_report(arena, lid);
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("The module {name} is a functor, not a structure"),
    )
}

fn format_cannot_scrape_alias_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    path: &crate::types::Path,
) -> String {
    let name = format_longident_for_report(arena, lid);
    let alias = format_type_path_for_report(path);
    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("The module {name} is an alias for module {alias}, which is missing"),
    )
}

fn format_unbound_constructor_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    alternatives: &[String],
) -> String {
    let name = format_longident_for_report(arena, lid);
    // typetexp.ml:742-750: spellcheck the last component of the longident.
    let hint = spellcheck_hint(name.rsplit('.').next().unwrap_or(&name), alternatives);
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_unbound_constructor(ppf, &name, hint.as_deref())
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_message_with_compiler_indentation(message: &str) -> String {
    let mut output = String::new();
    for line in message.lines() {
        output.push_str("  ");
        output.push_str(line);
        output.push('\n');
    }
    output
}

/// OCaml `Misc.spellcheck` + `Misc.did_you_mean` (compiler/ext/misc.ml:240-272):
/// every alternative at the best edit distance within the cutoff, most recent
/// tie first, rendered as "a, b or c".
/// `Typetexp.super_spellcheck` + `Typetexp.did_you_mean`
/// (compiler/ml/typetexp.ml:717-740): unlike `Misc.did_you_mean`, the head of
/// the `Misc.spellcheck` result is printed last and the rest in reverse.
fn super_spellcheck_hint(name: &str, alternatives: &[String]) -> Option<String> {
    let choices = spellcheck_choices(name, alternatives);
    let (last, rev_rest) = choices.split_first()?;
    Some(if rev_rest.is_empty() {
        (*last).to_string()
    } else {
        let rest: Vec<&str> = rev_rest.iter().rev().copied().collect();
        format!("{} or {}", rest.join(", "), last)
    })
}

/// `Misc.spellcheck` + `Misc.did_you_mean` (compiler/ext/misc.ml:240-272).
fn spellcheck_hint(name: &str, alternatives: &[String]) -> Option<String> {
    let best = spellcheck_choices(name, alternatives);
    let (last, rest) = best.split_last()?;
    Some(if rest.is_empty() {
        (*last).to_string()
    } else {
        format!("{} or {}", rest.join(", "), last)
    })
}

/// `Misc.spellcheck` (compiler/ext/misc.ml:240-257): the closest candidates,
/// in the order of OCaml's prepend-on-tie fold.
fn spellcheck_choices<'a>(name: &str, alternatives: &'a [String]) -> Vec<&'a str> {
    let cutoff = match name.len() {
        1 | 2 => 0,
        3 | 4 => 1,
        5 | 6 => 2,
        _ => 3,
    };
    let mut best: Vec<&str> = Vec::new();
    let mut best_dist = usize::MAX;
    for candidate in alternatives {
        let Some(dist) = ocaml_edit_distance(name, candidate, cutoff) else {
            continue;
        };
        if dist < best_dist {
            best = vec![candidate.as_str()];
            best_dist = dist;
        } else if dist == best_dist {
            best.insert(0, candidate.as_str());
        }
    }
    best
}

/// OCaml `Misc.edit_distance` (compiler/ext/misc.ml:195-238): Levenshtein
/// distance with adjacent transpositions, bounded by `cutoff`.
fn ocaml_edit_distance(a: &str, b: &str, cutoff: usize) -> Option<usize> {
    let a = a.as_bytes();
    let b = b.as_bytes();
    let (la, lb) = (a.len(), b.len());
    let cutoff = cutoff.min(la.max(lb));
    if la.abs_diff(lb) > cutoff {
        return None;
    }
    let mut m = vec![vec![cutoff + 1; lb + 1]; la + 1];
    m[0][0] = 0;
    for (i, row) in m.iter_mut().enumerate().skip(1) {
        row[0] = i;
    }
    for j in 1..=lb {
        m[0][j] = j;
    }
    for i in 1..=la {
        let lo = 1.max(i.saturating_sub(cutoff + 1));
        let hi = lb.min(i + cutoff + 1);
        for j in lo..=hi {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            let mut best = (1 + m[i - 1][j].min(m[i][j - 1])).min(m[i - 1][j - 1] + cost);
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                best = best.min(m[i - 2][j - 2] + cost);
            }
            m[i][j] = best;
        }
    }
    let result = m[la][lb];
    (result <= cutoff).then_some(result)
}

fn format_label_multiply_defined_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &str,
    jsx_component_info: Option<&crate::types::typecore::JsxPropErrorInfo>,
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    if let Some(jsx_component_info) = jsx_component_info {
        let mut message = String::new();
        message.push_str("The prop ");
        message.push_str(INFO);
        message.push_str(label);
        message.push_str(RESET);
        message.push_str(" has already been passed to the component ");
        if let Some(component_name) = &jsx_component_info.component_name {
            message.push_str(INFO);
            message.push('<');
            message.push_str(component_name);
            message.push_str(" />");
            message.push_str(RESET);
            message.push(' ');
        }

        let mut raw_message = format_message_with_compiler_indentation(&message);
        raw_message.push_str("You can't pass the same prop more than once.\n");
        return format_compiler_error_report_raw_message(
            arena,
            source,
            filename,
            loc,
            &raw_message,
        );
    }

    format_compiler_error_report(
        arena,
        source,
        filename,
        loc,
        &format!("The record field label {label} is defined several times"),
    )
}

fn format_labels_missing_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    labels: &[String],
    jsx_component_info: Option<&crate::types::typecore::JsxPropErrorInfo>,
) -> String {
    let component_name = jsx_component_info.map(|info| info.component_name.as_deref());
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_labels_missing(ppf, labels, component_name)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

/// `Typecore.report_error`'s `Expr_type_clash` (typecore.ml:4879-4894).
#[allow(clippy::too_many_arguments)]
fn format_expr_type_clash_report_ocaml(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
    context: &Option<TypeClashContext>,
    env: &crate::types::Env,
) -> String {
    if let Some((arity_a, arity_b)) = type_clash::expr_type_clash_arity_mismatch(type_ctx, trace) {
        return format_function_arity_mismatch_report(
            arena,
            source,
            filename,
            loc,
            arity_a as i32,
            arity_b as i32,
        );
    }
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_expr_type_clash(ppf, type_ctx, env, arena, source, loc, trace, context)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

/// A report whose message was laid out by Format like `Location.errorf`:
/// `default_error_reporter` prints it followed by `@,` and the final `@.`
/// (location.ml:237-251, 272-279), i.e. always two newlines.
fn format_compiler_error_report_formatted(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let mut output = String::new();
    push_compiler_error_report_header(&mut output, arena, source, filename, loc);
    output.push_str(&code_frame::apply_message_styles(message));
    output.push_str("\n\n");
    output
}

fn format_expr_type_clash_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
    context: &Option<TypeClashContext>,
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";
    const RESET: &str = "\x1b[0m";

    if let Some((actual_arity, expected_arity)) =
        expr_type_clash_uncurried_arity_mismatch(type_ctx, trace)
    {
        return format_function_arity_mismatch_report(
            arena,
            source,
            filename,
            loc,
            actual_arity,
            expected_arity,
        );
    }

    let Some((actual, expected)) = trace.first().copied() else {
        return format_compiler_error_report(arena, source, filename, loc, "Type error.");
    };

    let actual_is_function = trace.iter().any(|(actual, _)| {
        let actual = type_alias_full_expansion(type_ctx, *actual)
            .or_else(|| rendered_alias_expansion(type_ctx, *actual, trace, true))
            .unwrap_or_else(|| type_ctx.repr(*actual));
        matches!(&*type_ctx.borrow_desc(actual), TypeDesc::Tarrow { .. })
    });
    let expected_is_jsx_component = trace
        .iter()
        .any(|(_, expected)| type_is_jsx_component(type_ctx, *expected));
    let plain_function_to_component = actual_is_function
        && expected_is_jsx_component
        && !matches!(context, Some(TypeClashContext::JsxComponent));
    let missing_parameters = if actual_is_function {
        Vec::new()
    } else {
        collect_expected_function_arguments(type_ctx, expected)
    };
    let mut message = String::new();
    let mut printer = type_clash_printer(type_ctx, trace);

    if !missing_parameters.is_empty() {
        if missing_parameters.len() == 1 {
            message.push_str("This value might need to be ");
            message.push_str(INFO);
            message.push_str("wrapped in a function that takes an extra\nparameter");
            message.push_str(RESET);
            message.push_str(" of type ");
            message.push_str(&format_type_clash_arguments(type_ctx, &missing_parameters));
            message.push_str("\n\n");
        } else {
            message.push_str("This value seems to ");
            message.push_str(INFO);
            message.push_str("need to be wrapped in a function that takes extra arguments");
            message.push_str(RESET);
            message.push_str(" of type: ");
            message.push_str(&format_type_clash_arguments(type_ctx, &missing_parameters));
            message.push_str("\n\n");
        }
        message.push_str(INFO);
        message.push_str("Here's the original error message");
        message.push_str(RESET);
        message.push('\n');
    }

    if matches!(context, Some(TypeClashContext::Await)) {
        message.push_str("This has type: ");
        message.push_str(ERROR);
        message.push_str(&printer.format(actual));
        message.push_str(RESET);
        message.push('\n');
        message.push_str("But you're using ");
        message.push_str(INFO);
        message.push_str("await");
        message.push_str(RESET);
        message.push_str(" on this expression, so it is expected to be of type:\n  ");
        message.push_str(INFO);
        message.push_str(&printer.format(expected));
        message.push_str(RESET);
        append_extra_type_clash_help(type_ctx, arena, source, loc, context, trace, &mut message);
        let message = format_await_type_clash_message(&message);
        return format_compiler_error_report_raw_message(arena, source, filename, loc, &message);
    }

    let (error_text, expected_text): (Cow<'static, str>, Cow<'static, str>) = match context {
        Some(TypeClashContext::ArrayLiteral) => (
            Cow::Borrowed("This array item has type: "),
            Cow::Borrowed("But this array is expected to have items of type: "),
        ),
        Some(TypeClashContext::TaggedTemplateValue) => (
            Cow::Borrowed("This interpolated value has type: "),
            Cow::Borrowed("But this tag expects interpolations of type: "),
        ),
        Some(TypeClashContext::FunctionCall) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But this function argument is expecting: "),
        ),
        Some(TypeClashContext::FunctionArgument { .. }) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But this function argument is expecting: "),
        ),
        Some(TypeClashContext::JsxComponent) => (
            Cow::Borrowed("This JSX tag has type: "),
            Cow::Borrowed("But JSX component positions require:\n  "),
        ),
        Some(TypeClashContext::StatementFunctionCall) => (
            Cow::Borrowed("This function call returns: "),
            Cow::Borrowed("But it's expected to return: "),
        ),
        Some(TypeClashContext::ComparisonOperator) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But it's being compared to something of type: "),
        ),
        Some(TypeClashContext::StringConcat) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But string concatenation is expecting: "),
        ),
        Some(TypeClashContext::MathOperator {
            operator,
            is_constant,
            ..
        }) => (
            Cow::Borrowed(if is_constant.is_some() {
                "This value has type: "
            } else {
                "This has type: "
            }),
            Cow::Owned(format!(
                "But it's being used with the {INFO}{operator}{RESET} operator, which works on: "
            )),
        ),
        Some(TypeClashContext::RecordField { .. }) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But the record field "),
        ),
        Some(TypeClashContext::SetRecordField { .. }) => (
            Cow::Borrowed("You're assigning something to this field that has type: "),
            Cow::Borrowed("But the record field is of type: "),
        ),
        Some(TypeClashContext::IfCondition) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But \x1b[1;33mif\x1b[0m conditions must always be of type: "),
        ),
        Some(TypeClashContext::IfReturn) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But this \x1b[1;33mif\x1b[0m statement is expected to return: "),
        ),
        Some(TypeClashContext::TernaryReturn) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But this ternary is expected to return: "),
        ),
        Some(TypeClashContext::SwitchExpression) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But this switch is expected to return: "),
        ),
        Some(TypeClashContext::TryReturn) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But this try/catch is expected to return: "),
        ),
        Some(TypeClashContext::WhileCondition) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But a \x1b[1;33mwhile\x1b[0m loop condition must always be of type: "),
        ),
        Some(TypeClashContext::ForLoopCondition) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But a \x1b[1;33mfor\x1b[0m loop bounds must always be of type: "),
        ),
        Some(TypeClashContext::AssertCondition) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But assertions must always be of type: "),
        ),
        Some(TypeClashContext::LetUnwrapReturn) => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But this \x1b[1;33mlet?\x1b[0m is used where this type is expected: "),
        ),
        _ => (
            Cow::Borrowed("This has type: "),
            Cow::Borrowed("But it's expected to have type: "),
        ),
    };
    let suppress_alias_expansion = matches!(
        context,
        Some(TypeClashContext::IfCondition)
            | Some(TypeClashContext::WhileCondition)
            | Some(TypeClashContext::ForLoopCondition)
            | Some(TypeClashContext::AssertCondition)
    );

    message.push_str(&error_text);
    if suppress_alias_expansion {
        append_type_clash_type_without_alias_expansion(
            type_ctx,
            trace,
            true,
            ERROR,
            actual,
            &mut message,
        );
    } else {
        append_type_clash_type_with_printer(
            type_ctx,
            trace,
            true,
            ERROR,
            actual,
            &mut message,
            &mut printer,
        );
    }
    message.push('\n');
    if let Some(TypeClashContext::RecordField {
        field_name, jsx, ..
    }) = context
    {
        match (field_name.as_str(), jsx) {
            ("children", Some(JsxPropKind::Fragment)) => {
                message.push_str("But children of JSX fragments must be of type:\n  ");
            }
            ("children", Some(JsxPropKind::CustomComponent)) => {
                message.push_str("But children passed to this component must be of type:\n  ");
            }
            (_, Some(_)) => {
                message.push_str("But the component prop ");
                message.push_str(INFO);
                message.push_str(field_name);
                message.push_str(RESET);
                message.push_str(" is expected to have type: ");
            }
            _ => {
                message.push_str(&expected_text);
                message.push_str(INFO);
                message.push_str(field_name);
                message.push_str(RESET);
                message.push_str(" is expected to have type: ");
            }
        }
        if suppress_alias_expansion {
            append_type_clash_type_without_alias_expansion(
                type_ctx,
                trace,
                false,
                INFO,
                expected,
                &mut message,
            );
        } else {
            append_type_clash_type_with_printer(
                type_ctx,
                trace,
                false,
                INFO,
                expected,
                &mut message,
                &mut printer,
            );
        }
    } else if let Some(TypeClashContext::FunctionArgument { optional, name }) = context {
        message.push_str("But this");
        if *optional {
            message.push_str(" optional");
        }
        message.push_str(" function argument");
        if let Some(name) = name {
            message.push(' ');
            message.push_str(INFO);
            message.push('~');
            message.push_str(name);
            message.push_str(RESET);
        }
        message.push_str(" is expecting:");
        if plain_function_to_component {
            message.push_str("\n  ");
        }
        if type_is_object(type_ctx, expected) {
            message.push_str("\n  ");
            if let Some((field_name, expected_field_ty)) =
                object_field_expected_line(type_ctx, trace)
            {
                message.push_str(INFO);
                message.push_str("{..");
                message.push('"');
                message.push_str(&field_name);
                message.push('"');
                message.push_str(": ");
                message.push_str(&printer.format(expected_field_ty));
                message.push('}');
                message.push_str(RESET);
                append_extra_type_clash_help(
                    type_ctx,
                    arena,
                    source,
                    loc,
                    context,
                    trace,
                    &mut message,
                );

                if type_clash_array_to_tuple(type_ctx, trace)
                    || type_clash_expected_unit_actual(type_ctx, trace).is_some()
                {
                    let message = format_type_clash_message_with_empty_blank_lines(&message);
                    return format_compiler_error_report_raw_message(
                        arena, source, filename, loc, &message,
                    );
                }

                return format_compiler_error_report(arena, source, filename, loc, &message);
            }
        } else if !plain_function_to_component {
            message.push(' ');
        }
        append_type_clash_type_with_printer(
            type_ctx,
            trace,
            false,
            INFO,
            expected,
            &mut message,
            &mut printer,
        );
    } else {
        if plain_function_to_component {
            message.push_str("But it's expected to have type:\n  ");
        } else {
            message.push_str(&expected_text);
        }
        append_type_clash_type_with_printer(
            type_ctx,
            trace,
            false,
            INFO,
            expected,
            &mut message,
            &mut printer,
        );
        if plain_function_to_component {
            let inline = " \x1b[2m(defined as\x1b[0m \x1b[1;33mJsx.component";
            let multiline = " \x1b[2m(defined as\x1b[0m\n    \x1b[1;33mJsx.component";
            message = message.replace(inline, multiline);
        }
    }
    append_extra_type_clash_help(type_ctx, arena, source, loc, context, trace, &mut message);
    // Printtyp.super_unification_error uses a <hov 2> box for each heading
    // and type (printtyp.ml). The break after the heading is taken when the
    // complete type expansion cannot fit in the remaining line.
    message = wrap_type_clash_headings(&message);

    if matches!(
        context,
        Some(TypeClashContext::ArrayLiteral) | Some(TypeClashContext::MathOperator { .. })
    ) {
        let message = format_array_type_clash_message(&message);
        format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
    } else if matches!(
        context,
        Some(TypeClashContext::IfReturn)
            | Some(TypeClashContext::TernaryReturn)
            | Some(TypeClashContext::TryReturn)
    ) {
        let message = format_type_clash_return_message(&message);
        format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
    } else if matches!(
        context,
        Some(TypeClashContext::ComparisonOperator)
            | Some(TypeClashContext::IfCondition)
            | Some(TypeClashContext::StatementFunctionCall)
    ) {
        let message = format_type_clash_message_with_empty_blank_lines(&message);
        format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
    } else if matches!(
        context,
        Some(TypeClashContext::LetUnwrapReturn)
            | Some(TypeClashContext::SwitchExpression)
            | Some(TypeClashContext::JsxComponent)
    ) || plain_function_to_component
    {
        let message = format_type_clash_message_with_empty_blank_lines(&message);
        format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
    } else if type_clash_string_to_polyvariant(type_ctx, trace)
        || type_clash_string_to_variant(type_ctx, trace)
    {
        let message = format_type_clash_message_with_empty_blank_lines(&message);
        format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
    } else if type_clash_array_to_tuple(type_ctx, trace)
        || type_clash_expected_unit_actual(type_ctx, trace).is_some()
        || type_clash_actual_promise(type_ctx, trace)
    {
        let message = format_type_clash_message_with_empty_blank_lines(&message);
        format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
    } else if message.contains("These types are compatible at runtime") {
        format_compiler_error_report_with_bare_reset_lines(arena, source, filename, loc, &message)
    } else {
        format_compiler_error_report(arena, source, filename, loc, &message)
    }
}

fn format_pattern_type_clash_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";
    const RESET: &str = "\x1b[0m";

    let Some((actual, expected)) = trace.first().copied() else {
        return format_compiler_error_report(arena, source, filename, loc, "Type error.");
    };

    let mut message = String::new();
    let mut printer = type_clash_printer(type_ctx, trace);
    message.push_str("This pattern matches values of type ");
    append_type_clash_type_with_printer(
        type_ctx,
        trace,
        true,
        ERROR,
        actual,
        &mut message,
        &mut printer,
    );
    message.push('\n');
    message.push_str("but a pattern was expected which matches values of type ");
    append_type_clash_type_with_printer(
        type_ctx,
        trace,
        false,
        INFO,
        expected,
        &mut message,
        &mut printer,
    );
    if let Some(path) = type_clash_escape_constructor_path(type_ctx, trace) {
        message.push('\n');
        message.push_str("The type constructor ");
        message.push_str(&path);
        message.push_str(" would escape its scope");
        return format_compiler_error_report(arena, source, filename, loc, &message);
    }
    append_pattern_option_type_clash_help(type_ctx, actual, expected, &mut message);
    let is_polyvariant_explanation =
        append_polyvariant_type_clash_help(type_ctx, trace, &mut message);
    if !is_polyvariant_explanation {
        append_incompatible_type_parts(type_ctx, trace, &mut message);
    }

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_recursive_local_constraint_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";

    let Some((actual, expected)) = trace.first().copied() else {
        return format_compiler_error_report(arena, source, filename, loc, "Type error.");
    };

    let mut message = String::new();
    let mut printer = type_clash_printer(type_ctx, trace);
    message.push_str("Recursive local constraint when unifying ");
    append_type_clash_type_with_printer(
        type_ctx,
        trace,
        true,
        ERROR,
        actual,
        &mut message,
        &mut printer,
    );
    message.push('\n');
    message.push_str("with ");
    append_type_clash_type_with_printer(
        type_ctx,
        trace,
        false,
        INFO,
        expected,
        &mut message,
        &mut printer,
    );
    append_incompatible_type_parts(type_ctx, trace, &mut message);

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_or_pattern_type_clash_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    id: &Ident,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";

    let Some((left, right)) = trace.first().copied() else {
        return format_compiler_error_report(arena, source, filename, loc, "Type error.");
    };

    let mut message = String::new();
    let mut printer = type_clash_printer(type_ctx, trace);
    message.push_str("The variable ");
    message.push_str(id.name());
    message.push_str(" on the left-hand side of this or-pattern has type ");
    append_type_clash_type_with_printer(
        type_ctx,
        trace,
        true,
        ERROR,
        left,
        &mut message,
        &mut printer,
    );
    message.push('\n');
    message.push_str("but on the right-hand side it has type ");
    append_type_clash_type_with_printer(
        type_ctx,
        trace,
        false,
        INFO,
        right,
        &mut message,
        &mut printer,
    );

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_orpat_vars_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    id: &Ident,
    valid_idents: &[Ident],
) -> String {
    let message = format!(
        "Variable {} must occur on both sides of this | pattern",
        id.name()
    );
    let alternatives: Vec<String> = valid_idents
        .iter()
        .map(|valid| valid.name().to_string())
        .collect();

    if let Some(hint) = spellcheck_hint(id.name(), &alternatives) {
        let mut raw_message = format_message_with_compiler_indentation(&message);
        raw_message.push_str("Hint: Did you mean ");
        raw_message.push_str(&hint);
        raw_message.push('?');
        return format_compiler_error_report_raw_message(
            arena,
            source,
            filename,
            loc,
            &raw_message,
        );
    }

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_label_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> String {
    let Some((actual, expected)) = trace.first().copied() else {
        return format_compiler_error_report(arena, source, filename, loc, "Type error.");
    };

    const ERROR: &str = "\x1b[1;31m";
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";
    let message = format!(
        "The record field {} belongs to the type {ERROR}{}{RESET}\nbut is mixed here with fields of type {INFO}{}{RESET}",
        format_longident_for_report(arena, lid),
        format_type_expr(type_ctx, actual),
        format_type_expr(type_ctx, expected)
    );
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_polymorphic_label_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    lid: &Longident,
) -> String {
    let message = format!(
        "The record field {} is polymorphic. You cannot instantiate it in a pattern.",
        format_longident_for_report(arena, lid)
    );
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn append_pattern_option_type_clash_help(
    type_ctx: &TypeContext,
    actual: TypeExprRef,
    expected: TypeExprRef,
    message: &mut String,
) {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";
    const RESET: &str = "\x1b[0m";

    let actual_is_option =
        type_is_predef_path(type_ctx, actual, &crate::types::predef::path_option());
    let expected_is_option =
        type_is_predef_path(type_ctx, expected, &crate::types::predef::path_option());

    if actual_is_option && !expected_is_option {
        message.push_str("\n\nYou're expecting the value you're pattern matching on to be an ");
        message.push_str(INFO);
        message.push_str("option");
        message.push_str(RESET);
        message.push_str(", but the value is actually not an option.\n");
        message.push_str("Change your pattern match to work on the concrete value (remove ");
        message.push_str(ERROR);
        message.push_str("Some(_)");
        message.push_str(RESET);
        message.push_str(" or ");
        message.push_str(ERROR);
        message.push_str("None");
        message.push_str(RESET);
        message.push_str(" from the pattern) to make it work.");
    } else if expected_is_option && !actual_is_option {
        message.push_str("\n\nThe value you're pattern matching on here is wrapped in an ");
        message.push_str(INFO);
        message.push_str("option");
        message.push_str(RESET);
        message.push_str(", but you're trying to match on the actual value.\n");
        message.push_str("Wrap the highlighted pattern in ");
        message.push_str(INFO);
        message.push_str("Some()");
        message.push_str(RESET);
        message.push_str(" to make it work.");
    }
}

// Format's default margin is 78. The Location reporter adds two columns
// before the message; each <hov 2> heading box adds two more on a break.
fn type_clash_visible_width(text: &str) -> usize {
    let bytes = text.as_bytes();
    let mut i = 0;
    let mut width = 0;
    while i < bytes.len() {
        if bytes[i] == b'\x1b' && bytes.get(i + 1) == Some(&b'[') {
            i += 2;
            while i < bytes.len() && bytes[i] != b'm' {
                i += 1;
            }
            i += usize::from(i < bytes.len());
        } else {
            let ch = text[i..].chars().next().expect("valid UTF-8");
            width += 1;
            i += ch.len_utf8();
        }
    }
    width
}

fn wrap_type_clash_headings(message: &str) -> String {
    const MARGIN: usize = 78;
    const ERROR: &str = "\x1b[1;31m";
    const INFO: &str = "\x1b[1;33m";
    let mut lines = message.splitn(3, '\n');
    let Some(actual) = lines.next() else {
        return message.to_string();
    };
    let Some(expected) = lines.next() else {
        return message.to_string();
    };
    if !expected.starts_with("But ") {
        return message.to_string();
    }
    let rest = lines.next();
    let wrap = |line: &str, color: &str| {
        let Some(at) = line.find(color) else {
            return line.to_string();
        };
        let prefix = &line[..at];
        let ty = &line[at..];
        let mut result = if 2 + type_clash_visible_width(line) > MARGIN && prefix.ends_with(' ') {
            format!("{}\n  {}", prefix.trim_end(), ty)
        } else {
            line.to_string()
        };
        // super_type_expansion prints aliases in a nested <2> box. If the
        // expansion does not fit, break at the space following "defined as".
        if let Some(marker) = result.find("(defined as\x1b[0m ") {
            let expansion = marker + "(defined as\x1b[0m ".len();
            let start = result[..expansion].rfind('\n').map_or(0, |pos| pos + 1);
            let indent = if start == 0 { 2 } else { 4 };
            if indent + type_clash_visible_width(&result[start..]) > MARGIN {
                result.replace_range(expansion - 1..expansion, "\n    ");
            }
        }
        result
    };
    let mut output = wrap(actual, ERROR);
    output.push('\n');
    output.push_str(&wrap(expected, INFO));
    if let Some(rest) = rest {
        output.push('\n');
        output.push_str(rest);
    }
    output
}

/// `Printtyp.super_unification_error` starts with `reset ()` and marks the
/// loops of every type of the trace before printing any of them
/// (compiler/ml/printtyp.ml:1542-1556), so the names of the whole report come
/// from one session and source-named variables are reserved up front.
fn type_clash_printer<'a>(
    type_ctx: &'a TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> TypeExprPrinter<'a> {
    let mut printer = TypeExprPrinter::new(type_ctx);
    printer.reset();
    for (actual, expected) in trace {
        printer.mark_loops_once(*actual);
        printer.mark_loops_once(*expected);
    }
    printer
}

fn append_type_clash_type(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    actual_side: bool,
    color: &str,
    ty: TypeExprRef,
    message: &mut String,
) {
    append_type_clash_type_with_printer(
        type_ctx,
        trace,
        actual_side,
        color,
        ty,
        message,
        &mut TypeExprPrinter::new(type_ctx),
    );
}

fn append_type_clash_type_with_printer(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    actual_side: bool,
    color: &str,
    ty: TypeExprRef,
    message: &mut String,
    printer: &mut TypeExprPrinter<'_>,
) {
    const DIM: &str = "\x1b[2m";
    const RESET: &str = "\x1b[0m";

    let original_ty = ty;
    let ty = type_clash_display_type(type_ctx, trace, actual_side, ty);
    let ty_text = printer.format(ty);
    message.push_str(color);
    message.push_str(&ty_text);
    message.push_str(RESET);

    if ty == original_ty
        && let Some(expansion) = rendered_alias_expansion(type_ctx, ty, trace, actual_side)
        && {
            let expansion_text = printer.format(expansion);
            expansion_text != ty_text || !type_is_polyvariant(type_ctx, expansion)
        }
    {
        message.push(' ');
        message.push_str(DIM);
        message.push_str("(defined as");
        message.push_str(RESET);
        message.push(' ');
        message.push_str(color);
        message.push_str(&printer.format(expansion));
        message.push_str(RESET);
        message.push_str(DIM);
        message.push(')');
        message.push_str(RESET);
    }
}

fn append_type_clash_type_without_alias_expansion(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    actual_side: bool,
    color: &str,
    ty: TypeExprRef,
    message: &mut String,
) {
    const RESET: &str = "\x1b[0m";

    let ty = type_clash_display_type(type_ctx, trace, actual_side, ty);
    message.push_str(color);
    message.push_str(&format_type_expr(type_ctx, ty));
    message.push_str(RESET);
}

fn type_clash_display_type(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    actual_side: bool,
    ty: TypeExprRef,
) -> TypeExprRef {
    if type_is_polyvariant(type_ctx, ty)
        && let Some((actual, expected)) = polyvariant_diagnostic_type_pair(type_ctx, trace)
    {
        if actual_side { actual } else { expected }
    } else {
        ty
    }
}

fn rendered_alias_expansion(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
    trace: &[(TypeExprRef, TypeExprRef)],
    actual_side: bool,
) -> Option<TypeExprRef> {
    // OCaml's trace expansions come from `full_expand` (ctype.ml), i.e.
    // `expand_head`, which only rewrites a type-constructor head.
    if !matches!(
        &*type_ctx.get_desc(type_ctx.repr(ty)),
        TypeDesc::Tconstr { .. }
    ) {
        return None;
    }
    if let Some(expansion) = type_ctx.trace_expansion(type_ctx.repr(ty)) {
        let expansion = type_ctx.repr(expansion);
        return (!printtyp_same_path(type_ctx, ty, expansion)
            && !type_is_polyvariant(type_ctx, expansion))
        .then_some(expansion);
    }
    if let Some(expansion) = type_alias_expansion(type_ctx, ty)
        && !type_expansion_same(type_ctx, ty, expansion)
        && !type_is_polyvariant(type_ctx, expansion)
    {
        return Some(expand_promise_compat_alias(type_ctx, expansion));
    }

    let first = trace.first()?;
    let (top_actual, top_expected) = *first;
    let top = if actual_side {
        top_actual
    } else {
        top_expected
    };
    let top_repr = type_ctx.repr(top);
    let top_desc = type_ctx.get_desc(top_repr);
    let top_is_package = matches!(&*top_desc, TypeDesc::Tpackage { .. });
    drop(top_desc);
    if top_is_package {
        return None;
    }

    let top_text = format_type_expr(type_ctx, top);
    if let Some(expansion) = trace.iter().skip(1).find_map(|pair| {
        let ty = if actual_side { pair.0 } else { pair.1 };
        let is_candidate = !type_is_object(type_ctx, ty)
            && !type_is_polyvariant(type_ctx, ty)
            && type_ctx.repr(ty) != type_ctx.repr(top)
            && format_type_expr(type_ctx, ty) == top_text;
        is_candidate.then_some(ty)
    }) {
        return Some(expansion);
    }

    let counterpart_text = format_type_expr(
        type_ctx,
        if actual_side {
            top_expected
        } else {
            top_actual
        },
    );
    trace.iter().skip(1).find_map(|pair| {
        let left_text = format_type_expr(type_ctx, pair.0);
        let right_text = format_type_expr(type_ctx, pair.1);
        let left_is_candidate = !type_is_polyvariant(type_ctx, pair.0);
        let right_is_candidate = !type_is_polyvariant(type_ctx, pair.1);
        if actual_side {
            if left_is_candidate && right_text == counterpart_text && left_text != top_text {
                Some(pair.0)
            } else if right_is_candidate && left_text == counterpart_text && right_text != top_text
            {
                Some(pair.1)
            } else {
                None
            }
        } else if right_is_candidate && left_text == counterpart_text && right_text != top_text {
            Some(pair.1)
        } else if left_is_candidate && right_text == counterpart_text && left_text != top_text {
            Some(pair.0)
        } else {
            None
        }
    })
}

/// OCaml `Printtyp.same_path` (printtyp.ml:1220-1234) without a printing
/// environment, where `best_type_path p` is `(p, Id)`.
fn printtyp_same_path(type_ctx: &TypeContext, t: TypeExprRef, t2: TypeExprRef) -> bool {
    let t = type_ctx.repr(t);
    let t2 = type_ctx.repr(t2);
    if t == t2 {
        return true;
    }
    let d1 = type_ctx.get_desc(t);
    let d2 = type_ctx.get_desc(t2);
    match (&*d1, &*d2) {
        (
            TypeDesc::Tconstr {
                path: p1, args: a1, ..
            },
            TypeDesc::Tconstr {
                path: p2, args: a2, ..
            },
        ) => {
            p1.same(p2)
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(x, y)| type_ctx.repr(*x) == type_ctx.repr(*y))
        }
        _ => false,
    }
}

fn expand_promise_compat_alias(type_ctx: &TypeContext, ty: TypeExprRef) -> TypeExprRef {
    let mut current = type_ctx.repr(ty);
    let mut seen = AHashSet::new();
    while seen.insert(current) {
        let desc = type_ctx.get_desc(current);
        let TypeDesc::Tconstr { path, .. } = &*desc else {
            return current;
        };
        let is_promise_alias = path.name() == "Promise.t" || path.name() == "Stdlib.Promise.t";
        drop(desc);
        match type_alias_expansion(type_ctx, current) {
            Some(expansion)
                if is_promise_alias && !type_expansion_same(type_ctx, current, expansion) =>
            {
                current = type_ctx.repr(expansion);
            }
            _ => return current,
        }
    }
    current
}

fn format_not_subtype_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
    context: &Option<crate::types::SubtypeContext>,
) -> String {
    let Some((left, right)) = trace.first().copied() else {
        return format_compiler_error_report(arena, source, filename, loc, "Type error.");
    };

    let mut message = format!(
        "Type {} is not a subtype of {} ",
        format_not_subtype_head_type(type_ctx, left),
        format_not_subtype_head_type(type_ctx, right)
    );
    if let Some(extra) = format_subtype_context(context) {
        message.push_str("\n\n");
        message.push_str(&extra);
        if extra.is_empty() {
            message.push('\n');
        }
        return format_compiler_error_report_for_subtype_context(
            arena, source, filename, loc, &message,
        );
    }

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_not_subtype_head_type(type_ctx: &TypeContext, ty: TypeExprRef) -> String {
    let ty_text = format_type_expr(type_ctx, ty);
    if let Some(expansion) = type_alias_full_expansion(type_ctx, ty)
        && type_is_polyvariant(type_ctx, expansion)
        && !type_expansion_same(type_ctx, ty, expansion)
    {
        format!("{ty_text} = {}", format_type_expr(type_ctx, expansion))
    } else {
        ty_text
    }
}

fn format_subtype_context(context: &Option<crate::types::SubtypeContext>) -> Option<String> {
    use crate::types::SubtypeContext;
    use crate::types::ctype::{
        RecordFieldSubtypeViolation, SubtypeTypeKind, VariantConfigurationIssue,
        VariantConstructorAsPayload, VariantRuntimeRepresentationIssue,
    };

    const ERROR: &str = "\x1b[1;31m";
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    fn variant_as_payload_name(payload: VariantConstructorAsPayload) -> &'static str {
        match payload {
            VariantConstructorAsPayload::String => "string",
            VariantConstructorAsPayload::Int => "int",
            VariantConstructorAsPayload::Float => "float",
            VariantConstructorAsPayload::BigInt => "bigint",
            VariantConstructorAsPayload::Bool => "bool",
            VariantConstructorAsPayload::Null => "null",
            VariantConstructorAsPayload::Undefined => "undefined",
        }
    }

    fn subtype_type_kind_name(kind: SubtypeTypeKind) -> &'static str {
        match kind {
            SubtypeTypeKind::Abstract => "an abstract type",
            SubtypeTypeKind::Record => "a record",
            SubtypeTypeKind::Variant => "a variant",
            SubtypeTypeKind::Open => "an open type",
        }
    }

    match context {
        Some(SubtypeContext::CoercionTargetVariantNotUnboxed {
            variant_name,
            primitive,
        }) => Some(format!(
            "The variant {INFO}{}{RESET} is not unboxed, so it cannot be coerced to a {INFO}{}{RESET}. \nFix this by adding the {INFO}@unboxed{RESET} attribute to the variant {INFO}{}{RESET}.",
            variant_name.last(),
            primitive.last(),
            variant_name.last()
        )),
        Some(SubtypeContext::CoercionTargetVariantDoesNotCoverType {
            variant_name,
            primitive,
        }) => {
            let primitive_name = primitive.last();
            let mut chars = primitive_name.chars();
            let capitalized = match chars.next() {
                Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
                None => String::new(),
            };
            Some(format!(
                "The variant {INFO}{}{RESET} is unboxed, but has no catch-all case for the primitive {INFO}{primitive_name}{RESET}, and therefore does not cover all values of type {INFO}{primitive_name}{RESET}. \nFix this by adding a catch-all for {INFO}{}{RESET} to {INFO}{primitive_name}{RESET}, like {INFO}{capitalized}({primitive_name}){RESET}.",
                variant_name.last(),
                variant_name.last()
            ))
        }
        Some(SubtypeContext::VariantConstructorRuntimeRepresentationMismatch {
            variant_name,
            issues,
        }) => {
            let mut output = String::new();
            for issue in issues {
                let mut item = String::new();
                match issue {
                    VariantRuntimeRepresentationIssue::CannotCoerceNonUnboxedWithPayload {
                        constructor_name,
                        expected_typename,
                    } => {
                        item.push_str(&format!(
                            "The constructor {INFO}{constructor_name}{RESET} of variant {INFO}{}{RESET} has a payload, but the variant itself is not unboxed. \nThis means that the constructor {INFO}{constructor_name}{RESET} will be encoded as an object at runtime, which is not compatible with {INFO}{}{RESET}.",
                            variant_name.last(),
                            expected_typename.last()
                        ));
                    }
                    VariantRuntimeRepresentationIssue::InlineRecordCannotBeCoerced {
                        constructor_name,
                    } => {
                        item.push_str(&format!(
                            "The constructor {INFO}{constructor_name}{RESET} of variant {INFO}{}{RESET} has an inline record as payload. Currently, inline records cannot be coerced.",
                            variant_name.last()
                        ));
                    }
                    VariantRuntimeRepresentationIssue::AsPayloadNotEligibleForCoercion {
                        constructor_name,
                        expected_typename,
                        as_payload,
                    } => {
                        item.push_str(&format!(
                            "The constructor {INFO}{constructor_name}{RESET} of variant {INFO}{}{RESET} has an {INFO}@as{RESET} payload that has a runtime representation of {INFO}{}{RESET}, which is not compatible with the expected {INFO}{}{RESET}.",
                            variant_name.last(),
                            variant_as_payload_name(*as_payload),
                            expected_typename.last()
                        ));
                    }
                    VariantRuntimeRepresentationIssue::MismatchedUnboxedPayload { .. } => {}
                    VariantRuntimeRepresentationIssue::MismatchedAsPayload {
                        constructor_name,
                        expected_typename,
                        as_payload,
                    } => {
                        item.push_str(&format!(
                            "The constructor {INFO}{constructor_name}{RESET} of variant {INFO}{}{RESET} has ",
                            variant_name.last()
                        ));
                        if let Some(payload) = as_payload {
                            item.push_str(&format!(
                                "an {INFO}@as{RESET} payload that gives it the runtime type of {INFO}{}{RESET}.",
                                variant_as_payload_name(*payload)
                            ));
                        } else {
                            item.push_str(&format!(
                                "no {INFO}@as{RESET} payload, which makes it a {INFO}string{RESET} at runtime."
                            ));
                        }
                        item.push_str(&format!(
                            "\nThat runtime representation is not compatible with the expected runtime representation of {INFO}{}{RESET}.",
                            expected_typename.last()
                        ));
                        item.push_str(&format!(
                            "\n\nFix this by making sure all constructors in variant {INFO}{}{RESET} has a runtime representation of {INFO}{}{RESET}.",
                            variant_name.last(),
                            expected_typename.last()
                        ));
                    }
                }
                if item.is_empty() {
                    continue;
                }
                if !output.is_empty() {
                    output.push('\n');
                }
                output.push_str(&item);
            }
            (!issues.is_empty()).then_some(output)
        }
        Some(SubtypeContext::VariantConfigurationsMismatch {
            left_variant_name,
            right_variant_name,
            issue,
        }) => match issue {
            VariantConfigurationIssue::UnboxedConfigNotMatching {
                left_unboxed,
                right_unboxed,
            } => {
                fn unboxed_status(unboxed: bool) -> String {
                    if unboxed {
                        format!("{ERROR}not {RESET}unboxed")
                    } else {
                        format!("{ERROR}{RESET}unboxed")
                    }
                }

                Some(format!(
                    "The variants have different {INFO}@unboxed{RESET} configurations.\n- Variant {INFO}{}{RESET} is {}.\n- Variant {INFO}{}{RESET} is {}.\n\nFix this by making sure the variants either both have, or don't have, the {INFO}@unboxed{RESET} attribute.",
                    left_variant_name.last(),
                    unboxed_status(*left_unboxed),
                    right_variant_name.last(),
                    unboxed_status(*right_unboxed),
                ))
            }
            VariantConfigurationIssue::TagNameNotMatching {
                left_tag,
                right_tag,
            } => {
                fn tag_status(tag: &Option<String>, variant_name: &crate::types::Path) -> String {
                    match tag {
                        Some(tag) => format!(
                            "{INFO}{}{RESET} has tag {INFO}{tag}{RESET}.",
                            variant_name.last()
                        ),
                        None => {
                            format!("{INFO}{}{RESET} has no explicit tag.", variant_name.last())
                        }
                    }
                }

                Some(format!(
                    "The variants have different {INFO}@tag{RESET} configurations.\n- {}\n- {}\n\nFix this by making sure the variants either have the exact same {INFO}@tag{RESET} configuration, or no {INFO}@tag{RESET} at all.",
                    tag_status(left_tag, left_variant_name),
                    tag_status(right_tag, right_variant_name),
                ))
            }
            VariantConfigurationIssue::IncompatibleConstructorCount { constructor_names } => {
                let total_constructor_count = constructor_names.len();
                let names_to_print = constructor_names.iter().take(3).collect::<Vec<_>>();
                let not_printed_constructor_count =
                    total_constructor_count.saturating_sub(names_to_print.len());
                let mut names = names_to_print
                    .iter()
                    .map(|name| format!("{INFO}{name}{RESET}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                if not_printed_constructor_count > 0 {
                    names.push_str(&format!(" (+{not_printed_constructor_count} more)"));
                }
                Some(format!(
                    "{INFO}{}{RESET} has {total_constructor_count} constructor{} that {INFO}{}{RESET} does not have: {names}\nTherefore, it is not possible for {INFO}{}{RESET} to represent {INFO}{}{RESET}.",
                    left_variant_name.last(),
                    if total_constructor_count == 1 {
                        ""
                    } else {
                        "s"
                    },
                    right_variant_name.last(),
                    right_variant_name.last(),
                    left_variant_name.last(),
                ))
            }
        },
        Some(SubtypeContext::DifferentTypeKinds {
            left_typename,
            right_typename,
            left_type_kind,
            right_type_kind,
        }) => Some(format!(
            "The types of {INFO}{}{RESET} and {INFO}{}{RESET} are different:\n- {INFO}{}{RESET} is {}\n- {INFO}{}{RESET} is {}",
            left_typename.last(),
            right_typename.last(),
            left_typename.last(),
            subtype_type_kind_name(*left_type_kind),
            right_typename.last(),
            subtype_type_kind_name(*right_type_kind)
        )),
        Some(SubtypeContext::RecordFieldsMismatch {
            left_record_name,
            right_record_name,
            issues,
        }) => {
            let mut output = format!(
                "The record {INFO}{}{RESET} cannot be coerced to the record {INFO}{}{RESET} because:",
                left_record_name.last(),
                right_record_name.last()
            );
            for issue in issues {
                output.push_str("\n- ");
                match issue {
                    RecordFieldSubtypeViolation::OptionalMismatch {
                        label,
                        left_optional,
                        right_optional,
                    } => {
                        output.push_str(&format!("The field {INFO}{label}{RESET} "));
                        match (*left_optional, *right_optional) {
                            (true, false) => output.push_str(&format!(
                                "is optional in record {INFO}{}{RESET}, but is not optional in record {INFO}{}{RESET}",
                                left_record_name.last(),
                                right_record_name.last()
                            )),
                            (false, true) => output.push_str(&format!(
                                "is not optional in record {INFO}{}{RESET}, but is optional in record {INFO}{}{RESET}",
                                left_record_name.last(),
                                right_record_name.last()
                            )),
                            _ => {}
                        }
                    }
                    RecordFieldSubtypeViolation::FieldRuntimeNameMismatch {
                        label,
                        left_as,
                        right_as,
                    } => {
                        output.push_str(&format!(
                            "Field {INFO}{label}{RESET} runtime representation"
                        ));
                        if let Some(as_name) = left_as {
                            output.push_str(&format!(
                                " is configured to be {INFO}\"{as_name}\"{RESET} (via the @as attribute)"
                            ));
                        } else {
                            output.push_str(&format!(" is {INFO}\"{label}\"{RESET}"));
                        }
                        output.push_str(&format!(
                            " in record {INFO}{}{RESET}, but in record {INFO}{}{RESET}",
                            right_record_name.last(),
                            left_record_name.last()
                        ));
                        if let Some(as_name) = right_as {
                            output.push_str(&format!(
                                " it is configured to be {INFO}\"{as_name}\"{RESET} (via the @as attribute)."
                            ));
                        } else {
                            output.push_str(&format!(" it is {INFO}\"{label}\"{RESET}."));
                        }
                        output.push_str(" Runtime representations must match.");
                    }
                    RecordFieldSubtypeViolation::FieldMissing { label } => {
                        output.push_str(&format!(
                            "The field {INFO}{label}{RESET} is missing in record {INFO}{}{RESET}, but present in record {INFO}{}{RESET}",
                            right_record_name.last(),
                            left_record_name.last()
                        ));
                    }
                }
            }
            Some(output)
        }
        _ => None,
    }
}

fn format_compiler_error_report_with_empty_blank_lines(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);

    for line in message.lines() {
        if !line.is_empty() {
            output.push_str("  ");
            output.push_str(line);
        }
        output.push('\n');
    }
    output.push('\n');
    output
}

fn format_compiler_error_report_for_subtype_context(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header(&mut output, arena, source, filename, loc);

    let mut blank_lines = 0;
    for line in message.lines() {
        if line.is_empty() {
            if blank_lines == 0 {
                output.push('\n');
            } else {
                output.push_str("  \n");
            }
            blank_lines += 1;
        } else {
            output.push_str("  ");
            output.push_str(line);
            output.push('\n');
        }
    }
    output.push('\n');
    output
}

fn format_array_type_clash_message(message: &str) -> String {
    let mut output = String::new();
    let mut blank_lines = 0;

    for line in message.lines() {
        if line.is_empty() {
            blank_lines += 1;
            if blank_lines <= 2 {
                output.push('\n');
            } else {
                output.push_str("  \n");
            }
        } else {
            output.push_str("  ");
            output.push_str(line);
            output.push('\n');
        }
    }

    output
}

fn format_await_type_clash_message(message: &str) -> String {
    let mut output = String::new();

    for line in message.lines() {
        if line.is_empty() {
            output.push('\n');
        } else if line == "Possible solutions:" {
            output.push_str(line);
            output.push('\n');
        } else {
            output.push_str("  ");
            output.push_str(line);
            output.push('\n');
        }
    }

    output
}

fn format_type_clash_message_with_empty_blank_lines(message: &str) -> String {
    let mut output = String::new();

    for line in message.lines() {
        if line.is_empty() {
            output.push('\n');
        } else {
            output.push_str("  ");
            output.push_str(line);
            output.push('\n');
        }
    }

    output
}

fn format_type_clash_return_message(message: &str) -> String {
    let lines: Vec<&str> = message.lines().collect();
    let mut output = String::new();

    for (idx, line) in lines.iter().enumerate() {
        if line.is_empty() {
            if lines
                .get(idx + 1)
                .is_some_and(|next| next.starts_with("You can convert "))
            {
                output.push_str("  \n");
            } else {
                output.push('\n');
            }
        } else {
            output.push_str("  ");
            output.push_str(line);
            output.push('\n');
        }
    }

    output
}

fn append_extra_type_clash_help(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    context: &Option<TypeClashContext>,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    if let Some(path) = type_clash_escape_constructor_path(type_ctx, trace) {
        message.push('\n');
        message.push_str("The type constructor ");
        message.push_str(&path);
        message.push_str(" would escape its scope");
        if !type_clash_top_actual_is_package(type_ctx, trace) {
            return;
        }
    } else if let Some((var, ty)) = type_clash_occurs_pair(type_ctx, trace) {
        // OCaml Printtyp.explanation (compiler/ml/printtyp.ml:1341-1345).
        let mut printer = TypeExprPrinter::new(type_ctx);
        message.push('\n');
        message.push_str("The type variable ");
        message.push_str(&printer.format(var));
        message.push_str(" occurs inside ");
        message.push_str(&printer.format(ty));
    }

    if matches!(context, Some(TypeClashContext::ArrayLiteral)) {
        message.push_str("\n\n");
        message.push_str("Arrays can only contain items of the same type.\n\n");
        message.push_str("Possible solutions:\n");
        message.push_str("- Convert all values in the array to the same type.\n");
        message.push_str("- Use a tuple, if your array is of fixed length. Tuples can mix types freely, and compiles to a JavaScript array. Example of a tuple: `let myTuple = (10, \"hello\", 15.5, true)");
    }

    if type_clash_array_to_tuple(type_ctx, trace) {
        message.push_str("\n\n- Fix this by passing a tuple instead of an array");
        if let Some(rewrite) = suggested_array_to_tuple_rewrite(arena, source, loc) {
            message.push_str(", like: ");
            message.push_str(INFO);
            message.push_str(&rewrite);
            message.push_str(RESET);
        } else {
            message.push_str(INFO);
            message.push_str(RESET);
        }
        message.push_str("\n\n");
    }

    if matches!(context, Some(TypeClashContext::Await)) {
        message.push_str("\n\n");
        message.push_str("You're trying to await something that is not a promise.\n\n");
        message.push_str("Possible solutions:\n");
        message.push_str("- Remove the ");
        message.push_str(INFO);
        message.push_str("await");
        message.push_str(RESET);
        message.push_str(" if this is not expected to be a promise\n");
        message.push_str("- Wrap the expression in ");
        message.push_str(INFO);
        message.push_str("Promise.resolve");
        message.push_str(RESET);
        message.push_str(" to convert the expression to a promise");
        return;
    }

    if matches!(context, Some(TypeClashContext::ComparisonOperator)) {
        message.push_str("\n\n");
        message.push_str("You can only compare things of the same type.");
    }

    if matches!(context, Some(TypeClashContext::JsxComponent)) {
        message.push_str("\n\nJSX tags must be React components, not plain functions.\n\n");
        message.push_str("Possible solutions:\n");
        message.push_str("- If this function takes labeled props, annotate it with ");
        message.push_str(INFO);
        message.push_str("@react.component");
        message.push_str(RESET);
        message.push_str("\n- If this function takes a single props record, annotate it with ");
        message.push_str(INFO);
        message.push_str("@react.componentWithProps");
        message.push_str(RESET);
        message.push_str("\n- If this is already a valid component-like value, wrap it with ");
        message.push_str(INFO);
        message.push_str("React.component(...)");
        message.push_str(RESET);
    } else if trace.iter().any(|(actual, expected)| {
        matches!(
            &*type_ctx.borrow_desc(type_ctx.repr(*actual)),
            TypeDesc::Tarrow { .. }
        ) && type_is_jsx_component(type_ctx, *expected)
    }) {
        message.push_str(
            "\n\nA React component is expected here, but this expression is a plain function.\n\n",
        );
        message.push_str("Possible solutions:\n");
        message.push_str("- Extract it to a component annotated with ");
        message.push_str(INFO);
        message.push_str("@react.component");
        message.push_str(RESET);
        message.push_str(" or ");
        message.push_str(INFO);
        message.push_str("@react.componentWithProps");
        message.push_str(RESET);
        message.push_str("\n- If this is already a valid component-like value, wrap it with ");
        message.push_str(INFO);
        message.push_str("React.component(...)");
        message.push_str(RESET);
    }

    if matches!(context, Some(TypeClashContext::IfCondition)) {
        message.push_str("\n\n");
        message.push_str("To fix this, change the highlighted code so it evaluates to a ");
        message.push_str(INFO);
        message.push_str("bool");
        message.push_str(RESET);
        message.push('.');
    }

    if matches!(context, Some(TypeClashContext::IfReturn)) {
        message.push_str("\n\n");
        message.push_str(INFO);
        message.push_str("if");
        message.push_str(RESET);
        message.push_str(" expressions must return the same type in all branches (");
        message.push_str(INFO);
        message.push_str("if");
        message.push_str(RESET);
        message.push_str(", ");
        message.push_str(INFO);
        message.push_str("else if");
        message.push_str(RESET);
        message.push_str(", ");
        message.push_str(INFO);
        message.push_str("else");
        message.push_str(RESET);
        message.push_str(").");
    }

    if matches!(context, Some(TypeClashContext::TernaryReturn)) {
        message.push_str("\n\n");
        message.push_str("Ternaries (");
        message.push_str(INFO);
        message.push('?');
        message.push_str(RESET);
        message.push_str(" and ");
        message.push_str(INFO);
        message.push(':');
        message.push_str(RESET);
        message.push_str(") must return the same type in both branches.");
    }

    if matches!(context, Some(TypeClashContext::SwitchExpression)) {
        message.push_str("\n\n");
        message.push_str("All branches in a ");
        message.push_str(INFO);
        message.push_str("switch");
        message.push_str(RESET);
        message.push_str(" must return the same type.\n");
        message.push_str("To fix this, change your branch to return the expected type.");
    }

    if matches!(context, Some(TypeClashContext::TryReturn)) {
        message.push_str("\n\n");
        message.push_str("The ");
        message.push_str(INFO);
        message.push_str("try");
        message.push_str(RESET);
        message.push_str(" body and the ");
        message.push_str(INFO);
        message.push_str("catch");
        message.push_str(RESET);
        message.push_str(" block must return the same type.\n");
        message.push_str("To fix this, change your try/catch blocks to return the expected type.");
    }

    if matches!(context, Some(TypeClashContext::StatementFunctionCall)) {
        message.push_str("\n\n");
        message.push_str("- Did you mean to assign this to a variable?\n");
        message.push_str(
            "- If you don't care about the result of this expression, you can assign it to ",
        );
        message.push_str(INFO);
        message.push('_');
        message.push_str(RESET);
        message.push_str(" via ");
        message.push_str(INFO);
        message.push_str("let _ = ...");
        message.push_str(RESET);
        message.push_str(" or pipe it to ");
        message.push_str(INFO);
        message.push_str("ignore");
        message.push_str(RESET);
        message.push_str(" via ");
        message.push_str(INFO);
        message.push_str("expression->ignore");
        message.push_str(RESET);
        message.push_str("\n\n\n");
    }

    if append_let_unwrap_return_help(type_ctx, trace, context, message) {
        return;
    }

    if append_optional_function_argument_help(type_ctx, arena, source, loc, context, trace, message)
    {
        return;
    }

    if !matches!(
        context,
        Some(TypeClashContext::StatementFunctionCall)
            | Some(TypeClashContext::SwitchExpression)
            | Some(TypeClashContext::TryReturn)
    ) && let Some(actual) = type_clash_expected_unit_actual(type_ctx, trace)
    {
        message.push_str("\n\n");
        if type_is_jsx_element_like(type_ctx, trace, actual) {
            message.push_str("- Did you forget to wrap this + adjacent JSX in a JSX fragment (");
            message.push_str(INFO);
            message.push_str("<></>");
            message.push_str(RESET);
            message.push_str(")?\n");
            message.push_str("- Did you mean to assign this to a variable?\n\n\n");
        } else {
            message.push_str("- Did you mean to assign this to a variable?\n");
            message.push_str(
                "- If you don't care about the result of this expression, you can assign it to ",
            );
            message.push_str(INFO);
            message.push('_');
            message.push_str(RESET);
            message.push_str(" via ");
            message.push_str(INFO);
            message.push_str("let _ = ...");
            message.push_str(RESET);
            message.push_str(" or pipe it to ");
            message.push_str(INFO);
            message.push_str("ignore");
            message.push_str(RESET);
            message.push_str(" via ");
            message.push_str(INFO);
            message.push_str("expression->ignore");
            message.push_str(RESET);
            message.push_str("\n\n\n");
        }
        return;
    }

    if append_optional_record_field_help(type_ctx, arena, source, loc, context, trace, message) {
        return;
    }

    if append_string_to_polyvariant_help(type_ctx, arena, source, loc, trace, message) {
        return;
    }

    if append_string_to_variant_help(type_ctx, arena, source, loc, trace, message) {
        return;
    }

    if type_clash_actual_promise(type_ctx, trace) {
        message.push_str("\n\n");
        message.push_str("- Did you mean to await this promise before using it?");
        message.push_str("\n\n");
        return;
    }

    if append_jsx_element_type_clash_help(type_ctx, trace, message) {
        return;
    }

    if append_braced_ident_record_help(type_ctx, arena, source, loc, context, trace, message) {
        return;
    }

    if append_object_literal_record_help(type_ctx, arena, source, loc, trace, message) {
        return;
    }

    let is_math_operator = append_math_operator_help(type_ctx, trace, context, message);
    let is_object_field_mismatch = append_object_field_mismatch_help(type_ctx, trace, message);
    let is_object_field_missing = append_object_field_missing_help(type_ctx, trace, message);
    let is_polyvariant_explanation = append_polyvariant_type_clash_help(type_ctx, trace, message);
    if !is_math_operator
        && !is_object_field_mismatch
        && !is_object_field_missing
        && !is_polyvariant_explanation
    {
        if append_runtime_coercion_help(type_ctx, arena, source, loc, trace, message) {
            return;
        }
        append_incompatible_type_parts(type_ctx, trace, message);
        append_dict_literal_help(type_ctx, trace, message);
    }
    append_simple_conversion_help(type_ctx, arena, source, loc, trace, message);
}

fn type_clash_escape_constructor_path(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<String> {
    for (actual, expected) in trace.iter().rev() {
        if let Some(path) = escaped_constructor_path(type_ctx, *actual, *expected) {
            return Some(path);
        }
        if let Some(path) = escaped_constructor_path(type_ctx, *expected, *actual) {
            return Some(path);
        }
    }
    None
}

/// The deepest trace pair with a type variable, when that variable occurs in
/// the other side (OCaml `Printtyp.mismatch` + `explanation`, printtyp.ml:1319-1345).
fn type_clash_occurs_pair(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<(TypeExprRef, TypeExprRef)> {
    let (a, b) = trace.iter().rev().find(|(a, b)| {
        let a = type_ctx.repr(*a);
        let b = type_ctx.repr(*b);
        matches!(&*type_ctx.get_desc(a), TypeDesc::Tvar(_))
            || matches!(&*type_ctx.get_desc(b), TypeDesc::Tvar(_))
    })?;
    let (a, b) = (type_ctx.repr(*a), type_ctx.repr(*b));
    let (var, ty) = if matches!(&*type_ctx.get_desc(a), TypeDesc::Tvar(_)) {
        (a, b)
    } else {
        (b, a)
    };
    crate::types::ctype::occur_check(
        type_ctx,
        None,
        crate::types::ctype::UnifyMode::Expression,
        var,
        ty,
    )
    .is_err()
    .then_some((var, ty))
}

fn type_clash_top_actual_is_package(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> bool {
    trace.first().is_some_and(|(actual, _)| {
        let actual = type_ctx.repr(*actual);
        let desc = type_ctx.get_desc(actual);
        matches!(&*desc, TypeDesc::Tpackage { .. })
    })
}

fn escaped_constructor_path(
    type_ctx: &TypeContext,
    constr_ty: TypeExprRef,
    var_ty: TypeExprRef,
) -> Option<String> {
    let var_ty = type_ctx.repr(var_ty);
    if !matches!(&*type_ctx.borrow_desc(var_ty), TypeDesc::Tvar(_)) {
        return None;
    }

    let var_level = type_ctx.get_level(var_ty);
    escaped_constructor_path_in_type(type_ctx, constr_ty, var_level, &mut AHashSet::new())
}

fn escaped_constructor_path_in_type(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
    var_level: i32,
    seen: &mut AHashSet<TypeExprRef>,
) -> Option<String> {
    let ty = type_ctx.repr(ty);
    if !seen.insert(ty) {
        return None;
    }

    let desc = type_ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            if var_level < path.binding_time() {
                return Some(path.name());
            }
            for arg in args {
                if let Some(path) =
                    escaped_constructor_path_in_type(type_ctx, *arg, var_level, seen)
                {
                    return Some(path);
                }
            }
            None
        }
        TypeDesc::Tpackage { args, .. } | TypeDesc::Ttuple(args) => {
            for arg in args {
                if let Some(path) =
                    escaped_constructor_path_in_type(type_ctx, *arg, var_level, seen)
                {
                    return Some(path);
                }
            }
            None
        }
        TypeDesc::Tarrow { args, ret } => args
            .iter()
            .find_map(|arg| escaped_constructor_path_in_type(type_ctx, arg.typ, var_level, seen))
            .or_else(|| escaped_constructor_path_in_type(type_ctx, *ret, var_level, seen)),
        TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) | TypeDesc::Tpoly { body: next, .. } => {
            escaped_constructor_path_in_type(type_ctx, *next, var_level, seen)
        }
        TypeDesc::Tobject { fields, .. } | TypeDesc::Tfield { rest: fields, .. } => {
            escaped_constructor_path_in_type(type_ctx, *fields, var_level, seen)
        }
        TypeDesc::Tvariant(row) => {
            for (_, field) in &row.row_fields {
                match field {
                    crate::types::type_expr::RowField::Rpresent(Some(arg)) => {
                        if let Some(path) =
                            escaped_constructor_path_in_type(type_ctx, *arg, var_level, seen)
                        {
                            return Some(path);
                        }
                    }
                    crate::types::type_expr::RowField::Reither { types, .. } => {
                        for arg in types {
                            if let Some(path) =
                                escaped_constructor_path_in_type(type_ctx, *arg, var_level, seen)
                            {
                                return Some(path);
                            }
                        }
                    }
                    _ => {}
                }
            }
            escaped_constructor_path_in_type(type_ctx, row.row_more, var_level, seen)
        }
        _ => None,
    }
}

fn append_math_operator_help(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    context: &Option<TypeClashContext>,
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let Some(TypeClashContext::MathOperator {
        for_float,
        operator,
        is_constant,
    }) = context
    else {
        return false;
    };

    let bottom_aliases = bottom_type_clash_aliases(trace);
    if operator == "+"
        && bottom_aliases.is_some_and(|(actual, expected)| {
            type_is_predef_path(type_ctx, actual, &crate::types::predef::path_string())
                || type_is_predef_path(type_ctx, expected, &crate::types::predef::path_string())
        })
    {
        message.push_str("\n\nAre you looking to concatenate strings? Use the operator ");
        message.push_str(INFO);
        message.push_str("++");
        message.push_str(RESET);
        message.push_str(", which concatenates strings.\n\nPossible solutions:\n- Change the ");
        message.push_str(INFO);
        message.push('+');
        message.push_str(RESET);
        message.push_str(" operator to ");
        message.push_str(INFO);
        message.push_str("++");
        message.push_str(RESET);
        message.push_str(" to concatenate strings instead.");
        return true;
    }

    let operator_for_other_type = match operator.as_str() {
        "+" => "+.",
        "+." => "+",
        "/" => "/.",
        "/." => "/",
        "-" => "-.",
        "*" => "*.",
        "*." => "*",
        other => other,
    };
    let operator_text = match operator.as_bytes().first().copied() {
        Some(b'+') => "add",
        Some(b'-') => "subtract",
        Some(b'/') => "divide",
        Some(b'*') => "multiply",
        _ => "compute",
    };
    let target_type = if *for_float { "float" } else { "int" };

    message.push_str(
        "\n\nFloats and ints have their own mathematical operators. This means you cannot ",
    );
    message.push_str(operator_text);
    message.push_str(" a float and an int without converting between the two.\n\nPossible solutions:\n- Ensure all values in this calculation have the type ");
    message.push_str(INFO);
    message.push_str(target_type);
    message.push_str(RESET);
    message.push_str(". You can convert between floats and ints via ");
    message.push_str(INFO);
    message.push_str("Float.toInt");
    message.push_str(RESET);
    message.push_str(" and ");
    message.push_str(INFO);
    message.push_str("Int.fromFloat");
    message.push_str(RESET);
    message.push('.');

    if let Some(constant) = is_constant {
        message.push_str("\n- Make ");
        message.push_str(INFO);
        message.push_str(constant);
        message.push_str(RESET);
        message.push_str(if *for_float { " a " } else { " an " });
        message.push_str(INFO);
        message.push_str(target_type);
        message.push_str(RESET);
        if *for_float {
            message.push_str(" by adding a trailing dot: ");
            message.push_str(INFO);
            message.push_str(constant);
            message.push('.');
            message.push_str(RESET);
        } else {
            message.push_str(" by removing the dot or explicitly converting to int");
        }
    } else if [
        bottom_aliases,
        nested_type_clash_pair(type_ctx, trace),
        trace.first().copied(),
    ]
    .into_iter()
    .flatten()
    .any(|(actual, expected)| {
        type_pair_has_names(type_ctx, actual, expected, "float", "int")
            || type_pair_has_names(type_ctx, actual, expected, "int", "float")
    }) {
        message.push_str("\n- Change the operator to ");
        message.push_str(INFO);
        message.push_str(operator_for_other_type);
        message.push_str(RESET);
        message.push_str(", which works on ");
        message.push_str(INFO);
        message.push_str(if *for_float { "int" } else { "float" });
        message.push_str(RESET);
    }

    true
}

fn type_pair_has_names(
    type_ctx: &TypeContext,
    actual: TypeExprRef,
    expected: TypeExprRef,
    actual_name: &str,
    expected_name: &str,
) -> bool {
    simple_type_constr_name(type_ctx, actual).as_deref() == Some(actual_name)
        && simple_type_constr_name(type_ctx, expected).as_deref() == Some(expected_name)
}

fn append_let_unwrap_return_help(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    context: &Option<TypeClashContext>,
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    if !matches!(context, Some(TypeClashContext::LetUnwrapReturn)) {
        return false;
    }

    enum LetUnwrapKind {
        Option,
        Result,
        Unknown,
    }

    let kind = [
        trace.first().copied(),
        bottom_type_clash_aliases(trace),
        nested_type_clash_pair(type_ctx, trace),
    ]
    .into_iter()
    .flatten()
    .find_map(|(actual, expected)| {
        if type_is_predef_path(type_ctx, actual, &crate::types::predef::path_option())
            || type_is_predef_path(type_ctx, expected, &crate::types::predef::path_option())
        {
            Some(LetUnwrapKind::Option)
        } else if type_is_predef_path(type_ctx, actual, &crate::types::predef::path_result())
            || type_is_predef_path(type_ctx, expected, &crate::types::predef::path_result())
        {
            Some(LetUnwrapKind::Result)
        } else {
            None
        }
    })
    .unwrap_or(LetUnwrapKind::Unknown);

    match kind {
        LetUnwrapKind::Option => {
            message.push_str("\n\nThis ");
            message.push_str(INFO);
            message.push_str("let?");
            message.push_str(RESET);
            message.push_str(" unwraps an ");
            message.push_str(INFO);
            message.push_str("option");
            message.push_str(RESET);
            message.push_str("; use it where the enclosing function or let binding returns an ");
            message.push_str(INFO);
            message.push_str("option");
            message.push_str(RESET);
            message.push_str(" so ");
            message.push_str(INFO);
            message.push_str("None");
            message.push_str(RESET);
            message.push_str(" can propagate.\n\nPossible solutions:\n- Change the enclosing function or let binding to return ");
            message.push_str(INFO);
            message.push_str("option<'t>");
            message.push_str(RESET);
            message.push_str(" and use ");
            message.push_str(INFO);
            message.push_str("Some");
            message.push_str(RESET);
            message.push_str(" for success; ");
            message.push_str(INFO);
            message.push_str("let?");
            message.push_str(RESET);
            message.push_str(" will propagate ");
            message.push_str(INFO);
            message.push_str("None");
            message.push_str(RESET);
            message.push_str(".\n- Replace ");
            message.push_str(INFO);
            message.push_str("let?");
            message.push_str(RESET);
            message.push_str(" with a ");
            message.push_str(INFO);
            message.push_str("switch");
            message.push_str(RESET);
            message.push_str(" and handle the ");
            message.push_str(INFO);
            message.push_str("None");
            message.push_str(RESET);
            message.push_str(" case explicitly.\n- If you want a default value instead of early return, unwrap using ");
            message.push_str(INFO);
            message.push_str("Option.getOr(default)");
            message.push_str(RESET);
            message.push('.');
        }
        LetUnwrapKind::Result => {
            message.push_str("\n\nThis ");
            message.push_str(INFO);
            message.push_str("let?");
            message.push_str(RESET);
            message.push_str(" unwraps a ");
            message.push_str(INFO);
            message.push_str("result");
            message.push_str(RESET);
            message.push_str("; use it where the enclosing function or let binding returns a ");
            message.push_str(INFO);
            message.push_str("result");
            message.push_str(RESET);
            message.push_str(" so ");
            message.push_str(INFO);
            message.push_str("Error");
            message.push_str(RESET);
            message.push_str(" can propagate.\n\nPossible solutions:\n- Change the enclosing function or let binding to return ");
            message.push_str(INFO);
            message.push_str("result<'ok, 'error>");
            message.push_str(RESET);
            message.push_str("; use ");
            message.push_str(INFO);
            message.push_str("Ok");
            message.push_str(RESET);
            message.push_str(" for success, and ");
            message.push_str(INFO);
            message.push_str("let?");
            message.push_str(RESET);
            message.push_str(" will propagate ");
            message.push_str(INFO);
            message.push_str("Error");
            message.push_str(RESET);
            message.push_str(".\n- Replace ");
            message.push_str(INFO);
            message.push_str("let?");
            message.push_str(RESET);
            message.push_str(" with a ");
            message.push_str(INFO);
            message.push_str("switch");
            message.push_str(RESET);
            message.push_str(" and handle the ");
            message.push_str(INFO);
            message.push_str("Error");
            message.push_str(RESET);
            message.push_str(" case explicitly.\n- If you want a default value instead of early return, unwrap using ");
            message.push_str(INFO);
            message.push_str("Result.getOr(default)");
            message.push_str(RESET);
            message.push('.');
        }
        LetUnwrapKind::Unknown => {
            message.push_str("\n\n");
            message.push_str(INFO);
            message.push_str("let?");
            message.push_str(RESET);
            message.push_str(" can only be used in a context that expects ");
            message.push_str(INFO);
            message.push_str("option");
            message.push_str(RESET);
            message.push_str(" or ");
            message.push_str(INFO);
            message.push_str("result");
            message.push_str(RESET);
            message.push_str(".\n\nPossible solutions:\n- Change the enclosing function or let binding to return an ");
            message.push_str(INFO);
            message.push_str("option<'t>");
            message.push_str(RESET);
            message.push_str(" or ");
            message.push_str(INFO);
            message.push_str("result<'ok, 'error>");
            message.push_str(RESET);
            message.push_str(" and propagate with ");
            message.push_str(INFO);
            message.push_str("Some/Ok");
            message.push_str(RESET);
            message.push_str(".\n- Replace ");
            message.push_str(INFO);
            message.push_str("let?");
            message.push_str(RESET);
            message.push_str(" with a ");
            message.push_str(INFO);
            message.push_str("switch");
            message.push_str(RESET);
            message.push_str(" and handle the ");
            message.push_str(INFO);
            message.push_str("None/Error");
            message.push_str(RESET);
            message.push_str(" case explicitly.\n- If you want a default value instead of early return, unwrap using ");
            message.push_str(INFO);
            message.push_str("Option.getOr(default)");
            message.push_str(RESET);
            message.push_str(" or ");
            message.push_str(INFO);
            message.push_str("Result.getOr(default)");
            message.push_str(RESET);
            message.push('.');
        }
    }

    true
}

fn type_is_predef_path(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
    expected_path: &crate::types::path::Path,
) -> bool {
    let repr = type_ctx.repr(ty);
    match &*type_ctx.get_desc(repr) {
        TypeDesc::Tconstr { path, .. } => path.same(expected_path),
        TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => {
            type_is_predef_path(type_ctx, *next, expected_path)
        }
        _ => false,
    }
}

fn type_is_jsx_component(type_ctx: &TypeContext, ty: TypeExprRef) -> bool {
    let repr = type_ctx.repr(ty);
    match &*type_ctx.get_desc(repr) {
        TypeDesc::Tconstr {
            path: crate::types::path::Path::Pdot(parent, name, _),
            ..
        } => {
            name == "component"
                && matches!(
                    parent.as_ref(),
                    crate::types::path::Path::Pident(id) if id.name() == "Jsx"
                )
        }
        TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => type_is_jsx_component(type_ctx, *next),
        _ => false,
    }
}

fn type_expands_to_predef_path(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
    expected_path: &crate::types::path::Path,
) -> bool {
    let mut current = type_ctx.repr(ty);
    let mut seen = AHashSet::new();
    loop {
        if !seen.insert(current) {
            return false;
        }
        if type_is_predef_path(type_ctx, current, expected_path) {
            return true;
        }
        let Some(expansion) = type_alias_expansion(type_ctx, current) else {
            return false;
        };
        let expansion = type_ctx.repr(expansion);
        if type_expansion_same(type_ctx, current, expansion) {
            return false;
        }
        current = expansion;
    }
}

fn type_clash_actual_promise(type_ctx: &TypeContext, trace: &[(TypeExprRef, TypeExprRef)]) -> bool {
    let is_promise_like =
        |ty| type_expands_to_predef_path(type_ctx, ty, &crate::types::predef::path_promise());
    trace
        .first()
        .copied()
        .into_iter()
        .chain(bottom_type_clash_aliases(trace))
        .any(|(actual, expected)| is_promise_like(actual) && !is_promise_like(expected))
}

fn append_optional_record_field_help(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    context: &Option<TypeClashContext>,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let Some(TypeClashContext::RecordField {
        field_name,
        optional: true,
        jsx,
    }) = context
    else {
        return false;
    };
    let Some((actual, _expected)) = trace.first().copied() else {
        return false;
    };
    let TypeDesc::Tconstr { path, .. } = &*type_ctx.get_desc(type_ctx.repr(actual)) else {
        return false;
    };
    if !path.same(&crate::types::predef::path_option()) {
        return false;
    }

    let passed_text = source_text_at_loc(arena, source, loc).unwrap_or_default();
    message.push_str("\n\n");
    message.push_str(INFO);
    message.push_str(field_name);
    message.push_str(RESET);
    if jsx.is_some() {
        message.push_str(
            " is an optional component prop, and you're passing an optional value to it.\n",
        );
        message.push_str("Values passed to an optional component prop don't need to be wrapped in an option. You might need to adjust the type of the value supplied.\n");
    } else {
        message.push_str(
            " is an optional record field, and you're passing an optional value to it.\n",
        );
        message.push_str("Values passed to an optional record field don't need to be wrapped in an option. You might need to adjust the type of the value supplied.\n");
    }
    message.push_str("     \n");
    message.push_str("Possible solutions: \n");
    message.push_str("- Unwrap the option from the value you're passing in\n");
    message.push_str("- If you really do want to pass the optional value, prepend the value with ");
    message.push_str(INFO);
    message.push('?');
    message.push_str(RESET);
    message.push_str(" to show you want to pass the option, like: ");
    message.push_str(INFO);
    if jsx.is_some() {
        message.push_str(field_name);
        message.push_str("=?");
        message.push_str(&passed_text);
    } else {
        message.push('{');
        message.push_str(field_name);
        message.push_str(": ?");
        message.push_str(&passed_text);
    }
    message.push_str(RESET);
    if jsx.is_none() {
        message.push('}');
    }
    true
}

fn append_optional_function_argument_help(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    context: &Option<TypeClashContext>,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let Some(TypeClashContext::FunctionArgument { optional: true, .. }) = context else {
        return false;
    };
    let Some((actual, _expected)) = trace.first().copied() else {
        return false;
    };
    if !type_is_predef_path(type_ctx, actual, &crate::types::predef::path_option()) {
        return false;
    }

    let passed_text = source_text_at_loc(arena, source, loc).unwrap_or_default();
    message.push_str("\n\n");
    message.push_str("You're passing an optional value into an optional function argument.\n");
    message.push_str("Values passed to an optional function argument don't need to be wrapped in an option. You might need to adjust the type of the value supplied.\n");
    message.push_str("     \n");
    message.push_str("Possible solutions: \n");
    message.push_str("- Unwrap the option from the value you're passing in\n");
    message.push_str("- If you really do want to pass the optional value, prepend the value with ");
    message.push_str(INFO);
    message.push('?');
    message.push_str(RESET);
    message.push_str(" to show you want to pass the option, like: ");
    message.push_str(INFO);
    message.push('?');
    message.push_str(&passed_text);
    message.push_str(RESET);

    true
}

fn source_text_at_loc(arena: &ParseArena, source: &str, loc: LocIdx) -> Option<String> {
    let start = arena.loc_start(loc).cnum as usize;
    let end = arena.loc_end(loc).cnum as usize;
    crate::source_text::latin1_slice(source, start, end)
        .map(str::trim)
        .map(str::to_string)
}

fn append_runtime_coercion_help(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let Some(rewrite) = runtime_coercion_suggestion(type_ctx, arena, source, loc, trace) else {
        return false;
    };

    message.push_str("\n\nPossible solutions: \n");
    message.push_str("- These types are compatible at runtime. You can use the coercion operator to convert to the expected type: ");
    message.push_str(INFO);
    message.push_str(&rewrite);
    message.push_str(RESET);
    message.push_str("\n\n");
    true
}

fn runtime_coercion_suggestion(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<String> {
    let (actual, expected) = trace.first().copied()?;
    if type_is_polyvariant(type_ctx, actual) && type_is_polyvariant(type_ctx, expected) {
        return None;
    }

    let target_ty = bottom_type_clash_aliases(trace)
        .map(|(_, target)| target)
        .unwrap_or(expected);
    let target_type_string = format_type_expr(type_ctx, target_ty);

    if !runtime_coercion_compatible(type_ctx, actual, expected) {
        return None;
    }

    let target_expr_text = source_text_at_loc(arena, source, loc)?;
    if source_text_is_constant(&target_expr_text) {
        return None;
    }

    Some(format!("({target_expr_text} :> {target_type_string})\n"))
}

fn runtime_coercion_compatible(
    type_ctx: &TypeContext,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> bool {
    let env = crate::types::Env::empty();
    crate::types::ctype::subtype_now(type_ctx, &env, actual, expected).is_ok()
        || runtime_record_coercion_compatible(type_ctx, actual, expected)
        || runtime_variant_to_primitive_coercion_compatible(type_ctx, actual, expected)
}

fn runtime_record_coercion_compatible(
    type_ctx: &TypeContext,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> bool {
    let Some((actual_repr, actual_fields)) = record_fields_for_type(type_ctx, actual) else {
        return false;
    };
    let Some((expected_repr, expected_fields)) = record_fields_for_type(type_ctx, expected) else {
        return false;
    };
    if actual_repr != expected_repr {
        return false;
    }

    expected_fields.iter().all(|expected_field| {
        let Some(actual_field) = actual_fields
            .iter()
            .find(|actual_field| actual_field.ld_id.name() == expected_field.ld_id.name())
        else {
            return false;
        };
        actual_field.ld_optional == expected_field.ld_optional
            && label_declaration_runtime_name(actual_field)
                == label_declaration_runtime_name(expected_field)
            && runtime_field_type_compatible(type_ctx, actual_field.ld_type, expected_field.ld_type)
    })
}

fn record_fields_for_type(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
) -> Option<(
    crate::types::decl::RecordRepresentation,
    Vec<crate::types::decl::LabelDeclaration>,
)> {
    let repr = type_ctx.repr(ty);
    let desc = type_ctx.get_desc(repr);
    let TypeDesc::Tconstr { path, .. } = &*desc else {
        return None;
    };
    let decl = type_decl_for_path(type_ctx, path)?;
    match decl.type_kind {
        crate::types::decl::TypeKind::TypeRecord(fields, record_repr) => {
            Some((record_repr, fields.into_vec()))
        }
        _ => None,
    }
}

fn runtime_field_type_compatible(
    type_ctx: &TypeContext,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> bool {
    type_ctx.repr(actual) == type_ctx.repr(expected)
        || format_type_expr(type_ctx, actual) == format_type_expr(type_ctx, expected)
        || {
            let env = crate::types::Env::empty();
            crate::types::ctype::subtype_now(type_ctx, &env, actual, expected).is_ok()
        }
}

fn label_declaration_runtime_name(label: &crate::types::decl::LabelDeclaration) -> String {
    // `Record_runtime.declaration_name`.
    label.declaration_name()
}

fn runtime_variant_to_primitive_coercion_compatible(
    type_ctx: &TypeContext,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> bool {
    let Some(expected_path) = primitive_coercion_target_path(type_ctx, expected) else {
        return false;
    };
    let Some((actual_path, constructors, type_params, layout, unboxed)) =
        variant_constructors_for_type(type_ctx, actual)
    else {
        return false;
    };
    if actual_path.same(&crate::types::predef::path_bool()) || !type_params.is_empty() {
        return false;
    }

    constructors
        .iter()
        .enumerate()
        .all(|(position, constructor)| {
            variant_constructor_runtime_matches_primitive(
                type_ctx,
                constructor,
                &layout.constructors[position],
                unboxed,
                &expected_path,
            )
        })
}

fn primitive_coercion_target_path(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
) -> Option<crate::types::Path> {
    let repr = type_ctx.repr(ty);
    let desc = type_ctx.get_desc(repr);
    let TypeDesc::Tconstr { path, args, .. } = &*desc else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    [
        crate::types::predef::path_string(),
        crate::types::predef::path_int(),
        crate::types::predef::path_float(),
        crate::types::predef::path_bigint(),
    ]
    .into_iter()
    .find(|primitive_path| path.same(primitive_path))
}

fn variant_constructors_for_type(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
) -> Option<(
    crate::types::Path,
    Vec<crate::types::decl::ConstructorDeclaration>,
    Vec<TypeExprRef>,
    crate::types::VariantLayout,
    bool,
)> {
    let repr = type_ctx.repr(ty);
    let desc = type_ctx.get_desc(repr);
    let TypeDesc::Tconstr { path, .. } = &*desc else {
        return None;
    };
    let decl = type_decl_for_path(type_ctx, path)?;
    match decl.type_kind {
        crate::types::decl::TypeKind::TypeVariant(constructors, layout_ref) => {
            let layout = type_ctx.variant_layout(layout_ref);
            let unboxed = decl.type_representation == crate::types::TypeRepresentation::Unboxed
                || layout.configuration().unboxed;
            Some((
                path.clone(),
                constructors.into_vec(),
                decl.type_params,
                layout,
                unboxed,
            ))
        }
        _ => None,
    }
}

fn variant_constructor_runtime_matches_primitive(
    type_ctx: &TypeContext,
    constructor: &crate::types::decl::ConstructorDeclaration,
    case: &crate::types::VariantConstructorCase,
    unboxed: bool,
    target_path: &crate::types::Path,
) -> bool {
    match &constructor.cd_args {
        crate::types::decl::ConstructorArguments::CstrTuple(args) if args.is_empty() => {
            let tag = match case {
                crate::types::VariantConstructorCase::Constant(tag) => &tag.literal,
                crate::types::VariantConstructorCase::Block(_) => unreachable!(),
            };
            match variant_constructor_as_payload(tag) {
                None | Some(VariantConstructorAsPayload::String) => {
                    target_path.same(&crate::types::predef::path_string())
                }
                Some(VariantConstructorAsPayload::Int) => {
                    target_path.same(&crate::types::predef::path_int())
                }
                Some(VariantConstructorAsPayload::Float) => {
                    target_path.same(&crate::types::predef::path_float())
                }
                Some(VariantConstructorAsPayload::BigInt) => {
                    target_path.same(&crate::types::predef::path_bigint())
                }
                Some(
                    VariantConstructorAsPayload::Bool
                    | VariantConstructorAsPayload::Null
                    | VariantConstructorAsPayload::Undefined,
                ) => false,
            }
        }
        crate::types::decl::ConstructorArguments::CstrTuple(args) if args.len() == 1 && unboxed => {
            !target_path.same(&crate::types::predef::path_int())
                && type_expr_path_same(type_ctx, args[0], target_path)
        }
        _ => false,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum VariantConstructorAsPayload {
    String,
    Int,
    Float,
    BigInt,
    Bool,
    Null,
    Undefined,
}

fn variant_constructor_as_payload(
    tag: &Option<crate::types::VariantLiteralTag>,
) -> Option<VariantConstructorAsPayload> {
    tag.as_ref().map(|tag| match tag {
        crate::types::VariantLiteralTag::String(_) => VariantConstructorAsPayload::String,
        crate::types::VariantLiteralTag::Int(_) => VariantConstructorAsPayload::Int,
        crate::types::VariantLiteralTag::Float(_) => VariantConstructorAsPayload::Float,
        crate::types::VariantLiteralTag::BigInt(_) => VariantConstructorAsPayload::BigInt,
        crate::types::VariantLiteralTag::Bool(_) => VariantConstructorAsPayload::Bool,
        crate::types::VariantLiteralTag::Null => VariantConstructorAsPayload::Null,
        crate::types::VariantLiteralTag::Undefined => VariantConstructorAsPayload::Undefined,
    })
}

fn type_expr_path_same(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
    target_path: &crate::types::Path,
) -> bool {
    matches!(
        &*type_ctx.get_desc(type_ctx.repr(ty)),
        TypeDesc::Tconstr { path, args, .. } if args.is_empty() && path.same(target_path)
    )
}

fn source_text_is_constant(source_text: &str) -> bool {
    let text = source_text.trim();
    simple_string_literal_value(text).is_some()
        || (text.starts_with('\'') && text.ends_with('\''))
        || text
            .as_bytes()
            .first()
            .is_some_and(|byte| byte.is_ascii_digit())
}

fn append_string_to_polyvariant_help(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let Some(row) = trace.iter().copied().find_map(|(actual, expected)| {
        (simple_type_constr_name(type_ctx, actual).as_deref() == Some("string"))
            .then(|| polyvariant_row(type_ctx, expected))
            .flatten()
    }) else {
        return false;
    };
    let Some(source_literal) = source_text_at_loc(arena, source, loc) else {
        return false;
    };
    let Some(string_value) = simple_string_literal_value(&source_literal) else {
        return false;
    };
    let fields = visible_polyvariant_fields(type_ctx, &row);
    if !fields
        .iter()
        .any(|(label, _)| label.as_str() == string_value)
    {
        return false;
    }

    message.push_str("\n\nPossible solutions:\n");
    message.push_str("- The constant passed matches one of the expected polymorphic variant constructors. Did you mean to pass this as a polymorphic variant? If so, rewrite ");
    message.push_str(INFO);
    message.push_str(&source_literal);
    message.push_str(RESET);
    message.push_str(" to ");
    message.push_str(INFO);
    message.push('#');
    message.push_str(&string_value);
    message.push_str(RESET);
    true
}

fn append_string_to_variant_help(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let Some((constructors, layout)) = trace.iter().copied().find_map(|(actual, expected)| {
        (simple_type_constr_name(type_ctx, actual).as_deref() == Some("string"))
            .then(|| concrete_variant_constructors(type_ctx, expected))
            .flatten()
    }) else {
        return false;
    };
    let Some(source_literal) = source_text_at_loc(arena, source, loc) else {
        return false;
    };
    let Some(string_value) = simple_string_literal_value(&source_literal) else {
        return false;
    };
    let Some(constructor_name) =
        constructors
            .iter()
            .enumerate()
            .find_map(|(position, constructor)| {
                let runtime_repr = variant_constructor_string_runtime_repr(
                    constructor,
                    &layout.constructors[position],
                )?;
                (runtime_repr == string_value).then(|| constructor.cd_id.name().to_string())
            })
    else {
        return false;
    };

    message.push_str("\n\nPossible solutions:\n");
    message.push_str("- The constant passed matches the runtime representation of one of the expected variant constructors. Did you mean to pass this as a variant constructor? If so, rewrite ");
    message.push_str(INFO);
    message.push_str(&source_literal);
    message.push_str(RESET);
    message.push_str(" to ");
    message.push_str(INFO);
    message.push_str(&constructor_name);
    message.push_str(RESET);
    true
}

fn concrete_variant_constructors(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
) -> Option<(
    Vec<crate::types::decl::ConstructorDeclaration>,
    crate::types::VariantLayout,
)> {
    let mut current = type_ctx.repr(ty);
    let mut seen = Vec::new();

    loop {
        if seen.contains(&current) {
            return None;
        }
        seen.push(current);

        let desc = type_ctx.get_desc(current);
        match &*desc {
            TypeDesc::Tconstr { path, .. } => {
                let decl = type_decl_for_path(type_ctx, path)?;
                match decl.type_kind {
                    crate::types::decl::TypeKind::TypeVariant(constructors, layout_ref) => {
                        return Some((
                            constructors.into_vec(),
                            type_ctx.variant_layout(layout_ref),
                        ));
                    }
                    crate::types::decl::TypeKind::TypeAbstract => {
                        current = type_ctx.repr(decl.type_manifest?);
                    }
                    _ => return None,
                }
            }
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => {
                current = type_ctx.repr(*next);
            }
            _ => return None,
        }
    }
}

fn type_decl_for_path(
    type_ctx: &TypeContext,
    path: &crate::types::Path,
) -> Option<crate::types::TypeDeclaration> {
    if let crate::types::Path::Pident(id) = path
        && id.stamp() != 0
        && let Some(decl) = type_ctx.find_type_decl_by_stamp(id.stamp())
    {
        return Some(decl.clone());
    }

    if let Some(decl) = type_ctx.find_type_decl_by_path(&path.name()) {
        return Some(decl.clone());
    }

    type_ctx
        .find_type_decl(path.head_name())
        .map(|decl| decl.clone())
}

fn variant_constructor_string_runtime_repr(
    constructor: &crate::types::decl::ConstructorDeclaration,
    case: &crate::types::VariantConstructorCase,
) -> Option<String> {
    let tag = match case {
        crate::types::VariantConstructorCase::Constant(tag) => &tag.literal,
        crate::types::VariantConstructorCase::Block(block) => &block.tag().literal,
    };
    match tag {
        Some(crate::types::VariantLiteralTag::String(value)) => Some(value.clone()),
        Some(_) => None,
        None => Some(constructor.cd_id.name().to_string()),
    }
}

fn type_clash_string_to_polyvariant(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> bool {
    trace.iter().copied().any(|(actual, expected)| {
        simple_type_constr_name(type_ctx, actual).as_deref() == Some("string")
            && polyvariant_row(type_ctx, expected).is_some()
    })
}

fn type_clash_string_to_variant(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> bool {
    trace.iter().copied().any(|(actual, expected)| {
        simple_type_constr_name(type_ctx, actual).as_deref() == Some("string")
            && concrete_variant_constructors(type_ctx, expected).is_some()
    })
}

fn simple_string_literal_value(source_literal: &str) -> Option<String> {
    let quoted = source_literal.strip_prefix('"')?.strip_suffix('"')?;
    if quoted.contains('\\') {
        return None;
    }
    Some(quoted.to_string())
}

fn append_object_literal_record_help(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";
    const RESET: &str = "\x1b[0m";

    let has_object_record_mismatch = [
        bottom_type_clash_aliases(trace),
        nested_type_clash_pair(type_ctx, trace),
        trace.first().copied(),
    ]
    .into_iter()
    .flatten()
    .any(|(actual, expected)| {
        type_is_object(type_ctx, actual) && type_is_record(type_ctx, expected)
    });
    if !has_object_record_mismatch {
        return false;
    }

    message.push_str("\n\nYou're passing a ");
    message.push_str(ERROR);
    message.push_str("ReScript object");
    message.push_str(RESET);
    message.push_str(" where a ");
    message.push_str(INFO);
    message.push_str("record");
    message.push_str(RESET);
    message.push_str(
        " is expected. Objects are written with quoted keys, and records with unquoted keys.",
    );
    message.push_str("\n\nPossible solutions: \n- Rewrite the object to a record");
    if let Some(rewrite) = source_text_at_loc(arena, source, loc)
        .and_then(|text| object_literal_to_record_rewrite(&text))
    {
        message.push_str(", like: ");
        message.push_str(INFO);
        message.push_str(&rewrite);
        message.push_str(RESET);
    }
    message.push('\n');
    message.push('\n');

    true
}

fn append_braced_ident_record_help(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    context: &Option<TypeClashContext>,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    if !matches!(context, Some(TypeClashContext::BracedIdent)) {
        return false;
    }
    let Some((_, expected)) = trace.first().copied() else {
        return false;
    };
    if !type_is_record(type_ctx, expected) {
        return false;
    }

    let rewrite = source_text_at_loc(arena, source, loc)
        .map(|text| braced_ident_record_rewrite(&text))
        .unwrap_or_default();

    message
        .push_str("\n\nYou might have meant to pass this as a record, but wrote it as a block.\n");
    message.push_str(
        "Braces with a single identifier counts as a block, not a record with a single (punned) field.\n\n",
    );
    message.push_str("Possible solutions: \n");
    message.push_str("- Write out the full record with field and value, like: ");
    message.push_str(INFO);
    message.push_str(&rewrite);
    message.push_str(RESET);
    message.push_str("\n- Return the expected record from the block");

    true
}

fn braced_ident_record_rewrite(text: &str) -> String {
    let ident = text
        .trim()
        .trim_start_matches('{')
        .trim_end_matches('}')
        .trim();
    format!("{{{ident}: {ident}}}")
}

fn object_literal_to_record_rewrite(text: &str) -> Option<String> {
    let mut output = String::with_capacity(text.len());
    let chars: Vec<char> = text.chars().collect();
    let mut index = 0;
    let mut changed = false;

    while index < chars.len() {
        if chars[index] != '"' {
            output.push(chars[index]);
            index += 1;
            continue;
        }

        let start = index + 1;
        let mut end = start;
        let mut escaped = false;
        while end < chars.len() {
            let ch = chars[end];
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                break;
            }
            end += 1;
        }
        if end >= chars.len() {
            return None;
        }

        let key: String = chars[start..end].iter().collect();
        let mut after = end + 1;
        while after < chars.len() && chars[after].is_whitespace() {
            after += 1;
        }
        if after < chars.len() && chars[after] == ':' && is_record_field_rewrite_key(&key) {
            output.push_str(&key);
            changed = true;
        } else {
            output.push('"');
            output.push_str(&key);
            output.push('"');
        }
        index = end + 1;
    }

    changed.then_some(output)
}

fn is_record_field_rewrite_key(key: &str) -> bool {
    let mut chars = key.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn append_jsx_element_type_clash_help(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let Some((actual, _expected)) = jsx_element_type_clash_pair(type_ctx, trace) else {
        return false;
    };

    let repr = type_ctx.repr(actual);
    match &*type_ctx.get_desc(repr) {
        TypeDesc::Tconstr { path, args: _, .. } if path.same(&crate::types::predef::path_int()) => {
            message.push_str("\n\nIn JSX, all content must be JSX elements. You can convert int to a JSX element with ");
            message.push_str(INFO);
            message.push_str("React.int");
            message.push_str(RESET);
            message.push_str(".\n\n");
            true
        }
        TypeDesc::Tconstr { path, args: _, .. }
            if path.same(&crate::types::predef::path_string()) =>
        {
            message.push_str("\n\nIn JSX, all content must be JSX elements. You can convert string to a JSX element with ");
            message.push_str(INFO);
            message.push_str("React.string");
            message.push_str(RESET);
            message.push_str(".\n\n");
            true
        }
        TypeDesc::Tconstr { path, args: _, .. }
            if path.same(&crate::types::predef::path_float()) =>
        {
            message.push_str("\n\nIn JSX, all content must be JSX elements. You can convert float to a JSX element with ");
            message.push_str(INFO);
            message.push_str("React.float");
            message.push_str(RESET);
            message.push_str(".\n\n");
            true
        }
        TypeDesc::Tconstr { path, args, .. }
            if args.len() == 1 && path.same(&crate::types::predef::path_option()) =>
        {
            message.push_str("\n\nYou need to unwrap this option to its underlying value first, then turn that value into a JSX element.\nFor ");
            message.push_str(INFO);
            message.push_str("None");
            message.push_str(RESET);
            message.push_str(", you can use ");
            message.push_str(INFO);
            message.push_str("React.null");
            message.push_str(RESET);
            message.push_str(" to output nothing into JSX.\n\n");
            true
        }
        TypeDesc::Tconstr { path, args, .. }
            if args.len() == 1 && path.same(&crate::types::predef::path_array()) =>
        {
            if type_is_jsx_element_named(type_ctx, args[0]) {
                message.push_str("\n\nIn JSX, all content must be JSX elements. You can convert array to a JSX element with ");
                message.push_str(INFO);
                message.push_str("React.array");
                message.push_str(RESET);
                message.push_str(" (for example by using a pipe: ->React.array.).\n\n");
            } else {
                message.push_str("\n\nYou need to convert each item in this array to a JSX element first, then use ");
                message.push_str(INFO);
                message.push_str("React.array");
                message.push_str(RESET);
                message.push_str(
                    " to convert the array of JSX elements into a single JSX element.\n\n",
                );
            }
            true
        }
        _ => false,
    }
}

fn jsx_element_type_clash_pair(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<(TypeExprRef, TypeExprRef)> {
    [
        trace.first().copied(),
        bottom_type_clash_aliases(trace),
        nested_type_clash_pair(type_ctx, trace),
    ]
    .into_iter()
    .flatten()
    .find(|(_, expected)| type_is_expected_jsx_element(type_ctx, trace, *expected))
}

fn type_is_expected_jsx_element(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    ty: TypeExprRef,
) -> bool {
    type_is_jsx_element(type_ctx, ty)
        || rendered_alias_expansion(type_ctx, ty, trace, false)
            .is_some_and(|expansion| type_is_jsx_element(type_ctx, expansion))
}

fn type_is_jsx_element_named(type_ctx: &TypeContext, ty: TypeExprRef) -> bool {
    type_is_jsx_element(type_ctx, ty) || format_type_expr(type_ctx, ty).ends_with(".element")
}

fn type_clash_expected_unit_actual(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<TypeExprRef> {
    [trace.first().copied(), bottom_type_clash_aliases(trace)]
        .into_iter()
        .flatten()
        .find_map(|(actual, expected)| type_is_unit(type_ctx, expected).then_some(actual))
}

fn type_is_unit(type_ctx: &TypeContext, ty: TypeExprRef) -> bool {
    let repr = type_ctx.repr(ty);
    match &*type_ctx.get_desc(repr) {
        TypeDesc::Tconstr { path, .. } => path.same(&crate::types::predef::path_unit()),
        TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => type_is_unit(type_ctx, *next),
        _ => false,
    }
}

fn type_is_jsx_element_like(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    ty: TypeExprRef,
) -> bool {
    type_is_jsx_element(type_ctx, ty)
        || rendered_alias_expansion(type_ctx, ty, trace, true)
            .is_some_and(|expansion| type_is_jsx_element(type_ctx, expansion))
}

fn type_is_jsx_element(type_ctx: &TypeContext, ty: TypeExprRef) -> bool {
    let repr = type_ctx.repr(ty);
    match &*type_ctx.get_desc(repr) {
        TypeDesc::Tconstr { path, .. } => path.name() == "Jsx.element",
        TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => type_is_jsx_element(type_ctx, *next),
        _ => false,
    }
}

fn append_incompatible_type_parts(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";

    let reports = super_trace_reports(type_ctx, trace);
    if reports.is_empty() {
        return;
    };

    for (idx, report) in reports.iter().enumerate() {
        if idx == 0 {
            message.push_str("\n\nThe incompatible parts:\n  ");
        } else {
            message.push_str("\n  \n  Further expanded:\n    ");
        }
        append_type_expansion_report(
            type_ctx,
            report.actual,
            report.actual_expansion,
            ERROR,
            message,
        );
        message.push_str(" vs ");
        append_type_expansion_report(
            type_ctx,
            report.expected,
            report.expected_expansion,
            INFO,
            message,
        );
    }
}

#[derive(Clone, Copy)]
struct TypeExpansionReport {
    actual: TypeExprRef,
    actual_expansion: TypeExprRef,
    expected: TypeExprRef,
    expected_expansion: TypeExprRef,
}

fn append_type_expansion_report(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
    expansion: TypeExprRef,
    color: &str,
    message: &mut String,
) {
    const DIM: &str = "\x1b[2m";
    const RESET: &str = "\x1b[0m";

    message.push_str(color);
    message.push_str(&format_type_expr(type_ctx, ty));
    message.push_str(RESET);
    if !type_expansion_same(type_ctx, ty, expansion) {
        message.push(' ');
        message.push_str(DIM);
        message.push_str("(defined as");
        message.push_str(RESET);
        message.push(' ');
        message.push_str(color);
        message.push_str(&format_type_expr(type_ctx, expansion));
        message.push_str(RESET);
        message.push_str(DIM);
        message.push(')');
        message.push_str(RESET);
    }
}

fn super_trace_reports(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Vec<TypeExpansionReport> {
    let expanded = expanded_type_clash_trace(type_ctx, trace);
    if expanded.len() < 4 {
        return Vec::new();
    }
    let top_actual_text = format_type_expr(type_ctx, expanded[0].0);
    let top_expected_text = format_type_expr(type_ctx, expanded[1].0);

    let groups = expanded[2..]
        .chunks_exact(2)
        .map(|chunk| TypeExpansionReport {
            actual: chunk[0].0,
            actual_expansion: chunk[0].1,
            expected: chunk[1].0,
            expected_expansion: chunk[1].1,
        })
        .collect::<Vec<_>>();

    let mut reports: Vec<TypeExpansionReport> = Vec::new();
    for (idx, group) in groups.iter().copied().enumerate() {
        let actual_text = format_type_expr(type_ctx, group.actual);
        let expected_text = format_type_expr(type_ctx, group.expected);
        // Semantically equivalent to the original six-term disjunction:
        // (A∧B) ∨ (C∧D) ∨ (A∧¬B) ∨ (B∧¬A) ∨ (C∧¬D) ∨ (D∧¬C) ≡ A ∨ B ∨ C ∨ D
        let is_top_pair_expansion = actual_text == top_actual_text
            || expected_text == top_expected_text
            || actual_text == top_expected_text
            || expected_text == top_actual_text;
        if is_top_pair_expansion {
            continue;
        }

        let is_same_expansion = type_expansion_same(type_ctx, group.actual, group.actual_expansion)
            && type_expansion_same(type_ctx, group.expected, group.expected_expansion);
        let duplicates_previous_expansion = reports.iter().any(|previous| {
            let previous_actual_expansion = format_type_expr(type_ctx, previous.actual_expansion);
            let previous_expected = format_type_expr(type_ctx, previous.expected);
            let previous_actual = format_type_expr(type_ctx, previous.actual);
            let previous_expected_expansion =
                format_type_expr(type_ctx, previous.expected_expansion);
            (actual_text == previous_actual_expansion && expected_text == previous_expected)
                || (actual_text == previous_expected && expected_text == previous_actual_expansion)
                || (actual_text == previous_actual && expected_text == previous_expected_expansion)
                || (actual_text == previous_expected_expansion && expected_text == previous_actual)
        });
        if is_same_expansion && duplicates_previous_expansion {
            continue;
        }
        if is_same_expansion && idx + 1 != groups.len() {
            continue;
        }
        reports.push(group);
    }
    reports
}

fn expanded_type_clash_trace(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Vec<(TypeExprRef, TypeExprRef)> {
    let mut expanded = Vec::with_capacity(trace.len() * 2);
    for (actual, expected) in trace {
        expanded.push(expanded_type_clash_entry(type_ctx, *actual));
        expanded.push(expanded_type_clash_entry(type_ctx, *expected));
    }
    expanded
}

fn expanded_type_clash_entry(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
) -> (TypeExprRef, TypeExprRef) {
    let repr = type_ctx.repr(ty);
    let expansion = type_ctx
        .trace_expansion(repr)
        .or_else(|| type_alias_expansion(type_ctx, repr))
        .unwrap_or(repr);
    (repr, expansion)
}

fn type_alias_expansion(type_ctx: &TypeContext, ty: TypeExprRef) -> Option<TypeExprRef> {
    let repr = type_ctx.repr(ty);
    let desc = type_ctx.get_desc(repr);
    let TypeDesc::Tconstr { path, args, .. } = &*desc else {
        return None;
    };
    let path = path.clone();
    let args = args.clone();
    drop(desc);

    let manifest = type_decl_manifest_for_path(type_ctx, &path)?;
    let (params, manifest) = manifest;
    let expansion = if params.len() == args.len() {
        crate::types::ctype::subst_type_params(type_ctx, &params, &args, manifest)
    } else {
        manifest
    };
    Some(type_ctx.repr(expansion))
}

fn type_alias_full_expansion(type_ctx: &TypeContext, ty: TypeExprRef) -> Option<TypeExprRef> {
    let original = type_ctx.repr(ty);
    let mut current = original;
    let mut seen = AHashSet::new();
    let mut changed = false;

    while seen.insert(current) {
        let Some(next) = type_alias_expansion(type_ctx, current) else {
            break;
        };
        let next = type_ctx.repr(next);
        if next == current {
            break;
        }
        current = next;
        changed = true;
    }

    changed.then_some(current)
}

fn type_decl_manifest_for_path(
    type_ctx: &TypeContext,
    path: &crate::types::Path,
) -> Option<(Vec<TypeExprRef>, TypeExprRef)> {
    let from_decl = |decl: std::cell::Ref<'_, crate::types::TypeDeclaration>| {
        decl.type_manifest
            .map(|manifest| (decl.type_params.clone(), manifest))
    };

    // A predefined type (e.g. `promise`) has no manifest; resolving it by name
    // could pick a user declaration that shadows it.
    if let crate::types::Path::Pident(id) = path
        && crate::types::predef::find_predef_ident(id.name())
            .is_some_and(|predef| predef.stamp() == id.stamp())
    {
        return None;
    }

    // Once the declaration for `path` is found, its manifest (or lack of one)
    // is the answer; falling back to another declaration with the same name
    // would expand an unrelated type.
    if let crate::types::Path::Pident(id) = path
        && id.stamp() != 0
        && let Some(decl) = type_ctx.find_type_decl_by_stamp(id.stamp())
    {
        return from_decl(decl);
    }

    if let Some(decl) = type_ctx.find_type_decl_by_path(&path.name()) {
        return from_decl(decl);
    }

    if let Some(decl) = type_ctx.find_type_decl(path.head_name())
        && let Some(result) = from_decl(decl)
    {
        return Some(result);
    }

    None
}

fn type_expansion_same(type_ctx: &TypeContext, ty: TypeExprRef, expansion: TypeExprRef) -> bool {
    type_ctx.repr(ty) == type_ctx.repr(expansion)
        || format_type_expr(type_ctx, ty) == format_type_expr(type_ctx, expansion)
}

fn append_polyvariant_type_clash_help(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";
    const RESET: &str = "\x1b[0m";

    let Some((actual_ty, expected_ty)) = polyvariant_diagnostic_type_pair(type_ctx, trace) else {
        return false;
    };
    let Some((actual_row, expected_row)) = polyvariant_row_pair(type_ctx, actual_ty, expected_ty)
    else {
        return false;
    };

    let actual_fields = visible_polyvariant_fields(type_ctx, &actual_row);
    let expected_fields = visible_polyvariant_fields(type_ctx, &expected_row);
    let common_labels = actual_fields
        .iter()
        .filter(|(actual_label, _)| {
            expected_fields
                .iter()
                .any(|(expected_label, _)| expected_label == actual_label)
        })
        .count();

    if actual_row.row_closed
        && expected_row.row_closed
        && common_labels == 0
        && !actual_fields.is_empty()
        && !expected_fields.is_empty()
    {
        message.push_str(
            "\n\nThese polymorphic variants are incompatible - they share no common constructors.",
        );
        return true;
    }

    let missing_from_actual = expected_fields
        .iter()
        .filter(|(expected_label, _)| {
            !actual_fields
                .iter()
                .any(|(actual_label, _)| actual_label == expected_label)
        })
        .map(|(label, _)| label.as_str())
        .collect::<Vec<_>>();
    if actual_row.row_closed && !missing_from_actual.is_empty() {
        let constructors_txt = if missing_from_actual.len() == 1 {
            "constructor"
        } else {
            "constructors"
        };
        message.push_str("\n\nThe first polymorphic variant is ");
        message.push_str(INFO);
        message.push_str("closed");
        message.push_str(RESET);
        message.push_str(" and doesn't include the ");
        message.push_str(constructors_txt);
        message.push_str(": ");
        message.push_str(ERROR);
        message.push_str(&format_polyvariant_tags(&missing_from_actual));
        message.push_str(RESET);
        message.push_str(".\n\nPossible solutions:\n- Either make the first variant ");
        message.push_str(INFO);
        message.push_str("open");
        message.push_str(RESET);
        message.push_str(" so it can accept additional constructors. To do this, make sure the type starts with ");
        message.push_str(INFO);
        message.push_str("[>");
        message.push_str(RESET);
        message.push_str(" instead of ");
        message.push_str(INFO);
        message.push('[');
        message.push_str(RESET);
        message.push_str("\n- Or add the missing ");
        message.push_str(constructors_txt);
        message.push_str(" to it.");
        return true;
    }

    let missing_from_expected = actual_fields
        .iter()
        .filter(|(actual_label, _)| {
            !expected_fields
                .iter()
                .any(|(expected_label, _)| expected_label == actual_label)
        })
        .map(|(label, _)| label.as_str())
        .collect::<Vec<_>>();
    if expected_row.row_closed && !missing_from_expected.is_empty() {
        let constructors_txt = if missing_from_expected.len() == 1 {
            "constructor"
        } else {
            "constructors"
        };
        message.push_str("\n\nThe second polymorphic variant is ");
        message.push_str(INFO);
        message.push_str("closed");
        message.push_str(RESET);
        message.push_str(" and doesn't include the ");
        message.push_str(constructors_txt);
        message.push_str(": ");
        message.push_str(ERROR);
        message.push_str(&format_polyvariant_tags(&missing_from_expected));
        message.push_str(RESET);
        message.push_str(".\n\nPossible solutions:\n- Either make the second variant ");
        message.push_str(INFO);
        message.push_str("open");
        message.push_str(RESET);
        message.push_str(" so it can accept additional constructors. To do this, make sure the type starts with ");
        message.push_str(INFO);
        message.push_str("[>");
        message.push_str(RESET);
        message.push_str(" instead of ");
        message.push_str(INFO);
        message.push('[');
        message.push_str(RESET);
        message.push_str("\n- Or add the missing ");
        message.push_str(constructors_txt);
        message.push_str(" to it.");
        return true;
    }

    if actual_row.row_closed
        && expected_row.row_closed
        && actual_fields.len() == 1
        && expected_fields.len() == 1
        && actual_fields[0].0 == expected_fields[0].0
    {
        let constructor = format_polyvariant_tag(actual_fields[0].0.as_str());
        message.push_str("\n\nBoth polymorphic variants have the constructor ");
        message.push_str(INFO);
        message.push_str(&constructor);
        message.push_str(RESET);
        message.push_str(
            ", but their payload types are incompatible.\nMake sure the payload types for ",
        );
        message.push_str(INFO);
        message.push_str(&constructor);
        message.push_str(RESET);
        message.push_str(" match exactly in both polymorphic variants.");
        return true;
    }

    false
}

fn polyvariant_row_pair(
    type_ctx: &TypeContext,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> Option<(
    crate::types::type_expr::RowDesc,
    crate::types::type_expr::RowDesc,
)> {
    Some((
        polyvariant_row(type_ctx, actual)?,
        polyvariant_row(type_ctx, expected)?,
    ))
}

fn polyvariant_diagnostic_type_pair(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<(TypeExprRef, TypeExprRef)> {
    let mut fallback = None;
    // OCaml `Printtyp.mismatch` reads the expanded trace (`expand_trace`), so a
    // pair of variant abbreviations is explained through their expansions.
    let expanded = |ty: TypeExprRef| type_ctx.trace_expansion(type_ctx.repr(ty)).unwrap_or(ty);
    for (actual, expected) in trace.iter().copied() {
        let (actual, expected) = (expanded(actual), expanded(expected));
        if polyvariant_row_pair(type_ctx, actual, expected).is_none() {
            continue;
        }
        if fallback.is_none() {
            fallback = Some((actual, expected));
        }
        if format_type_expr(type_ctx, actual) != format_type_expr(type_ctx, expected) {
            return Some((actual, expected));
        }
    }
    fallback
}

fn polyvariant_row(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
) -> Option<crate::types::type_expr::RowDesc> {
    let repr = type_ctx.repr(ty);
    let desc = type_ctx.get_desc(repr);
    let row = match &*desc {
        TypeDesc::Tvariant(row) => crate::types::btype::row_repr(type_ctx, row),
        _ => return None,
    };
    Some(row)
}

fn type_is_polyvariant(type_ctx: &TypeContext, ty: TypeExprRef) -> bool {
    matches!(
        &*type_ctx.borrow_desc(type_ctx.repr(ty)),
        TypeDesc::Tvariant(_)
    )
}

fn visible_polyvariant_fields(
    type_ctx: &TypeContext,
    row: &crate::types::type_expr::RowDesc,
) -> Vec<(
    crate::types::asttypes::Label,
    crate::types::type_expr::RowField,
)> {
    let mut fields = row
        .row_fields
        .iter()
        .filter_map(|(label, field)| {
            let field = crate::types::btype::row_field_repr(type_ctx, field);
            (!matches!(field, crate::types::type_expr::RowField::Rabsent))
                .then(|| (label.clone(), field))
        })
        .collect::<Vec<_>>();
    fields.sort_by(|(left, _), (right, _)| left.as_str().cmp(right.as_str()));
    fields
}

fn format_polyvariant_tags(labels: &[&str]) -> String {
    labels
        .iter()
        .map(|label| format_polyvariant_tag(label))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_polyvariant_tag(label: &str) -> String {
    format!("#{label}")
}

fn append_object_field_mismatch_help(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";
    const RESET: &str = "\x1b[0m";

    let Some((field_name, actual_ty, expected_ty)) = trace
        .iter()
        .find_map(|(actual, expected)| object_field_mismatch_pair(type_ctx, *actual, *expected))
    else {
        return false;
    };

    message.push_str("\n\nTypes for field ");
    message.push_str(INFO);
    message.push('"');
    message.push_str(&field_name);
    message.push('"');
    message.push_str(RESET);
    message.push_str(" are incompatible:\n");
    message.push_str("Field ");
    message.push_str(INFO);
    message.push('"');
    message.push_str(&field_name);
    message.push('"');
    message.push_str(RESET);
    message.push_str(" in the passed object has type ");
    message.push_str(ERROR);
    message.push_str(&format_type_expr(type_ctx, actual_ty));
    message.push_str(RESET);
    message.push_str(", but is expected to have type ");
    message.push_str(INFO);
    message.push_str(&format_type_expr(type_ctx, expected_ty));
    message.push_str(RESET);
    message.push('.');

    true
}

fn append_object_field_missing_help(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) -> bool {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let Some((first_object, field_name, field_ty)) = trace
        .iter()
        .find_map(|(actual, expected)| object_field_missing_pair(type_ctx, *actual, *expected))
    else {
        return false;
    };

    message.push_str("\n\nThe ");
    message.push_str(if first_object { "first" } else { "second" });
    message.push_str(" object is expected to have a field ");
    message.push_str(INFO);
    message.push('"');
    message.push_str(&field_name);
    message.push('"');
    message.push_str(RESET);
    message.push_str(" of type ");
    message.push_str(INFO);
    message.push_str(&format_type_expr(type_ctx, field_ty));
    message.push_str(RESET);
    message.push_str(", but it does not.");

    true
}

fn object_field_expected_line(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<(String, TypeExprRef)> {
    trace
        .iter()
        .find_map(|(actual, expected)| object_field_mismatch_pair(type_ctx, *actual, *expected))
        .map(|(field_name, _, expected_field_ty)| (field_name, expected_field_ty))
        .or_else(|| {
            trace
                .iter()
                .find_map(|(actual, expected)| {
                    object_field_missing_pair(type_ctx, *actual, *expected)
                })
                .map(|(_, field_name, field_ty)| (field_name, field_ty))
        })
}

fn object_field_mismatch_pair(
    type_ctx: &TypeContext,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> Option<(String, TypeExprRef, TypeExprRef)> {
    let actual_repr = type_ctx.repr(actual);
    let expected_repr = type_ctx.repr(expected);
    let actual_desc = type_ctx.get_desc(actual_repr);
    let expected_desc = type_ctx.get_desc(expected_repr);
    let result = match (&*actual_desc, &*expected_desc) {
        (
            TypeDesc::Tfield {
                name: actual_name,
                typ: actual_ty,
                rest: actual_rest,
                ..
            },
            TypeDesc::Tfield {
                name: expected_name,
                typ: expected_ty,
                rest: expected_rest,
                ..
            },
        ) if actual_name == expected_name
            && type_is_nil(type_ctx, *actual_rest)
            && type_is_nil(type_ctx, *expected_rest) =>
        {
            Some((actual_name.clone(), *actual_ty, *expected_ty))
        }
        _ => None,
    };
    drop(actual_desc);
    drop(expected_desc);
    result
}

fn object_field_missing_pair(
    type_ctx: &TypeContext,
    actual: TypeExprRef,
    expected: TypeExprRef,
) -> Option<(bool, String, TypeExprRef)> {
    let actual_repr = type_ctx.repr(actual);
    let expected_repr = type_ctx.repr(expected);
    let actual_desc = type_ctx.get_desc(actual_repr);
    let expected_desc = type_ctx.get_desc(expected_repr);
    let result = match (&*actual_desc, &*expected_desc) {
        (TypeDesc::Tnil | TypeDesc::Tconstr { .. }, TypeDesc::Tfield { name, typ, .. }) => {
            Some((true, name.clone(), *typ))
        }
        (TypeDesc::Tfield { name, typ, .. }, TypeDesc::Tnil | TypeDesc::Tconstr { .. }) => {
            Some((false, name.clone(), *typ))
        }
        _ => None,
    };
    drop(actual_desc);
    drop(expected_desc);
    result
}

fn type_is_nil(type_ctx: &TypeContext, ty: TypeExprRef) -> bool {
    matches!(&*type_ctx.borrow_desc(type_ctx.repr(ty)), TypeDesc::Tnil)
}

fn append_dict_literal_help(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let has_dict_literal_mismatch = [
        bottom_type_clash_aliases(trace),
        nested_type_clash_pair(type_ctx, trace),
        trace.first().copied(),
    ]
    .into_iter()
    .flatten()
    .any(|(actual, expected)| type_is_object(type_ctx, actual) && type_is_dict(type_ctx, expected));
    if !has_dict_literal_mismatch {
        return;
    }

    message.push_str("\n\nDicts are written like: ");
    message.push_str(INFO);
    message.push_str("dict{\"a\": 1, \"b\": 2}");
    message.push_str(RESET);
    message.push_str("\n\n");
}

fn type_is_object(type_ctx: &TypeContext, ty: TypeExprRef) -> bool {
    let repr = type_ctx.repr(ty);
    matches!(
        &*type_ctx.borrow_desc(repr),
        TypeDesc::Tobject { .. } | TypeDesc::Tfield { .. }
    )
}

fn type_is_record(type_ctx: &TypeContext, ty: TypeExprRef) -> bool {
    let repr = type_ctx.repr(ty);
    match &*type_ctx.get_desc(repr) {
        TypeDesc::Tconstr { path, .. } => type_path_is_record(type_ctx, path),
        TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => type_is_record(type_ctx, *next),
        _ => false,
    }
}

fn type_path_is_record(type_ctx: &TypeContext, path: &crate::types::Path) -> bool {
    if let crate::types::Path::Pident(id) = path
        && id.stamp() != 0
        && let Some(decl) = type_ctx.find_type_decl_by_stamp(id.stamp())
    {
        return matches!(
            &decl.type_kind,
            crate::types::decl::TypeKind::TypeRecord(_, _)
        );
    }

    if let Some(decl) = type_ctx.find_type_decl_by_path(&path.name()) {
        return matches!(
            &decl.type_kind,
            crate::types::decl::TypeKind::TypeRecord(_, _)
        );
    }

    type_ctx
        .find_type_decl(path.head_name())
        .is_some_and(|decl| {
            matches!(
                &decl.type_kind,
                crate::types::decl::TypeKind::TypeRecord(_, _)
            )
        })
}

fn type_is_dict(type_ctx: &TypeContext, ty: TypeExprRef) -> bool {
    let repr = type_ctx.repr(ty);
    match &*type_ctx.get_desc(repr) {
        TypeDesc::Tconstr { path, .. } => {
            path.same(&crate::types::predef::path_dict()) || path.last() == "dict"
        }
        TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => type_is_dict(type_ctx, *next),
        _ => false,
    }
}

fn type_clash_array_to_tuple(type_ctx: &TypeContext, trace: &[(TypeExprRef, TypeExprRef)]) -> bool {
    [
        bottom_type_clash_aliases(trace),
        nested_type_clash_pair(type_ctx, trace),
        trace.first().copied(),
    ]
    .into_iter()
    .flatten()
    .any(|(actual, expected)| {
        let actual_is_array = match &*type_ctx.get_desc(type_ctx.repr(actual)) {
            TypeDesc::Tconstr { path, .. } => path.head_name() == "array",
            _ => false,
        };
        let expected_is_tuple = matches!(
            &*type_ctx.borrow_desc(type_ctx.repr(expected)),
            TypeDesc::Ttuple(_)
        );

        actual_is_array && expected_is_tuple
    })
}

fn suggested_array_to_tuple_rewrite(
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
) -> Option<String> {
    let start = arena.loc_start(loc).cnum as usize;
    let end = arena.loc_end(loc).cnum as usize;
    let text = crate::source_text::latin1_slice(source, start, end)?.trim();
    let inner = text.strip_prefix('[')?.strip_suffix(']')?;
    Some(format!("({inner})"))
}

fn append_simple_conversion_help(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let Some((actual_name, expected_name, converter)) =
        simple_conversion_candidate(type_ctx, trace)
    else {
        return;
    };

    message.push_str("\n\nYou can convert ");
    message.push_str(INFO);
    message.push_str(&actual_name);
    message.push_str(RESET);
    message.push_str(" to ");
    message.push_str(INFO);
    message.push_str(&expected_name);
    message.push_str(RESET);
    message.push_str(" with ");
    message.push_str(INFO);
    message.push_str(converter);
    message.push_str(RESET);
    message.push('.');
    if actual_name == "float"
        && expected_name == "int"
        && source_loc_is_float_literal_with_trailing_dot(arena, source, loc)
    {
        message.push('\n');
        message.push_str("If this is a literal, try a number without a trailing dot (e.g. ");
        message.push_str(INFO);
        message.push_str("20");
        message.push_str(RESET);
        message.push_str(").");
    }
    if actual_name == "int" && expected_name == "float" {
        message.push('\n');
        message.push_str("If this is a literal, try a number with a trailing dot (e.g. ");
        message.push_str(INFO);
        message.push_str("20.");
        message.push_str(RESET);
        message.push_str(").");
    }
}

fn source_loc_is_float_literal_with_trailing_dot(
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
) -> bool {
    let start = arena.loc_start(loc).cnum as usize;
    let end = arena.loc_end(loc).cnum as usize;
    let Some(text) = crate::source_text::latin1_slice(source, start, end).map(str::trim) else {
        return false;
    };
    let (text, loc_has_dot) = if let Some(text) = text.strip_suffix('.') {
        (text, true)
    } else {
        (text, false)
    };
    !text.is_empty()
        && text.chars().all(|ch| ch.is_ascii_digit() || ch == '_')
        && (loc_has_dot || source.as_bytes().get(end).is_some_and(|byte| *byte == b'.'))
}

fn simple_conversion_candidate(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<(String, String, &'static str)> {
    let candidates = [
        trace.last().copied(),
        bottom_type_clash_aliases(trace),
        nested_type_clash_pair(type_ctx, trace),
        trace.first().copied(),
    ];

    for candidate in candidates.into_iter().flatten() {
        let Some(actual_name) = simple_type_constr_name(type_ctx, candidate.0) else {
            continue;
        };
        let Some(expected_name) = simple_type_constr_name(type_ctx, candidate.1) else {
            continue;
        };
        if let Some(converter) = simple_conversion(&actual_name, &expected_name) {
            return Some((actual_name, expected_name, converter));
        }
    }
    None
}

fn nested_type_clash_pair(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<(TypeExprRef, TypeExprRef)> {
    let (top_actual, top_expected) = trace.first().copied()?;
    let top_actual_text = format_type_expr(type_ctx, top_actual);
    let top_expected_text = format_type_expr(type_ctx, top_expected);
    trace
        .iter()
        .skip(1)
        .rev()
        .copied()
        .find(|(actual, expected)| {
            let actual_text = format_type_expr(type_ctx, *actual);
            let expected_text = format_type_expr(type_ctx, *expected);
            let is_top_alias_expansion = (actual_text == top_actual_text
                && expected_text != top_expected_text)
                || (expected_text == top_expected_text && actual_text != top_actual_text)
                || (actual_text == top_expected_text && expected_text != top_actual_text)
                || (expected_text == top_actual_text && actual_text != top_expected_text);
            !is_top_alias_expansion
                && (actual_text != top_actual_text || expected_text != top_expected_text)
        })
}

fn bottom_type_clash_aliases(
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<(TypeExprRef, TypeExprRef)> {
    let mut result = None;
    for window in trace.windows(2) {
        result = Some((window[0].1, window[1].1));
    }
    result
}

fn simple_type_constr_name(type_ctx: &TypeContext, ty: TypeExprRef) -> Option<String> {
    match &*type_ctx.get_desc(type_ctx.repr(ty)) {
        TypeDesc::Tconstr { path, args, .. } if args.is_empty() => {
            Some(path.head_name().to_string())
        }
        _ => None,
    }
}

fn simple_conversion(actual: &str, expected: &str) -> Option<&'static str> {
    match (actual, expected) {
        ("float", "int") => Some("Float.toInt"),
        ("float", "string") => Some("Float.toString"),
        ("int", "float") => Some("Int.toFloat"),
        ("int", "string") => Some("Int.toString"),
        ("string", "float") => Some("Float.fromString"),
        ("string", "int") => Some("Int.fromString"),
        _ => None,
    }
}

fn expr_type_clash_uncurried_arity_mismatch(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<(i32, i32)> {
    let (actual, expected) = trace.first().copied()?;
    let actual_arity = uncurried_arrow_arity(type_ctx, actual)?;
    let expected_arity = uncurried_arrow_arity(type_ctx, expected)?;
    (actual_arity != expected_arity).then_some((actual_arity, expected_arity))
}

fn uncurried_arrow_arity(type_ctx: &TypeContext, ty: TypeExprRef) -> Option<i32> {
    match &*type_ctx.get_desc(type_ctx.repr(ty)) {
        TypeDesc::Tarrow { args, .. } => Some(args.len() as i32),
        _ => None,
    }
}

fn format_function_arity_mismatch_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    actual_arity: i32,
    expected_arity: i32,
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";
    const RESET: &str = "\x1b[0m";

    let mut message = String::new();
    message.push_str("This function is expected to have ");
    message.push_str(INFO);
    message.push_str(&expected_arity.to_string());
    message.push_str(RESET);
    message.push(' ');
    message.push_str(if expected_arity == 1 {
        "argument"
    } else {
        "arguments"
    });
    message.push_str(", but");
    if actual_arity < expected_arity {
        message.push_str(" only");
    }
    message.push_str(" has ");
    message.push_str(ERROR);
    message.push_str(&actual_arity.to_string());
    message.push_str(RESET);

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn count_arrow_args(type_ctx: &TypeContext, ty: TypeExprRef, mut count: usize) -> usize {
    let mut current = ty;
    let mut seen = AHashSet::new();

    loop {
        let repr = type_ctx.repr(current);
        if !seen.insert(repr) {
            return count;
        }

        match &*type_ctx.get_desc(repr) {
            TypeDesc::Tarrow { args, ret } => {
                count += args.len();
                current = *ret;
            }
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => {
                current = *next;
            }
            _ => return count,
        }
    }
}

fn format_apply_non_function_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    typ: TypeExprRef,
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_apply_non_function(ppf, type_ctx, typ)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_tagged_template_non_tag_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    typ: TypeExprRef,
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_tagged_template_non_tag(ppf, type_ctx, typ)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_too_many_arguments_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    in_function: bool,
    ty: TypeExprRef,
) -> String {
    let message = if in_function {
        format!(
            "This function expects too many arguments,\nit should have type {}",
            format_type_expr(type_ctx, ty)
        )
    } else {
        format!(
            "This expression should not be a function,\nthe expected type is {}",
            format_type_expr(type_ctx, ty)
        )
    };
    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_abstract_wrong_label_report(
    type_ctx: &TypeContext,
    source: &str,
    filename: &str,
    loc: &Location,
    label: &TypeArgLabel,
    ty: TypeExprRef,
) -> String {
    let label_mark = match label {
        TypeArgLabel::Nolabel => "but its first argument is not labelled".to_string(),
        TypeArgLabel::Labelled(label) => {
            format!("but its first argument is labelled ~{}", label.txt)
        }
        TypeArgLabel::Optional(label) => {
            format!("but its first argument is labelled ?{}", label.txt)
        }
    };
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_abstract_wrong_label(ppf, type_ctx, &label_mark, ty)
    });
    let mut output = String::new();
    push_compiler_error_report_header_from_location(&mut output, source, filename, loc);
    output.push_str(&code_frame::apply_message_styles(&message));
    output.push_str("\n\n");
    output
}

fn format_apply_wrong_label_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    label: &ParserArgLabel,
    ty: TypeExprRef,
    suppress_info_style: bool,
) -> String {
    let label = match label {
        ParserArgLabel::Nolabel => None,
        ParserArgLabel::Labelled(loc) => Some(format!("~{}", arena.get_string(loc.txt))),
        ParserArgLabel::Optional(loc) => Some(format!("?{}", arena.get_string(loc.txt))),
    };
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_apply_wrong_label(ppf, type_ctx, label.as_deref(), ty)
    });
    let report = format_compiler_error_report_formatted(arena, source, filename, loc, &message);
    if suppress_info_style {
        report.replace("\x1b[1;33m", "").replace("\x1b[0m", "")
    } else {
        report
    }
}

fn format_field_not_optional_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &str,
    typ: TypeExprRef,
) -> String {
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_field_not_optional(ppf, type_ctx, name, typ)
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_unbound_record_field_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    field_name: &str,
    from_type: Option<TypeExprRef>,
    alternatives: &[String],
) -> String {
    let hint = spellcheck_hint(
        field_name.rsplit('.').next().unwrap_or(field_name),
        alternatives,
    );
    let message = type_clash::render_error_message(|ppf| {
        type_clash::print_unbound_label(ppf, type_ctx, field_name, from_type, hint.as_deref())
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn collect_expected_function_arguments(
    type_ctx: &TypeContext,
    expected: TypeExprRef,
) -> Vec<(TypeArgLabel, TypeExprRef)> {
    let mut args = Vec::new();
    let mut current = expected;
    let mut seen = AHashSet::new();

    loop {
        let repr = type_ctx.repr(current);
        if !seen.insert(repr) {
            break;
        }

        match &*type_ctx.get_desc(repr) {
            TypeDesc::Tarrow { args: params, ret } => {
                args.extend(params.iter().map(|arg| (arg.label().clone(), arg.typ)));
                current = *ret;
            }
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => current = *next,
            _ => break,
        }
    }

    args
}

fn format_type_clash_arguments(
    type_ctx: &TypeContext,
    args: &[(TypeArgLabel, TypeExprRef)],
) -> String {
    args.iter()
        .map(|(label, ty)| {
            let ty = format_type_expr(type_ctx, *ty);
            match label {
                TypeArgLabel::Nolabel => ty,
                TypeArgLabel::Labelled(label) => format!("(~{}: {ty})", label.txt),
                TypeArgLabel::Optional(label) => format!("(?{}: {ty})", label.txt),
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_uncurried_arity_mismatch_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    function_type: TypeExprRef,
    expected_arity: usize,
    provided_arity: usize,
    provided_args: &[crate::parser::ast::ArgLabel],
    arity_suggestion: Option<&str>,
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const ERROR: &str = "\x1b[1;31m";
    const RESET: &str = "\x1b[0m";

    let args_from_type = collect_function_arg_labels(type_ctx, function_type);
    let args_from_type_unlabelled = args_from_type
        .iter()
        .filter(|arg| matches!(arg, TypeArgLabel::Nolabel))
        .count();
    let provided_unlabelled = provided_args
        .iter()
        .filter(|arg| matches!(arg, crate::parser::ast::ArgLabel::Nolabel))
        .count();
    let mismatch_in_unlabelled_args = args_from_type_unlabelled != provided_unlabelled;

    let required_args = args_from_type
        .iter()
        .filter_map(|arg| match arg {
            TypeArgLabel::Labelled(label) => Some(label.txt.clone()),
            TypeArgLabel::Nolabel | TypeArgLabel::Optional(_) => None,
        })
        .collect::<Vec<_>>();
    let passed_named_args = provided_args
        .iter()
        .filter_map(|arg| parser_arg_label_name(arg, arena).map(str::to_string))
        .collect::<Vec<_>>();
    let missing_required_args = required_args
        .iter()
        .filter(|arg| !passed_named_args.contains(arg))
        .cloned()
        .collect::<Vec<_>>();

    let named_args_of_fn_type = args_from_type
        .iter()
        .filter_map(|arg| match arg {
            TypeArgLabel::Labelled(label) | TypeArgLabel::Optional(label) => {
                Some(label.txt.clone())
            }
            TypeArgLabel::Nolabel => None,
        })
        .collect::<Vec<_>>();
    let superfluous_args = passed_named_args
        .iter()
        .filter(|arg| !named_args_of_fn_type.contains(arg))
        .cloned()
        .collect::<Vec<_>>();

    let is_fallback = missing_required_args.is_empty()
        && superfluous_args.is_empty()
        && !mismatch_in_unlabelled_args;

    // typecore.ml:5150-5220 lays the message out in one `@[<v>...@]` box.
    use crate::types::printtyp::{TAG_ERROR, TAG_INFO, TAG_RESET};
    let type_text = format_type_expr(type_ctx, function_type);
    let plural = |n: usize| if n == 1 { "" } else { "s" };
    let message = type_clash::render_error_message(|ppf| {
        let tagged =
            |ppf: &mut crate::parser::formatter::Formatter<&mut Vec<u8>>, tag: &str, text: &str| {
                ppf.string_as(0, tag);
                ppf.str(text);
                ppf.string_as(0, TAG_RESET);
            };
        ppf.open_vbox(0);
        ppf.open_box(crate::parser::formatter::BoxKind::Box, 2);
        ppf.str("This function call is incorrect.");
        ppf.close_box();
        ppf.cut();
        ppf.str("The function has type:");
        ppf.space();
        ppf.str(&type_text);
        if !is_fallback {
            ppf.cut();
        }
        if !missing_required_args.is_empty() {
            ppf.cut();
            ppf.str(&format!(
                "- Missing arguments that must be provided: {}",
                missing_required_args
                    .iter()
                    .map(|arg| format!("~{arg}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
            ppf.cut();
            ppf.str("- Hint: Did you want to partially apply the function? You can do that by putting `...` just before the closing parens of the function call. Example: ");
            tagged(ppf, TAG_INFO, "yourFn(~arg1=someVar, ...)");
        }
        if !superfluous_args.is_empty() {
            ppf.cut();
            ppf.str(&format!(
                "- Called with arguments it does not take: {}",
                superfluous_args.join(", ")
            ));
        }
        if mismatch_in_unlabelled_args {
            ppf.cut();
            ppf.str("- The function takes ");
            tagged(
                ppf,
                TAG_INFO,
                &unlabelled_arg_count_message(
                    args_from_type_unlabelled,
                    provided_unlabelled,
                    CountPosition::Left,
                ),
            );
            ppf.str(&format!(
                " unlabelled argument{}, but is called with ",
                plural(args_from_type_unlabelled)
            ));
            tagged(
                ppf,
                TAG_ERROR,
                &unlabelled_arg_count_message(
                    provided_unlabelled,
                    args_from_type_unlabelled,
                    CountPosition::Right,
                ),
            );
        }
        if is_fallback {
            ppf.cut();
            ppf.cut();
            ppf.str("It is called with ");
            tagged(ppf, TAG_ERROR, &provided_arity.to_string());
            ppf.str(&format!(
                " argument{} but{} requires ",
                plural(provided_arity),
                if provided_arity > expected_arity {
                    " just"
                } else {
                    ""
                }
            ));
            tagged(ppf, TAG_INFO, &expected_arity.to_string());
            ppf.str(".");
        }
        if let Some(suggestion) = arity_suggestion {
            ppf.cut();
            ppf.cut();
            ppf.str("Hint: Try ");
            tagged(ppf, TAG_INFO, suggestion);
            ppf.str(" instead (takes ");
            tagged(ppf, TAG_INFO, &provided_arity.to_string());
            ppf.str(&format!(" argument{}).", plural(provided_arity)));
        }
        ppf.close_box();
    });
    format_compiler_error_report_formatted(arena, source, filename, loc, &message)
}

fn format_constructor_arity_mismatch_report(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    name: &Longident,
    is_inline_record: bool,
    expected: usize,
    provided: usize,
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let name = format_longident_for_report(arena, name);
    let message = if is_inline_record && expected == 1 {
        let suffix = if provided == 0 {
            ", but it's not being passed any arguments"
        } else {
            ""
        };
        format!(
            "This variant constructor {INFO}{name}{RESET} expects an inline record as payload{suffix}."
        )
    } else {
        let argument = if expected == 1 {
            "argument"
        } else {
            "arguments"
        };
        let only = if provided < expected { " only" } else { "" };
        format!(
            "This variant constructor {INFO}{name}{RESET} expects {expected} {argument}, but it's{only} being passed {provided}."
        )
    };

    format_compiler_error_report(arena, source, filename, loc, &message)
}

fn format_longident_for_report(arena: &ParseArena, lid: &Longident) -> String {
    match lid {
        Longident::Lident(name) => arena.get_string(*name).to_string(),
        Longident::Ldot(prefix, name) => {
            format!(
                "{}.{}",
                format_longident_for_report(arena, prefix),
                arena.get_string(*name)
            )
        }
        Longident::Lapply(func, arg) => {
            format!(
                "{}({})",
                format_longident_for_report(arena, func),
                format_longident_for_report(arena, arg)
            )
        }
    }
}

#[derive(Clone, Copy)]
enum CountPosition {
    Left,
    Right,
}

fn unlabelled_arg_count_message(
    count: usize,
    other_count: usize,
    position: CountPosition,
) -> String {
    match (count, position) {
        (0, CountPosition::Left) => "no".to_string(),
        (0, CountPosition::Right) => "none".to_string(),
        _ if count > other_count => count.to_string(),
        _ => format!("just {count}"),
    }
}

fn parser_arg_label_name<'a>(
    label: &crate::parser::ast::ArgLabel,
    arena: &'a ParseArena,
) -> Option<&'a str> {
    match label {
        crate::parser::ast::ArgLabel::Nolabel => None,
        crate::parser::ast::ArgLabel::Labelled(loc)
        | crate::parser::ast::ArgLabel::Optional(loc) => Some(arena.get_string(loc.txt)),
    }
}

fn collect_function_arg_labels(
    type_ctx: &TypeContext,
    function_type: TypeExprRef,
) -> Vec<TypeArgLabel> {
    let mut labels = Vec::new();
    let mut current = function_type;
    let mut seen = AHashSet::new();

    loop {
        if !seen.insert(current) {
            break;
        }

        match &*type_ctx.get_desc(current) {
            TypeDesc::Tarrow { args, ret } => {
                labels.extend(args.iter().map(|arg| arg.label().clone()));
                current = *ret;
            }
            _ => break,
        }
    }

    labels
}

fn format_type_expr(type_ctx: &TypeContext, ty: TypeExprRef) -> String {
    TypeExprPrinter::new(type_ctx).format(ty)
}

fn format_package_type_expr_for_error(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    ty: TypeExprRef,
) -> String {
    let repr = type_ctx.repr(ty);
    let desc = (*type_ctx.get_desc(repr)).clone();
    let TypeDesc::Tpackage { path, lids, args } = desc else {
        return format_type_expr(type_ctx, ty);
    };
    if lids.is_empty() {
        return format_type_expr(type_ctx, ty);
    }

    let constraints = lids
        .iter()
        .zip(args.iter())
        .map(|(lid, arg)| {
            format!(
                "type {} = {}",
                format_longident_for_report(arena, lid),
                format_type_expr(type_ctx, *arg)
            )
        })
        .collect::<Vec<_>>();
    format!("module({} with {})", path.name(), constraints.join(" and "))
}

fn format_non_generalizable_type_expr(type_ctx: &TypeContext, ty: TypeExprRef) -> String {
    TypeExprPrinter::new_with_weak_names(type_ctx).format(ty)
}

/// A `Printtyp` naming session (compiler/ml/printtyp.ml): type variables
/// keep their names across every type printed with the same printer.
struct TypeExprPrinter<'a> {
    type_ctx: &'a TypeContext,
    printtyp: crate::types::printtyp::Printtyp<'a>,
    weak_names: bool,
    /// Types whose loops were marked since the last `reset`. OCaml's callers
    /// mark each printed type once (`reset_and_mark_loops`,
    /// `prepare_expansion`); marking an open object or row a second time
    /// would alias it.
    marked: Vec<TypeExprRef>,
}

impl<'a> TypeExprPrinter<'a> {
    fn new(type_ctx: &'a TypeContext) -> Self {
        Self {
            type_ctx,
            printtyp: crate::types::printtyp::Printtyp::new(type_ctx),
            weak_names: false,
            marked: Vec::new(),
        }
    }

    fn new_with_weak_names(type_ctx: &'a TypeContext) -> Self {
        Self {
            weak_names: true,
            ..Self::new(type_ctx)
        }
    }

    /// `Printtyp.reset`.
    fn reset(&mut self) {
        self.printtyp.reset();
        self.marked.clear();
    }

    /// `Printtyp.mark_loops`.
    fn mark_loops(&mut self, ty: TypeExprRef) {
        self.marked.push(self.type_ctx.repr(ty));
        self.printtyp.mark_loops(ty);
    }

    /// `Printtyp.mark_loops` unless the session already marked `ty`.
    fn mark_loops_once(&mut self, ty: TypeExprRef) {
        if !self.marked.contains(&self.type_ctx.repr(ty)) {
            self.mark_loops(ty);
        }
    }

    /// `Printtyp.type_expr` without marking.
    fn print(&mut self, ty: TypeExprRef) -> String {
        self.printtyp.type_expr(ty)
    }

    /// Print `ty` (marking its loops first if the session has not):
    /// `type_expr`, or `type_sch` for a weak-name printer.
    fn format(&mut self, ty: TypeExprRef) -> String {
        self.mark_loops_once(ty);
        if self.weak_names {
            self.printtyp.type_sch(ty)
        } else {
            self.printtyp.type_expr(ty)
        }
    }
}

fn generated_type_var_name(idx: usize) -> String {
    let letter = (b'a' + (idx % 26) as u8) as char;
    if idx < 26 {
        format!("'{letter}")
    } else {
        format!("'{letter}{}", idx / 26)
    }
}

#[cfg(test)]
#[derive(Clone, Debug, Default)]
struct PreJsDiscriminatorTrace {
    type_context_stamp: i32,
    raw_converter_stamp: i32,
    raw_max_stamp: i32,
    raw_lambda: String,
    lowered_lambda: String,
    js_program: String,
}

/// Compile ReScript source to JavaScript.
pub fn compile_source_to_js(source: &str, filename: &str) -> Result<String> {
    compile_source_to_js_with_options(source, filename, &CompilerOptions::default())
}

/// Compile ReScript source to JavaScript with options.
pub fn compile_source_to_js_with_options(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> Result<String> {
    compile_source_to_js_with_options_inner(
        source,
        filename,
        options,
        #[cfg(test)]
        None,
    )
}

#[cfg(test)]
fn compile_source_to_js_with_trace(
    source: &str,
    filename: &str,
    trace: &mut PreJsDiscriminatorTrace,
) -> Result<String> {
    compile_source_to_js_with_options_inner(
        source,
        filename,
        &CompilerOptions::default(),
        Some(trace),
    )
}

/// Output of [`run_implementation_frontend`]: the rewritten structure plus the
/// file-level settings later phases read from the source structure.
pub struct ImplementationFrontend {
    pub structure: Structure,
    /// A frontend warning was configured as an error.
    pub warnings_fatal: bool,
    pub frontend_warning_specs: Vec<ppx::WarningAttributeSpec>,
    pub file_config: FileConfigOverrides,
    pub file_directives: Vec<String>,
    pub debug: bool,
    pub jsx_preserve: bool,
    pub experimental_let_unwrap: bool,
}

/// Everything OCaml runs between parsing and type checking an implementation:
/// parser warnings, external PPXs (`Cmd_ppx_apply.apply_rewriters`) and
/// `Ppx_entry.rewrite_implementation` (compiler/frontend/ppx_entry.ml:45-60),
/// together with the frontend checks Rust performs around them. This is also
/// what `bsc -bs-ast` does before writing the AST
/// (compiler/core/js_implementation.ml:172-186). Warning reports are appended
/// to `out` in emission order; the caller prints or captures them.
pub fn run_implementation_frontend(
    parser: &mut Parser<'_>,
    structure: Structure,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    out: &mut String,
) -> Result<ImplementationFrontend> {
    let parser_warnings_have_errors =
        format_parser_warnings(parser, source, filename, options, out);
    if parser.has_errors() {
        return Err(parser_error_to_anyhow(&parser, source, filename));
    }
    let structure =
        apply_external_structure_ppxs(options, filename, parser.arena_mut(), structure)?;
    let frontend_warnings =
        ppx::collect_leading_builtin_warning_attributes(&structure, parser.arena());
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_attribute_specs(&structure, parser.arena());
    let mut ppx_warnings_have_errors = parser_warnings_have_errors
        | format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            &warning_config_for_options(options),
            &frontend_warnings,
            out,
        );
    let config_processing = validate_file_config_from_structure(
        &structure,
        parser.arena(),
        &warning_config_for_options_and_leading_attrs(options, &frontend_warning_specs),
    );
    for (warning, config) in &config_processing.warnings {
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            config,
            std::slice::from_ref(warning),
            out,
        );
    }
    if let Some(err) = config_processing.error {
        return Err(config_payload_error_to_anyhow(
            err,
            parser.arena(),
            source,
            filename,
        ));
    }
    let file_config = config_processing.overrides;
    let file_warning_config = warning_config_for_options_file_config_and_leading_attrs(
        options,
        &file_config,
        &frontend_warning_specs,
    );
    let file_directives = extract_file_directives_from_structure(&structure, parser.arena())
        .map_err(|err| directive_payload_error_to_anyhow(err, parser.arena(), source, filename))?;
    let debug = debug_for_structure(&structure, options, parser.arena());
    let jsx_preserve = jsx_preserve_for_structure(&structure, options, parser.arena());
    let experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
    if !options.no_builtin_ppx {
        reject_disabled_let_unwrap_in_structure(
            experimental_let_unwrap,
            &structure,
            parser.arena(),
            source,
            filename,
        )?;
        reject_enabled_invalid_let_unwrap_in_structure(
            experimental_let_unwrap,
            &structure,
            parser.arena(),
            source,
            filename,
        )?;
    }
    // Source fallback path: only run JSX rewrite when the file enables `-bs-jsx`.
    let jsx_version = options.jsx_version.or(file_config.jsx_version);
    let structure = if let Some(jsx_version) = jsx_version {
        let (structure, jsx_warnings) = jsx_ppx::transform_structure_collecting_warnings(
            structure,
            jsx_version,
            jsx_module_name(options, Some(&file_config)),
            parser.arena_mut(),
        );
        let jsx_warnings = jsx_preprocessor_warnings_to_ppx(parser.arena_mut(), jsx_warnings);
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            &file_warning_config,
            &jsx_warnings,
            out,
        );
        structure.map_err(|e| jsx_ppx_error_to_anyhow(e, parser.arena(), source, filename))?
    } else {
        structure
    };

    let structure = if options.no_builtin_ppx {
        structure
    } else {
        // OCaml `Ast_config.process_str` marks the leading `@@config` before
        // the builtin mapper runs (compiler/frontend/ppx_entry.ml:48-50).
        ppx::mark_config_attributes_structure(&structure, parser.arena());
        // Rewrite expressions: desugar pipe (->), setter (#=), property access (##),
        // await, tagged templates, encode externals, and apply spice mapper rewrites.
        // spice is handled here, so avoid running a second top-level spice expansion pass.
        // The mapper's warnings precede its error.
        let (rewritten, ppx_warnings) =
            ppx::rewrite_structure_with_warnings(&structure, parser.arena_mut());
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            &file_warning_config,
            &ppx_warnings,
            out,
        );
        let rewritten =
            rewritten.map_err(|e| ppx_error_to_anyhow(e, parser.arena(), source, filename))?;
        // OCaml `Bs_ast_invariant.emit_external_warnings_on_structure` runs over
        // the rewritten structure (compiler/frontend/ppx_entry.ml:60-63).
        let (unused_attribute_warnings, invariant_error) =
            ppx::collect_unused_attribute_warnings_structure(&rewritten, parser.arena());
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            &file_warning_config,
            &unused_attribute_warnings,
            out,
        );
        if let Some(e) = invariant_error {
            return Err(ppx_error_to_anyhow(e, parser.arena(), source, filename));
        }
        rewritten
    };
    // js_implementation.ml:125-129: `after_parsing_impl` runs the second
    // `Ast_config.process_str` after the builtin ppx.
    for (warning, config) in &config_processing.late_warnings {
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            config,
            std::slice::from_ref(warning),
            out,
        );
    }
    // js_implementation.ml:130 `if !Js_config.no_export then no_export ast`,
    // applied once to the top-level structure after the frontend.
    let structure =
        crate::binary_ast::writer::apply_no_export_config(parser.arena_mut(), structure);
    Ok(ImplementationFrontend {
        structure,
        warnings_fatal: ppx_warnings_have_errors,
        frontend_warning_specs,
        file_config,
        file_directives,
        debug,
        jsx_preserve,
        experimental_let_unwrap,
    })
}

fn compile_source_to_js_with_options_inner(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    #[cfg(test)] mut discriminator_trace: Option<&mut PreJsDiscriminatorTrace>,
) -> Result<String> {
    // Parse
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);
    let mut frontend_output = String::new();
    let frontend = run_implementation_frontend(
        &mut parser,
        structure,
        source,
        filename,
        options,
        &mut frontend_output,
    );
    if !options.frontend_already_reported {
        write_stderr(&frontend_output);
    }
    let ImplementationFrontend {
        structure,
        warnings_fatal: ppx_warnings_have_errors,
        frontend_warning_specs,
        file_config,
        file_directives,
        debug,
        jsx_preserve,
        experimental_let_unwrap,
    } = frontend?;
    let ppx_warnings_have_errors = if options.frontend_already_reported {
        report_stored_ast_config_warnings(
            first_config_attribute_of_structure(&structure, parser.arena()),
            true,
            parser.arena(),
            source,
            filename,
            options,
        )
    } else {
        ppx_warnings_have_errors
    };
    parser.arena_mut().reserve_typecheck_synthetic_capacity();

    // Type check
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    tctx.experimental_let_unwrap = experimental_let_unwrap;
    tctx.transparent_modules = options.transparent_modules;
    apply_warning_options(&mut tctx, options);
    // Ppx_entry.rewrite_* (ppx_entry.ml:28, 47) applies the leading warning
    // attributes; compiling a preprocessed `.ast` does not run it again.
    if !options.frontend_already_reported {
        apply_leading_warning_attribute_options(&mut tctx, &frontend_warning_specs);
    }
    apply_file_config_warning_options(&mut tctx, &file_config);
    let mut env = initial_env(&type_ctx);

    // Load Pervasives and extend the initial environment
    let mut pers_env = PersistentEnv::new();
    let (load_path, load_path_display) = shared_load_path_with_display(options);
    type_ctx.set_load_paths_shared(load_path.clone());
    pers_env.set_load_path_shared(load_path.clone(), load_path_display);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_jsx_module(options.jsx_module.clone());
    let current_unit_name = options.current_unit_name();
    pers_env.set_compiling_module(current_unit_name.clone());
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        current_unit_name.as_deref(),
    );

    // Store persistent env in the type check context for module resolution
    tctx.set_persistent_env(pers_env);

    let (typed_structure, final_env) =
        match type_structure(&mut tctx, &env, parser.arena(), &structure) {
            Ok(result) => result,
            Err(e) => {
                // OCaml compiler/ext/misc.ml:337-392: `Color.color_enabled`
                // starts as `true` and takes the configured `-color` value at
                // the first `Location.setup_colors` (location.ml:45-47), which
                // printing a warning triggers. Messages formatted afterwards
                // only carry style escapes when colors are enabled.
                tctx.drain_open_slot_uses();
                let suppress_info_style =
                    !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
                emit_type_warnings(parser.arena(), source, filename, &tctx.warnings);
                if let Some(error) = tctx
                    .persistent_env
                    .as_ref()
                    .and_then(|persistent_env| persistent_env.last_error())
                {
                    return Err(persistent_env_error_to_anyhow(error, filename));
                }
                return Err(type_mod_error_to_anyhow(
                    e,
                    &type_ctx,
                    parser.arena(),
                    source,
                    filename,
                    suppress_info_style,
                ));
            }
        };
    if let Some(error) = tctx
        .persistent_env
        .as_ref()
        .and_then(|persistent_env| persistent_env.last_error())
    {
        return Err(persistent_env_error_to_anyhow(error, filename));
    }
    tctx.drain_open_slot_uses();
    emit_type_warnings(parser.arena(), source, filename, &tctx.warnings);
    // js_implementation.ml:158-163: `Warnings.check_fatal` runs only after
    // `Typemod.type_implementation_more`, whose delayed checks
    // (typemod.ml:1769-1776) still report their warnings.
    let early_warnings_have_errors =
        ppx_warnings_have_errors || type_warnings_have_errors(&tctx.warnings);
    let delayed_type_warning_start = tctx.warnings.len();

    let source_file_for_interface = options.source_filename.as_deref().unwrap_or(filename);
    let has_resi = source_file_for_interface.ends_with(".res")
        && source_has_interface(options, source_file_for_interface);
    let gentype_ignore_interface = options.gentype_config.is_some()
        && has_resi
        && interface_source_has_gentype_ignore_interface(source_file_for_interface);
    if options.assume_compiled_interface
        && source_file_for_interface.ends_with(".res")
        && !compiled_interface_file_exists(options, source_file_for_interface)
    {
        let intf_name = interface_source_name(source_file_for_interface);
        return Err(UserDiagnostic::new(
            format_interface_not_compiled_report(source, filename, parser.filename(), &intf_name),
            2,
        )
        .into());
    }

    // Apply interface constraints: moregen linking for non-generic Tvars.
    // OCaml's Includemod.compunit -> moregeneral -> moregen links weak (non-generic)
    // type variables from value-restricted expressions to the corresponding types
    // from the .resi interface. This happens BEFORE sexp serialization.
    apply_moregen_constraints(
        &mut tctx,
        &type_ctx,
        &typed_structure,
        options,
        Some(has_resi),
    );
    check_compunit_inclusion_for_errors(
        &mut tctx,
        &type_ctx,
        &env,
        &typed_structure,
        source_file_for_interface,
        &|| source.to_string(),
        filename,
        has_resi,
        None,
    )?;

    // OCaml compiler/ml/typemod.ml:1755-1758 reads the compiled interface
    // through Env.read_signature; persistent Env errors raised there abort
    // implementation typing before warnings are reported as success.
    if let Some(error) = tctx
        .persistent_env
        .as_ref()
        .and_then(|persistent_env| persistent_env.last_error())
    {
        return Err(persistent_env_error_to_anyhow(error, filename));
    }

    // OCaml's no-interface path runs inferred-signature inclusion before
    // checking non-generalizable schemes and normalizing the signature
    // (compiler/ml/typemod.ml:1766-1771). Besides producing the export
    // coercion, the real Includemod traversal performs substitution and Ident
    // allocations that must precede Lambda identifier allocation.
    let (inferred_simple_signature, inferred_implementation_coercion) = if !has_resi {
        let simple_signature =
            crate::types::includemod::simplify_signature(&typed_structure.str_type);
        let implementation_coercion = crate::types::includemod::compunit(
            &type_ctx,
            &env,
            source_file_for_interface,
            &typed_structure.str_type,
            "(inferred signature)",
            &simple_signature,
        )
        .map_err(|e| anyhow!("Inferred signature inclusion failed: {e:?}"))?;
        if let Err(e) =
            crate::types::typemod::check_nongen_schemes(&type_ctx, &final_env, &simple_signature)
        {
            // The warnings printed so far have set up colors (misc.ml:337-392).
            let suppress_info_style =
                !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
            return Err(type_mod_error_to_anyhow(
                e,
                &type_ctx,
                parser.arena(),
                source,
                filename,
                suppress_info_style,
            ));
        }
        normalize_signature(&type_ctx, &final_env, &simple_signature);
        (Some(simple_signature), Some(implementation_coercion))
    } else {
        (None, None)
    };

    // OCaml compiler/ml/typemod.ml:1769-1776 forces delayed checks before
    // compiler/core/js_implementation.ml:148-156 prints `-dtyped-sexp`; Rust
    // typedtree-only runs must therefore flush value-usage checks before the dump.
    tctx.flush_value_usage_checks();
    let delayed_warnings = &tctx.warnings[delayed_type_warning_start..];
    emit_type_warnings(parser.arena(), source, filename, delayed_warnings);
    // `Warnings.check_fatal` only runs at lam_compile_main.ml:420 (or right
    // after typing for typedtree/cmi-only runs, js_implementation.ml:158-159),
    // so a fatal typing warning still lets Translmod report its warnings.
    let typing_warnings_fatal =
        early_warnings_have_errors || type_warnings_have_errors(delayed_warnings);
    let post_type_warning_start = tctx.warnings.len();

    // Print typed tree if requested
    if options.dump_typed_sexp {
        let mut stderr = std::io::stderr();
        let _ = print_typed_structure(parser.arena(), &type_ctx, &typed_structure, &mut stderr);
    }
    if options.dump_typed_sexp_locs {
        let mut stderr = std::io::stderr();
        let _ = print_typed_structure_with_locs(
            parser.arena(),
            &type_ctx,
            &typed_structure,
            &mut stderr,
        );
    }

    // `Env.save_signature` renames the bound identifiers of a copy of the
    // inferred signature (env.ml:1886-1892), taking stamps; no file is written.
    if let Some(simple_signature) = inferred_simple_signature.as_deref()
        && !has_resi
    {
        saved_signature_copy(&type_ctx, simple_signature);
    }

    // `process_with_gentype` runs after the JS is emitted
    // (js_implementation.ml:164), which a fatal warning prevents.
    if options.gentype_config.is_some()
        && (!has_resi || gentype_ignore_interface)
        && !typing_warnings_fatal
    {
        let module_name = current_unit_name
            .clone()
            .unwrap_or_else(|| module_name_from_source_filename(source_file_for_interface));
        if !has_resi && let Some(simple_signature) = inferred_simple_signature.as_deref() {
            // OCaml saves the inferred signature before GenType consumes CMT
            // data in compiler/ml/typemod.ml:1779-1788 and
            // compiler/gentype/GenTypeMain.ml:136-175. The direct Rust CLI
            // path does not write/read a CMT, so expose the same pre-finalized
            // raw signature to GenType's alias scraping path.
            let current_raw_sig =
                std::sync::Arc::new(crate::types::typecore::copy_lookup_signature_for_subst(
                    simple_signature,
                    &type_ctx,
                ));
            type_ctx.register_gentype_raw_module_sig(&module_name, current_raw_sig.clone());
            type_ctx.register_raw_module_sig(&module_name, current_raw_sig);
        }
        process_gentype_typed_artifact_if_enabled(
            options,
            crate::gentype::main::TypedArtifactAnnots::Implementation(&typed_structure),
            parser.arena(),
            &type_ctx,
            source_file_for_interface,
            &module_name,
            false,
        )?;
    }

    // Typedtree parity runs only need typechecking output.
    // Skipping Lambda/JS lowering avoids unrelated downstream failures
    // (timeouts/crashes) from obscuring typedtree parity results.
    if (options.dump_typed_sexp || options.dump_typed_sexp_locs)
        && std::env::var_os("RUST_TYPEDTREE_ONLY").is_some()
    {
        if typing_warnings_fatal {
            return Err(UserDiagnostic::new(String::new(), 2).into());
        }
        return Ok(String::new());
    }

    let lambda_start_stamp = synchronize_lambda_start_stamp(&type_ctx);

    let raw_trace = std::env::var_os("RUST_DRAWLAMBDA_STAGE_TRACE").is_some();
    if options.dump_lambda && raw_trace {
        eprintln!("[drawlambda-stage] start");
    }
    let unit_name = options.current_unit_name().unwrap_or_default();
    let implementation_coercion = inferred_implementation_coercion.unwrap_or_else(|| {
        compute_raw_implementation_coercion(
            &mut tctx,
            &type_ctx,
            &env,
            &typed_structure,
            options,
            Some(has_resi),
        )
    });
    let mut raw_converter =
        crate::raw_lambda::convert::RawLambdaConverter::with_start_stamp_and_unit_name(
            parser.arena(),
            &type_ctx,
            &env,
            lambda_start_stamp,
            unit_name,
        );
    raw_converter.set_preserve_expanded_sparse_records(
        options.dump_lambda || options.dump_lambda_sexp || options.dump_lambda_sexp_locs,
    );
    raw_converter.set_no_assert_false(options.no_assert_false);
    raw_converter.set_noassert(options.noassert);
    raw_converter.set_warning_config(tctx.warning_config.clone());
    if let Some(persistent_env) = tctx.persistent_env.clone() {
        raw_converter.set_persistent_env(persistent_env);
    }
    if options.dump_lambda && raw_trace {
        eprintln!("[drawlambda-stage] before-convert");
    }
    let raw_lambda =
        raw_converter.convert_structure_with_coercion(&typed_structure, &implementation_coercion);
    let raw_warnings = raw_converter.take_warnings();
    let hoisted_functions = raw_converter.take_hoisted_functions();
    if let Some(diagnostic) = raw_converter.take_diagnostic() {
        // A Translmod error escapes before `Warnings.check_fatal`.
        emit_type_warnings(parser.arena(), source, filename, &raw_warnings);
        return Err(UserDiagnostic::new(
            format_compiler_error_report_from_location(
                source,
                filename,
                &diagnostic.loc,
                &diagnostic.message,
            ),
            2,
        )
        .into());
    }
    let late_type_warnings = &tctx.warnings[post_type_warning_start..];
    emit_type_warnings(parser.arena(), source, filename, late_type_warnings);
    emit_type_warnings(parser.arena(), source, filename, &raw_warnings);
    // lam_compile_main.ml:420 `Warnings.check_fatal ()` runs after the
    // lambda and JS passes (checked below, after `lam_compile`).
    let warnings_fatal = typing_warnings_fatal
        || type_warnings_have_errors(late_type_warnings)
        || type_warnings_have_errors(&raw_warnings);
    let possible_required_modules = raw_converter.take_possible_required_modules();
    let raw_lambda_current_stamp = raw_converter.current_stamp();
    #[cfg(test)]
    if let Some(trace) = discriminator_trace.as_deref_mut() {
        trace.type_context_stamp = type_ctx.current_stamp();
        trace.raw_converter_stamp = raw_lambda_current_stamp;
        trace.raw_max_stamp = crate::raw_lambda::lower::max_ident_stamp_for_test(&raw_lambda);
        trace.raw_lambda = format!("{raw_lambda:#?}");
    }

    let (lowered_lambda, export_idents) =
        crate::raw_lambda::lower::lower_to_translmod_lambda_with_start_stamp(
            raw_lambda,
            raw_lambda_current_stamp,
        );
    // js_implementation.ml:165 prints `-drawlambda` on Translmod's result.
    if options.dump_lambda {
        use std::io::Write;
        let mut buf = Vec::new();
        crate::lambda::printlambda::print_lambda(&lowered_lambda, &mut buf);
        buf.push(b'\n');
        let mut stderr = std::io::stderr();
        let _ = stderr.write_all(&buf);
        let _ = stderr.flush();
        if std::env::var_os("RUST_RAWLAMBDA_ONLY").is_some() {
            std::process::exit(0);
        }
    }
    // lam_compile_main.ml:288-290: the first pass of Lam_compile_main.compile.
    let lowered_lambda =
        crate::lambda::lam_pass_collapse_var_aliases::collapse(lowered_lambda, &export_idents);
    if let Some(name) = crate::lambda::lam_compile_main::duplicate_export_name(&lowered_lambda) {
        return Err(duplicate_export_error(filename, &name));
    }

    #[cfg(test)]
    if let Some(trace) = discriminator_trace.as_deref_mut() {
        trace.lowered_lambda = format!("{lowered_lambda:#?}");
    }

    if options.dump_lambda_sexp || options.dump_lambda_sexp_locs {
        if options.dump_lambda_sexp {
            use std::io::Write;
            let mut stderr = std::io::stderr();
            let _ = crate::lambda::sexp_lambda::print_lambda(&lowered_lambda, &mut stderr);
            let _ = stderr.flush();
        }
        if options.dump_lambda_sexp_locs {
            use std::io::Write;
            let mut stderr = std::io::stderr();
            let _ =
                crate::lambda::sexp_lambda::print_lambda_with_locs(&lowered_lambda, &mut stderr);
            let _ = stderr.flush();
        }

        // Optimized-lambda parity only needs the dump output. Mirror the
        // typedtree parity short-circuit so large JS-backend work cannot turn
        // an exact dump match into a timeout-only failure.
        if std::env::var_os("RUST_LAMBDA_DUMP_ONLY").is_some() {
            std::process::exit(0);
        }
    }

    // Lambda -> JS IR
    let mut module_path_resolver = ModulePathResolver::from_compile_options(
        options.source_filename.as_deref(),
        options.output_path.as_deref(),
        options.output_module_format,
        options.package_name.as_deref(),
        options.runtime_path.as_deref(),
        tctx.persistent_env.clone(),
        options.make_runtime,
    );
    module_path_resolver.set_package_specs(&options.js_package_specs);
    for module in &possible_required_modules {
        if matches!(module.kind, Kind::Ml) && !module.dynamic_import {
            if let Some(path) =
                module_path_resolver.resolve_local_module_fallback_path(module.id.name())
            {
                module_path_resolver.set_module_path_override(module.id.name(), path);
            }
        }
    }
    let mut compiler = LambdaCompiler::with_module_path_resolver_and_options(
        Some(module_path_resolver),
        jsx_preserve,
        options.check_div_by_zero,
        options.cross_module_inline,
    );
    compiler.set_source_map_enabled(
        options.source_map != crate::js_ir::source_map::SourceMapMode::None,
    );
    compiler.set_hoisted_functions(hoisted_functions);
    let program = compiler.compile_deps_program_with_possible_required_modules(
        &lowered_lambda,
        &possible_required_modules,
    );
    #[cfg(test)]
    if let Some(trace) = discriminator_trace.as_deref_mut() {
        trace.js_program = format!("{program:#?}");
    }
    if let Some(diagnostic) = compiler.take_diagnostic() {
        return Err(UserDiagnostic::new(
            format_compiler_error_report_from_location(
                source,
                filename,
                &diagnostic.loc,
                &diagnostic.message,
            ),
            2,
        )
        .into());
    }
    // lam_compile_main.ml:420 `Warnings.check_fatal ()`.
    if warnings_fatal {
        return Err(UserDiagnostic::new(String::new(), 2).into());
    }
    let module_path_resolver = compiler
        .take_module_path_resolver()
        .expect("lambda compiler retained module path resolver");
    check_module_path_resolution_errors(&program, &module_path_resolver, filename)?;

    // JS IR -> JS source. File-based compilation writes the companion map
    // here because its public return value remains the generated JS string;
    // in-process compilation carries the map on `JsOutput` instead.
    let (js, source_map) = render_js_program(
        &program,
        &module_path_resolver,
        &file_directives,
        debug,
        jsx_preserve,
        options,
        options.output_path.as_deref(),
        std::sync::Arc::new(parser.arena().source_file_names()),
    );
    if let Some(output_path) = options.output_path.as_deref() {
        let map_path = PathBuf::from(format!("{}.map", output_path.display()));
        if let Some(source_map) = source_map {
            if let Some(parent) = map_path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(map_path, source_map)?;
        } else {
            let _ = std::fs::remove_file(map_path);
        }
    }

    // The CLI compiler is a short-lived process. Skipping teardown for the
    // large typechecking arenas keeps snapshot runs inside the harness timeout
    // once output has already been produced.
    if SKIP_CLI_CLEANUP.load(Ordering::Relaxed) {
        std::mem::forget(compiler);
        std::mem::forget(program);
        std::mem::forget(lowered_lambda);
        std::mem::forget(raw_converter);
        std::mem::forget(implementation_coercion);
        std::mem::forget(typed_structure);
        std::mem::forget(final_env);
        std::mem::forget(env);
        std::mem::forget(tctx);
        std::mem::forget(type_ctx);
        std::mem::forget(structure);
        std::mem::forget(parser);
    }

    Ok(js)
}

/// Build a structural module coercion by matching interface items to implementation
/// positions by name, without type-checking. Used as a fallback when `compunit`
/// fails due to type representation differences (e.g., OCaml CMI stamps vs Rust stamps).
///
/// This matches OCaml's `Tcoerce_structure` behavior: for each runtime component
/// in the interface signature, find its runtime position in the implementation
/// signature and emit a `(pos, Tcoerce_none)` entry. Items in the implementation
/// that don't appear in the interface are excluded from the export block.
fn build_name_based_coercion(
    impl_sig: &crate::types::decl::Signature,
    intf_sig: &crate::types::decl::Signature,
) -> crate::types::typedtree::ModuleCoercion {
    use crate::types::decl::{AliasPresence, ModuleType, SignatureItem, ValueKind};
    use crate::types::includemod::is_runtime_component;
    use crate::types::typedtree::{EnvRef, ModuleCoercion, PrimitiveCoercion};

    fn module_type_coercion(impl_mty: &ModuleType, intf_mty: &ModuleType) -> ModuleCoercion {
        match (impl_mty, intf_mty) {
            (
                ModuleType::MtyAlias(pres_impl, impl_path),
                ModuleType::MtyAlias(pres_sig, intf_path),
            ) => {
                // OCaml `try_modtypes` first compares normalized alias paths,
                // then only emits `Tcoerce_alias` for absent implementation
                // aliases matched against present interface aliases
                // (compiler/ml/includemod.ml:209-228). Same absent aliases are
                // runtime-empty on both sides, so the fallback must keep them
                // identity instead of materializing the target module.
                if impl_path.same(intf_path)
                    && matches!(pres_impl, AliasPresence::MtaAbsent)
                    && matches!(pres_sig, AliasPresence::MtaPresent)
                {
                    ModuleCoercion::Tcoerce_alias(
                        EnvRef(0),
                        impl_path.clone(),
                        Box::new(ModuleCoercion::Tcoerce_none),
                    )
                } else {
                    ModuleCoercion::Tcoerce_none
                }
            }
            (ModuleType::MtyAlias(AliasPresence::MtaAbsent, impl_path), _) => {
                // OCaml wraps an absent implementation alias when the
                // interface expects an expanded module type
                // (compiler/ml/includemod.ml:230-241). This name-based
                // fallback cannot safely expand the target after the real
                // inclusion check failed, so preserve the existing alias
                // coercion at the same boundary.
                ModuleCoercion::Tcoerce_alias(
                    EnvRef(0),
                    impl_path.clone(),
                    Box::new(ModuleCoercion::Tcoerce_none),
                )
            }
            (ModuleType::MtySignature(impl_sig), ModuleType::MtySignature(intf_sig)) => {
                // OCaml recurses into submodule signatures when building
                // structural coercions (compiler/ml/includemod.ml:253-292,
                // 329-342), so an interface can hide fields inside an exported
                // module without leaking the implementation block shape.
                build_name_based_coercion(impl_sig, intf_sig)
            }
            (
                ModuleType::MtyFunctor {
                    result: impl_result,
                    ..
                },
                ModuleType::MtyFunctor {
                    result: intf_result,
                    ..
                },
            ) => {
                let result = module_type_coercion(impl_result, intf_result);
                if matches!(result, ModuleCoercion::Tcoerce_none) {
                    ModuleCoercion::Tcoerce_none
                } else {
                    // OCaml represents functor inclusion as a result coercion
                    // over the applied body (compiler/ml/includemod.ml:144-166;
                    // compiler/ml/translmod.ml:160-168). This fallback is used
                    // only after the real inclusion check failed, so keep the
                    // argument side identity and preserve the observable result
                    // export shape.
                    ModuleCoercion::Tcoerce_functor(
                        Box::new(ModuleCoercion::Tcoerce_none),
                        Box::new(result),
                    )
                }
            }
            _ => ModuleCoercion::Tcoerce_none,
        }
    }

    // Build name → runtime_position map from the implementation signature.
    // OCaml indexes every implementation component with the current runtime
    // position, then advances only for runtime components. That lets primitive
    // implementations satisfy regular interface values via Tcoerce_primitive.
    // See compiler/ml/includemod.ml:313-342 and 381-390.
    let mut impl_name_to_component: std::collections::HashMap<String, (usize, &SignatureItem)> =
        std::collections::HashMap::new();
    let mut runtime_pos = 0usize;
    for item in impl_sig {
        match item {
            SignatureItem::SigValue(id, _)
            | SignatureItem::SigModule(id, _, _)
            | SignatureItem::SigTypext(id, _, _) => {
                impl_name_to_component.insert(id.name().to_string(), (runtime_pos, item));
            }
            _ => {}
        }
        if is_runtime_component(item) {
            runtime_pos += 1;
        }
    }
    let len_impl = runtime_pos;

    // Build coercions and runtime_fields from the interface signature.
    // For each runtime component in the interface, look up its position in the impl.
    let mut coercions: Vec<(usize, ModuleCoercion)> = Vec::new();
    let mut runtime_fields: Vec<String> = Vec::new();

    for item in intf_sig {
        if !is_runtime_component(item) {
            continue;
        }
        let name = match item {
            SignatureItem::SigValue(id, _)
            | SignatureItem::SigModule(id, _, _)
            | SignatureItem::SigTypext(id, _, _) => id.name().to_string(),
            _ => continue,
        };
        if let Some(&(pos, impl_item)) = impl_name_to_component.get(&name) {
            let coercion = match (item, impl_item) {
                (
                    SignatureItem::SigValue(_, sig_desc),
                    SignatureItem::SigValue(impl_id, impl_desc),
                ) if !matches!(sig_desc.val_kind, ValueKind::ValPrim(_)) => {
                    match &impl_desc.val_kind {
                        ValueKind::ValPrim(prim) => {
                            // Mirrors compiler/ml/includecore.ml:52-63:
                            // Val_prim implementation + regular interface
                            // value is exported by a primitive coercion.
                            ModuleCoercion::Tcoerce_primitive(PrimitiveCoercion {
                                pc_desc: prim.clone(),
                                pc_type: sig_desc.val_type,
                                pc_loc: impl_desc.val_loc.clone(),
                                pc_id: impl_id.clone(),
                            })
                        }
                        ValueKind::ValReg => ModuleCoercion::Tcoerce_none,
                    }
                }
                (
                    SignatureItem::SigModule(_, sig_md, _),
                    SignatureItem::SigModule(_, impl_md, _),
                ) => module_type_coercion(&impl_md.md_type, &sig_md.md_type),
                _ => ModuleCoercion::Tcoerce_none,
            };
            coercions.push((pos, coercion));
            runtime_fields.push(name);
        }
    }

    let len_sig = coercions.len();

    // Check if this is already an identity coercion (same items in same order)
    let is_identity = len_impl == len_sig
        && coercions
            .iter()
            .enumerate()
            .all(|(expected_pos, (actual_pos, coercion))| {
                *actual_pos == expected_pos && matches!(coercion, ModuleCoercion::Tcoerce_none)
            });

    if is_identity {
        ModuleCoercion::Tcoerce_none
    } else {
        ModuleCoercion::Tcoerce_structure(coercions, Vec::new(), runtime_fields)
    }
}

fn report_compunit_inclusion_warnings(
    tctx: &mut TypeCheckContext<'_>,
    warnings: Vec<crate::diagnostics::Warning>,
) {
    let loc = tctx.arena.none_loc();
    for warning in warnings {
        tctx.report_warning(loc, warning);
    }
}

fn direct_compunit_error_location(
    error: &crate::types::includemod::IncludeModError,
) -> Option<&Location> {
    use crate::types::includemod::IncludeModError;

    match error {
        IncludeModError::ValueTypeMismatch { actual, .. } => Some(&actual.val_loc),
        IncludeModError::TypeDeclarationMismatch { actual, .. } => Some(&actual.type_loc),
        IncludeModError::MissingField { loc, .. } => Some(loc),
        IncludeModError::SignatureMismatch(errors) if errors.len() == 1 => {
            direct_compunit_error_location(&errors[0])
        }
        _ => None,
    }
}

fn format_compiler_error_report_raw_message_from_location(
    source: &str,
    filename: &str,
    loc: &Location,
    message: &str,
) -> String {
    let mut output = String::new();

    push_compiler_error_report_header_from_location(&mut output, source, filename, loc);
    output.push_str(message);
    if !message.ends_with('\n') {
        output.push('\n');
    }
    output.push('\n');
    output
}

fn format_compunit_mismatch_report(
    type_ctx: &TypeContext,
    source: &str,
    filename: &str,
    impl_name: &str,
    intf_name: &str,
    error: &crate::types::includemod::IncludeModError,
) -> String {
    let file_loc = Location::in_file(StrIdx::default());
    let loc = direct_compunit_error_location(error).unwrap_or(&file_loc);
    let mut message = String::new();
    message.push_str("  The implementation ");
    message.push_str(impl_name);
    message.push('\n');
    message.push_str("  does not match the interface ");
    message.push_str(intf_name);
    message.push_str(":\n");
    message.push_str(
        &crate::types::includemod::format_error_without_signature_header(type_ctx, filename, error),
    );
    // The report is located where the error is (location.ml prints
    // `loc.loc_start.pos_fname`), e.g. at a value only the interface declares.
    let loc_file = crate::types::includemod::location_filename(type_ctx, filename, loc);
    if loc_file != filename
        && let Ok(bytes) = std::fs::read(&loc_file)
    {
        let loc_source = crate::source_text::latin1_bytes_to_string(bytes);
        return format_compiler_error_report_raw_message_from_location(
            &loc_source,
            &loc_file,
            loc,
            &message,
        );
    }
    format_compiler_error_report_raw_message_from_location(source, filename, loc, &message)
}

/// The `.cmi` name `Typemod.type_implementation` reports for an interface:
/// `find_in_path_uncap !Config.load_path (modulename ^ ".cmi")`
/// (typemod.ml:1742-1749), the file the interface compile wrote, in
/// `interface_cmi_dir` (or next to the source).
fn in_process_interface_display_name(options: &CompilerOptions, source_file: &str) -> String {
    match &options.interface_cmi_dir {
        Some(dir) => {
            let stem = std::path::Path::new(source_file)
                .file_stem()
                .map(|stem| stem.to_string_lossy().into_owned())
                .unwrap_or_default();
            dir.join(format!("{stem}.cmi"))
                .to_string_lossy()
                .into_owned()
        }
        None => interface_cmi_name(source_file),
    }
}

#[allow(clippy::too_many_arguments)]
/// The result of checking an implementation against its interface: OCaml's
/// one `Includemod.compunit` call gives both the coercion Translmod uses and
/// the inclusion warnings (typemod.ml:1742-1758).
struct CompunitInclusion {
    coercion: crate::types::typedtree::ModuleCoercion,
    warnings: Vec<crate::diagnostics::Warning>,
}

fn check_compunit_inclusion_for_errors(
    tctx: &mut TypeCheckContext<'_>,
    type_ctx: &TypeContext,
    env: &Env,
    typed_structure: &crate::types::typedtree::Structure,
    source_file: &str,
    source: &dyn Fn() -> String,
    filename: &str,
    has_resi: bool,
    interface_file: Option<&str>,
) -> Result<Option<CompunitInclusion>> {
    if !has_resi || !source_file.ends_with(".res") {
        return Ok(None);
    }

    let module_name = module_name_from_source_filename(source_file);
    if module_name.is_empty() {
        return Ok(None);
    }

    let Some(pers) = &mut tctx.persistent_env else {
        return Ok(None);
    };
    let source_dir = std::path::Path::new(source_file)
        .parent()
        .map(|d| d.to_path_buf())
        .unwrap_or_else(|| std::path::PathBuf::from("."));
    if !pers.load_path_contains(&source_dir) {
        pers.add_load_path(source_dir);
    }
    let _ = pers.find_pers_struct(&module_name, type_ctx);
    // In-process, the interface was saved without a `.cmi`; its raw `ps_sig`
    // travels with the registered portable structure.
    let raw_in_process_sig = if pers.is_in_process_mode() {
        type_ctx.get_gentype_raw_module_sig(&module_name)
    } else {
        None
    };
    let Some(target_sig) =
        raw_in_process_sig.or_else(|| pers.read_raw_sig_shared(&module_name, type_ctx))
    else {
        return Ok(None);
    };
    // Env.read_signature forces ps_sig, whose Subst.signature identity copy
    // renames every bound interface identifier before compunit inclusion
    // (compiler/ml/env.ml:1867-1869, compiler/ml/subst.ml:322-354).
    rename_saved_signature_idents(type_ctx, target_sig.as_ref());

    let mut inclusion_warnings = Vec::new();
    match crate::types::includemod::compunit_with_warnings(
        type_ctx,
        env,
        source_file,
        &typed_structure.str_type,
        &interface_file
            .map(str::to_string)
            .unwrap_or_else(|| interface_cmi_name(source_file)),
        target_sig.as_ref(),
        &mut inclusion_warnings,
    ) {
        Ok(coercion) => Ok(Some(CompunitInclusion {
            coercion,
            warnings: inclusion_warnings,
        })),
        Err(error) => Err(UserDiagnostic::new(
            format_compunit_mismatch_report(
                type_ctx,
                &source(),
                filename,
                source_file,
                &interface_file
                    .map(str::to_string)
                    .unwrap_or_else(|| interface_cmi_name(source_file)),
                &error,
            ),
            2,
        )
        .into()),
    }
}

fn compute_raw_implementation_coercion(
    tctx: &mut TypeCheckContext<'_>,
    type_ctx: &TypeContext,
    env: &Env,
    typed_structure: &crate::types::typedtree::Structure,
    options: &CompilerOptions,
    known_has_interface: Option<bool>,
) -> crate::types::typedtree::ModuleCoercion {
    let Some(source_file) = &options.source_filename else {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    };
    if !source_file.ends_with(".res") {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    }

    let impl_sig = &typed_structure.str_type;
    let has_resi = known_has_interface
        .unwrap_or_else(|| std::path::Path::new(&format!("{source_file}i")).exists());
    if !has_resi {
        // The no-interface coercion is computed at the Typemod boundary before
        // signature normalization and passed through to Lambda translation.
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    }

    let module_name = module_name_from_source_filename(source_file);
    if module_name.is_empty() {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    }
    let Some(pers) = &mut tctx.persistent_env else {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    };
    let source_dir = std::path::Path::new(source_file)
        .parent()
        .map(|d| d.to_path_buf())
        .unwrap_or_else(|| std::path::PathBuf::from("."));
    if !pers.load_path_contains(&source_dir) {
        pers.add_load_path(source_dir);
    }
    let _ = pers.find_pers_struct(&module_name, type_ctx);
    let target_sig = match pers.read_raw_sig_shared(&module_name, type_ctx) {
        Some(sig) => sig,
        None => return crate::types::typedtree::ModuleCoercion::Tcoerce_none,
    };

    let mut inclusion_warnings = Vec::new();
    let inclusion_result = crate::types::includemod::compunit_with_warnings(
        type_ctx,
        env,
        source_file,
        impl_sig,
        "(inferred signature)",
        target_sig.as_ref(),
        &mut inclusion_warnings,
    );
    report_compunit_inclusion_warnings(tctx, inclusion_warnings);

    match inclusion_result {
        Ok(cc) => cc,
        Err(_) if has_resi => {
            // compunit can fail when the OCaml-built CMI has different type stamps
            // than what Rust's type-checker produces. In that case, fall back to a
            // name-based structural coercion that at least filters the export block
            // to match the interface's set of exported items. This ensures functors
            // and other implementation-only items are excluded from the module export
            // block, matching OCaml's behavior.
            build_name_based_coercion(impl_sig, &target_sig)
        }
        Err(_) => crate::types::typedtree::ModuleCoercion::Tcoerce_none,
    }
}

/// Type-check an interface file and dump typed sexp if requested.
/// Interface files (.resi) don't produce JS output, only .cmi files.
/// Output of [`run_interface_frontend`].
pub struct InterfaceFrontend {
    pub signature: Signature,
    /// A frontend warning was configured as an error.
    pub warnings_fatal: bool,
    pub frontend_warning_specs: Vec<ppx::WarningAttributeSpec>,
    pub file_config: FileConfigOverrides,
    pub experimental_let_unwrap: bool,
}

/// The interface counterpart of [`run_implementation_frontend`]: parser
/// warnings, external PPXs and `Ppx_entry.rewrite_signature`
/// (compiler/frontend/ppx_entry.ml:27-43). Warning reports go to `out`.
pub fn run_interface_frontend(
    parser: &mut Parser<'_>,
    signature: Signature,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    out: &mut String,
) -> Result<InterfaceFrontend> {
    let parser_warnings_have_errors =
        format_parser_warnings(parser, source, filename, options, out);
    if parser.has_errors() {
        return Err(parser_error_to_anyhow(&parser, source, filename));
    }
    let signature =
        apply_external_signature_ppxs(options, filename, parser.arena_mut(), signature)?;
    let frontend_warnings =
        ppx::collect_leading_builtin_warning_signature_attributes(&signature, parser.arena());
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_signature_attribute_specs(&signature, parser.arena());
    let mut ppx_warnings_have_errors = parser_warnings_have_errors
        | format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            &warning_config_for_options(options),
            &frontend_warnings,
            out,
        );
    let config_processing = validate_file_config_from_signature(
        &signature,
        parser.arena(),
        &warning_config_for_options_and_leading_attrs(options, &frontend_warning_specs),
    );
    for (warning, config) in &config_processing.warnings {
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            config,
            std::slice::from_ref(warning),
            out,
        );
    }
    if let Some(err) = config_processing.error {
        return Err(config_payload_error_to_anyhow(
            err,
            parser.arena(),
            source,
            filename,
        ));
    }
    let file_config = config_processing.overrides;
    let file_warning_config = warning_config_for_options_file_config_and_leading_attrs(
        options,
        &file_config,
        &frontend_warning_specs,
    );
    let experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
    let mut builtin_ppx_warnings = Vec::new();
    let signature = preprocess_signature_for_typecheck_with_source(
        signature,
        options,
        parser.arena_mut(),
        source,
        filename,
        &mut builtin_ppx_warnings,
    );
    ppx_warnings_have_errors |= format_ppx_warnings_with_config(
        parser.arena(),
        source,
        filename,
        &file_warning_config,
        &builtin_ppx_warnings,
        out,
    );
    let signature = signature?;
    if !options.no_builtin_ppx {
        // OCaml `Ast_config.process_sig` + `emit_external_warnings_on_signature`.
        ppx::mark_config_attributes_signature(&signature, parser.arena());
        let (unused_attribute_warnings, invariant_error) =
            ppx::collect_unused_attribute_warnings_signature(&signature, parser.arena());
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            &file_warning_config,
            &unused_attribute_warnings,
            out,
        );
        if let Some(e) = invariant_error {
            return Err(ppx_error_to_anyhow(e, parser.arena(), source, filename));
        }
    }
    // js_implementation.ml:36-38: the second `Ast_config.process_sig`.
    for (warning, config) in &config_processing.late_warnings {
        ppx_warnings_have_errors |= format_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            config,
            std::slice::from_ref(warning),
            out,
        );
    }
    Ok(InterfaceFrontend {
        signature,
        warnings_fatal: ppx_warnings_have_errors,
        frontend_warning_specs,
        file_config,
        experimental_let_unwrap,
    })
}

pub fn typecheck_interface_source(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> Result<()> {
    // Parse as signature
    let mut parser = Parser::new(filename, source);
    let signature = module::parse_signature(&mut parser);
    let mut frontend_output = String::new();
    let frontend = run_interface_frontend(
        &mut parser,
        signature,
        source,
        filename,
        options,
        &mut frontend_output,
    );
    if !options.frontend_already_reported {
        write_stderr(&frontend_output);
    }
    let InterfaceFrontend {
        signature,
        warnings_fatal: ppx_warnings_have_errors,
        frontend_warning_specs,
        file_config,
        experimental_let_unwrap,
    } = frontend?;
    let ppx_warnings_have_errors = if options.frontend_already_reported {
        report_stored_ast_config_warnings(
            first_config_attribute_of_signature(&signature, parser.arena()),
            false,
            parser.arena(),
            source,
            filename,
            options,
        )
    } else {
        ppx_warnings_have_errors
    };
    parser.arena_mut().reserve_typecheck_synthetic_capacity();

    // Type check
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    tctx.experimental_let_unwrap = experimental_let_unwrap;
    tctx.transparent_modules = options.transparent_modules;
    apply_warning_options(&mut tctx, options);
    // Ppx_entry.rewrite_* (ppx_entry.ml:28, 47) applies the leading warning
    // attributes; compiling a preprocessed `.ast` does not run it again.
    if !options.frontend_already_reported {
        apply_leading_warning_attribute_options(&mut tctx, &frontend_warning_specs);
    }
    apply_file_config_warning_options(&mut tctx, &file_config);
    let mut env = initial_env(&type_ctx);

    // Load Pervasives and extend the initial environment
    let mut pers_env = PersistentEnv::new();
    let (load_path, load_path_display) = shared_load_path_with_display(options);
    type_ctx.set_load_paths_shared(load_path.clone());
    pers_env.set_load_path_shared(load_path.clone(), load_path_display);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_jsx_module(options.jsx_module.clone());
    let current_unit_name = options.current_unit_name();
    pers_env.set_compiling_module(current_unit_name.clone());
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        current_unit_name.as_deref(),
    );

    tctx.set_persistent_env(pers_env);

    let typed_signature = match transl_signature(&mut tctx, &env, parser.arena(), &signature) {
        Ok(typed_signature) => typed_signature,
        Err(e) => {
            // See the implementation path above (compiler/ext/misc.ml:337-392).
            tctx.drain_open_slot_uses();
            let suppress_info_style =
                !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
            emit_type_warnings(parser.arena(), source, filename, &tctx.warnings);
            if let Some(error) = tctx
                .persistent_env
                .as_ref()
                .and_then(|persistent_env| persistent_env.last_error())
            {
                return Err(persistent_env_error_to_anyhow(error, filename));
            }
            return Err(type_mod_error_to_anyhow(
                e,
                &type_ctx,
                parser.arena(),
                source,
                filename,
                suppress_info_style,
            ));
        }
    };
    if let Some(error) = tctx
        .persistent_env
        .as_ref()
        .and_then(|persistent_env| persistent_env.last_error())
    {
        return Err(persistent_env_error_to_anyhow(error, filename));
    }
    // js_implementation.ml:62: `ignore (Includemod.signatures initial_env sg
    // sg)`, which marks the declarations of the interface used.
    let sig_type = crate::types::typemod::decl_signature_from_typed_signature(
        &typed_signature,
        parser.arena(),
    );
    let _ = crate::types::includemod::compunit(
        &type_ctx, &env, filename, &sig_type, filename, &sig_type,
    );
    // js_implementation.ml:64 `Delayed_checks.force_delayed_checks ()`.
    tctx.flush_value_usage_checks();
    emit_type_warnings(parser.arena(), source, filename, &tctx.warnings);
    if ppx_warnings_have_errors || type_warnings_have_errors(&tctx.warnings) {
        return Err(UserDiagnostic::new(String::new(), 2).into());
    }

    // Print typed tree if requested
    if options.dump_typed_sexp {
        let mut stderr = std::io::stderr();
        let _ = print_typed_signature(parser.arena(), &type_ctx, &typed_signature, &mut stderr);
    }
    if options.dump_typed_sexp_locs {
        let mut stderr = std::io::stderr();
        let _ = print_typed_signature_with_locs(
            parser.arena(),
            &type_ctx,
            &typed_signature,
            &mut stderr,
        );
    }

    Ok(())
}

/// Type-check an interface file and dump typed sexp if requested.
pub fn typecheck_interface_file(path: &std::path::Path, options: &CompilerOptions) -> Result<()> {
    let bytes =
        std::fs::read(path).with_context(|| format!("Failed to read {}", path.display()))?;
    let source = crate::source_text::latin1_bytes_to_string(bytes);
    let filename = path.to_string_lossy();
    typecheck_interface_source(&source, &filename, options)
}

/// Compile a file to JavaScript.
pub fn compile_file_to_js(path: &std::path::Path) -> Result<String> {
    compile_file_to_js_with_options(path, &CompilerOptions::default())
}

/// Compile a file to JavaScript with options.
pub fn compile_file_to_js_with_options(
    path: &std::path::Path,
    options: &CompilerOptions,
) -> Result<String> {
    // Read file as raw bytes, converting each byte to a char (Latin-1 encoding).
    // This matches OCaml's byte-level string handling where each byte is a character.
    // In Latin-1 mode, char offset == original byte offset, which is critical for
    // correct position tracking in the scanner.
    let bytes =
        std::fs::read(path).with_context(|| format!("Failed to read {}", path.display()))?;
    let source = crate::source_text::latin1_bytes_to_string(bytes);
    let filename = path.to_string_lossy();
    compile_source_to_js_with_options(&source, &filename, options)
}

// =====================================================================/// Build the load path from compiler options.
///
/// Matches OCaml's `res_compmisc.ml:init_path()`:
/// - Expands `-I` directories
/// - Appends `{runtime_path}/lib/ocaml` as the stdlib directory (unless no_stdlib)
fn build_load_path(options: &CompilerOptions) -> Vec<PathBuf> {
    build_load_path_with_display(options).0
}

/// Load path shared by modules with the same compiler options, built once
/// per worker thread. Normalizing every include path again for each
/// in-process module allocated thousands of paths per module.
fn shared_load_path_with_display(
    options: &CompilerOptions,
) -> (std::sync::Arc<Vec<PathBuf>>, std::sync::Arc<Vec<PathBuf>>) {
    type Key = (Option<PathBuf>, Vec<PathBuf>, Option<PathBuf>);
    thread_local! {
        static CACHE: std::cell::RefCell<Vec<(Key, std::sync::Arc<Vec<PathBuf>>, std::sync::Arc<Vec<PathBuf>>)>> =
            const { std::cell::RefCell::new(Vec::new()) };
    }
    let cwd = crate::process_cwd::current_dir().ok();
    CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if let Some((_, paths, display)) =
            cache.iter().find(|((runtime, includes, entry_cwd), _, _)| {
                runtime == &options.runtime_path
                    && includes == &options.include_paths
                    && entry_cwd == &cwd
            })
        {
            return (paths.clone(), display.clone());
        }
        let (paths, display) = build_load_path_with_display(options);
        let (paths, display) = (std::sync::Arc::new(paths), std::sync::Arc::new(display));
        if cache.len() >= 64 {
            cache.remove(0);
        }
        cache.push((
            (
                options.runtime_path.clone(),
                options.include_paths.clone(),
                cwd,
            ),
            paths.clone(),
            display.clone(),
        ));
        (paths, display)
    })
}

fn build_load_path_with_display(options: &CompilerOptions) -> (Vec<PathBuf>, Vec<PathBuf>) {
    let stdlib_dir = options
        .runtime_path
        .as_ref()
        .map(|runtime_path| runtime_path.join("lib").join("ocaml"));
    let cwd = crate::process_cwd::current_dir().ok();

    let mut paths = Vec::new();
    let mut display_paths = Vec::new();

    for path in &options.include_paths {
        paths.push(normalize_load_path_entry(
            path,
            stdlib_dir.as_deref(),
            cwd.as_deref(),
        ));
        display_paths.push(display_load_path_entry(
            path,
            stdlib_dir.as_deref(),
            cwd.as_deref(),
        ));
    }

    if let Some(stdlib_dir) = stdlib_dir {
        paths.push(normalize_load_path_entry(&stdlib_dir, None, cwd.as_deref()));
        display_paths.push(stdlib_dir);
    }

    (paths, display_paths)
}

fn display_load_path_entry(
    path: &FsPath,
    stdlib_dir: Option<&FsPath>,
    cwd: Option<&FsPath>,
) -> PathBuf {
    if let Some(raw) = path.to_str()
        && raw.starts_with('+')
    {
        return normalize_load_path_entry(path, stdlib_dir, cwd);
    }

    path.to_path_buf()
}

fn normalize_load_path_entry(
    path: &FsPath,
    stdlib_dir: Option<&FsPath>,
    cwd: Option<&FsPath>,
) -> PathBuf {
    if let Some(raw) = path.to_str() {
        if let Some(rest) = raw.strip_prefix('+') {
            if let Some(stdlib_dir) = stdlib_dir {
                return normalize_lexical_path(stdlib_dir.join(rest));
            }
        }
    }

    if path.is_absolute() {
        return normalize_lexical_path(path.to_path_buf());
    }

    match cwd {
        Some(cwd) => normalize_lexical_path(cwd.join(path)),
        None => normalize_lexical_path(path.to_path_buf()),
    }
}

fn normalize_lexical_path(path: PathBuf) -> PathBuf {
    let mut prefix: Option<OsString> = None;
    let mut has_root = false;
    let mut parts: Vec<OsString> = Vec::new();

    for component in path.components() {
        match component {
            Component::Prefix(value) => prefix = Some(value.as_os_str().to_os_string()),
            Component::RootDir => has_root = true,
            Component::CurDir => {}
            Component::ParentDir => match parts.last() {
                Some(last) if last != ".." => {
                    parts.pop();
                }
                _ if !has_root && prefix.is_none() => parts.push(OsString::from("..")),
                _ => {}
            },
            Component::Normal(part) => parts.push(part.to_os_string()),
        }
    }

    let mut normalized = PathBuf::new();
    if let Some(prefix) = prefix {
        normalized.push(prefix);
    }
    if has_root {
        normalized.push(std::path::MAIN_SEPARATOR.to_string());
    }
    for part in parts {
        normalized.push(part);
    }

    if normalized.as_os_str().is_empty() && !has_root {
        PathBuf::from(".")
    } else {
        normalized
    }
}

/// Load the Pervasives and Stdlib modules into the initial environment.
///
/// This is equivalent to OCaml's `res_compmisc.ml:initial_env()` which loads
/// Pervasives.cmi and Stdlib.cmi and opens them into the environment.
///
/// When `nopervasives` is true (matching OCaml's `-nopervasives` flag), the
/// implicit Pervasives and Stdlib opens are skipped. This is used by
/// `@rescript/runtime` modules which bootstrap Pervasives themselves.
///
/// When `compiling_module` is `Some(name)`, any explicit `-open` that matches
/// that module name is skipped to prevent circular self-loading (matching
/// OCaml's `res_compmisc.ml:initial_env` which filters `modulename` from
/// `open_modules`).
pub fn load_pervasives<'a>(
    pers_env: &mut PersistentEnv,
    env: &mut Env,
    ctx: &'a TypeContext,
    open_modules: &[String],
    nopervasives: bool,
    compiling_module: Option<&str>,
) {
    if !nopervasives {
        // Try to load and open Pervasives
        if pers_env.open_module("Pervasives", env, ctx) {
            env.mark_implicit_open_root("Pervasives");
            // OCaml `Res_compmisc.initial_env` opens implicit modules through
            // `type_open` (compiler/core/res_compmisc.ml:48-63). In in-process
            // and standalone builds alike, that reaches Env.open_signature at
            // compiler/ml/env.ml:1874-1877, which adds opened components but
            // not a root `Pervasives` module binding. Keep the raw signature
            // registered for ps_comps-style descriptor lookup without changing
            // source module lookup shape.
            if !pers_env.is_in_process_mode() {
                if let Some(md) = pers_env.get_module_declaration("Pervasives", ctx) {
                    if let crate::types::decl::ModuleType::MtySignature(ref sig) = md.md_type {
                        ctx.register_raw_module_sig("Pervasives", sig.clone());
                    }
                }
            }
        }

        // Try to load and open Stdlib
        if pers_env.open_module("Stdlib", env, ctx) {
            env.mark_implicit_open_root("Stdlib");
            // Same implicit-open behavior as above; keep the opened bindings,
            // but let explicit module lookup use the persistent registry.
            if !pers_env.is_in_process_mode() {
                if let Some(md) = pers_env.get_module_declaration("Stdlib", ctx) {
                    if let crate::types::decl::ModuleType::MtySignature(ref sig) = md.md_type {
                        ctx.register_raw_module_sig("Stdlib", sig.clone());
                    }
                }
            }
        }
    }

    // Apply explicit `-open` modules in argument order, skipping self-opens.
    for module_name in open_modules {
        if let Some(compiling) = compiling_module {
            if module_name == compiling {
                continue;
            }
        }
        if pers_env.open_module(module_name, env, ctx) {
            // OCaml compiler/core/res_compmisc.ml:42-66 applies command-line
            // `-open` modules through Typemod.type_open_ (typemod.ml:83-96),
            // which calls Env.open_signature (env.ml:1874-1877). That exposes
            // opened components but does not install a root module binding, so
            // later Env.normalize_path can still reach the persistent-root
            // force path through env.ml:903-914.
            if !pers_env.is_in_process_mode() {
                if let Some(md) = pers_env.get_module_declaration(module_name, ctx) {
                    if let crate::types::decl::ModuleType::MtySignature(ref sig) = md.md_type {
                        ctx.register_raw_module_sig(module_name, sig.clone());
                    }
                }
            }
        }
    }
}

use crate::types::env::Env;

/// Type-check a ReScript source file and write the typed tree as sexp to a writer.
/// This reuses the parse -> ppx -> typecheck pipeline but skips codegen.
/// For structure files (.res), writes `(structure ...)`.
/// For signature files (.resi), writes `(signature ...)`.
pub fn typecheck_and_dump_sexp<W: std::io::Write>(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    writer: &mut W,
) -> Result<()> {
    let is_interface = filename.ends_with(".resi");

    if is_interface {
        // Parse as signature
        let mut parser = Parser::new(filename, source);
        let signature = module::parse_signature(&mut parser);
        if parser.has_errors() {
            return Err(anyhow!(
                "Parse failed with {} error(s)",
                parser.diagnostics().len()
            ));
        }
        let frontend_warnings =
            ppx::collect_leading_builtin_warning_signature_attributes(&signature, parser.arena());
        let frontend_warning_specs = ppx::collect_leading_builtin_warning_signature_attribute_specs(
            &signature,
            parser.arena(),
        );
        let _ = emit_ppx_warnings(
            parser.arena(),
            source,
            filename,
            options,
            &frontend_warnings,
        );
        let config_processing = validate_file_config_from_signature(
            &signature,
            parser.arena(),
            &warning_config_for_options_and_leading_attrs(options, &frontend_warning_specs),
        );
        for (warning, config) in config_processing
            .warnings
            .iter()
            .chain(config_processing.late_warnings.iter())
        {
            let _ = emit_ppx_warnings_with_config(
                parser.arena(),
                source,
                filename,
                config,
                std::slice::from_ref(warning),
            );
        }
        if let Some(err) = config_processing.error {
            return Err(config_payload_error_to_anyhow(
                err,
                parser.arena(),
                source,
                filename,
            ));
        }
        let file_config = config_processing.overrides;
        let experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
        let signature = preprocess_signature_for_typecheck_with_source(
            signature,
            options,
            parser.arena_mut(),
            source,
            filename,
            &mut Vec::new(),
        )?;
        parser.arena_mut().reserve_typecheck_synthetic_capacity();

        // Type check
        crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
        let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
        // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
        // at module initialization, consuming stamp 1000 before any compilation.
        let _ = id_gen.next_stamp();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
        tctx.experimental_let_unwrap = experimental_let_unwrap;
        tctx.transparent_modules = options.transparent_modules;
        apply_warning_options(&mut tctx, options);
        apply_leading_warning_attribute_options(&mut tctx, &frontend_warning_specs);
        apply_file_config_warning_options(&mut tctx, &file_config);
        let mut env = initial_env(&type_ctx);

        let mut pers_env = PersistentEnv::new();
        let (load_path, load_path_display) = shared_load_path_with_display(options);
        type_ctx.set_load_paths_shared(load_path.clone());
        pers_env.set_load_path_shared(load_path, load_path_display);
        pers_env.set_open_modules(options.open_modules.clone());
        pers_env.set_jsx_version(options.jsx_version);
        pers_env.set_jsx_module(options.jsx_module.clone());
        let current_unit_name = options.current_unit_name();
        pers_env.set_compiling_module(current_unit_name.clone());
        load_pervasives(
            &mut pers_env,
            &mut env,
            &type_ctx,
            &options.open_modules,
            options.nopervasives,
            current_unit_name.as_deref(),
        );
        tctx.set_persistent_env(pers_env);

        let typed_signature = transl_signature(&mut tctx, &env, parser.arena(), &signature)
            .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

        print_typed_signature_with_locs(parser.arena(), &type_ctx, &typed_signature, writer)
            .map_err(|e| anyhow!("Failed to write sexp: {e}"))?;
    } else {
        // Parse as structure
        let mut parser = Parser::new(filename, source);
        let structure = module::parse_structure(&mut parser);
        if parser.has_errors() {
            return Err(anyhow!(
                "Parse failed with {} error(s)",
                parser.diagnostics().len()
            ));
        }
        let frontend_warning_specs =
            ppx::collect_leading_builtin_warning_attribute_specs(&structure, parser.arena());
        let file_config = extract_file_config_from_structure(&structure, parser.arena());
        let file_warning_config = warning_config_for_options_file_config_and_leading_attrs(
            options,
            &file_config,
            &frontend_warning_specs,
        );
        let experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
        if !options.no_builtin_ppx {
            reject_disabled_let_unwrap_in_structure(
                experimental_let_unwrap,
                &structure,
                parser.arena(),
                source,
                filename,
            )?;
            reject_enabled_invalid_let_unwrap_in_structure(
                experimental_let_unwrap,
                &structure,
                parser.arena(),
                source,
                filename,
            )?;
        }

        let jsx_version = options.jsx_version.or(file_config.jsx_version);
        let structure = if let Some(jsx_version) = jsx_version {
            let (structure, jsx_warnings) = jsx_ppx::transform_structure_collecting_warnings(
                structure,
                jsx_version,
                jsx_module_name(options, Some(&file_config)),
                parser.arena_mut(),
            );
            let jsx_warnings = jsx_preprocessor_warnings_to_ppx(parser.arena_mut(), jsx_warnings);
            let _ = emit_ppx_warnings_with_config(
                parser.arena(),
                source,
                filename,
                &file_warning_config,
                &jsx_warnings,
            );
            structure.map_err(|e| jsx_ppx_error_to_anyhow(e, parser.arena(), source, filename))?
        } else {
            structure
        };

        let structure = if options.no_builtin_ppx {
            structure
        } else {
            ppx::mark_config_attributes_structure(&structure, parser.arena());
            let structure = ppx::expand_extensions(&structure, parser.arena_mut())
                .map_err(|e| ppx_error_to_anyhow(e, parser.arena(), source, filename))?;
            parser
                .arena_mut()
                .set_builtin_spice(options.builtin_spice());
            let (rewritten, ppx_warnings) =
                ppx::rewrite_structure_with_warnings(&structure, parser.arena_mut());
            let _ = emit_ppx_warnings_with_config(
                parser.arena(),
                source,
                filename,
                &file_warning_config,
                &ppx_warnings,
            );
            let rewritten =
                rewritten.map_err(|e| ppx_error_to_anyhow(e, parser.arena(), source, filename))?;
            let (unused_attribute_warnings, invariant_error) =
                ppx::collect_unused_attribute_warnings_structure(&rewritten, parser.arena());
            let _ = emit_ppx_warnings_with_config(
                parser.arena(),
                source,
                filename,
                &file_warning_config,
                &unused_attribute_warnings,
            );
            if let Some(e) = invariant_error {
                return Err(ppx_error_to_anyhow(e, parser.arena(), source, filename));
            }
            rewritten
        };
        // js_implementation.ml:130 `no_export` after the frontend.
        let structure =
            crate::binary_ast::writer::apply_no_export_config(parser.arena_mut(), structure);
        parser.arena_mut().reserve_typecheck_synthetic_capacity();

        // Type check
        crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
        let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
        tctx.experimental_let_unwrap = experimental_let_unwrap;
        tctx.transparent_modules = options.transparent_modules;
        apply_warning_options(&mut tctx, options);
        apply_leading_warning_attribute_options(&mut tctx, &frontend_warning_specs);
        apply_file_config_warning_options(&mut tctx, &file_config);
        let mut env = initial_env(&type_ctx);

        let mut pers_env = PersistentEnv::new();
        let (load_path, load_path_display) = shared_load_path_with_display(options);
        type_ctx.set_load_paths_shared(load_path.clone());
        pers_env.set_load_path_shared(load_path, load_path_display);
        pers_env.set_open_modules(options.open_modules.clone());
        pers_env.set_jsx_version(options.jsx_version);
        pers_env.set_jsx_module(options.jsx_module.clone());
        let current_unit_name = options.current_unit_name();
        pers_env.set_compiling_module(current_unit_name.clone());
        load_pervasives(
            &mut pers_env,
            &mut env,
            &type_ctx,
            &options.open_modules,
            options.nopervasives,
            current_unit_name.as_deref(),
        );
        tctx.set_persistent_env(pers_env);

        let (typed_structure, _final_env) =
            type_structure(&mut tctx, &env, parser.arena(), &structure)
                .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

        apply_moregen_constraints(&mut tctx, &type_ctx, &typed_structure, options, None);

        print_typed_structure_with_locs(parser.arena(), &type_ctx, &typed_structure, writer)
            .map_err(|e| anyhow!("Failed to write sexp: {e}"))?;
    }

    Ok(())
}

struct MoregenDebugLog {
    lines: Option<Vec<String>>,
}

macro_rules! moregen_debug {
    ($debug:expr, $($arg:tt)*) => {
        if $debug.enabled() {
            $debug.push(format!($($arg)*));
        }
    };
}

impl MoregenDebugLog {
    fn from_env() -> Self {
        let lines = std::env::var_os("RUST_DEBUG_MOREGEN").map(|_| Vec::new());
        Self { lines }
    }

    fn enabled(&self) -> bool {
        self.lines.is_some()
    }

    fn push(&mut self, line: String) {
        if let Some(lines) = self.lines.as_mut() {
            lines.push(line);
        }
    }

    fn write(&self, module_name: &str) {
        let Some(lines) = self.lines.as_ref() else {
            return;
        };
        if lines.is_empty() {
            return;
        }
        let debug_file = std::env::temp_dir().join(format!("moregen_debug_{}.txt", module_name));
        let Ok(mut file) = std::fs::File::create(debug_file) else {
            return;
        };
        use std::io::Write;
        for line in lines {
            let _ = writeln!(file, "{}", line);
        }
    }
}

/// Apply moregen-like interface constraints: link non-generic Tvars in the
/// implementation to corresponding types from the .resi interface.
///
/// This matches OCaml's Includemod.compunit -> moregeneral -> moregen mechanism.
/// OCaml runs this after type_structure but before sexp serialization. The key
/// insight is that value-restricted expressions (like `basicComponent("interop")`)
/// produce non-generic Tvars that `instance()` returns by identity. When moregen
/// links these shared Tvars to interface types, ALL references update.
fn apply_moregen_constraints(
    tctx: &mut TypeCheckContext<'_>,
    type_ctx: &TypeContext,
    typed_structure: &crate::types::typedtree::Structure,
    options: &CompilerOptions,
    known_has_interface: Option<bool>,
) {
    use crate::types::decl::SignatureItem;
    use crate::types::type_expr::TypeExprRef;

    let source_file = match &options.source_filename {
        Some(f) => f,
        None => return,
    };

    // Only apply when a .resi file exists
    if !source_file.ends_with(".res") {
        return;
    }
    let has_resi = known_has_interface.unwrap_or_else(|| {
        let resi_file = format!("{}i", source_file);
        std::path::Path::new(&resi_file).exists()
    });
    if !has_resi {
        return;
    }

    // Extract module name from source filename
    let module_name = module_name_from_source_filename(source_file);
    if module_name.is_empty() {
        return;
    }

    // Load the RAW interface signature from CMI (without path substitution).
    // OCaml's ps_sig retains raw Pident paths; path substitution happens lazily
    // in components_of_module_maker, not on the sig used for moregen.
    // Using raw paths ensures moregen_link propagates Pident (local) paths
    // instead of Pdot (module-qualified) paths to the implementation.
    let iface_sig = {
        let pers = match &mut tctx.persistent_env {
            Some(p) => p,
            None => return,
        };
        // Temporarily add source dir to load path
        let source_dir = std::path::Path::new(source_file)
            .parent()
            .map(|d| d.to_path_buf())
            .unwrap_or_else(|| PathBuf::from("."));
        let already_in_path = pers.load_path_contains(&source_dir);
        if !already_in_path {
            pers.add_load_path(source_dir.clone());
        }
        // Ensure the module is loaded first (for side effects like registering types)
        let _ = pers.find_pers_struct(&module_name, type_ctx);
        // Then read raw sig without path substitution for moregen
        let result = pers.read_raw_sig_shared(&module_name, type_ctx);
        match result {
            Some(sig) => sig,
            None => return,
        }
    };

    // Rewrite CMI interface type paths to use implementation idents.
    // OCaml does this in Includemod.signatures → pair_components which builds
    // a Subst mapping id2→Pident(id1) for each paired Sig_type/Sig_module, then
    // applies it via Subst.type_expr during type comparisons.
    // We apply the same remapping up front: for each type in the interface sig,
    // find the corresponding implementation type by name and remap the CMI
    // stamp to the implementation's Pident path in all type_exprs.
    {
        let impl_sig = &typed_structure.str_type;
        let mut stamp_remap: ahash::AHashMap<i32, crate::types::Path> = ahash::AHashMap::new();
        // Match OCaml pair_components: remap Sig_type, Sig_module, Sig_modtype
        for iface_item in iface_sig.iter() {
            let (iface_id, find_fn): (
                &crate::ident::Ident,
                Box<dyn Fn(&SignatureItem) -> Option<&crate::ident::Ident>>,
            ) = match iface_item {
                SignatureItem::SigType(id, _, _) => (
                    id,
                    Box::new(|i| match i {
                        SignatureItem::SigType(impl_id, _, _) => Some(impl_id),
                        _ => None,
                    }),
                ),
                SignatureItem::SigModule(id, _, _) => (
                    id,
                    Box::new(|i| match i {
                        SignatureItem::SigModule(impl_id, _, _) => Some(impl_id),
                        _ => None,
                    }),
                ),
                SignatureItem::SigModtype(id, _) => (
                    id,
                    Box::new(|i| match i {
                        SignatureItem::SigModtype(impl_id, _) => Some(impl_id),
                        _ => None,
                    }),
                ),
                _ => continue,
            };
            if let Some(impl_id) = impl_sig.iter().find_map(|i| {
                let candidate = find_fn(i)?;
                (candidate.name() == iface_id.name()).then_some(candidate)
            }) {
                if iface_id.stamp() != 0
                    && impl_id.stamp() != 0
                    && iface_id.stamp() != impl_id.stamp()
                {
                    stamp_remap.insert(
                        iface_id.stamp(),
                        crate::types::Path::pident(impl_id.clone()),
                    );
                }
            }
        }
        if !stamp_remap.is_empty() {
            // Apply stamp remapping to interface type_exprs
            crate::cmi::persistent_env::substitute_type_paths_in_sig_with_stamp_map(
                iface_sig.as_ref(),
                &stamp_remap,
                type_ctx,
            );
        }
    }

    // Build a map from value name -> interface type
    let mut iface_val_types: ahash::AHashMap<String, TypeExprRef> = ahash::AHashMap::new();
    for item in iface_sig.iter() {
        if let SignatureItem::SigValue(id, vd) = item {
            iface_val_types.insert(id.name().to_string(), vd.val_type);
        }
    }

    // Walk top-level implementation structure items and match with interface.
    // Also recurse into modules to find inner non-generic Tvars.
    let mut debug = MoregenDebugLog::from_env();

    // Debug: dump all top-level binding names and types
    if debug.enabled() {
        moregen_debug!(
            debug,
            "TOTAL TOP-LEVEL ITEMS: {}",
            typed_structure.str_items.len()
        );
        for item in &typed_structure.str_items {
            match &item.str_desc {
                crate::types::typedtree::StructureItemDesc::Tstr_value(_, bindings) => {
                    for binding in bindings {
                        let name = extract_pat_name(&binding.vb_pat);
                        moregen_debug!(debug, "TOP-LEVEL VALUE: {:?}", name);
                        if name.as_deref() == Some("wrapJsForReason") {
                            moregen_debug!(
                                debug,
                                "=== wrapJsForReason pat_type={:?} level={}",
                                binding.vb_pat.pat_type,
                                type_ctx.get_level(type_ctx.repr(binding.vb_pat.pat_type))
                            );
                            dump_all_tvars(
                                type_ctx,
                                binding.vb_pat.pat_type,
                                &mut debug,
                                &mut ahash::AHashSet::new(),
                                0,
                            );
                        }
                    }
                }
                crate::types::typedtree::StructureItemDesc::Tstr_module(mb) => {
                    moregen_debug!(debug, "TOP-LEVEL MODULE: {}", mb.mb_name.txt);
                }
                _ => {
                    moregen_debug!(debug, "TOP-LEVEL OTHER");
                }
            }
        }
    }

    moregen_link_structure(type_ctx, typed_structure, &iface_val_types, &mut debug);
    debug.write(&module_name);
}

fn moregen_link_structure(
    type_ctx: &TypeContext,
    structure: &crate::types::typedtree::Structure,
    iface_val_types: &ahash::AHashMap<String, crate::types::type_expr::TypeExprRef>,
    debug: &mut MoregenDebugLog,
) {
    for item in &structure.str_items {
        match &item.str_desc {
            crate::types::typedtree::StructureItemDesc::Tstr_value(_, bindings) => {
                for binding in bindings {
                    let name = extract_pat_name(&binding.vb_pat);
                    if let Some(ref name) = name {
                        if let Some(&iface_ty) = iface_val_types.get(name) {
                            moregen_debug!(
                                debug,
                                "moregen_link: {} impl={:?} iface={:?}",
                                name,
                                binding.vb_pat.pat_type,
                                iface_ty
                            );
                            let iface_inst = crate::types::ctype::instance(type_ctx, iface_ty);
                            moregen_link(
                                type_ctx,
                                binding.vb_pat.pat_type,
                                iface_inst,
                                &mut ahash::AHashSet::new(),
                                debug,
                            );
                            if let crate::types::typedtree::ExpressionDesc::Texp_ident(_, _, desc) =
                                &binding.vb_expr.exp_desc
                            {
                                moregen_debug!(
                                    debug,
                                    "moregen_link_alias: {} aliased={:?} iface={:?}",
                                    name,
                                    desc.val_type,
                                    iface_ty
                                );
                                let iface_inst = crate::types::ctype::instance(type_ctx, iface_ty);
                                moregen_link_exported_alias(
                                    type_ctx,
                                    desc.val_type,
                                    iface_inst,
                                    &mut ahash::AHashSet::new(),
                                    debug,
                                );
                                moregen_link_exported_alias(
                                    type_ctx,
                                    binding.vb_pat.pat_type,
                                    desc.val_type,
                                    &mut ahash::AHashSet::new(),
                                    debug,
                                );
                                moregen_link_exported_alias(
                                    type_ctx,
                                    binding.vb_expr.exp_type,
                                    desc.val_type,
                                    &mut ahash::AHashSet::new(),
                                    debug,
                                );
                            }
                        } else {
                            moregen_debug!(debug, "no iface match: {}", name);
                        }
                    }
                }
            }
            crate::types::typedtree::StructureItemDesc::Tstr_module(mb) => {
                moregen_link_mod_expr(type_ctx, &mb.mb_expr, iface_val_types, debug);
            }
            _ => {}
        }
    }
}

fn moregen_link_mod_expr(
    type_ctx: &TypeContext,
    mod_expr: &crate::types::typedtree::ModuleExpr,
    iface_val_types: &ahash::AHashMap<String, crate::types::type_expr::TypeExprRef>,
    debug: &mut MoregenDebugLog,
) {
    match &mod_expr.mod_desc {
        crate::types::typedtree::ModuleExprDesc::Tmod_structure(s) => {
            moregen_link_structure(type_ctx, s, iface_val_types, debug);
        }
        crate::types::typedtree::ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
            moregen_link_mod_expr(type_ctx, inner, iface_val_types, debug);
        }
        _ => {}
    }
}

fn dump_all_tvars(
    ctx: &TypeContext,
    ty: crate::types::type_expr::TypeExprRef,
    debug: &mut MoregenDebugLog,
    seen: &mut ahash::AHashSet<crate::types::type_expr::TypeExprRef>,
    depth: usize,
) {
    use crate::types::type_expr::{GENERIC_LEVEL, TypeDesc};
    let ty = ctx.repr(ty);
    if !seen.insert(ty) {
        return;
    }
    let level = ctx.get_level(ty);
    let desc = ctx.get_desc(ty);
    let indent = "  ".repeat(depth);
    match &*desc {
        TypeDesc::Tvar(name) => {
            let generic_str = if level == GENERIC_LEVEL {
                "GENERIC"
            } else {
                "NON-GENERIC"
            };
            moregen_debug!(
                debug,
                "{}Tvar({:?}) {:?} {} level={}",
                indent,
                name,
                ty,
                generic_str,
                level
            );
        }
        TypeDesc::Tconstr { path, args, .. } => {
            moregen_debug!(
                debug,
                "{}Tconstr({:?}) {:?} level={} args={}",
                indent,
                path,
                ty,
                level,
                args.len()
            );
            let args = args.clone();
            drop(desc);
            for arg in &args {
                dump_all_tvars(ctx, *arg, debug, seen, depth + 1);
            }
            return;
        }
        TypeDesc::Tarrow { args, ret } => {
            let (args, ret) = (args.clone(), *ret);
            drop(desc);
            for arg in args {
                dump_all_tvars(ctx, arg.typ, debug, seen, depth + 1);
            }
            dump_all_tvars(ctx, ret, debug, seen, depth + 1);
            return;
        }
        _ => {}
    }
    drop(desc);
}

fn extract_pat_name(pat: &crate::types::typedtree::Pattern) -> Option<String> {
    match &pat.pat_desc {
        crate::types::typedtree::PatternDesc::Tpat_var(id, _) => Some(id.name().to_string()),
        crate::types::typedtree::PatternDesc::Tpat_alias(_, id, _) => Some(id.name().to_string()),
        _ => None,
    }
}

/// Check if two paths are compatible for moregen linking.
/// OCaml's moregen uses path equality because both impl and iface have
/// the same qualified paths (due to Subst.type_declaration). In Rust,
/// impl has local Pident while iface has qualified Pdot, so we compare
/// the leaf name instead.
fn moregen_paths_compatible(p1: &crate::types::Path, p2: &crate::types::Path) -> bool {
    use crate::types::Path;
    if p1.same(p2) {
        return true;
    }
    let leaf1 = match p1 {
        Path::Pident(id) => id.name(),
        Path::Pdot(_, name, _) => name.as_str(),
        _ => return false,
    };
    let leaf2 = match p2 {
        Path::Pident(id) => id.name(),
        Path::Pdot(_, name, _) => name.as_str(),
        _ => return false,
    };
    leaf1 == leaf2
}

/// Walk two types structurally and link non-generic Tvars in the impl
/// to the corresponding interface types. Matches OCaml's moregen.
fn moregen_link(
    ctx: &TypeContext,
    impl_ty: crate::types::type_expr::TypeExprRef,
    iface_ty: crate::types::type_expr::TypeExprRef,
    visited: &mut ahash::AHashSet<(
        crate::types::type_expr::TypeExprRef,
        crate::types::type_expr::TypeExprRef,
    )>,
    debug: &mut MoregenDebugLog,
) {
    moregen_link_impl(ctx, impl_ty, iface_ty, visited, debug, false);
}

fn moregen_link_exported_alias(
    ctx: &TypeContext,
    impl_ty: crate::types::type_expr::TypeExprRef,
    iface_ty: crate::types::type_expr::TypeExprRef,
    visited: &mut ahash::AHashSet<(
        crate::types::type_expr::TypeExprRef,
        crate::types::type_expr::TypeExprRef,
    )>,
    debug: &mut MoregenDebugLog,
) {
    // OCaml Ctype.moregeneral instantiates generic variables on copies before
    // comparison (compiler/ml/ctype.ml:3124-3139). Only non-generic variables
    // are shared with the original typedtree and can be linked by inclusion.
    moregen_link_impl(ctx, impl_ty, iface_ty, visited, debug, false);
}

fn moregen_link_impl(
    ctx: &TypeContext,
    impl_ty: crate::types::type_expr::TypeExprRef,
    iface_ty: crate::types::type_expr::TypeExprRef,
    visited: &mut ahash::AHashSet<(
        crate::types::type_expr::TypeExprRef,
        crate::types::type_expr::TypeExprRef,
    )>,
    debug: &mut MoregenDebugLog,
    allow_generic_anonymous: bool,
) {
    use crate::types::type_expr::{GENERIC_LEVEL, TypeDesc};

    let impl_ty = ctx.repr(impl_ty);
    let iface_ty = ctx.repr(iface_ty);
    if impl_ty == iface_ty {
        return;
    }
    if !visited.insert((impl_ty, iface_ty)) {
        return;
    }

    let impl_desc = ctx.get_desc(impl_ty);
    let iface_desc = ctx.get_desc(iface_ty);

    match (&*impl_desc, &*iface_desc) {
        (TypeDesc::Tvar(name), _) if ctx.get_level(impl_ty) != GENERIC_LEVEL => {
            // Non-generic impl Tvar: link to interface type
            if debug.enabled() {
                let iface_summary = match &*iface_desc {
                    TypeDesc::Tvar(n) => format!("Tvar({:?})", n),
                    TypeDesc::Tconstr { path, .. } => format!("Tconstr({:?})", path),
                    _ => "other".to_string(),
                };
                moregen_debug!(
                    debug,
                    "  LINK {:?} Tvar({:?}) level={} -> {}",
                    impl_ty,
                    name,
                    ctx.get_level(impl_ty),
                    iface_summary
                );
            }
            drop(impl_desc);
            drop(iface_desc);
            crate::types::ctype::link_type(ctx, impl_ty, iface_ty);
        }
        (TypeDesc::Tvar(name), _) if allow_generic_anonymous && name.is_none() => {
            if debug.enabled() {
                let iface_summary = match &*iface_desc {
                    TypeDesc::Tvar(n) => format!("Tvar({:?})", n),
                    TypeDesc::Tconstr { path, .. } => format!("Tconstr({:?})", path),
                    _ => "other".to_string(),
                };
                moregen_debug!(
                    debug,
                    "  LINK exported generic {:?} Tvar({:?}) level={} -> {}",
                    impl_ty,
                    name,
                    ctx.get_level(impl_ty),
                    iface_summary
                );
            }
            drop(impl_desc);
            drop(iface_desc);
            crate::types::ctype::link_type(ctx, impl_ty, iface_ty);
        }
        (TypeDesc::Tvar(name), _) => {
            moregen_debug!(
                debug,
                "  SKIP generic {:?} Tvar({:?}) level={}",
                impl_ty,
                name,
                ctx.get_level(impl_ty)
            );
        }
        (
            TypeDesc::Tconstr {
                path: p1, args: a1, ..
            },
            TypeDesc::Tconstr {
                path: p2, args: a2, ..
            },
        ) if moregen_paths_compatible(p1, p2) && a1.len() == a2.len() => {
            moregen_debug!(
                debug,
                "  Tconstr match: {:?} ~ {:?} args={}",
                p1,
                p2,
                a1.len()
            );
            let a1 = a1.clone();
            let a2 = a2.clone();
            drop(impl_desc);
            drop(iface_desc);
            for (a, b) in a1.iter().zip(a2.iter()) {
                moregen_link_impl(ctx, *a, *b, visited, debug, allow_generic_anonymous);
            }
        }
        (TypeDesc::Tarrow { args: a1, ret: r1 }, TypeDesc::Tarrow { args: a2, ret: r2 })
            if a1.len() == a2.len() =>
        {
            moregen_debug!(debug, "  Tarrow match");
            let (a1, a2, r1, r2) = (a1.clone(), a2.clone(), *r1, *r2);
            drop(impl_desc);
            drop(iface_desc);
            for (a1, a2) in a1.iter().zip(&a2) {
                moregen_link_impl(ctx, a1.typ, a2.typ, visited, debug, false);
            }
            moregen_link_impl(ctx, r1, r2, visited, debug, allow_generic_anonymous);
        }
        (TypeDesc::Ttuple(t1), TypeDesc::Ttuple(t2)) if t1.len() == t2.len() => {
            let t1 = t1.clone();
            let t2 = t2.clone();
            drop(impl_desc);
            drop(iface_desc);
            for (a, b) in t1.iter().zip(t2.iter()) {
                moregen_link_impl(ctx, *a, *b, visited, debug, allow_generic_anonymous);
            }
        }
        (
            TypeDesc::Tconstr {
                path: p1, args: a1, ..
            },
            TypeDesc::Tconstr {
                path: p2, args: a2, ..
            },
        ) => {
            moregen_debug!(
                debug,
                "  Tconstr MISMATCH: impl={:?}({}) iface={:?}({})",
                p1,
                a1.len(),
                p2,
                a2.len()
            );
        }
        _ => {
            moregen_debug!(debug, "  NO match");
        }
    }
}

/// Per-file configuration overrides extracted from `@@config({flags: [...]})`.
#[derive(Debug, Default, Clone)]
pub struct FileConfigOverrides {
    pub let_unwrap: bool,
    pub jsx_version: Option<i32>,
    /// `-bs-jsx-module`.
    pub jsx_module: Option<String>,
    /// `-w`/`-warn-error` specs in application order (`true` = `-warn-error`).
    pub warning_ops: Vec<(bool, String)>,
}

#[derive(Clone, Copy)]
enum BscFlagArity {
    Unit,
    String,
}

/// The arity of a `command_line_flags` entry
/// (compiler/bsc/rescript_compiler_main.ml:233-499), or `None` for an
/// unknown option.
fn bsc_flag_arity(flag: &str) -> Option<BscFlagArity> {
    Some(match flag {
        "-I"
        | "-w"
        | "-o"
        | "-ppx"
        | "-open"
        | "-bs-jsx"
        | "-bs-jsx-module"
        | "-bs-jsx-mode"
        | "-bs-source-map"
        | "-bs-source-map-sources-content"
        | "-bs-source-map-root"
        | "-bs-package-output"
        | "-bs-project-root"
        | "-bs-package-name"
        | "-bs-ns"
        | "-bs-gentype-module"
        | "-bs-gentype-module-resolution"
        | "-bs-gentype-generated-extension"
        | "-bs-gentype-suffix"
        | "-bs-gentype-shim"
        | "-bs-gentype-debug"
        | "-bs-gentype-dep"
        | "-bs-gentype-source-dir"
        | "-bs-gentype-dep-path"
        | "-bs-gentype-bsb-project-root"
        | "-color"
        | "-e"
        | "-reprint-source"
        | "-format"
        | "-pp"
        | "-enable-experimental"
        | "-runtime-path"
        | "-warn-error" => BscFlagArity::String,
        "-bs-read-cmi"
        | "-bs-jsx-preserve"
        | "-bs-ast"
        | "-bs-test-ast-conversion"
        | "-bs-syntax-only"
        | "-bs-g"
        | "-as-pp"
        | "-no-alias-deps"
        | "-bs-gentype"
        | "-bs-gentype-export-interfaces"
        | "-nostdlib"
        | "-bs-cmi-only"
        | "-bs-cmi"
        | "-bs-cmj"
        | "-bs-no-version-header"
        | "-bs-no-builtin-ppx"
        | "-bs-cross-module-opt"
        | "-bs-no-cross-module-opt"
        | "-debug-ir"
        | "-check-lam"
        | "-bs-no-check-div-by-zero"
        | "-bs-noassertfalse"
        | "-noassert"
        | "-bs-loc"
        | "-dtypedtree"
        | "-dtyped-sexp"
        | "-dtyped-sexp-locs"
        | "-dparsetree"
        | "-dparsetree-sexp-locs"
        | "-drawlambda"
        | "-dlambda-sexp"
        | "-dlambda-sexp-locs"
        | "-dsource"
        | "-only-parse"
        | "-editor-mode"
        | "-ignore-parse-errors"
        | "-verbose"
        | "-keep-locs"
        | "-no-keep-locs"
        | "-nopervasives"
        | "-v"
        | "-version"
        | "-absname"
        | "-bs-no-bin-annot"
        | "-short-paths"
        | "-unsafe"
        | "-warn-help"
        | "-make-runtime" => BscFlagArity::Unit,
        _ => return None,
    })
}

/// `file_level_flags_handler` on a string array: `Bsc_args.parse_exn`
/// (compiler/ext/bsc_args.ml) applying each option in order. Returns `false`
/// when parsing raises, after the options before the failure were applied.
fn run_file_level_flags(
    flags: &[String],
    overrides: &mut FileConfigOverrides,
    state: &mut WarningConfig,
) -> bool {
    let mut i = 0;
    while i < flags.len() {
        let flag = flags[i].as_str();
        i += 1;
        // Anything not starting with `-` is an anonymous argument.
        if !flag.starts_with('-') {
            continue;
        }
        let Some(arity) = bsc_flag_arity(flag) else {
            return false;
        };
        let BscFlagArity::String = arity else {
            continue;
        };
        let Some(arg) = flags.get(i) else {
            return false;
        };
        i += 1;
        match flag {
            // `Warnings.parse_options` commits only a well-formed list
            // (compiler/ext/warnings.ml:250-254).
            "-w" | "-warn-error" => {
                let as_error = flag == "-warn-error";
                let mut next = state.clone();
                let parsed = if as_error {
                    next.parse_as_error(arg)
                } else {
                    next.parse(arg)
                };
                if parsed.is_err() {
                    return false;
                }
                *state = next;
                overrides.warning_ops.push((as_error, arg.clone()));
            }
            "-bs-jsx" => {
                if arg != "4" {
                    return false;
                }
                overrides.jsx_version = Some(4);
            }
            "-bs-jsx-module" => {
                apply_jsx_module_flag(arg, &mut overrides.jsx_module, &mut overrides.jsx_version);
            }
            "-enable-experimental" => {
                if arg == "LetUnwrap" {
                    overrides.let_unwrap = true;
                }
            }
            "-bs-source-map" => {
                if !matches!(
                    arg.to_ascii_lowercase().as_str(),
                    "linked" | "inline" | "hidden" | "false" | "none"
                ) {
                    return false;
                }
            }
            "-bs-source-map-sources-content" => {
                if !matches!(arg.to_ascii_lowercase().as_str(), "true" | "false") {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

fn extract_single_string_payload(
    payload: &Payload,
    arena: &crate::parse_arena::ParseArena,
) -> Option<String> {
    crate::ast_payload::semantic_string_of_payload(arena, payload)
        .ok()
        .flatten()
}

fn extract_file_directives_from_structure(
    structure: &Structure,
    arena: &crate::parse_arena::ParseArena,
) -> std::result::Result<Vec<String>, DirectivePayloadError> {
    let mut directives = Vec::new();

    for item in structure {
        let StructureItemDesc::Pstr_attribute(attr) = &*item.pstr_desc else {
            continue;
        };
        if arena.get_string(attr.0.txt) != "directive" {
            continue;
        }
        // ast_config.ml process_directives: reject a json payload, then read
        // the payload's semantic string.
        if let Err(err) = crate::ast_payload::reject_json_literal_payload(arena, &attr.1) {
            return Err(DirectivePayloadError {
                loc: err.loc,
                message: err.message,
            });
        }
        let Some(directive) = extract_single_string_payload(&attr.1, arena) else {
            return Err(DirectivePayloadError {
                loc: item.pstr_loc,
                message: "Expected a string literal.",
            });
        };
        directives.push(directive);
    }

    Ok(directives)
}

#[derive(Debug, Clone, Copy)]
struct DirectivePayloadError {
    loc: LocIdx,
    message: &'static str,
}

#[derive(Debug, Clone)]
struct ConfigPayloadError {
    loc: LocIdx,
    message: String,
}

impl std::fmt::Display for DirectivePayloadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.message)
    }
}

impl std::error::Error for DirectivePayloadError {}

impl std::fmt::Display for ConfigPayloadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ConfigPayloadError {}

fn config_payload_error_to_anyhow(
    err: ConfigPayloadError,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    UserDiagnostic::new(
        format_compiler_error_report(arena, source, filename, err.loc, &err.message),
        2,
    )
    .into()
}

#[derive(Debug, Clone, Copy)]
struct ConfigAction {
    name: StrIdx,
    loc: LocIdx,
    expr: Option<ExprIdx>,
}

fn push_config_warning(
    warnings: &mut Vec<ppx::PpxWarning>,
    loc: LocIdx,
    warning: crate::diagnostics::Warning,
) {
    warnings.push(ppx::PpxWarning { loc, warning });
}

fn push_invalid_config_record_warning(warnings: &mut Vec<ppx::PpxWarning>, loc: LocIdx) {
    push_config_warning(
        warnings,
        loc,
        crate::diagnostics::Warning::BsDeriveWarning {
            message: "invalid attribute config-record, ignoring".to_string(),
        },
    );
}

fn config_payload_actions(
    payload: &Payload,
    default_loc: LocIdx,
    arena: &ParseArena,
    warnings: &mut Vec<ppx::PpxWarning>,
) -> Result<Vec<ConfigAction>, ConfigPayloadError> {
    let Payload::PStr(items) = payload else {
        push_invalid_config_record_warning(warnings, default_loc);
        return Ok(Vec::new());
    };
    if items.is_empty() {
        return Ok(Vec::new());
    }
    if items.len() != 1 {
        push_invalid_config_record_warning(warnings, default_loc);
        return Ok(Vec::new());
    }
    let StructureItemDesc::Pstr_eval(inner) = &*items[0].pstr_desc else {
        push_invalid_config_record_warning(warnings, default_loc);
        return Ok(Vec::new());
    };
    let (expr_idx, _) = &**inner;
    let expr = arena.get_expr(*expr_idx);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, with_obj) = &**inner;
            if with_obj.is_some() {
                push_config_warning(
                    warnings,
                    expr.pexp_loc,
                    crate::diagnostics::Warning::BsDeriveWarning {
                        message: "`with` is not supported, discarding".to_string(),
                    },
                );
                return Ok(Vec::new());
            }
            let mut actions = Vec::with_capacity(fields.len());
            for field in fields {
                let Longident::Lident(name_idx) = arena.get_longident(field.lid.txt) else {
                    return Err(ConfigPayloadError {
                        loc: default_loc,
                        message: "Qualified label is not allowed".to_string(),
                    });
                };
                let field_expr = arena.get_expr(field.expr);
                let punned = match &*field_expr.pexp_desc {
                    // OCaml compiler/ml/ast_payload.ml:206-214 compares the
                    // label and identifier names, so separately interned Rust
                    // StrIdx values for `no_export: no_export` must still
                    // count as the punned `None` payload.
                    ExpressionDesc::Pexp_ident(lid) => matches!(
                        arena.get_longident(lid.txt),
                        Longident::Lident(value_idx) if value_idx == name_idx
                            || arena.get_string(*value_idx) == arena.get_string(*name_idx)
                    ),
                    _ => false,
                };
                actions.push(ConfigAction {
                    name: *name_idx,
                    loc: field.lid.loc,
                    expr: if punned { None } else { Some(field.expr) },
                });
            }
            Ok(actions)
        }
        ExpressionDesc::Pexp_ident(lid) => {
            let Longident::Lident(name_idx) = arena.get_longident(lid.txt) else {
                push_invalid_config_record_warning(warnings, default_loc);
                return Ok(Vec::new());
            };
            Ok(vec![ConfigAction {
                name: *name_idx,
                loc: lid.loc,
                expr: None,
            }])
        }
        _ => {
            push_invalid_config_record_warning(warnings, default_loc);
            Ok(Vec::new())
        }
    }
}

fn validate_config_bool_literal(
    expr_idx: ExprIdx,
    arena: &ParseArena,
) -> Result<(), ConfigPayloadError> {
    let expr = arena.get_expr(expr_idx);
    let is_bool_literal = match &*expr.pexp_desc {
        ExpressionDesc::Pexp_construct(lid, args) if args.txt.is_empty() => matches!(
            arena.get_longident(lid.txt),
            Longident::Lident(name_idx)
                if matches!(arena.get_string(*name_idx), "true" | "false")
        ),
        _ => false,
    };
    if is_bool_literal {
        Ok(())
    } else {
        Err(ConfigPayloadError {
            loc: expr.pexp_loc,
            message: "expect `true` or `false` in this field".to_string(),
        })
    }
}

/// Compiling a stored `.ast`/`.iast`: `Js_implementation.after_parsing_impl`
/// (and `interface_mliast`) run `Ast_config.process_str`/`process_sig` once
/// more under the command-line warning state
/// (compiler/core/js_implementation.ml:38, 129). Returns whether a reported
/// warning is an error.
fn report_stored_ast_config_warnings(
    attr: Option<&crate::parser::ast::Attribute>,
    allow_no_export: bool,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> bool {
    let processing = process_file_config(
        attr,
        allow_no_export,
        arena,
        &warning_config_for_options(options),
        1,
    );
    let mut out = String::new();
    let mut has_error = false;
    for (warning, config) in &processing.warnings {
        has_error |= format_ppx_warnings_with_config(
            arena,
            source,
            filename,
            config,
            std::slice::from_ref(warning),
            &mut out,
        );
    }
    write_stderr(&out);
    has_error
}

/// The string array of a `flags` field, or the error
/// `file_level_flags_handler` raises before parsing
/// (compiler/bsc/rescript_compiler_main.ml:502-514).
fn config_flags_strings(
    expr_idx: Option<ExprIdx>,
    arena: &ParseArena,
) -> Result<Option<(Vec<String>, LocIdx)>, ConfigPayloadError> {
    let Some(expr_idx) = expr_idx else {
        return Ok(None);
    };
    let expr = arena.get_expr(expr_idx);
    let ExpressionDesc::Pexp_array(elements) = &*expr.pexp_desc else {
        return Err(ConfigPayloadError {
            loc: expr.pexp_loc,
            message: "string array expected".to_string(),
        });
    };
    let mut flags = Vec::with_capacity(elements.len());
    for elem_idx in elements.iter() {
        let elem = arena.get_expr(*elem_idx);
        // rescript_compiler_main.ml file_level_flags_handler:
        // `Ast_payload.semantic_string_of_expression`.
        let value = match crate::ast_payload::semantic_string_of_expression(arena, elem) {
            Ok(value) => value,
            Err(err) => {
                return Err(ConfigPayloadError {
                    loc: err.loc,
                    message: err.message.to_string(),
                });
            }
        };
        let Some(value) = value else {
            return Err(ConfigPayloadError {
                loc: elem.pexp_loc,
                message: "string literal expected".to_string(),
            });
        };
        flags.push(value);
    }
    Ok(Some((flags, expr.pexp_loc)))
}

/// `Ast_config.process_str`/`process_sig` (compiler/frontend/ast_config.ml),
/// run `runs` times like the direct bsc path (Ppx_entry, then
/// Js_implementation.after_parsing_impl).
#[derive(Default)]
struct FileConfigProcessing {
    overrides: FileConfigOverrides,
    /// Warnings together with the warning state they were emitted under.
    warnings: Vec<(ppx::PpxWarning, WarningConfig)>,
    /// The warnings of the second `Ast_config.process_str`, which
    /// `Js_implementation.after_parsing_impl` runs after the builtin ppx
    /// (js_implementation.ml:125-129).
    late_warnings: Vec<(ppx::PpxWarning, WarningConfig)>,
    error: Option<ConfigPayloadError>,
}

fn process_file_config(
    attr: Option<&crate::parser::ast::Attribute>,
    allow_no_export: bool,
    arena: &ParseArena,
    base: &WarningConfig,
    runs: usize,
) -> FileConfigProcessing {
    let mut result = FileConfigProcessing::default();
    let Some(attr) = attr else {
        return result;
    };
    let mut state = base.clone();
    for run in 0..runs {
        let mut run_warnings: Vec<(ppx::PpxWarning, WarningConfig)> = Vec::new();
        let mut overrides = FileConfigOverrides::default();
        let mut payload_warnings = Vec::new();
        let actions = config_payload_actions(&attr.1, attr.0.loc, arena, &mut payload_warnings);
        for warning in payload_warnings {
            run_warnings.push((warning, state.clone()));
        }
        let actions = match actions {
            Ok(actions) => actions,
            Err(err) => {
                push_config_run_warnings(&mut result, run, run_warnings);
                result.error = Some(err);
                return result;
            }
        };
        // `Ast_payload.table_dispatch` (compiler/ml/ast_payload.ml).
        for action in actions {
            let outcome = match arena.get_string(action.name) {
                "no_export" if allow_no_export => match action.expr {
                    Some(expr_idx) => validate_config_bool_literal(expr_idx, arena),
                    None => Ok(()),
                },
                "flags" => match config_flags_strings(action.expr, arena) {
                    Ok(Some((flags, loc))) => {
                        if !run_file_level_flags(&flags, &mut overrides, &mut state) {
                            run_warnings.push((
                                ppx::PpxWarning {
                                    loc,
                                    warning: crate::diagnostics::Warning::Preprocessor {
                                        message: "invalid flags for bsc".to_string(),
                                    },
                                },
                                state.clone(),
                            ));
                        }
                        Ok(())
                    }
                    Ok(None) => Ok(()),
                    Err(err) => Err(err),
                },
                name => Err(ConfigPayloadError {
                    loc: action.loc,
                    message: format!("{name} is not supported"),
                }),
            };
            if let Err(err) = outcome {
                push_config_run_warnings(&mut result, run, run_warnings);
                result.overrides = overrides;
                result.error = Some(err);
                return result;
            }
        }
        push_config_run_warnings(&mut result, run, run_warnings);
        result.overrides = overrides;
    }
    result
}

fn push_config_run_warnings(
    result: &mut FileConfigProcessing,
    run: usize,
    warnings: Vec<(ppx::PpxWarning, WarningConfig)>,
) {
    if run == 0 {
        result.warnings.extend(warnings);
    } else {
        result.late_warnings.extend(warnings);
    }
}

/// `iter_on_config_str`: only the first `@@config` among the leading
/// attributes is processed (compiler/frontend/ast_config.ml:55-65).
fn first_config_attribute_of_structure<'s>(
    structure: &'s Structure,
    arena: &ParseArena,
) -> Option<&'s crate::parser::ast::Attribute> {
    for item in structure {
        let StructureItemDesc::Pstr_attribute(attr) = &*item.pstr_desc else {
            return None;
        };
        if arena.get_string(attr.0.txt) == "config" {
            return Some(attr);
        }
    }
    None
}

/// `iter_on_config_sig` (compiler/frontend/ast_config.ml:72-81).
fn first_config_attribute_of_signature<'s>(
    signature: &'s Signature,
    arena: &ParseArena,
) -> Option<&'s crate::parser::ast::Attribute> {
    for item in signature {
        let SignatureItemDesc::Psig_attribute(attr) = &*item.psig_desc else {
            return None;
        };
        if arena.get_string(attr.0.txt) == "config" {
            return Some(attr);
        }
    }
    None
}

fn validate_file_config_from_structure(
    structure: &Structure,
    arena: &ParseArena,
    base: &WarningConfig,
) -> FileConfigProcessing {
    process_file_config(
        first_config_attribute_of_structure(structure, arena),
        true,
        arena,
        base,
        2,
    )
}

fn validate_file_config_from_signature(
    signature: &Signature,
    arena: &ParseArena,
    base: &WarningConfig,
) -> FileConfigProcessing {
    process_file_config(
        first_config_attribute_of_signature(signature, arena),
        false,
        arena,
        base,
        2,
    )
}

/// Extract `@@config({flags: [...]})` overrides from a parsed structure.
pub fn extract_file_config_from_structure(
    structure: &Structure,
    arena: &crate::parse_arena::ParseArena,
) -> FileConfigOverrides {
    process_file_config(
        first_config_attribute_of_structure(structure, arena),
        true,
        arena,
        &WarningConfig::new(),
        1,
    )
    .overrides
}

/// Extract `@@config({flags: [...]})` overrides from a parsed signature.
pub fn extract_file_config_from_signature(
    signature: &Signature,
    arena: &crate::parse_arena::ParseArena,
) -> FileConfigOverrides {
    process_file_config(
        first_config_attribute_of_signature(signature, arena),
        false,
        arena,
        &WarningConfig::new(),
        1,
    )
    .overrides
}

/// Typecheck a stored structure AST (from parse phase) and dump sexp.
/// Applies remaining PPX passes (expand_extensions, rewrite_structure) before typechecking.
pub fn typecheck_stored_structure_and_dump_sexp<W: std::io::Write>(
    mut arena: crate::parse_arena::ParseArena,
    structure: Structure,
    options: &CompilerOptions,
    writer: &mut W,
) -> Result<()> {
    // Reset counter: the arena was already used during binary AST writing
    // (write_structure_ast_current_with_extra_deps → rewrite_structure), which
    // expanded %%private items and incremented local_module_counter.
    // OCaml starts fresh for each bsc invocation, so we reset to match.
    arena.reset_local_module_counter();

    let file_config = extract_file_config_from_structure(&structure, &arena);
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_attribute_specs(&structure, &arena);
    let experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;

    let jsx_version = options.jsx_version.or(file_config.jsx_version);
    let structure = if let Some(jsx_version) = jsx_version {
        jsx_ppx::transform_structure_result(
            structure,
            jsx_version,
            jsx_module_name(options, Some(&file_config)),
            &mut arena,
        )
        .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?
    } else {
        structure
    };

    let structure = if options.no_builtin_ppx {
        structure
    } else {
        let structure = ppx::expand_extensions(&structure, &mut arena)
            .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?;
        arena.set_builtin_spice(options.builtin_spice());
        ppx::rewrite_structure(&structure, &mut arena)
            .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?
    };

    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    crate::types::typecore::prepare_typecheck_arena(&mut arena);
    let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
    tctx.experimental_let_unwrap = experimental_let_unwrap;
    tctx.transparent_modules = options.transparent_modules;
    apply_warning_options(&mut tctx, options);
    // Ppx_entry.rewrite_* (ppx_entry.ml:28, 47) applies the leading warning
    // attributes; compiling a preprocessed `.ast` does not run it again.
    if !options.frontend_already_reported {
        apply_leading_warning_attribute_options(&mut tctx, &frontend_warning_specs);
    }
    apply_file_config_warning_options(&mut tctx, &file_config);
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::new();
    let (load_path, load_path_display) = shared_load_path_with_display(options);
    type_ctx.set_load_paths_shared(load_path.clone());
    pers_env.set_load_path_shared(load_path, load_path_display);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_jsx_module(options.jsx_module.clone());
    let current_unit_name = options.current_unit_name();
    pers_env.set_compiling_module(current_unit_name.clone());
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        current_unit_name.as_deref(),
    );
    tctx.set_persistent_env(pers_env);

    let (typed_structure, _final_env) = type_structure(&mut tctx, &env, &arena, &structure)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

    print_typed_structure_with_locs(&arena, &type_ctx, &typed_structure, writer)
        .map_err(|e| anyhow!("Failed to write sexp: {e}"))?;

    Ok(())
}

/// Typecheck a stored signature AST (from parse phase) and dump sexp.
pub fn typecheck_stored_signature_and_dump_sexp<W: std::io::Write>(
    mut arena: crate::parse_arena::ParseArena,
    signature: Signature,
    options: &CompilerOptions,
    writer: &mut W,
) -> Result<()> {
    let file_config = extract_file_config_from_signature(&signature, &arena);
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_signature_attribute_specs(&signature, &arena);
    let experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;

    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    crate::types::typecore::prepare_typecheck_arena(&mut arena);
    let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
    tctx.experimental_let_unwrap = experimental_let_unwrap;
    tctx.transparent_modules = options.transparent_modules;
    apply_warning_options(&mut tctx, options);
    // Ppx_entry.rewrite_* (ppx_entry.ml:28, 47) applies the leading warning
    // attributes; compiling a preprocessed `.ast` does not run it again.
    if !options.frontend_already_reported {
        apply_leading_warning_attribute_options(&mut tctx, &frontend_warning_specs);
    }
    apply_file_config_warning_options(&mut tctx, &file_config);
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::new();
    let (load_path, load_path_display) = shared_load_path_with_display(options);
    type_ctx.set_load_paths_shared(load_path.clone());
    pers_env.set_load_path_shared(load_path, load_path_display);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_jsx_module(options.jsx_module.clone());
    let current_unit_name = options.current_unit_name();
    pers_env.set_compiling_module(current_unit_name.clone());
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        current_unit_name.as_deref(),
    );
    tctx.set_persistent_env(pers_env);

    let typed_signature = transl_signature(&mut tctx, &env, &arena, &signature)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

    print_typed_signature_with_locs(&arena, &type_ctx, &typed_signature, writer)
        .map_err(|e| anyhow!("Failed to write sexp: {e}"))?;

    Ok(())
}

/// Normalize types to match OCaml's normalize_signature.
/// OCaml calls normalize_type on each Sig_value's val_type in the top-level
/// inferred signature. normalize_type is recursive (walks all children via
/// iter_type_expr), so all types reachable from a top-level val_type are normalized.
///
/// Key: OCaml's val_type comes from `enter_variable` during pattern typing, which
/// uses `build_as_type(inner)` for alias patterns. For `Tpat_alias(Tpat_any, "v")`,
/// val_type = Tpat_any's pat_type, NOT the outer pattern's pat_type. We look up
/// val_type from the env to match this behavior exactly.
/// `Typemod.normalize_signature` (compiler/ml/typemod.ml:1634-1645): run
/// `Ctype.normalize_type` over the value types of the (simplified)
/// signature, recursing into module types. typemod.ml:1765-1766 applies it to
/// `simplify_signature sg`, so shadowed items are left as typed.
pub(crate) fn normalize_signature(
    type_ctx: &TypeContext,
    env: &Env,
    sig: &[crate::types::decl::SignatureItem],
) {
    use crate::types::decl::SignatureItem;
    for item in sig {
        match item {
            SignatureItem::SigValue(_, desc) => {
                crate::types::ctype::normalize_type(type_ctx, env, desc.val_type);
            }
            SignatureItem::SigModule(_, md, _) => normalize_modtype(type_ctx, env, &md.md_type),
            _ => {}
        }
    }
}

fn normalize_modtype(type_ctx: &TypeContext, env: &Env, mty: &crate::types::decl::ModuleType) {
    use crate::types::decl::ModuleType;
    match mty {
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        ModuleType::MtySignature(sig) => normalize_signature(type_ctx, env, sig),
        ModuleType::MtyFunctor { result, .. } => normalize_modtype(type_ctx, env, result),
    }
}

fn rename_saved_module_type_idents(type_ctx: &TypeContext, mty: &crate::types::decl::ModuleType) {
    use crate::types::decl::ModuleType;

    match mty {
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        ModuleType::MtySignature(sig) => rename_saved_signature_idents(type_ctx, sig),
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            // Subst.modtype renames the functor binder before traversing its
            // argument and result module types (compiler/ml/subst.ml:345-348).
            drop(type_ctx.rename_ident(param));
            if let Some(param_type) = param_type {
                rename_saved_module_type_idents(type_ctx, param_type);
            }
            rename_saved_module_type_idents(type_ctx, result);
        }
    }
}

fn rename_saved_signature_idents(
    type_ctx: &TypeContext,
    sig: &[crate::types::decl::SignatureItem],
) {
    use crate::types::decl::SignatureItem;

    // Subst.signature first runs rename_bound_idents over the complete
    // signature, then traverses each renamed component in source order
    // (compiler/ml/subst.ml:322-354). Preserve both allocation passes even
    // though the direct Rust CMI writer does not need the copied identifiers.
    for item in sig {
        match item {
            SignatureItem::SigType(id, _, _)
            | SignatureItem::SigModule(id, _, _)
            | SignatureItem::SigModtype(id, _)
            | SignatureItem::SigValue(id, _)
            | SignatureItem::SigTypext(id, _, _) => {
                drop(type_ctx.rename_ident(id));
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }

    for item in sig {
        match item {
            SignatureItem::SigModule(_, md, _) => {
                rename_saved_module_type_idents(type_ctx, &md.md_type);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(mty) = &mtd.mtd_type {
                    rename_saved_module_type_idents(type_ctx, mty);
                }
            }
            SignatureItem::SigValue(_, _)
            | SignatureItem::SigType(_, _, _)
            | SignatureItem::SigTypext(_, _, _)
            | SignatureItem::SigClass
            | SignatureItem::SigClassType => {}
        }
    }
}

/// `Env.save_signature` (env.ml:1886-1892) writes `Subst.signature
/// (Subst.for_saving Subst.identity) sg`: a copy whose bound identifiers are
/// renamed (subst.ml:322-364), taking fresh stamps.
fn saved_signature_copy(
    type_ctx: &TypeContext,
    sig: &[crate::types::decl::SignatureItem],
) -> crate::types::decl::Signature {
    crate::cmi::persistent_env::freshened_signature_bound_idents_from_kind(
        "save_signature",
        sig,
        type_ctx,
    )
}

fn synchronize_lambda_start_stamp(type_ctx: &TypeContext) -> i32 {
    // OCaml uses a single mutable `Ident.currentstamp` across typechecking and
    // Lambda translation. Rust still has a few typedtree locals created through
    // `Ident::create_local`, so synchronize before raw-lambda creates fresh
    // identifiers. Otherwise a raw-lambda temp can reuse a typedtree stamp.
    let stamp = type_ctx
        .current_stamp()
        .max(crate::ident::Ident::current_local_stamp());
    type_ctx.set_current_time(stamp);
    crate::ident::Ident::set_current_time(stamp);
    stamp
}

/// Result of an in-process `.res` compilation.
pub struct InProcessCompileResult {
    pub js_output: String,
    pub js_outputs: Vec<JsOutput>,
    pub signature: crate::types::decl::Signature,
    pub pers_struct: Option<PortablePersStruct>,
    pub new_alias_rewrites: ahash::AHashMap<String, crate::types::path::Path>,
    pub is_pure: bool,
    pub cmj_export_constants: ahash::AHashMap<String, CmjExportConstant>,
    pub cmj_export_arities: ahash::AHashMap<String, CmjExportArity>,
    /// `.cmj` `persistent_closed_lambda` exports for cross-module inlining
    /// (lam_stats_export.ml:53-89).
    pub cmj_export_lambdas: ahash::AHashMap<String, crate::lambda::Lambda>,
    pub hoisted_exports: Vec<crate::lambda::HoistedExport>,
    /// Intermediate-representation sexps, populated when
    /// `CompilerOptions::capture_intermediates` is true (for the playground).
    pub typed_tree_sexp: String,
    pub raw_lambda_sexp: String,
    pub lambda_sexp: String,
    /// The intermediate representations requested by `CompilerOptions::dumps`.
    pub dumps: Vec<(DumpKind, String)>,
    /// The warning reports the file compile prints to stderr.
    pub warnings: String,
}

/// Owned in-process compilation state after typechecking and Lambda lowering,
/// before JS backend metadata from dependencies is required.
pub struct InProcessPreJsCompileResult {
    pub lowered_lambda: crate::lambda::Lambda,
    pub possible_required_modules: AHashSet<ModuleId>,
    pub hoisted_functions: Vec<crate::lambda::HoistedFunction>,
    pub hoisted_exports: Vec<crate::lambda::HoistedExport>,
    pub ident_stamp_at_js_boundary: i32,
    pub file_directives: Vec<String>,
    pub debug: bool,
    pub jsx_preserve: bool,
    pub signature: crate::types::decl::Signature,
    pub pers_struct: Option<PortablePersStruct>,
    pub new_alias_rewrites: ahash::AHashMap<String, crate::types::path::Path>,
    pub source_file_names: std::sync::Arc<std::collections::HashMap<crate::intern::StrIdx, String>>,
    /// Intermediate-representation sexps, populated when
    /// `CompilerOptions::capture_intermediates` is true (for the playground).
    pub typed_tree_sexp: String,
    pub raw_lambda_sexp: String,
    pub lambda_sexp: String,
    /// The intermediate representations requested by `CompilerOptions::dumps`.
    pub dumps: Vec<(DumpKind, String)>,
    /// The warning reports the file compile prints to stderr.
    pub warnings: String,
    /// The units whose interface type checking read.
    pub loaded_units: Vec<String>,
    /// What the typed tree read of other units (with
    /// `CompilerOptions::collect_unit_reads`).
    pub unit_reads: Vec<crate::cmi::item_deps::UnitRead>,
}

pub struct InProcessJsMetadataReady {
    pub is_pure: bool,
    pub cmj_export_constants: ahash::AHashMap<String, CmjExportConstant>,
    pub cmj_export_arities: ahash::AHashMap<String, CmjExportArity>,
    pub cmj_export_lambdas: ahash::AHashMap<String, crate::lambda::Lambda>,
    pub hoisted_exports: Vec<crate::lambda::HoistedExport>,
    pub pers_struct: Option<PortablePersStruct>,
    pub new_alias_rewrites: ahash::AHashMap<String, crate::types::path::Path>,
}

/// Signature payload produced after in-process implementation typechecking but
/// before Lambda/JS compilation. Rewatch uses this to unblock dependent
/// typechecking while preserving OCaml's save-before-translation order
/// (compiler/ml/typemod.ml:1779-1788; compiler/ml/translmod.ml:267).
pub struct InProcessSignatureReady {
    pub pers_struct: Option<PortablePersStruct>,
    pub new_alias_rewrites: ahash::AHashMap<String, crate::types::path::Path>,
}

pub type InProcessSignatureReadyHook<'a> =
    dyn FnMut(InProcessSignatureReady) -> Result<Option<ModuleRegistry>> + 'a;

pub type InProcessBeforeJsHook<'a> =
    dyn FnMut(&AHashSet<ModuleId>) -> Result<Option<ModuleRegistry>> + 'a;

pub type InProcessJsMetadataReadyHook<'a> = dyn FnMut(InProcessJsMetadataReady) -> Result<()> + 'a;

/// Result of an in-process `.resi` interface type-check.
pub struct InProcessInterfaceResult {
    pub signature: crate::types::decl::Signature,
    pub pers_struct: Option<PortablePersStruct>,
    pub new_alias_rewrites: ahash::AHashMap<String, crate::types::path::Path>,
    /// Mirrors compiler/gentype/GenTypeMain.ml:93-134: when a `.resi`
    /// contains `@@genType.ignoreInterface`, GenType must select the
    /// implementation typed artifact for generated output.
    pub gentype_ignore_interface: bool,
    /// The typed-tree dumps requested by `CompilerOptions::dumps`.
    pub dumps: Vec<(DumpKind, String)>,
    /// The warning reports the file compile prints to stderr.
    pub warnings: String,
    /// The units whose interface type checking read.
    pub loaded_units: Vec<String>,
    /// What the typed signature read of other units (with
    /// `CompilerOptions::collect_unit_reads`).
    pub unit_reads: Vec<crate::cmi::item_deps::UnitRead>,
}

fn process_gentype_typed_artifact_if_enabled<'a>(
    options: &CompilerOptions,
    annots: crate::gentype::main::TypedArtifactAnnots<'a>,
    arena: &'a ParseArena,
    type_ctx: &'a TypeContext,
    filename: &str,
    module_name: &str,
    is_interface: bool,
) -> Result<()> {
    let Some(config) = options.gentype_config.as_ref() else {
        return Ok(());
    };
    // Mirrors compiler/core/js_implementation.ml:33-34 and 170, but uses the
    // in-memory typedtree that Rust already has instead of reopening the CMT
    // saved by compiler/ml/typemod.ml:1763-1764 and 1785-1787.
    crate::timing::measure(crate::timing::Phase::Gentype, || {
        crate::gentype::main::process_typed_artifact(
            config,
            options.gentype_resolver.as_deref(),
            crate::gentype::main::TypedArtifact {
                annots,
                arena,
                ctx: type_ctx,
                source_file: Some(filename),
                compiler_module_name: module_name.to_string(),
                // OCaml passes outputprefix.cmt into GenTypeMain.process_cmt_file
                // from compiler/core/js_implementation.ml:72/170, then computes
                // file_name with compiler/gentype/Paths.ml:61-86. The in-process
                // path has the source filename here, so derive the same
                // outputprefix-shaped GenType name instead of reusing the
                // capitalized compiler module name.
                file_name: crate::gentype::paths::get_module_name_from_source_path(filename),
                is_interface,
                declarations_only: options.gentype_declarations_only,
            },
        )
    })
    .with_context(|| format!("GenType failed for {filename}"))
}

/// Type-check an interface source in process, running the frontend as the
/// file compile does (its warnings go to stderr).
pub fn typecheck_interface_source_in_process(
    source: &str,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> Result<InProcessInterfaceResult> {
    let mut parser = Parser::new(filename, source);
    let signature = module::parse_signature(&mut parser);
    let mut frontend_output = String::new();
    let frontend = run_interface_frontend(
        &mut parser,
        signature,
        source,
        filename,
        options,
        &mut frontend_output,
    );
    write_stderr(&frontend_output);
    let frontend = frontend?;
    let mut effective_options = options.clone();
    effective_options.experimental_let_unwrap = frontend.experimental_let_unwrap;
    let mut arena = parser.into_arena();
    crate::types::typecore::prepare_typecheck_arena(&mut arena);
    let result = typecheck_preprocessed_signature_in_process(
        &arena,
        &frontend.signature,
        filename,
        module_name,
        &effective_options,
        registry,
    )?;
    if frontend.warnings_fatal {
        return Err(UserDiagnostic::new(String::new(), 2).into());
    }
    Ok(result)
}

pub fn compile_source_in_process(
    source: &str,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
) -> Result<InProcessCompileResult> {
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);
    let mut frontend_output = String::new();
    let frontend = run_implementation_frontend(
        &mut parser,
        structure,
        source,
        filename,
        options,
        &mut frontend_output,
    );
    write_stderr(&frontend_output);
    let frontend = frontend?;
    let warnings_fatal = frontend.warnings_fatal;
    let experimental_let_unwrap = frontend.experimental_let_unwrap;
    // The frontend already applied `no_export` (js_implementation.ml:130).
    let structure = frontend.structure;
    parser.arena_mut().reserve_typecheck_synthetic_capacity();

    let mut effective_options = options.clone();
    effective_options.experimental_let_unwrap = experimental_let_unwrap;

    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    let result = compile_preprocessed_structure_in_process(
        parser.arena(),
        &structure,
        filename,
        module_name,
        &effective_options,
        registry,
        has_interface,
    )?;
    // Like the direct compile: a frontend warning configured as an error fails
    // the compilation once type checking has reported its own diagnostics.
    if warnings_fatal {
        return Err(UserDiagnostic::new(String::new(), 2).into());
    }
    Ok(result)
}

fn module_format_for_output_path(path: &FsPath) -> ModuleFormat {
    match path.file_name().and_then(|name| name.to_str()) {
        Some(name) if name.ends_with(".mjs") => ModuleFormat::EsModule,
        _ => ModuleFormat::CommonJs,
    }
}

fn effective_js_output_targets(options: &CompilerOptions) -> Vec<JsOutputTarget> {
    if !options.js_output_targets.is_empty() {
        return options.js_output_targets.clone();
    }

    options
        .output_path
        .as_ref()
        .map(|path| JsOutputTarget {
            path: path.clone(),
            module_format: options
                .output_module_format
                .unwrap_or_else(|| module_format_for_output_path(path)),
        })
        .into_iter()
        .collect()
}

fn render_js_program(
    program: &DepsProgram,
    resolver: &ModulePathResolver,
    file_directives: &[String],
    debug: bool,
    jsx_preserve: bool,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    source_file_names: std::sync::Arc<std::collections::HashMap<crate::intern::StrIdx, String>>,
) -> (String, Option<String>) {
    let source_path = options.source_filename.as_deref().map(FsPath::new);
    let source_map_target = output_path.map(FsPath::to_path_buf).or_else(|| {
        (options.source_map == crate::js_ir::source_map::SourceMapMode::Inline).then(|| {
            let source = source_path.unwrap_or_else(|| FsPath::new("_none_.res"));
            source.with_extension("js")
        })
    });
    if let (Some(target), Some(source)) = (source_map_target.as_deref(), source_path) {
        print_deps_program_with_source_map(
            program,
            Some(resolver),
            file_directives,
            debug,
            jsx_preserve,
            !options.no_version_header,
            target,
            source,
            options.source_map,
            options.source_map_sources_content,
            &options.source_map_root,
            source_file_names,
        )
    } else {
        (
            print_deps_program_with_directives_and_options(
                program,
                Some(resolver),
                file_directives,
                debug,
                jsx_preserve,
                !options.no_version_header,
            ),
            None,
        )
    }
}

fn compile_js_program_for_output(
    lowered_lambda: &crate::lambda::Lambda,
    hoisted_functions: &[crate::lambda::HoistedFunction],
    possible_required_modules: &AHashSet<ModuleId>,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    output_module_format: Option<ModuleFormat>,
    persistent_env: Option<PersistentEnv>,
    jsx_preserve: bool,
) -> Result<(
    DepsProgram,
    ModulePathResolver,
    ahash::AHashMap<String, CmjExportConstant>,
    ahash::AHashMap<String, CmjExportArity>,
    ahash::AHashMap<String, crate::lambda::Lambda>,
)> {
    let _span = info_span!(
        "compiler.js_backend",
        module = options.module_name.as_deref().unwrap_or(""),
        owned = false,
        possible_required_modules = possible_required_modules.len()
    )
    .entered();
    let mut module_path_resolver = ModulePathResolver::from_compile_options(
        options.source_filename.as_deref(),
        output_path,
        output_module_format,
        options.package_name.as_deref(),
        options.runtime_path.as_deref(),
        persistent_env,
        options.make_runtime,
    );
    module_path_resolver.set_package_specs(&options.js_package_specs);
    for module in possible_required_modules {
        if matches!(module.kind, Kind::Ml) && !module.dynamic_import {
            if let Some(path) =
                module_path_resolver.resolve_local_module_fallback_path(module.id.name())
            {
                module_path_resolver.set_module_path_override(module.id.name(), path);
            }
        }
    }
    let mut compiler = LambdaCompiler::with_module_path_resolver_and_options(
        Some(module_path_resolver),
        jsx_preserve,
        options.check_div_by_zero,
        options.cross_module_inline,
    );
    compiler.set_source_map_enabled(
        options.source_map != crate::js_ir::source_map::SourceMapMode::None,
    );
    compiler.set_hoisted_functions(hoisted_functions.to_vec());
    let program = compiler.compile_deps_program_with_possible_required_modules(
        lowered_lambda,
        possible_required_modules,
    );
    // lam_compile_main.ml reports a primitive's Location error before the
    // fatal-warnings check, as the file compile does.
    if let Some(diagnostic) = compiler.take_diagnostic() {
        let filename = options.source_filename.as_deref().unwrap_or("_none_");
        return Err(UserDiagnostic::new(
            format_compiler_error_report_from_location(
                &read_in_process_source(filename),
                filename,
                &diagnostic.loc,
                &diagnostic.message,
            ),
            2,
        )
        .into());
    }
    let module_path_resolver = compiler
        .take_module_path_resolver()
        .expect("lambda compiler retained module path resolver");
    let cmj_export_constants = compiler.take_cmj_export_constants();
    let cmj_export_arities = compiler.take_cmj_export_arities();
    let cmj_export_lambdas = compiler.take_cmj_export_lambdas();

    Ok((
        program,
        module_path_resolver,
        cmj_export_constants,
        cmj_export_arities,
        cmj_export_lambdas,
    ))
}

fn compile_js_program_for_output_owned(
    lowered_lambda: crate::lambda::Lambda,
    hoisted_functions: &[crate::lambda::HoistedFunction],
    possible_required_modules: &AHashSet<ModuleId>,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    output_module_format: Option<ModuleFormat>,
    persistent_env: Option<PersistentEnv>,
    jsx_preserve: bool,
) -> Result<(
    DepsProgram,
    ModulePathResolver,
    ahash::AHashMap<String, CmjExportConstant>,
    ahash::AHashMap<String, CmjExportArity>,
    ahash::AHashMap<String, crate::lambda::Lambda>,
)> {
    // The pre-JS result already collected the modules of this lowered lambda
    // into `possible_required_modules` (see
    // `compile_preprocessed_structure_in_process_until_js`).
    let collected_possible_required_modules = possible_required_modules.clone();
    compile_js_program_for_output_owned_with_collected_modules(
        lowered_lambda,
        hoisted_functions,
        collected_possible_required_modules,
        options,
        output_path,
        output_module_format,
        persistent_env,
        jsx_preserve,
    )
}

fn compile_js_program_for_output_owned_with_collected_modules(
    lowered_lambda: crate::lambda::Lambda,
    hoisted_functions: &[crate::lambda::HoistedFunction],
    possible_required_modules: AHashSet<ModuleId>,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    output_module_format: Option<ModuleFormat>,
    persistent_env: Option<PersistentEnv>,
    jsx_preserve: bool,
) -> Result<(
    DepsProgram,
    ModulePathResolver,
    ahash::AHashMap<String, CmjExportConstant>,
    ahash::AHashMap<String, CmjExportArity>,
    ahash::AHashMap<String, crate::lambda::Lambda>,
)> {
    let _span = info_span!(
        "compiler.js_backend",
        module = options.module_name.as_deref().unwrap_or(""),
        owned = true,
        possible_required_modules = possible_required_modules.len(),
        precomputed_possible_required_modules = true
    )
    .entered();
    let mut module_path_resolver = ModulePathResolver::from_compile_options(
        options.source_filename.as_deref(),
        output_path,
        output_module_format,
        options.package_name.as_deref(),
        options.runtime_path.as_deref(),
        persistent_env,
        options.make_runtime,
    );
    module_path_resolver.set_package_specs(&options.js_package_specs);
    for module in &possible_required_modules {
        if matches!(module.kind, Kind::Ml) && !module.dynamic_import {
            if let Some(path) =
                module_path_resolver.resolve_local_module_fallback_path(module.id.name())
            {
                module_path_resolver.set_module_path_override(module.id.name(), path);
            }
        }
    }
    let mut compiler = LambdaCompiler::with_module_path_resolver_and_options(
        Some(module_path_resolver),
        jsx_preserve,
        options.check_div_by_zero,
        options.cross_module_inline,
    );
    compiler.set_source_map_enabled(
        options.source_map != crate::js_ir::source_map::SourceMapMode::None,
    );
    compiler.set_hoisted_functions(hoisted_functions.to_vec());
    let program = compiler.compile_deps_program_with_collected_possible_required_modules_owned(
        lowered_lambda,
        possible_required_modules,
    );
    // lam_compile_main.ml reports a primitive's Location error before the
    // fatal-warnings check, as the file compile does.
    if let Some(diagnostic) = compiler.take_diagnostic() {
        let filename = options.source_filename.as_deref().unwrap_or("_none_");
        return Err(UserDiagnostic::new(
            format_compiler_error_report_from_location(
                &read_in_process_source(filename),
                filename,
                &diagnostic.loc,
                &diagnostic.message,
            ),
            2,
        )
        .into());
    }
    let module_path_resolver = compiler
        .take_module_path_resolver()
        .expect("lambda compiler retained module path resolver");
    let cmj_export_constants = compiler.take_cmj_export_constants();
    let cmj_export_arities = compiler.take_cmj_export_arities();
    let cmj_export_lambdas = compiler.take_cmj_export_lambdas();

    Ok((
        program,
        module_path_resolver,
        cmj_export_constants,
        cmj_export_arities,
        cmj_export_lambdas,
    ))
}
pub fn compile_preprocessed_structure_in_process(
    arena: &crate::parse_arena::ParseArena,
    structure: &Structure,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
) -> Result<InProcessCompileResult> {
    compile_preprocessed_structure_in_process_with_signature_hook(
        arena,
        structure,
        filename,
        module_name,
        options,
        registry,
        has_interface,
        None,
        None,
    )
}

pub fn compile_preprocessed_structure_in_process_with_signature_hook(
    arena: &crate::parse_arena::ParseArena,
    structure: &Structure,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
    mut signature_ready: Option<&mut InProcessSignatureReadyHook<'_>>,
    mut before_js: Option<&mut InProcessBeforeJsHook<'_>>,
) -> Result<InProcessCompileResult> {
    let pre_js = compile_preprocessed_structure_in_process_until_js(
        arena,
        structure,
        filename,
        module_name,
        options,
        registry,
        has_interface,
        false,
        signature_ready.as_deref_mut(),
    )?;

    let refreshed_registry = if let Some(hook) = before_js.as_deref_mut() {
        hook(&pre_js.possible_required_modules)?
    } else {
        None
    };
    let js_registry = refreshed_registry.as_ref().unwrap_or(registry);
    finish_preprocessed_structure_in_process_from_js_boundary(pre_js, options, js_registry)
}

/// The type-checking context and initial environment an in-process
/// implementation is typed in: the registry's units are the persistent
/// environment, Pervasives (and `-open`s) opened as `Res_compmisc.initial_env`
/// does (res_compmisc.ml:56-62).
fn in_process_structure_type_check_context<'a>(
    type_ctx: &'a TypeContext,
    arena: &'a crate::parse_arena::ParseArena,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    module_name: &str,
    file_config: &FileConfigOverrides,
    frontend_warning_specs: &[ppx::WarningAttributeSpec],
) -> (TypeCheckContext<'a>, Env) {
    let mut tctx = TypeCheckContext::new(type_ctx, arena);
    tctx.experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
    tctx.transparent_modules = options.transparent_modules;
    apply_warning_options(&mut tctx, options);
    // Ppx_entry.rewrite_* (ppx_entry.ml:28, 47) applies the leading warning
    // attributes; compiling a preprocessed `.ast` does not run it again.
    if !options.frontend_already_reported {
        apply_leading_warning_attribute_options(&mut tctx, frontend_warning_specs);
    }
    apply_file_config_warning_options(&mut tctx, file_config);
    let mut env = initial_env(type_ctx);

    let mut pers_env = PersistentEnv::from_registry(registry);
    pers_env.set_visible_package_roots(options.visible_package_roots.clone());
    let (load_path, load_path_display) = shared_load_path_with_display(options);
    type_ctx.set_load_paths_shared(load_path.clone());
    pers_env.set_load_path_shared(load_path, load_path_display);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_jsx_module(options.jsx_module.clone());
    pers_env.set_nopervasives(options.nopervasives);
    pers_env.set_compiling_module(Some(module_name.to_string()));
    load_pervasives(
        &mut pers_env,
        &mut env,
        type_ctx,
        &options.open_modules,
        options.nopervasives,
        Some(module_name),
    );
    tctx.set_persistent_env(pers_env);
    (tctx, env)
}

/// The typed tree of one module, type-checked on demand for editor tooling,
/// which works on it in memory.
pub struct ToolingTypedModule {
    pub type_ctx: TypeContext,
    pub typed: ToolingTyped,
}

/// What type-checking a module for editor tooling produced.
pub enum ToolingTyped {
    Implementation(crate::types::typedtree::Structure),
    Interface(crate::types::typedtree::TypedSignature),
    /// The compiler's report of a module that does not type-check.
    Failed(String),
}

/// Type-check an implementation for editor tooling, as the in-process build
/// does (`compile_preprocessed_structure_in_process_until_js`), keeping the
/// typed tree instead of compiling it further.
pub fn typecheck_structure_for_tooling(
    arena: &crate::parse_arena::ParseArena,
    structure: &Structure,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> ToolingTypedModule {
    let file_config = extract_file_config_from_structure(structure, arena);
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_attribute_specs(structure, arena);
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    let typed = {
        let (mut tctx, env) = in_process_structure_type_check_context(
            &type_ctx,
            arena,
            options,
            registry,
            module_name,
            &file_config,
            &frontend_warning_specs,
        );
        match type_structure(&mut tctx, &env, arena, structure) {
            Ok((typed_structure, _final_env)) => ToolingTyped::Implementation(typed_structure),
            Err(e) => {
                let source = read_in_process_source(filename);
                let report = match tctx
                    .persistent_env
                    .as_ref()
                    .and_then(|env| env.last_error())
                {
                    Some(error) => persistent_env_error_to_anyhow(error, filename),
                    None => type_mod_error_to_anyhow(e, &type_ctx, arena, &source, filename, false),
                };
                ToolingTyped::Failed(format!("{report:#}"))
            }
        }
    };
    ToolingTypedModule { type_ctx, typed }
}

/// Type-check an interface for editor tooling, as the in-process build does
/// (`typecheck_preprocessed_signature_in_process`), keeping the typed tree.
pub fn typecheck_signature_for_tooling(
    arena: &crate::parse_arena::ParseArena,
    signature: &Signature,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> ToolingTypedModule {
    let file_config = extract_file_config_from_signature(signature, arena);
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_signature_attribute_specs(signature, arena);
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    let typed = {
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        tctx.experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
        tctx.transparent_modules = options.transparent_modules;
        apply_warning_options(&mut tctx, options);
        if !options.frontend_already_reported {
            apply_leading_warning_attribute_options(&mut tctx, &frontend_warning_specs);
        }
        apply_file_config_warning_options(&mut tctx, &file_config);
        let mut env = initial_env(&type_ctx);
        let mut pers_env = PersistentEnv::from_registry(registry);
        pers_env.set_visible_package_roots(options.visible_package_roots.clone());
        let (load_path, load_path_display) = shared_load_path_with_display(options);
        type_ctx.set_load_paths_shared(load_path.clone());
        pers_env.set_load_path_shared(load_path, load_path_display);
        pers_env.set_open_modules(options.open_modules.clone());
        pers_env.set_jsx_version(options.jsx_version);
        pers_env.set_jsx_module(options.jsx_module.clone());
        pers_env.set_nopervasives(options.nopervasives);
        pers_env.set_compiling_module(Some(module_name.to_string()));
        load_pervasives(
            &mut pers_env,
            &mut env,
            &type_ctx,
            &options.open_modules,
            options.nopervasives,
            Some(module_name),
        );
        tctx.set_persistent_env(pers_env);
        match transl_signature(&mut tctx, &env, arena, signature) {
            Ok(typed_signature) => ToolingTyped::Interface(typed_signature),
            Err(e) => {
                let source = read_in_process_source(filename);
                let report = match tctx
                    .persistent_env
                    .as_ref()
                    .and_then(|env| env.last_error())
                {
                    Some(error) => persistent_env_error_to_anyhow(error, filename),
                    None => type_mod_error_to_anyhow(e, &type_ctx, arena, &source, filename, false),
                };
                ToolingTyped::Failed(format!("{report:#}"))
            }
        }
    };
    ToolingTypedModule { type_ctx, typed }
}

pub fn compile_preprocessed_structure_in_process_until_js(
    arena: &crate::parse_arena::ParseArena,
    structure: &Structure,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
    gentype_ignore_interface: bool,
    mut signature_ready: Option<&mut InProcessSignatureReadyHook<'_>>,
) -> Result<InProcessPreJsCompileResult> {
    let _span = info_span!(
        "compiler.in_process_compile",
        module = %module_name,
        file = %filename,
        has_interface,
        skip_js_render = options.skip_js_render,
        js_targets = options.js_output_targets.len()
    )
    .entered();
    let original_alias_count = registry.alias_rewrite_len();
    let (file_directives, debug, jsx_preserve) = {
        let _phase = info_span!("compiler.directives").entered();
        (
            extract_file_directives_from_structure(structure, arena)?,
            debug_for_structure(structure, options, arena),
            jsx_preserve_for_structure(structure, options, arena),
        )
    };
    let file_config = extract_file_config_from_structure(structure, arena);
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_attribute_specs(structure, arena);

    log::debug!(
        "[compile_source_in_process] {} type-check start",
        module_name
    );
    let env_setup_span = info_span!("compiler.env_setup").entered();
    let env_setup_start = crate::timing::enabled().then(std::time::Instant::now);
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    let (mut tctx, env) = in_process_structure_type_check_context(
        &type_ctx,
        arena,
        options,
        registry,
        module_name,
        &file_config,
        &frontend_warning_specs,
    );
    drop(env_setup_span);
    if let Some(start) = env_setup_start {
        crate::timing::record(crate::timing::Phase::EnvSetup, start.elapsed());
    }

    // Diagnostics are reported against the source file, read only when
    // there is something to report.
    let source_cell = std::cell::OnceCell::new();
    let source = || -> &str { source_cell.get_or_init(|| read_in_process_source(filename)) };

    let typed = crate::timing::measure(crate::timing::Phase::Typecheck, || {
        let _phase = info_span!("compiler.type_structure").entered();
        type_structure(&mut tctx, &env, arena, structure)
    });
    let (typed_structure, final_env) = match typed {
        Ok(result) => result,
        Err(e) => {
            // As in the file compile: the warnings reported so far precede
            // the error report.
            tctx.drain_open_slot_uses();
            let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
            let suppress_info_style =
                !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
            if let Some(error) = tctx
                .persistent_env
                .as_ref()
                .and_then(|persistent_env| persistent_env.last_error())
            {
                return Err(prefix_diagnostic(
                    &warnings,
                    persistent_env_error_to_anyhow(error, filename),
                ));
            }
            return Err(prefix_diagnostic(
                &warnings,
                type_mod_error_to_anyhow(
                    e,
                    &type_ctx,
                    arena,
                    source(),
                    filename,
                    suppress_info_style,
                ),
            ));
        }
    };
    tctx.drain_open_slot_uses();
    // Debugging aid: `RESCRIPT_DUMP_TYPED_SEXP=<Module>` prints the
    // in-process typed tree of that module like `bsc -dtyped-sexp`.
    if std::env::var("RESCRIPT_DUMP_TYPED_SEXP").is_ok_and(|name| name == module_name) {
        let _ = print_typed_structure(arena, &type_ctx, &typed_structure, &mut std::io::stderr());
    }

    let mut inferred_implementation_coercion = None;
    // Interface matching, non-generalizable checks and signature
    // normalization are part of OCaml's `type_implementation`
    // (compiler/ml/typemod.ml:1740-1788); account for them as typecheck.
    let signature_prepare_start = crate::timing::enabled().then(std::time::Instant::now);
    let mut published_signature = {
        let _phase = info_span!("compiler.signature_prepare").entered();
        if has_interface {
            apply_moregen_constraints(
                &mut tctx,
                &type_ctx,
                &typed_structure,
                options,
                Some(has_interface),
            );
        }

        let simple_signature =
            crate::types::includemod::simplify_signature(&typed_structure.str_type);
        if !has_interface {
            inferred_implementation_coercion = Some(
                crate::types::includemod::compunit(
                    &type_ctx,
                    &env,
                    filename,
                    &typed_structure.str_type,
                    "(inferred signature)",
                    &simple_signature,
                )
                .map_err(|e| anyhow!("Inferred signature inclusion failed: {e:?}"))?,
            );
            if let Err(e) = crate::types::typemod::check_nongen_schemes(
                &type_ctx,
                &final_env,
                &simple_signature,
            ) {
                let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
                let suppress_info_style =
                    !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
                return Err(prefix_diagnostic(
                    &warnings,
                    type_mod_error_to_anyhow(
                        e,
                        &type_ctx,
                        arena,
                        source(),
                        filename,
                        suppress_info_style,
                    ),
                ));
            }
            normalize_signature(&type_ctx, &final_env, &simple_signature);
        }

        // `Env.save_signature` (typemod.ml:1779-1788) renames the bound
        // identifiers of a copy of the signature (env.ml:1886-1892). In-process
        // builds write no `.cmi`, but the copy still takes its stamps.
        if !has_interface {
            saved_signature_copy(&type_ctx, &simple_signature);
        }

        simple_signature
    };
    if let Some(start) = signature_prepare_start {
        crate::timing::record(crate::timing::Phase::Typecheck, start.elapsed());
    }
    // typemod.ml:1742-1758: with an interface, the implementation is checked
    // against it (marking the included declarations used) before the delayed
    // checks, as the file compile does.
    let mut interface_inclusion = None;
    if has_interface {
        let interface_file = in_process_interface_display_name(options, filename);
        match check_compunit_inclusion_for_errors(
            &mut tctx,
            &type_ctx,
            &env,
            &typed_structure,
            filename,
            &|| source().to_string(),
            filename,
            true,
            Some(interface_file.as_str()),
        ) {
            Ok(inclusion) => interface_inclusion = inclusion,
            Err(error) => {
                let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
                return Err(prefix_diagnostic(&warnings, error));
            }
        }
    }
    // typemod.ml:1769-1776 forces the delayed usage checks before Lambda
    // translation, as the file compile does.
    tctx.flush_value_usage_checks();
    let post_type_warning_start = tctx.warnings.len();
    // js_implementation.ml:148-156 prints `-dtyped-sexp` here, before the
    // signature is saved: `register_in_memory_signature` below finalizes the
    // current unit's type paths in place (`allOptRec` becomes
    // `Current.allOptRec`), which must not show in the dump.
    let mut dumps: Vec<(DumpKind, String)> = Vec::new();
    for kind in [DumpKind::TypedTree, DumpKind::TypedTreeLocs] {
        if options.dumps.contains(&kind) {
            let mut buf = Vec::new();
            let _ = if kind == DumpKind::TypedTree {
                crate::types::sexp_typedtree::print_typed_structure(
                    arena,
                    &type_ctx,
                    &typed_structure,
                    &mut buf,
                )
            } else {
                crate::types::sexp_typedtree::print_typed_structure_with_locs(
                    arena,
                    &type_ctx,
                    &typed_structure,
                    &mut buf,
                )
            };
            dumps.push((kind, latin1_dump(buf)));
        }
    }

    let unit_reads = if options.collect_unit_reads {
        crate::types::unit_reads::structure_reads(
            &type_ctx,
            &typed_structure,
            &options.open_modules,
        )
    } else {
        Vec::new()
    };

    // OCaml saves the inferred `.cmi` only in the no-interface branch before
    // Lambda translation mutates any shared type nodes
    // (compiler/ml/typemod.ml:1768-1788; translmod.ml:267). With a `.resi`,
    // the already-published interface remains the target signature for
    // `Translmod.transl_implementation`; do not replace it with the
    // implementation signature or the export coercion becomes identity.
    let (mut pers_struct, mut new_alias_rewrites, persistent_env_after_signature) = if has_interface
    {
        (
            None,
            Default::default(),
            tctx.persistent_env
                .take()
                .unwrap_or_else(PersistentEnv::new),
        )
    } else {
        let _phase = info_span!("compiler.signature_extract").entered();
        let signature_publish_start = crate::timing::enabled().then(std::time::Instant::now);
        let mut internal_env = tctx
            .persistent_env
            .take()
            .unwrap_or_else(PersistentEnv::new);

        let mut signature_for_save = if signature_ready.is_some() {
            std::mem::take(&mut published_signature)
        } else {
            published_signature.clone()
        };
        if !options.keep_locs {
            strip_saved_signature_locations(&mut signature_for_save);
        }
        strip_saved_extension_locations(&mut signature_for_save);
        // OCaml compiler/ml/env.ml:1949-1952 saves a fresh
        // `Subst.signature (Subst.for_saving Subst.identity) sg` copy before
        // installing the persistent structure. Keep Rust's GenType raw-signature
        // cache on its own type nodes too; `register_in_memory_signature`
        // finalizes component lookup paths in-place, and sharing those refs
        // would leak qualified `Current.t` paths back into the CMT-shaped
        // signature that compiler/gentype/TranslateStructure.ml:174-183 reads
        // through Env.scrape_alias.
        let current_raw_sig = std::sync::Arc::new(
            crate::types::typecore::copy_lookup_signature_for_subst(&signature_for_save, &type_ctx),
        );
        // typemod.ml:1778: `Builtin_attributes.deprecated_of_str ast`.
        internal_env.register_in_memory_signature(
            module_name,
            signature_for_save,
            filename,
            crate::types::typemod::deprecated_of_str(arena, structure),
            Vec::new(),
            &type_ctx,
        );
        // OCaml saves the current unit into the persistent table before
        // lambda translation (compiler/ml/typemod.ml:1779-1788). That save
        // also installs `ps_sig` for later lazy component forcing
        // (compiler/ml/env.ml:1960-1977). In-process builds do not write/read
        // the `.cmi`, so keep the pre-finalized current signature in the
        // TypeContext raw-signature cache before hiding the transient module.
        // This preserves the OCaml split between raw `ps_sig` and later lazy
        // component substitution in compiler/ml/env.ml:669-678 and
        // compiler/ml/env.ml:1513-1530.
        type_ctx.register_gentype_raw_module_sig(module_name, current_raw_sig.clone());
        type_ctx.register_raw_module_sig(module_name, current_raw_sig);

        let (pers_struct, new_alias_rewrites) = if options.publish_in_process_signature {
            internal_env.extract_module_update(
                module_name,
                original_alias_count,
                &type_ctx,
                Some(arena),
            )
        } else {
            (None, ahash::AHashMap::new())
        };
        // Keep the just-saved current unit visible through raw-lambda
        // conversion. OCaml saves the inferred signature in the no-interface
        // branch before translation (compiler/ml/typemod.ml:1779-1788), and
        // optional-pattern lowering can still expand current-unit aliases via
        // Env.find_type while choosing Pval_from_option_not_nest
        // (compiler/ml/typeopt.ml:40-88; compiler/ml/matching.ml:1259-1267).
        // `finish_preprocessed_structure_in_process_from_js_boundary` hides it
        // again before JS module-path probing.
        if let Some(start) = signature_publish_start {
            crate::timing::record(crate::timing::Phase::SignaturePublish, start.elapsed());
        }
        (pers_struct, new_alias_rewrites, internal_env)
    };
    if !has_interface && let Some(hook) = signature_ready.as_deref_mut() {
        let _ = hook(InProcessSignatureReady {
            pers_struct: pers_struct.take(),
            new_alias_rewrites: std::mem::take(&mut new_alias_rewrites),
        })?;
    }
    tctx.persistent_env = Some(persistent_env_after_signature);

    // Capture typed tree sexp for the playground (only if requested).
    let typed_tree_sexp = if options.capture_intermediates {
        let mut buf = Vec::new();
        let _ = crate::types::sexp_typedtree::print_typed_structure_with_locs(
            arena,
            &type_ctx,
            &typed_structure,
            &mut buf,
        );
        String::from_utf8_lossy(&buf).into_owned()
    } else {
        String::new()
    };

    if !has_interface || gentype_ignore_interface {
        // With a `.resi`, compiler/gentype/Paths.ml:61-86 makes the
        // implementation output prefix select the `.cmti` artifact first. The
        // in-process interface step above owns that artifact path unless
        // compiler/gentype/GenTypeMain.ml:93-134 selected the implementation
        // because the interface carries `@@genType.ignoreInterface`.
        process_gentype_typed_artifact_if_enabled(
            options,
            crate::gentype::main::TypedArtifactAnnots::Implementation(&typed_structure),
            arena,
            &type_ctx,
            filename,
            module_name,
            false,
        )?;
    }

    let lambda_start_stamp = synchronize_lambda_start_stamp(&type_ctx);

    let unit_name = options.current_unit_name().unwrap_or_default();
    let (
        raw_lambda,
        raw_warnings,
        raw_diagnostic,
        raw_possible_required_modules,
        raw_lambda_current_stamp,
        hoisted_functions,
        hoisted_exports,
    ) = match crate::timing::measure(crate::timing::Phase::Lambda, || {
        let _phase = info_span!("compiler.raw_lambda").entered();
        // The interface check above already computed the coercion; report
        // its inclusion warnings where the coercion is used, as before.
        let implementation_coercion = match (inferred_implementation_coercion, interface_inclusion)
        {
            (Some(coercion), _) => coercion,
            (None, Some(inclusion)) => {
                report_compunit_inclusion_warnings(&mut tctx, inclusion.warnings);
                inclusion.coercion
            }
            (None, None) => compute_raw_implementation_coercion(
                &mut tctx,
                &type_ctx,
                &env,
                &typed_structure,
                options,
                Some(has_interface),
            ),
        };
        let mut raw_converter =
            crate::raw_lambda::convert::RawLambdaConverter::with_start_stamp_and_unit_name(
                arena,
                &type_ctx,
                &env,
                lambda_start_stamp,
                unit_name,
            );
        raw_converter.set_preserve_expanded_sparse_records(
            options.capture_intermediates || options.dumps.iter().any(|kind| kind.is_lambda()),
        );
        raw_converter.set_no_assert_false(options.no_assert_false);
        raw_converter.set_noassert(options.noassert);
        raw_converter.set_warning_config(tctx.warning_config.clone());
        if let Some(persistent_env) = tctx.persistent_env.clone() {
            raw_converter.set_persistent_env(persistent_env);
        }
        // An uncaught exception in Translmod (`Misc.fatal_error`) ends the
        // file compile after the warnings it already printed; report it with
        // the warnings this compile buffered.
        let raw_lambda = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            raw_converter
                .convert_structure_with_coercion(&typed_structure, &implementation_coercion)
        })) {
            Ok(raw_lambda) => raw_lambda,
            Err(payload) => return Err(payload),
        };
        let raw_warnings = raw_converter.take_warnings();
        let raw_diagnostic = raw_converter.take_diagnostic();
        let possible_required_modules = raw_converter.take_possible_required_modules();
        let raw_lambda_current_stamp = raw_converter.current_stamp();
        let hoisted_functions = raw_converter.take_hoisted_functions();
        let hoisted_exports = raw_converter.take_hoisted_exports();
        Ok((
            raw_lambda,
            raw_warnings,
            raw_diagnostic,
            possible_required_modules,
            raw_lambda_current_stamp,
            hoisted_functions,
            hoisted_exports,
        ))
    }) {
        Ok(converted) => converted,
        Err(payload) => {
            let Some(report) = crate::misc::uncaught_exception_report(&*payload) else {
                std::panic::resume_unwind(payload);
            };
            return Err(UserDiagnostic::new(
                format!(
                    "{}{report}\n",
                    format_type_warnings_lazy(arena, &source, filename, &tctx.warnings)
                ),
                2,
            )
            .into());
        }
    };
    // The file compile reports the typing warnings, then Translmod's
    // (js_implementation.ml:161-167); a Translmod error escapes before
    // `Warnings.check_fatal`.
    let mut warnings = format_type_warnings_lazy(
        arena,
        &source,
        filename,
        &tctx.warnings[..post_type_warning_start],
    );
    if let Some(diagnostic) = raw_diagnostic {
        warnings.push_str(&format_type_warnings_lazy(
            arena,
            &source,
            filename,
            &raw_warnings,
        ));
        return Err(prefix_diagnostic(
            &warnings,
            UserDiagnostic::new(
                format_compiler_error_report_from_location(
                    source(),
                    filename,
                    &diagnostic.loc,
                    &diagnostic.message,
                ),
                2,
            )
            .into(),
        ));
    }
    let late_type_warnings = &tctx.warnings[post_type_warning_start..];
    warnings.push_str(&format_type_warnings_lazy(
        arena,
        &source,
        filename,
        late_type_warnings,
    ));
    warnings.push_str(&format_type_warnings_lazy(
        arena,
        &source,
        filename,
        &raw_warnings,
    ));
    // lam_compile_main.ml:420 `Warnings.check_fatal ()`: a warning configured
    // as an error fails the compilation after its reports.
    if type_warnings_have_errors(&tctx.warnings) || type_warnings_have_errors(&raw_warnings) {
        return Err(UserDiagnostic::new(warnings, 2).into());
    }
    // Capture raw lambda sexp for the playground (only if requested).
    let raw_lambda_sexp = if options.capture_intermediates {
        let mut buf = Vec::new();
        crate::raw_lambda::print::print_raw_lambda(&raw_lambda, &mut buf);
        String::from_utf8_lossy(&buf).into_owned()
    } else {
        String::new()
    };

    let lowered_lambda = crate::timing::measure(crate::timing::Phase::Lambda, || {
        let _phase = info_span!("compiler.lower_lambda").entered();
        crate::raw_lambda::lower::lower_to_translmod_lambda_with_start_stamp(
            raw_lambda,
            raw_lambda_current_stamp,
        )
    });
    let (lowered_lambda, export_idents) = lowered_lambda;
    // js_implementation.ml:165 prints `-drawlambda` on Translmod's result.
    if options.dumps.contains(&DumpKind::RawLambda) {
        let mut buf = Vec::new();
        crate::lambda::printlambda::print_lambda(&lowered_lambda, &mut buf);
        buf.push(b'\n');
        dumps.push((DumpKind::RawLambda, latin1_dump(buf)));
    }
    // lam_compile_main.ml:288-290: the first pass of Lam_compile_main.compile.
    let lowered_lambda = crate::timing::measure(crate::timing::Phase::Lambda, || {
        crate::lambda::lam_pass_collapse_var_aliases::collapse(lowered_lambda, &export_idents)
    });
    if let Some(name) = crate::lambda::lam_compile_main::duplicate_export_name(&lowered_lambda) {
        return Err(duplicate_export_error(filename, &name));
    }
    let mut possible_required_modules =
        crate::lambda::lam_compile::collect_possible_required_modules_for_lambda(&lowered_lambda);
    possible_required_modules.extend(raw_possible_required_modules);
    // OCaml has one mutable `Ident.currentstamp` through typechecking,
    // `Translmod.transl_implementation`, and `Lam_compile_main.compile`
    // (compiler/ext/ident.ml:26-58; compiler/core/js_implementation.ml:161-167).
    // Rewatch can split Rust in-process compilation before JS and resume it on a
    // different worker thread, so carry the module-local legacy stamp explicitly
    // instead of reading that worker's unrelated thread-local counter.
    let ident_stamp_at_js_boundary = crate::ident::Ident::current_local_stamp();

    for kind in [DumpKind::Lambda, DumpKind::LambdaLocs] {
        if options.dumps.contains(&kind) {
            let mut buf = Vec::new();
            let _ = if kind == DumpKind::Lambda {
                crate::lambda::sexp_lambda::print_lambda(&lowered_lambda, &mut buf)
            } else {
                crate::lambda::sexp_lambda::print_lambda_with_locs(&lowered_lambda, &mut buf)
            };
            dumps.push((kind, latin1_dump(buf)));
        }
    }

    // Capture lambda sexp for the playground (only if requested).
    let lambda_sexp = if options.capture_intermediates {
        let mut buf = Vec::new();
        let _ = crate::lambda::sexp_lambda::print_lambda_with_locs(&lowered_lambda, &mut buf);
        String::from_utf8_lossy(&buf).into_owned()
    } else {
        String::new()
    };

    Ok(InProcessPreJsCompileResult {
        lowered_lambda,
        possible_required_modules,
        hoisted_functions,
        hoisted_exports,
        ident_stamp_at_js_boundary,
        file_directives,
        debug,
        jsx_preserve,
        signature: published_signature,
        pers_struct,
        new_alias_rewrites,
        source_file_names: std::sync::Arc::new(arena.source_file_names()),
        typed_tree_sexp,
        raw_lambda_sexp,
        lambda_sexp,
        dumps,
        warnings,
        unit_reads,
        loaded_units: tctx
            .persistent_env
            .as_ref()
            .map(PersistentEnv::loaded_units)
            .unwrap_or_default(),
    })
}

pub fn finish_preprocessed_structure_in_process_from_js_boundary(
    pre_js: InProcessPreJsCompileResult,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> Result<InProcessCompileResult> {
    finish_preprocessed_structure_in_process_from_js_boundary_with_metadata_hook(
        pre_js, options, registry, None,
    )
}

pub fn finish_preprocessed_structure_in_process_from_js_boundary_with_metadata_hook(
    mut pre_js: InProcessPreJsCompileResult,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    mut metadata_ready: Option<&mut InProcessJsMetadataReadyHook<'_>>,
) -> Result<InProcessCompileResult> {
    let _span = info_span!(
        "compiler.in_process_js_finish",
        module = options.module_name.as_deref().unwrap_or(""),
        skip_js_render = options.skip_js_render,
        js_targets = options.js_output_targets.len()
    )
    .entered();
    let mut persistent_env_for_js = PersistentEnv::from_registry(registry);
    let (load_path, load_path_display) = shared_load_path_with_display(options);
    persistent_env_for_js.set_load_path_shared(load_path, load_path_display);
    persistent_env_for_js.set_open_modules(options.open_modules.clone());
    persistent_env_for_js.set_jsx_version(options.jsx_version);
    persistent_env_for_js.set_jsx_module(options.jsx_module.clone());
    persistent_env_for_js.set_nopervasives(options.nopervasives);
    persistent_env_for_js.set_compiling_module(options.module_name.clone());
    if let Some(module_name) = options.module_name.as_deref() {
        persistent_env_for_js.unregister_in_memory_signature(module_name);
    }
    let persistent_env_for_js = Some(persistent_env_for_js);
    crate::ident::Ident::set_current_time(pre_js.ident_stamp_at_js_boundary);
    let js_targets = effective_js_output_targets(options);
    let primary_target = js_targets.first();
    let primary_output_path = primary_target
        .map(|target| target.path.as_path())
        .or(options.output_path.as_deref());
    let primary_output_module_format = primary_target
        .map(|target| target.module_format)
        .or(options.output_module_format);
    let compile_multiple_js_targets = !options.skip_js_render && js_targets.len() > 1;
    let mut lowered_lambda = Some(pre_js.lowered_lambda);
    let (
        program,
        module_path_resolver,
        mut cmj_export_constants,
        mut cmj_export_arities,
        mut cmj_export_lambdas,
    ) = {
        let _phase = info_span!(
            "compiler.js_compile",
            multiple_targets = compile_multiple_js_targets
        )
        .entered();
        if compile_multiple_js_targets {
            compile_js_program_for_output(
                lowered_lambda
                    .as_ref()
                    .expect("lowered lambda retained for multiple JS targets"),
                &pre_js.hoisted_functions,
                &pre_js.possible_required_modules,
                options,
                primary_output_path,
                primary_output_module_format,
                persistent_env_for_js.clone(),
                pre_js.jsx_preserve,
            )?
        } else {
            compile_js_program_for_output_owned(
                lowered_lambda
                    .take()
                    .expect("lowered lambda consumed by single JS target"),
                &pre_js.hoisted_functions,
                &pre_js.possible_required_modules,
                options,
                primary_output_path,
                primary_output_module_format,
                persistent_env_for_js.clone(),
                pre_js.jsx_preserve,
            )?
        }
    };
    if !options.skip_js_render {
        check_module_path_resolution_errors(
            &program,
            &module_path_resolver,
            options.source_filename.as_deref().unwrap_or("_none_"),
        )?;
    }
    let is_pure = program.side_effect.is_none();
    if let Some(hook) = metadata_ready.as_deref_mut() {
        hook(InProcessJsMetadataReady {
            is_pure,
            cmj_export_constants: std::mem::take(&mut cmj_export_constants),
            cmj_export_arities: std::mem::take(&mut cmj_export_arities),
            cmj_export_lambdas: std::mem::take(&mut cmj_export_lambdas),
            hoisted_exports: pre_js.hoisted_exports.clone(),
            pers_struct: pre_js.pers_struct.take(),
            new_alias_rewrites: std::mem::take(&mut pre_js.new_alias_rewrites),
        })?;
    }
    let mut rendered_programs = if options.skip_js_render {
        crate::js_ir::dispose_deps_program_nonrecursive(program);
        Vec::new()
    } else {
        let mut rendered_programs = vec![(
            primary_target.map(|target| target.path.clone()),
            program,
            module_path_resolver,
        )];
        for target in js_targets.iter().skip(1) {
            let (program, module_path_resolver, _, _, _) = compile_js_program_for_output(
                lowered_lambda
                    .as_ref()
                    .expect("lowered lambda retained for secondary JS targets"),
                &pre_js.hoisted_functions,
                &pre_js.possible_required_modules,
                options,
                Some(&target.path),
                Some(target.module_format),
                persistent_env_for_js.clone(),
                pre_js.jsx_preserve,
            )?;
            check_module_path_resolution_errors(
                &program,
                &module_path_resolver,
                options.source_filename.as_deref().unwrap_or("_none_"),
            )?;
            rendered_programs.push((Some(target.path.clone()), program, module_path_resolver));
        }
        rendered_programs
    };

    let (js, js_outputs) = crate::timing::measure(crate::timing::Phase::Codegen, || {
        let _phase = info_span!(
            "compiler.js_print",
            skip_js_render = options.skip_js_render,
            rendered_programs = rendered_programs.len()
        )
        .entered();
        if options.skip_js_render {
            (String::new(), Vec::new())
        } else {
            let (primary_path, primary_program, primary_resolver) = rendered_programs.remove(0);
            let (mut primary_js, primary_source_map) = render_js_program(
                &primary_program,
                &primary_resolver,
                &pre_js.file_directives,
                pre_js.debug,
                pre_js.jsx_preserve,
                options,
                primary_path.as_deref(),
                pre_js.source_file_names.clone(),
            );
            let mut js_outputs = Vec::new();
            let js = if let Some(path) = primary_path {
                js_outputs.push(JsOutput {
                    path,
                    code: std::mem::take(&mut primary_js),
                    source_map: primary_source_map,
                });
                crate::js_ir::dispose_deps_program_nonrecursive(primary_program);
                String::new()
            } else {
                crate::js_ir::dispose_deps_program_nonrecursive(primary_program);
                primary_js
            };
            for (path, program, module_path_resolver) in rendered_programs {
                let Some(path) = path else {
                    crate::js_ir::dispose_deps_program_nonrecursive(program);
                    continue;
                };
                let (code, source_map) = render_js_program(
                    &program,
                    &module_path_resolver,
                    &pre_js.file_directives,
                    pre_js.debug,
                    pre_js.jsx_preserve,
                    options,
                    Some(&path),
                    pre_js.source_file_names.clone(),
                );
                crate::js_ir::dispose_deps_program_nonrecursive(program);
                js_outputs.push(JsOutput {
                    path,
                    code,
                    source_map,
                });
            }
            (js, js_outputs)
        }
    });
    Ok(InProcessCompileResult {
        js_output: js,
        js_outputs,
        signature: pre_js.signature,
        pers_struct: pre_js.pers_struct,
        new_alias_rewrites: pre_js.new_alias_rewrites,
        is_pure,
        cmj_export_constants,
        cmj_export_arities,
        cmj_export_lambdas,
        hoisted_exports: pre_js.hoisted_exports,
        typed_tree_sexp: pre_js.typed_tree_sexp,
        raw_lambda_sexp: pre_js.raw_lambda_sexp,
        lambda_sexp: pre_js.lambda_sexp,
        dumps: pre_js.dumps,
        warnings: pre_js.warnings,
    })
}

pub fn typecheck_interface_in_process(
    source: &str,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> Result<InProcessInterfaceResult> {
    let mut parser = Parser::new(filename, source);
    let signature = module::parse_signature(&mut parser);
    if parser.has_errors() {
        return Err(anyhow!(
            "Parse failed with {} error(s)",
            parser.diagnostics().len()
        ));
    }
    let frontend_warnings =
        ppx::collect_leading_builtin_warning_signature_attributes(&signature, parser.arena());
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_signature_attribute_specs(&signature, parser.arena());
    let _ = emit_ppx_warnings(
        parser.arena(),
        source,
        filename,
        options,
        &frontend_warnings,
    );
    let config_processing = validate_file_config_from_signature(
        &signature,
        parser.arena(),
        &warning_config_for_options_and_leading_attrs(options, &frontend_warning_specs),
    );
    for (warning, config) in config_processing
        .warnings
        .iter()
        .chain(config_processing.late_warnings.iter())
    {
        let _ = emit_ppx_warnings_with_config(
            parser.arena(),
            source,
            filename,
            config,
            std::slice::from_ref(warning),
        );
    }
    if let Some(err) = config_processing.error {
        return Err(config_payload_error_to_anyhow(
            err,
            parser.arena(),
            source,
            filename,
        ));
    }
    let signature = preprocess_signature_for_typecheck_with_source(
        signature,
        options,
        parser.arena_mut(),
        source,
        filename,
        &mut Vec::new(),
    )?;
    parser.arena_mut().reserve_typecheck_synthetic_capacity();

    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    typecheck_preprocessed_signature_in_process(
        parser.arena(),
        &signature,
        filename,
        module_name,
        options,
        registry,
    )
}

pub fn typecheck_preprocessed_signature_in_process(
    arena: &crate::parse_arena::ParseArena,
    signature: &Signature,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> Result<InProcessInterfaceResult> {
    let _span = info_span!(
        "compiler.in_process_signature",
        module = %module_name,
        file = %filename
    )
    .entered();
    let original_alias_count = registry.alias_rewrite_len();
    let file_config = extract_file_config_from_signature(signature, arena);
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_signature_attribute_specs(signature, arena);

    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    let mut tctx = TypeCheckContext::new(&type_ctx, arena);
    tctx.experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
    tctx.transparent_modules = options.transparent_modules;
    apply_warning_options(&mut tctx, options);
    // Ppx_entry.rewrite_* (ppx_entry.ml:28, 47) applies the leading warning
    // attributes; compiling a preprocessed `.ast` does not run it again.
    if !options.frontend_already_reported {
        apply_leading_warning_attribute_options(&mut tctx, &frontend_warning_specs);
    }
    apply_file_config_warning_options(&mut tctx, &file_config);
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::from_registry(registry);
    pers_env.set_visible_package_roots(options.visible_package_roots.clone());
    let (load_path, load_path_display) = shared_load_path_with_display(options);
    type_ctx.set_load_paths_shared(load_path.clone());
    pers_env.set_load_path_shared(load_path, load_path_display);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_jsx_module(options.jsx_module.clone());
    pers_env.set_nopervasives(options.nopervasives);
    pers_env.set_compiling_module(Some(module_name.to_string()));
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        Some(module_name),
    );

    tctx.set_persistent_env(pers_env);

    // Diagnostics are reported against the source file, read only when
    // there is something to report.
    let source_cell = std::cell::OnceCell::new();
    let source = || -> &str { source_cell.get_or_init(|| read_in_process_source(filename)) };

    let typed = crate::timing::measure(crate::timing::Phase::Typecheck, || {
        let _phase = info_span!("compiler.type_signature").entered();
        transl_signature(&mut tctx, &env, arena, signature)
    });
    let typed_signature = match typed {
        Ok(typed_signature) => typed_signature,
        Err(e) => {
            // As in the file compile: the warnings reported so far precede
            // the error report.
            tctx.drain_open_slot_uses();
            let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
            let suppress_info_style =
                !tctx.warnings.is_empty() && !crate::parser::code_frame::should_enable_color();
            if let Some(error) = tctx
                .persistent_env
                .as_ref()
                .and_then(|persistent_env| persistent_env.last_error())
            {
                return Err(prefix_diagnostic(
                    &warnings,
                    persistent_env_error_to_anyhow(error, filename),
                ));
            }
            return Err(prefix_diagnostic(
                &warnings,
                type_mod_error_to_anyhow(
                    e,
                    &type_ctx,
                    arena,
                    source(),
                    filename,
                    suppress_info_style,
                ),
            ));
        }
    };
    let unit_reads = if options.collect_unit_reads {
        crate::types::unit_reads::signature_reads(
            &type_ctx,
            &typed_signature,
            &options.open_modules,
        )
    } else {
        Vec::new()
    };
    // js_implementation.ml:62: `ignore (Includemod.signatures initial_env sg
    // sg)`, which marks the declarations of the interface used.
    let sig_type =
        crate::types::typemod::decl_signature_from_typed_signature(&typed_signature, arena);
    let _ = crate::types::includemod::compunit(
        &type_ctx, &env, filename, &sig_type, filename, &sig_type,
    );
    // js_implementation.ml:64 `Delayed_checks.force_delayed_checks ()`.
    tctx.flush_value_usage_checks();
    let warnings = format_type_warnings_lazy(arena, &source, filename, &tctx.warnings);
    if type_warnings_have_errors(&tctx.warnings) {
        return Err(UserDiagnostic::new(warnings, 2).into());
    }
    let mut dumps: Vec<(DumpKind, String)> = Vec::new();
    for kind in [DumpKind::TypedTree, DumpKind::TypedTreeLocs] {
        if options.dumps.contains(&kind) {
            let mut buf = Vec::new();
            let _ = if kind == DumpKind::TypedTree {
                print_typed_signature(arena, &type_ctx, &typed_signature, &mut buf)
            } else {
                print_typed_signature_with_locs(arena, &type_ctx, &typed_signature, &mut buf)
            };
            dumps.push((kind, latin1_dump(buf)));
        }
    }
    let gentype_ignore_interface = options.gentype_config.is_some()
        && crate::gentype::annotation::signature_check_annotation(
            arena,
            &|_loc, attributes| {
                crate::gentype::annotation::get_attribute_payload(
                    arena,
                    crate::gentype::annotation::tag_is_gentype_ignore_interface,
                    attributes,
                )
                .is_some()
            },
            &typed_signature,
        );
    if !gentype_ignore_interface {
        process_gentype_typed_artifact_if_enabled(
            options,
            crate::gentype::main::TypedArtifactAnnots::Interface(&typed_signature),
            arena,
            &type_ctx,
            filename,
            module_name,
            true,
        )?;
    }
    let decl_signature =
        crate::types::typemod::decl_signature_from_typed_signature(&typed_signature, arena);

    let typed_module_type = crate::types::typedtree::ModuleType {
        mty_desc: crate::types::typedtree::ModuleTypeDesc::Tmty_signature(typed_signature),
        mty_type: crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(decl_signature)),
        mty_env: crate::types::typedtree::EnvRef(0),
        mty_loc: crate::parse_arena::LocIdx(0),
        mty_attributes: crate::parser::ast::Attributes::new(),
    };
    let published_signature =
        match crate::types::typemod::decl_module_type_from_typed(&typed_module_type) {
            Some(crate::types::decl::ModuleType::MtySignature(sig)) => {
                std::sync::Arc::unwrap_or_clone(sig)
            }
            _ => {
                return Err(anyhow!(
                    "Failed to extract interface signature from typed tree"
                ));
            }
        };

    // js_implementation.ml:66-70 saves the interface through
    // `Env.save_signature`, whose `Subst.for_saving` copy renames the bound
    // identifiers (env.ml:1886-1892). In-process builds write no `.cmi`, but
    // the copy still takes its stamps, as in OCaml.
    if let crate::types::typedtree::ModuleTypeDesc::Tmty_signature(_) = &typed_module_type.mty_desc
    {
        saved_signature_copy(&type_ctx, &published_signature);
    }

    let mut internal_env = tctx
        .persistent_env
        .take()
        .unwrap_or_else(PersistentEnv::new);

    // js_implementation.ml:66: `Builtin_attributes.deprecated_of_sig ast`.
    // The raw `ps_sig` of the saved interface (env.ml:1949-1952,
    // env.ml:669-678), before registration substitutes component paths in
    // place. The implementation is checked against it (typemod.ml:1742-1758),
    // as the file compile checks against the `.cmi`.
    let raw_signature = {
        let mut raw = crate::types::typecore::copy_lookup_signature_for_subst(
            &published_signature,
            &type_ctx,
        );
        // The check reads the signature as saved in the `.cmi`
        // (env.ml:1949-1952 reads the file back), so drop the same locations.
        if !options.keep_locs {
            strip_saved_signature_locations(&mut raw);
        }
        strip_saved_extension_locations(&mut raw);
        std::sync::Arc::new(raw)
    };
    let mut saved_signature = published_signature.clone();
    if !options.keep_locs {
        strip_saved_signature_locations(&mut saved_signature);
    }
    strip_saved_extension_locations(&mut saved_signature);
    let crcs = Vec::new();
    internal_env.register_in_memory_signature(
        module_name,
        saved_signature,
        filename,
        crate::types::typemod::deprecated_of_sig(arena, signature),
        crcs,
        &type_ctx,
    );
    type_ctx.register_raw_module_sig(module_name, raw_signature);

    let (pers_struct, new_alias_rewrites) = internal_env.extract_module_update(
        module_name,
        original_alias_count,
        &type_ctx,
        Some(arena),
    );

    Ok(InProcessInterfaceResult {
        signature: published_signature,
        pers_struct,
        new_alias_rewrites,
        gentype_ignore_interface,
        dumps,
        warnings,
        loaded_units: internal_env.loaded_units(),
        unit_reads,
    })
}

/// Typecheck a `.res` implementation file in-process.
/// Mirrors `typecheck_interface_in_process` but parses a structure (not a
/// signature) and uses `type_structure`. No lambda or JS conversion is
/// performed; the result is the module's published signature plus a
/// portable `PersStruct` for the shared registry.
pub fn typecheck_implementation_in_process(
    source: &str,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
) -> Result<InProcessInterfaceResult> {
    let original_alias_count = registry.alias_rewrite_len();

    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);
    if parser.has_errors() {
        return Err(anyhow!(
            "Parse failed with {} error(s)",
            parser.diagnostics().len()
        ));
    }
    let file_config = extract_file_config_from_structure(&structure, parser.arena());
    let frontend_warning_specs =
        ppx::collect_leading_builtin_warning_attribute_specs(&structure, parser.arena());
    // js_implementation.ml:130 `no_export` after parsing.
    let structure =
        crate::binary_ast::writer::apply_no_export_config(parser.arena_mut(), structure);
    parser.arena_mut().reserve_typecheck_synthetic_capacity();

    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    tctx.experimental_let_unwrap = options.experimental_let_unwrap || file_config.let_unwrap;
    tctx.transparent_modules = options.transparent_modules;
    apply_warning_options(&mut tctx, options);
    // Ppx_entry.rewrite_* (ppx_entry.ml:28, 47) applies the leading warning
    // attributes; compiling a preprocessed `.ast` does not run it again.
    if !options.frontend_already_reported {
        apply_leading_warning_attribute_options(&mut tctx, &frontend_warning_specs);
    }
    apply_file_config_warning_options(&mut tctx, &file_config);
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::from_registry(registry);
    pers_env.set_visible_package_roots(options.visible_package_roots.clone());
    let (load_path, load_path_display) = shared_load_path_with_display(options);
    type_ctx.set_load_paths_shared(load_path.clone());
    pers_env.set_load_path_shared(load_path, load_path_display);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_jsx_module(options.jsx_module.clone());
    pers_env.set_nopervasives(options.nopervasives);
    pers_env.set_compiling_module(Some(module_name.to_string()));
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        Some(module_name),
    );

    tctx.set_persistent_env(pers_env);

    let (typed_structure, _final_env) =
        crate::timing::measure(crate::timing::Phase::Typecheck, || {
            type_structure(&mut tctx, &env, parser.arena(), &structure)
                .map_err(|e| anyhow!("Type checking failed: {e:?}"))
        })?;
    let _ = has_interface; // post-typecheck constraint pass not ported here

    let published_signature =
        crate::types::includemod::simplify_signature(&typed_structure.str_type);

    let mut internal_env = tctx
        .persistent_env
        .take()
        .unwrap_or_else(PersistentEnv::new);

    // typemod.ml:1778: `Builtin_attributes.deprecated_of_str ast`.
    internal_env.register_in_memory_signature(
        module_name,
        published_signature.clone(),
        filename,
        crate::types::typemod::deprecated_of_str(parser.arena(), &structure),
        Vec::new(),
        &type_ctx,
    );

    let (pers_struct, new_alias_rewrites) = internal_env.extract_module_update(
        module_name,
        original_alias_count,
        &type_ctx,
        Some(parser.arena()),
    );

    Ok(InProcessInterfaceResult {
        signature: published_signature,
        pers_struct,
        new_alias_rewrites,
        gentype_ignore_interface: false,
        dumps: Vec::new(),
        warnings: String::new(),
        loaded_units: internal_env.loaded_units(),
        unit_reads: Vec::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::build_name_based_coercion;
    use super::extract_file_directives_from_structure;
    use super::max_lambda_input_stamp;
    use super::normalize_load_path_entry;
    use crate::ident::{Ident, IdentFlags};
    use crate::location::Location;
    use crate::parse_arena::{LidentIdx, LocIdx, Located};
    use crate::parser::ast::{Attributes, RecFlag};
    use crate::parser::{Parser, module};
    use crate::types::decl::{
        AliasPresence, ModuleDeclaration, ModuleType, RecStatus, SignatureItem, ValueKind,
    };
    use crate::types::path::Path as TypePath;
    use crate::types::typedtree::ModuleCoercion;
    use crate::types::typedtree::{
        EnvRef, Expression, ExpressionDesc, Pattern, PatternDesc, Structure, StructureItem,
        StructureItemDesc, ValueBinding,
    };
    use crate::types::{TypeExprRef, ValueDescription};
    use std::path::PathBuf;

    #[test]
    fn max_lambda_input_stamp_includes_typed_paths_and_signature_items() {
        let binding_id = Ident::new("x", 4100, IdentFlags::NONE);
        let expr_path_id = Ident::new("ExprPath", 4200, IdentFlags::NONE);
        let sig_module_id = Ident::new("SigModule", 4300, IdentFlags::NONE);
        let sig_alias_id = Ident::new("SigAlias", 4400, IdentFlags::NONE);

        let binding = ValueBinding {
            vb_pat: Pattern {
                pat_desc: PatternDesc::Tpat_var(binding_id, Located::mknoloc("x".to_string())),
                pat_loc: LocIdx::none(),
                pat_extra: Default::default(),
                pat_type: TypeExprRef::null(),
                pat_env: EnvRef(0),
                pat_attributes: Attributes::new(),
            },
            vb_expr: Expression {
                exp_desc: ExpressionDesc::Texp_constant(crate::types::typedtree::Constant::Int(1)),
                exp_loc: LocIdx::none(),
                exp_extra: Default::default(),
                exp_type: TypeExprRef::null(),
                exp_env: EnvRef(0),
                exp_attributes: Attributes::new(),
            },
            vb_attributes: Attributes::new(),
            vb_loc: LocIdx::none(),
        };

        let eval_expr = Expression {
            exp_desc: ExpressionDesc::Texp_ident(
                TypePath::pident(expr_path_id),
                Located::mknoloc(LidentIdx(0)),
                std::sync::Arc::new(ValueDescription {
                    val_type: TypeExprRef::null(),
                    val_kind: ValueKind::ValReg,
                    val_loc: Location::none(),
                    val_attributes: Vec::new(),
                    val_path: None,
                }),
            ),
            exp_loc: LocIdx::none(),
            exp_extra: Default::default(),
            exp_type: TypeExprRef::null(),
            exp_env: EnvRef(0),
            exp_attributes: Attributes::new(),
        };

        let structure = Structure {
            str_items: vec![
                StructureItem {
                    str_desc: StructureItemDesc::Tstr_value(RecFlag::Nonrecursive, vec![binding]),
                    str_loc: LocIdx::none(),
                    str_env: EnvRef(0),
                },
                StructureItem {
                    str_desc: StructureItemDesc::Tstr_eval(eval_expr, Attributes::new()),
                    str_loc: LocIdx::none(),
                    str_env: EnvRef(0),
                },
            ],
            str_type: vec![SignatureItem::SigModule(
                sig_module_id,
                ModuleDeclaration {
                    md_type: ModuleType::MtyIdent(TypePath::pident(sig_alias_id)),
                    md_attributes: Vec::new(),
                    md_loc: Location::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            )],
            str_final_env: EnvRef(0),
        };

        assert_eq!(max_lambda_input_stamp(&structure), 4400);
    }

    #[test]
    fn normalize_load_path_entry_expands_relative_paths_against_cwd() {
        let cwd = std::path::Path::new("/repo/tests/tests/lib/bs");
        let normalized =
            normalize_load_path_entry(std::path::Path::new("../ocaml"), None, Some(cwd));
        assert_eq!(normalized, PathBuf::from("/repo/tests/tests/lib/ocaml"));
    }

    #[test]
    fn name_based_coercion_keeps_same_absent_module_alias_identity() {
        let module_id = Ident::create_local("Alias");
        let target_id = Ident::create_persistent("Alias_Target");
        let md = ModuleDeclaration {
            md_type: ModuleType::MtyAlias(AliasPresence::MtaAbsent, TypePath::pident(target_id)),
            md_attributes: vec![],
            md_loc: Location::none(),
            md_path: None,
        };
        let sig = vec![SignatureItem::SigModule(module_id, md, RecStatus::TrecNot)];

        let coercion = build_name_based_coercion(&sig, &sig);

        assert!(matches!(coercion, ModuleCoercion::Tcoerce_none));
    }

    #[test]
    fn normalize_load_path_entry_expands_plus_paths_from_stdlib() {
        let normalized = normalize_load_path_entry(
            std::path::Path::new("+compiler-libs"),
            Some(std::path::Path::new("/runtime/lib/ocaml")),
            Some(std::path::Path::new("/repo")),
        );
        assert_eq!(
            normalized,
            PathBuf::from("/runtime/lib/ocaml/compiler-libs")
        );
    }

    #[test]
    fn release_optional_default_lowering_compiles_without_arena_aliasing() {
        let source = r#"
let labelled = (~x, ~y=2, ()) => x
let optional = (~x=?, ()) => x
"#;

        let output = super::compile_source_to_js(source, "core_patterns_optional_defaults.res")
            .expect("optional-default functions should compile");
        assert!(output.contains("function labelled"));
        assert!(output.contains("function optional"));
    }

    #[test]
    fn tuple_let_before_nested_optional_default_keeps_stamp_ownership() {
        const SOURCE: &str = r#"
let pair = x => (x, _ => ())

let makeUpdater = initialValue => {
  let (state, setState) = pair(0)
  let (value, setValue) = pair(initialValue)
  let updateValue = (~persist=true, newValue) => {
    if persist {
      setState(newValue)
    }
    setValue(value)
  }
  (state, value, updateValue)
}
"#;
        const CASES: [(&str, i32); 2] = [("fresh_worker_tls", 1000), ("reused_worker_tls", 8192)];

        let mut observations = Vec::new();
        for (case, tls_start) in CASES {
            let observation = std::thread::spawn(move || {
                Ident::set_current_time(tls_start);
                let mut trace = super::PreJsDiscriminatorTrace::default();
                let output = super::compile_source_to_js_with_trace(
                    SOURCE,
                    "hooks_settings_reduced.res",
                    &mut trace,
                )
                .expect("reduced Hooks stamp discriminator should compile");
                (case, tls_start, trace, output)
            })
            .join()
            .expect("owned discriminator thread should not panic");
            observations.push(observation);
        }

        // Preserve both complete traces before checking any invariant so a red
        // assertion still leaves the first execution evidence in test output.
        for (case, tls_start, trace, output) in &observations {
            eprintln!(
                "[hooks-prejs-discriminator] case={case} tls_start={tls_start} type_context_stamp={} raw_converter_stamp={} raw_max_stamp={}\n[raw]\n{}\n[lowered]\n{}\n[js-ir]\n{}\n[js]\n{}",
                trace.type_context_stamp,
                trace.raw_converter_stamp,
                trace.raw_max_stamp,
                trace.raw_lambda,
                trace.lowered_lambda,
                trace.js_program,
                output
            );
        }

        for (case, _, trace, output) in observations {
            assert!(
                trace.raw_max_stamp <= trace.raw_converter_stamp,
                "{case}: RawLambda contains an identifier above the reported raw stamp (raw_max={}, reported={}, type_context={})",
                trace.raw_max_stamp,
                trace.raw_converter_stamp,
                trace.type_context_stamp
            );
            // The typechecker names the optional parameter `persistOpt`
            // (typecore.ml `type_function`'s structural optional default).
            assert!(
                trace.raw_lambda.contains("persistOpt/"),
                "{case}: raw function lost the optional source parameter"
            );
            assert!(
                output.contains("(persistOpt, newValue)"),
                "{case}: JS-visible optional parameter was remapped"
            );
        }
    }

    #[test]
    fn release_synthetic_record_labels_and_qualified_paths_are_stable() {
        let source = r#"
module M = {
  type t = {x: int, y: int, optional?: string}
  let value = {x: 1, y: 2}
}

let extract = ({M.x, y: _}: M.t) => x
let value: M.t = {M.x: 3, y: 4}
"#;

        let output = super::compile_source_to_js(source, "synthetic_record_labels.res")
            .expect("synthetic record labels and qualified paths should compile");
        assert!(output.contains("function extract"));
        assert!(output.contains("value"));
    }

    #[test]
    fn extract_file_directives_preserves_source_order() {
        let mut parser = Parser::new(
            "directives.res",
            "@@directive(\"first directive;\")\n@@directive(\"second directive;\")\nlet a = 1",
        );
        let structure = module::parse_structure(&mut parser);

        assert!(!parser.has_errors());
        assert_eq!(
            extract_file_directives_from_structure(&structure, parser.arena()).unwrap(),
            vec![
                "first directive;".to_string(),
                "second directive;".to_string()
            ]
        );
    }
}
