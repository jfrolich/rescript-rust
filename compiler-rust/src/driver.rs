//! Compiler driver utilities.
//!
//! This module wires together parsing, type-checking, Lambda conversion, and
//! JS IR codegen to produce JavaScript output.

use std::ffi::OsString;
use std::fmt;
use std::path::{Component, Path as FsPath, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};

use ahash::AHashSet;
use anyhow::{Context, Result, anyhow};
use tracing::info_span;

use crate::binary_ast::ppx;
use crate::cmi::persistent_env::{
    CmjExportArity, CmjExportConstant, ModuleRegistry, PersistentEnv,
};
use crate::cmi::portable_types::PortablePersStruct;
use crate::context::IdGenerator;
use crate::js_ir::{
    DepsProgram, Kind, ModuleFormat, ModuleId, ModulePathResolver,
    print_deps_program_with_directives_and_options,
};
use crate::lambda::lam_compile::LambdaCompiler;
use crate::location::Location;
use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::{
    Attribute, Constant, Expression, ModuleExpr, ModuleExprDesc, Payload, Signature,
    SignatureItemDesc, Structure, StructureItemDesc,
};
use crate::parser::{Parser, code_frame, jsx_ppx, module};
use crate::types::sexp_typedtree::{
    print_typed_signature, print_typed_signature_with_locs, print_typed_structure,
    print_typed_structure_with_locs,
};
use crate::types::typecore::TypeCoreError;
use crate::types::typemod::TypeModError;
use crate::types::{
    ArgLabel as TypeArgLabel, TypeCheckContext, TypeClashContext, TypeContext, TypeDesc,
    TypeExprRef, initial_env, transl_signature, type_structure,
};

// OCaml's Predef sets `Ident.set_current_time 999`. OCaml's Parmatch.extra_pat
// then eagerly creates Ident.create "+" consuming stamp 1000.
// We match this by starting at 999 and consuming one stamp.
const OCAML_NON_PREDEF_STAMP_START: i32 = 999;
static SKIP_CLI_CLEANUP: AtomicBool = AtomicBool::new(false);

#[derive(Debug)]
pub struct UserDiagnostic {
    output: String,
    exit_code: i32,
}

impl UserDiagnostic {
    fn new(output: String, exit_code: i32) -> Self {
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

/// WASM-safe timing: native returns `Instant::now()`, WASM returns `None`
/// (Instant::now panics on WASM since time isn't implemented there).
#[inline]
fn phase_now() -> Option<std::time::Instant> {
    #[cfg(not(target_arch = "wasm32"))]
    {
        Some(std::time::Instant::now())
    }
    #[cfg(target_arch = "wasm32")]
    {
        None
    }
}

#[inline]
fn phase_elapsed_ms(t: Option<std::time::Instant>) -> u128 {
    t.map(|t| t.elapsed().as_millis()).unwrap_or(0)
}

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

fn has_react_component_attr(attrs: &[Attribute], arena: &crate::parse_arena::ParseArena) -> bool {
    attrs.iter().any(|attr| {
        matches!(
            arena.get_string(attr.0.txt),
            "react.component" | "jsx.component"
        )
    })
}

fn has_react_component_with_props_attr(
    attrs: &[Attribute],
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    attrs.iter().any(|attr| {
        matches!(
            arena.get_string(attr.0.txt),
            "react.componentWithProps" | "jsx.componentWithProps"
        )
    })
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
        ExtensionConstructorKind, FunctionParam, FunctionParamPattern, IncludeDescription,
        MethKind, ModuleBinding, ModuleCoercion, ModuleExpr, ModuleExprDesc, ModuleType,
        ModuleTypeConstraint, ModuleTypeDeclaration, ModuleTypeDesc, OpenDeclaration, PatExtra,
        Pattern, PatternDesc, RowFieldDesc, Structure, StructureItemDesc,
        TypedConstructorArguments, TypedCoreType, TypedCoreTypeDesc, TypedSignature,
        TypedSignatureItemDesc, TypedTypeDeclaration, TypedTypeKind, TypedValueDescription,
        ValueBinding, WithConstraint,
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
            TypedCoreTypeDesc::Ttyp_arrow(arg, ret, _) => {
                visit_typed_core_type(max_stamp, &arg.typ);
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
            PatternDesc::Tpat_record(fields, _) => {
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
                PatExtra::Tpat_type(path, _) | PatExtra::Tpat_open(path, _, _) => {
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
        visit_ident(max_stamp, &param.param_id);
        if let Some(default) = &param.default {
            visit_expression(max_stamp, default);
        }
        match &param.pat {
            FunctionParamPattern::Simple(pattern) => visit_pattern(max_stamp, pattern),
            FunctionParamPattern::Nested(params) => {
                for nested in params {
                    visit_function_param(max_stamp, nested);
                }
            }
        }
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
                for case in body {
                    visit_case(max_stamp, case);
                }
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
            ExpressionDesc::Texp_send(expr, meth, maybe_arg) => {
                visit_expression(max_stamp, expr);
                if let MethKind::Tmeth_val(id) = meth {
                    visit_ident(max_stamp, id);
                }
                if let Some(arg) = maybe_arg {
                    visit_expression(max_stamp, arg);
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
                ExpExtra::Texp_constraint(core_type) | ExpExtra::Texp_coerce(core_type) => {
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
            DeclTypeKind::TypeVariant(constructors) => {
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
        ED::Pexp_constant(c) => matches!(&**c, Constant::String(s, _) if s == value),
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
        ED::Pexp_construct(_, arg) => arg
            .as_ref()
            .is_some_and(|arg| expression_has_string_literal(arena.get_expr(*arg), value, arena)),
        ED::Pexp_variant(inner) => {
            let (_, arg) = &**inner;
            arg.as_ref().is_some_and(|arg| {
                expression_has_string_literal(arena.get_expr(*arg), value, arena)
            })
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
        ED::Pexp_send(inner) => {
            let (expr, _) = &**inner;
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        ED::Pexp_setfield(inner) => {
            let (lhs, _, rhs) = &**inner;
            expression_has_string_literal(arena.get_expr(*lhs), value, arena)
                || expression_has_string_literal(arena.get_expr(*rhs), value, arena)
        }
        ED::Pexp_sequence(lhs, rhs) | ED::Pexp_while(lhs, rhs) => {
            expression_has_string_literal(arena.get_expr(*lhs), value, arena)
                || expression_has_string_literal(arena.get_expr(*rhs), value, arena)
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
        ED::Pexp_ident(_)
        | ED::Pexp_break
        | ED::Pexp_continue
        | ED::Pexp_jsx_element(_)
        | ED::Pexp_inline_for(_)
        | ED::Pexp_comptime_typeinfo(_)
        | ED::Pexp_comptime_field(_)
        | ED::Pexp_comptime_compile_error(_)
        | ED::Pexp_comptime_typename(_)
        | ED::Pexp_comptime_record(_)
        | ED::Pexp_comptime_variant(_)
        | ED::Pexp_comptime_build_variant(_)
        | ED::Pexp_comptime_variant_case(_)
        | ED::Pexp_comptime_build_record(_)
        | ED::Pexp_comptime_record_field(_) => false,
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
        PD::Ppat_constant(c) => matches!(&**c, Constant::String(s, _) if s == value),
        PD::Ppat_alias(inner, _) | PD::Ppat_exception(inner) | PD::Ppat_open(_, inner) => {
            pattern_has_string_literal(arena.get_pat(*inner), value, arena)
        }
        PD::Ppat_constraint(inner) => {
            let (inner_pat, _) = &**inner;
            pattern_has_string_literal(arena.get_pat(*inner_pat), value, arena)
        }
        PD::Ppat_tuple(items) | PD::Ppat_array(items) => items
            .iter()
            .any(|item| pattern_has_string_literal(arena.get_pat(*item), value, arena)),
        PD::Ppat_construct(_, Some(arg)) => {
            pattern_has_string_literal(arena.get_pat(*arg), value, arena)
        }
        PD::Ppat_variant(inner) => {
            let (_, arg) = &**inner;
            arg.as_ref()
                .is_some_and(|arg| pattern_has_string_literal(arena.get_pat(*arg), value, arena))
        }
        PD::Ppat_or(lhs, rhs) => {
            pattern_has_string_literal(arena.get_pat(*lhs), value, arena)
                || pattern_has_string_literal(arena.get_pat(*rhs), value, arena)
        }
        PD::Ppat_record(inner) => {
            let (rows, _) = &**inner;
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

fn module_expr_needs_jsx_rewrite(
    module_expr: &ModuleExpr,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    match &*module_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(structure) => structure_needs_jsx_rewrite(structure, arena),
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_, _, body) = &**inner;
            module_expr_needs_jsx_rewrite(arena.get_mod_expr(*body), arena)
        }
        ModuleExprDesc::Pmod_apply(lhs, rhs) => {
            module_expr_needs_jsx_rewrite(arena.get_mod_expr(*lhs), arena)
                || module_expr_needs_jsx_rewrite(arena.get_mod_expr(*rhs), arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, _) => {
            module_expr_needs_jsx_rewrite(arena.get_mod_expr(*inner), arena)
        }
        _ => false,
    }
}

fn structure_needs_jsx_rewrite(
    structure: &Structure,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    structure.iter().any(|item| match &*item.pstr_desc {
        // External @react.component declarations need JSX PPX lowering.
        StructureItemDesc::Pstr_primitive(vd) => {
            has_react_component_attr(&vd.pval_attributes, arena)
        }
        StructureItemDesc::Pstr_value(inner) => {
            let (_, bindings) = &**inner;
            bindings.iter().any(|vb| {
                has_react_component_attr(&vb.pvb_attributes, arena)
                    || has_react_component_with_props_attr(&vb.pvb_attributes, arena)
            })
        }
        StructureItemDesc::Pstr_module(mb) => {
            module_expr_needs_jsx_rewrite(arena.get_mod_expr(mb.pmb_expr), arena)
        }
        StructureItemDesc::Pstr_recmodule(mbs) => mbs
            .iter()
            .any(|mb| module_expr_needs_jsx_rewrite(arena.get_mod_expr(mb.pmb_expr), arena)),
        StructureItemDesc::Pstr_include(incl) => {
            module_expr_needs_jsx_rewrite(arena.get_mod_expr(incl.pincl_mod), arena)
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
    /// JSX version from CLI `-bs-jsx` (e.g. 4). When set, enables JSX PPX rewrite.
    pub jsx_version: Option<i32>,
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
    /// When true, do not implicitly open Pervasives and Stdlib.
    pub nopervasives: bool,
    /// The module name being compiled. Used to filter self-opens.
    pub module_name: Option<String>,
    /// Current npm package name from `-bs-package-name`.
    pub package_name: Option<String>,
    /// Compile the runtime package (`-make-runtime`).
    pub make_runtime: bool,
    /// When true, `compile_source_in_process` captures the typed tree,
    /// raw lambda, and lambda sexps for display (used by the playground).
    pub capture_intermediates: bool,
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
            source_filename: None,
            output_path: None,
            output_module_format: None,
            js_output_targets: Vec::new(),
            jsx_version: None,
            experimental_let_unwrap: false,
            jsx_preserve: false,
            debug: false,
            no_version_header: false,
            check_div_by_zero: true,
            cross_module_inline: false,
            no_assert_false: false,
            nopervasives: false,
            module_name: None,
            package_name: None,
            make_runtime: false,
            capture_intermediates: false,
            skip_js_render: false,
            publish_in_process_signature: true,
        }
    }
}

impl CompilerOptions {
    fn preserve_canonical_typedtree(&self) -> bool {
        self.dump_typed_sexp || self.dump_typed_sexp_locs || self.capture_intermediates
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

fn preprocess_signature_for_typecheck(
    signature: Signature,
    options: &CompilerOptions,
    arena: &mut crate::parse_arena::ParseArena,
) -> Result<Signature> {
    preprocess_signature_for_typecheck_inner(signature, options, arena)
        .map_err(|e| anyhow!("PPX rewrite failed: {e}"))
}

fn preprocess_signature_for_typecheck_with_source(
    signature: Signature,
    options: &CompilerOptions,
    arena: &mut crate::parse_arena::ParseArena,
    source: &str,
    filename: &str,
) -> Result<Signature> {
    preprocess_signature_for_typecheck_inner(signature, options, arena)
        .map_err(|e| ppx_error_to_anyhow(e, arena, source, filename))
}

fn preprocess_signature_for_typecheck_inner(
    signature: Signature,
    options: &CompilerOptions,
    arena: &mut crate::parse_arena::ParseArena,
) -> std::result::Result<Signature, ppx::PpxError> {
    let signature = if let Some(jsx_version) = options.jsx_version {
        jsx_ppx::transform_signature(signature, jsx_version, arena)
    } else {
        signature
    };

    ppx::rewrite_signature(&signature, arena)
}

fn ppx_error_to_anyhow(
    err: ppx::PpxError,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    if let Some(loc) = err.loc() {
        UserDiagnostic::new(
            format_compiler_error_report(arena, source, filename, loc, err.message_text()),
            2,
        )
        .into()
    } else {
        anyhow!("PPX rewrite failed: {err}")
    }
}

fn type_mod_error_to_anyhow(
    err: TypeModError,
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
) -> anyhow::Error {
    match &err {
        TypeModError::CoreError(TypeCoreError::UncurriedArityMismatch {
            loc,
            function_type,
            expected_arity,
            provided_arity,
            provided_args,
            use_fallback_message,
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
                *use_fallback_message,
            ),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::ExprTypeClash {
            loc,
            trace,
            context,
        }) => UserDiagnostic::new(
            format_expr_type_clash_report(type_ctx, arena, source, filename, *loc, trace, context),
            2,
        )
        .into(),
        TypeModError::CoreError(TypeCoreError::UnboundRecordField {
            loc,
            field_name,
            from_type,
        }) => UserDiagnostic::new(
            format_unbound_record_field_report(
                type_ctx,
                arena,
                source,
                filename,
                *loc,
                field_name,
                *from_type,
            ),
            2,
        )
        .into(),
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
        _ => anyhow!("Type checking failed: {err:?}"),
    }
}

fn format_compiler_error_report_from_location(
    source: &str,
    filename: &str,
    loc: &Location,
    message: &str,
) -> String {
    let mut output = String::new();

    output.push_str("\n  We've found a bug for you!\n");
    output.push_str("  ");
    output.push_str(&code_frame::format_location(
        filename,
        &loc.loc_start,
        &loc.loc_end,
    ));
    output.push_str("\n\n");
    output.push_str(&code_frame::print(source, &loc.loc_start, &loc.loc_end));
    output.push('\n');

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
    let start_pos = arena.loc_start(loc);
    let end_pos = arena.loc_end(loc);
    let mut output = String::new();

    output.push_str("\n  We've found a bug for you!\n");
    output.push_str("  ");
    output.push_str(&code_frame::format_location(filename, start_pos, end_pos));
    output.push_str("\n\n");
    output.push_str(&code_frame::print(source, start_pos, end_pos));
    output.push('\n');

    for line in message.lines() {
        output.push_str("  ");
        output.push_str(line);
        output.push('\n');
    }
    output.push('\n');
    output
}

fn format_compiler_error_report_raw_message(
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    message: &str,
) -> String {
    let start_pos = arena.loc_start(loc);
    let end_pos = arena.loc_end(loc);
    let mut output = String::new();

    output.push_str("\n  We've found a bug for you!\n");
    output.push_str("  ");
    output.push_str(&code_frame::format_location(filename, start_pos, end_pos));
    output.push_str("\n\n");
    output.push_str(&code_frame::print(source, start_pos, end_pos));
    output.push('\n');
    output.push_str(message);
    if !message.ends_with('\n') {
        output.push('\n');
    }
    output.push('\n');
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

    let missing_parameters = collect_expected_function_arguments(type_ctx, expected);
    let mut message = String::new();

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
        message.push_str(&format_type_expr(type_ctx, actual));
        message.push_str(RESET);
        message.push('\n');
        message.push_str("But you're using ");
        message.push_str(INFO);
        message.push_str("await");
        message.push_str(RESET);
        message.push_str(" on this expression, so it is expected to be of type:\n  ");
        message.push_str(INFO);
        message.push_str(&format_type_expr(type_ctx, expected));
        message.push_str(RESET);
        append_extra_type_clash_help(type_ctx, arena, source, loc, context, trace, &mut message);
        let message = format_await_type_clash_message(&message);
        return format_compiler_error_report_raw_message(arena, source, filename, loc, &message);
    }

    let (error_text, expected_text) = match context {
        Some(TypeClashContext::ArrayLiteral) => (
            "This array item has type: ",
            "But this array is expected to have items of type: ",
        ),
        Some(TypeClashContext::FunctionCall) => (
            "This has type: ",
            "But this function argument is expecting: ",
        ),
        Some(TypeClashContext::AssertCondition) => (
            "This has type: ",
            "But assertions must always be of type: ",
        ),
        _ => ("This has type: ", "But it's expected to have type: "),
    };

    message.push_str(error_text);
    message.push_str(ERROR);
    message.push_str(&format_type_expr(type_ctx, actual));
    message.push_str(RESET);
    message.push('\n');
    message.push_str(expected_text);
    message.push_str(INFO);
    message.push_str(&format_type_expr(type_ctx, expected));
    message.push_str(RESET);
    append_extra_type_clash_help(type_ctx, arena, source, loc, context, trace, &mut message);

    if matches!(context, Some(TypeClashContext::ArrayLiteral)) {
        let message = format_array_type_clash_message(&message);
        format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
    } else if type_clash_array_to_tuple(type_ctx, trace) {
        let message = format_type_clash_message_with_empty_blank_lines(&message);
        format_compiler_error_report_raw_message(arena, source, filename, loc, &message)
    } else {
        format_compiler_error_report(arena, source, filename, loc, &message)
    }
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
    }

    append_simple_conversion_help(type_ctx, trace, message);
}

fn type_clash_array_to_tuple(type_ctx: &TypeContext, trace: &[(TypeExprRef, TypeExprRef)]) -> bool {
    let Some((actual, expected)) = bottom_type_clash_aliases(trace).or_else(|| trace.first().copied()) else {
        return false;
    };

    let actual_is_array = match &*type_ctx.get_desc(type_ctx.repr(actual)) {
        TypeDesc::Tconstr { path, .. } => path.head_name() == "array",
        _ => false,
    };
    let expected_is_tuple = matches!(&*type_ctx.get_desc(type_ctx.repr(expected)), TypeDesc::Ttuple(_));

    actual_is_array && expected_is_tuple
}

fn suggested_array_to_tuple_rewrite(
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
) -> Option<String> {
    let start = arena.loc_start(loc).cnum as usize;
    let end = arena.loc_end(loc).cnum as usize;
    let text = source.get(start..end)?.trim();
    let inner = text.strip_prefix('[')?.strip_suffix(']')?;
    Some(format!("({inner})"))
}

fn append_simple_conversion_help(
    type_ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
    message: &mut String,
) {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let Some((actual, expected)) = bottom_type_clash_aliases(trace).or_else(|| trace.first().copied()) else {
        return;
    };
    let Some(actual_name) = simple_type_constr_name(type_ctx, actual) else {
        return;
    };
    let Some(expected_name) = simple_type_constr_name(type_ctx, expected) else {
        return;
    };
    let Some(converter) = simple_conversion(&actual_name, &expected_name) else {
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
        TypeDesc::Tarrow {
            arity: Some(arity),
            ..
        } => Some(*arity),
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

fn format_unbound_record_field_report(
    type_ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    filename: &str,
    loc: LocIdx,
    field_name: &str,
    from_type: Option<TypeExprRef>,
) -> String {
    const INFO: &str = "\x1b[1;33m";
    const RESET: &str = "\x1b[0m";

    let mut message = String::new();
    let from_type_desc = from_type.map(|ty| {
        let repr = type_ctx.repr(ty);
        (repr, type_ctx.get_desc(repr).clone())
    });

    match from_type_desc {
        Some((_, TypeDesc::Tconstr { path, .. })) if path.head_name() == "option" => {
            message.push_str("You're trying to access the record field ");
            message.push_str(INFO);
            message.push_str(field_name);
            message.push_str(RESET);
            message.push_str(", but the value you're trying to access it on is an ");
            message.push_str(INFO);
            message.push_str("option");
            message.push_str(RESET);
            message.push_str(".\n");
            message.push_str("You need to unwrap the option first before accessing the record field.\n");
            message.push('\n');
            message.push_str("Possible solutions:\n");
            message.push_str("- Use ");
            message.push_str(INFO);
            message.push_str("Option.map");
            message.push_str(RESET);
            message.push_str(" to transform the option: ");
            message.push_str(INFO);
            message.push_str("xx->Option.map(field => field.");
            message.push_str(field_name);
            message.push(')');
            message.push_str(RESET);
            message.push('\n');
            message.push_str("- Or use ");
            message.push_str(INFO);
            message.push_str("Option.getOr");
            message.push_str(RESET);
            message.push_str(" with a default: ");
            message.push_str(INFO);
            message.push_str("xx->Option.getOr(defaultRecord).");
            message.push_str(field_name);
            message.push_str(RESET);
        }
        Some((_, TypeDesc::Tconstr { path, .. })) if path.head_name() == "array" => {
            message.push_str("You're trying to access the record field ");
            message.push_str(INFO);
            message.push_str(field_name);
            message.push_str(RESET);
            message.push_str(", but the value you're trying to access it on is an ");
            message.push_str(INFO);
            message.push_str("array");
            message.push_str(RESET);
            message.push_str(".\n");
            message.push_str("You need to access an individual element of the array if you want to access an individual record field.");
        }
        Some((ty, TypeDesc::Tconstr { .. })) => {
            message.push_str("You're trying to access the record field ");
            message.push_str(INFO);
            message.push_str(field_name);
            message.push_str(RESET);
            message.push_str(", but the thing you're trying to access it on is not a record. \n");
            message.push('\n');
            message.push_str("The type of the thing you're trying to access it on is:\n");
            message.push_str(&format_type_expr(type_ctx, ty));
            message.push_str(",\n\n");
            message.push_str("Only records have fields that can be accessed with dot notation.");
        }
        _ => {
            message.push_str(INFO);
            message.push_str(field_name);
            message.push_str(RESET);
            message.push_str(" refers to a record field, but no corresponding record type is in scope.");
        }
    }

    format_compiler_error_report(arena, source, filename, loc, &message)
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
            TypeDesc::Tarrow { arg, ret, .. } => {
                args.push((arg.lbl.clone(), arg.typ));
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
    use_fallback_message: bool,
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
    let mismatch_in_unlabelled_args =
        !use_fallback_message && args_from_type_unlabelled != provided_unlabelled;

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

    let is_fallback = use_fallback_message
        || (missing_required_args.is_empty()
            && superfluous_args.is_empty()
            && !mismatch_in_unlabelled_args);

    let mut message = String::new();
    message.push_str("This function call is incorrect.\n");
    message.push_str("The function has type:\n");
    message.push_str(&format_type_expr(type_ctx, function_type));
    message.push_str("\n\n");

    if !missing_required_args.is_empty() {
        message.push_str("- Missing arguments that must be provided: ");
        message.push_str(
            &missing_required_args
                .iter()
                .map(|arg| format!("~{arg}"))
                .collect::<Vec<_>>()
                .join(", "),
        );
        message.push('\n');
        message.push_str("- Hint: Did you want to partially apply the function? You can do that by putting `...` just before the closing parens of the function call. Example: ");
        message.push_str(INFO);
        message.push_str("yourFn(~arg1=someVar, ...)");
        message.push_str(RESET);
        message.push('\n');
    }

    if !superfluous_args.is_empty() {
        message.push_str("- Called with arguments it does not take: ");
        message.push_str(&superfluous_args.join(", "));
        message.push('\n');
    }

    if mismatch_in_unlabelled_args {
        message.push_str("- The function takes ");
        message.push_str(INFO);
        message.push_str(&unlabelled_arg_count_message(
            args_from_type_unlabelled,
            provided_unlabelled,
            CountPosition::Left,
        ));
        message.push_str(RESET);
        message.push_str(" unlabelled argument");
        if args_from_type_unlabelled != 1 {
            message.push('s');
        }
        message.push_str(", but is called with ");
        message.push_str(ERROR);
        message.push_str(&unlabelled_arg_count_message(
            provided_unlabelled,
            args_from_type_unlabelled,
            CountPosition::Right,
        ));
        message.push_str(RESET);
    }

    if is_fallback {
        message.push_str("It is called with ");
        message.push_str(ERROR);
        message.push_str(&provided_arity.to_string());
        message.push_str(RESET);
        message.push_str(" argument");
        if provided_arity != 1 {
            message.push('s');
        }
        message.push_str(" but");
        if provided_arity > expected_arity {
            message.push_str(" just");
        }
        message.push_str(" requires ");
        message.push_str(INFO);
        message.push_str(&expected_arity.to_string());
        message.push_str(RESET);
        message.push('.');
    }

    format_compiler_error_report(arena, source, filename, loc, &message)
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
        let repr = type_ctx.repr(current);
        if !seen.insert(repr) {
            break;
        }

        match &*type_ctx.get_desc(repr) {
            TypeDesc::Tarrow { arg, ret, .. } => {
                labels.push(arg.lbl.clone());
                current = *ret;
            }
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => current = *next,
            _ => break,
        }
    }

    labels
}

fn format_type_expr(type_ctx: &TypeContext, ty: TypeExprRef) -> String {
    TypeExprPrinter::new(type_ctx).format(ty)
}

struct TypeExprPrinter<'a> {
    type_ctx: &'a TypeContext,
    vars: ahash::AHashMap<TypeExprRef, String>,
    next_var: usize,
}

impl<'a> TypeExprPrinter<'a> {
    fn new(type_ctx: &'a TypeContext) -> Self {
        Self {
            type_ctx,
            vars: ahash::AHashMap::new(),
            next_var: 0,
        }
    }

    fn format(&mut self, ty: TypeExprRef) -> String {
        let repr = self.type_ctx.repr(ty);
        match &*self.type_ctx.get_desc(repr) {
            TypeDesc::Tvar(name) | TypeDesc::Tunivar(name) => self.format_type_var(repr, name),
            TypeDesc::Tarrow { .. } => self.format_arrow(repr),
            TypeDesc::Ttuple(types) => {
                let parts = types.iter().map(|ty| self.format(*ty)).collect::<Vec<_>>();
                format!("({})", parts.join(", "))
            }
            TypeDesc::Tconstr { path, args, .. } => {
                let name = path.last().to_string();
                if args.is_empty() {
                    name
                } else {
                    let args = args.iter().map(|ty| self.format(*ty)).collect::<Vec<_>>();
                    format!("{name}<{}>", args.join(", "))
                }
            }
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => self.format(*next),
            TypeDesc::Tpoly { body, .. } => self.format(*body),
            TypeDesc::Tobject { .. } => "<object>".to_string(),
            TypeDesc::Tfield { .. } => "<object-field>".to_string(),
            TypeDesc::Tnil => "<object-end>".to_string(),
            TypeDesc::Tvariant(_) => "<variant>".to_string(),
            TypeDesc::Tpackage { path, .. } => format!("module({})", path.name()),
        }
    }

    fn format_arrow(&mut self, ty: TypeExprRef) -> String {
        let mut args = Vec::new();
        let mut current = ty;
        let mut seen = AHashSet::new();

        loop {
            let repr = self.type_ctx.repr(current);
            if !seen.insert(repr) {
                break;
            }

            match &*self.type_ctx.get_desc(repr) {
                TypeDesc::Tarrow { arg, ret, .. } => {
                    args.push((
                        self.format_arrow_arg(&arg.lbl, arg.typ),
                        !matches!(arg.lbl, TypeArgLabel::Nolabel),
                    ));
                    current = *ret;
                }
                TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => current = *next,
                _ => break,
            }
        }

        let ret = self.format(current);
        if let [(arg, true)] = args.as_slice() {
            format!("({arg}) => {ret}")
        } else if let [(arg, false)] = args.as_slice() {
            format!("{arg} => {ret}")
        } else {
            let args = args
                .into_iter()
                .map(|(arg, _)| arg)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({args}) => {ret}")
        }
    }

    fn format_arrow_arg(&mut self, label: &TypeArgLabel, ty: TypeExprRef) -> String {
        let ty = self.format(ty);
        match label {
            TypeArgLabel::Nolabel => ty,
            TypeArgLabel::Labelled(label) => format!("~{}: {ty}", label.txt),
            TypeArgLabel::Optional(label) => format!("?{}: {ty}", label.txt),
        }
    }

    fn format_type_var(&mut self, ty: TypeExprRef, name: &Option<String>) -> String {
        if let Some(name) = name {
            if !name.is_empty() && name != "_" {
                return format!("'{name}");
            }
        }

        if let Some(existing) = self.vars.get(&ty) {
            return existing.clone();
        }

        let name = generated_type_var_name(self.next_var);
        self.next_var += 1;
        self.vars.insert(ty, name.clone());
        name
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
    // Parse
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);
    if parser.has_errors() {
        return Err(anyhow!(
            "Parse failed with {} error(s)",
            parser.diagnostics().len()
        ));
    }
    let file_directives = extract_file_directives_from_structure(&structure, parser.arena())?;
    let debug = debug_for_structure(&structure, options, parser.arena());
    let jsx_preserve = jsx_preserve_for_structure(&structure, options, parser.arena());
    let experimental_let_unwrap =
        experimental_let_unwrap_for_structure(&structure, options, parser.arena());
    // Source fallback path: only run JSX rewrite when the file enables `-bs-jsx`.
    let jsx_version = jsx_version_for_structure(&structure, options, parser.arena());
    let structure = if let Some(jsx_version) = jsx_version {
        jsx_ppx::transform_structure(structure, jsx_version, parser.arena_mut())
    } else {
        structure
    };

    // Expand extension points (%%raw, %raw, %re, %%private) without touching externals
    let structure = ppx::expand_extensions(&structure, parser.arena_mut());

    // Rewrite expressions: desugar pipe (->), setter (#=), property access (##),
    // await, tagged templates, encode externals, and apply spice mapper rewrites.
    // spice is handled here, so avoid running a second top-level spice expansion pass.
    let structure = ppx::rewrite_structure(&structure, parser.arena_mut())
        .map_err(|e| ppx_error_to_anyhow(e, parser.arena(), source, filename))?;

    // Type check
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    type_ctx.set_preserve_canonical_typedtree(options.preserve_canonical_typedtree());
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    tctx.experimental_let_unwrap = experimental_let_unwrap;
    let mut env = initial_env(&type_ctx);

    // Load Pervasives and extend the initial environment
    let mut pers_env = PersistentEnv::new();
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path.clone());
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        options.module_name.as_deref(),
    );

    // Store persistent env in the type check context for module resolution
    tctx.set_persistent_env(pers_env);

    let (typed_structure, final_env) = type_structure(&mut tctx, &env, parser.arena(), &structure)
        .map_err(|e| type_mod_error_to_anyhow(e, &type_ctx, parser.arena(), source, filename))?;

    // Apply interface constraints: moregen linking for non-generic Tvars.
    // OCaml's Includemod.compunit -> moregeneral -> moregen links weak (non-generic)
    // type variables from value-restricted expressions to the corresponding types
    // from the .resi interface. This happens BEFORE sexp serialization.
    apply_moregen_constraints(&mut tctx, &type_ctx, &typed_structure, options, None);

    // OCaml's type_implementation_more calls normalize_signature ONLY when there
    // is no .resi file (Mli_exists branch skips it). Match this behavior:
    // normalize sorts Tvariant row fields and Tobject field chains alphabetically.
    let has_resi = options
        .source_filename
        .as_ref()
        .is_some_and(|f| f.ends_with(".res") && std::path::Path::new(&format!("{}i", f)).exists());
    if !has_resi {
        normalize_signature_types(&type_ctx, &typed_structure, &final_env);
    }

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

    prepare_inferred_signature_for_saving(
        &type_ctx,
        &typed_structure,
        options.source_filename.as_deref(),
        has_resi,
    );

    // Typedtree parity runs only need typechecking output.
    // Skipping Lambda/JS lowering avoids unrelated downstream failures
    // (timeouts/crashes) from obscuring typedtree parity results.
    if (options.dump_typed_sexp || options.dump_typed_sexp_locs)
        && std::env::var_os("RUST_TYPEDTREE_ONLY").is_some()
    {
        return Ok(String::new());
    }

    let lambda_start_stamp = type_ctx.current_stamp();

    let raw_trace = std::env::var_os("RUST_DRAWLAMBDA_STAGE_TRACE").is_some();
    if options.dump_lambda && raw_trace {
        eprintln!("[drawlambda-stage] start");
    }
    let unit_name = options
        .source_filename
        .as_deref()
        .map(module_name_from_source_filename)
        .unwrap_or_default();
    let implementation_coercion = compute_raw_implementation_coercion(
        &mut tctx,
        &type_ctx,
        &env,
        &typed_structure,
        options,
        None,
    );
    let mut raw_converter =
        crate::raw_lambda::convert::RawLambdaConverter::with_start_stamp_and_unit_name(
            parser.arena(),
            &type_ctx,
            &env,
            lambda_start_stamp,
            unit_name,
        );
    raw_converter.set_no_assert_false(options.no_assert_false);
    if let Some(persistent_env) = tctx.persistent_env.clone() {
        raw_converter.set_persistent_env(persistent_env);
    }
    if options.dump_lambda && raw_trace {
        eprintln!("[drawlambda-stage] before-convert");
    }
    let raw_lambda =
        raw_converter.convert_structure_with_coercion(&typed_structure, &implementation_coercion);
    let possible_required_modules = raw_converter.take_possible_required_modules();
    let raw_lambda_current_stamp = raw_converter.current_stamp();
    if options.dump_lambda {
        if raw_trace {
            eprintln!("[drawlambda-stage] after-convert");
            eprintln!("[drawlambda-stage] before-print");
        }
        use std::io::Write;
        let mut stderr = std::io::stderr();
        let mut raw_buf = Vec::new();
        crate::raw_lambda::print::print_raw_lambda(&raw_lambda, &mut raw_buf);
        raw_buf.push(b'\n');
        let _ = stderr.write_all(&raw_buf);
        if raw_trace {
            eprintln!("[drawlambda-stage] after-print");
        }
        let raw_only = std::env::var_os("RUST_RAWLAMBDA_ONLY").is_some();
        if !raw_only {
            let _ = stderr.flush();
        }
        if raw_only {
            std::process::exit(0);
        }
    }

    let lowered_lambda = crate::raw_lambda::lower::lower_to_lambda_with_start_stamp(
        raw_lambda,
        raw_lambda_current_stamp,
    );

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
        Some(module_path_resolver.clone()),
        jsx_preserve,
        options.check_div_by_zero,
        options.cross_module_inline,
    );
    let program = compiler.compile_deps_program_with_possible_required_modules(
        &lowered_lambda,
        &possible_required_modules,
    );

    // JS IR -> JS source
    let js = print_deps_program_with_directives_and_options(
        &program,
        Some(&module_path_resolver),
        &file_directives,
        debug,
        jsx_preserve,
        !options.no_version_header,
    );

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

fn build_inferred_signature_coercion(
    impl_sig: &crate::types::decl::Signature,
) -> crate::types::typedtree::ModuleCoercion {
    use crate::types::decl::{SignatureItem, ValueKind};
    use crate::types::includemod::is_runtime_component;
    use crate::types::typedtree::ModuleCoercion;

    let mut seen_values = std::collections::HashSet::new();
    let mut keep = vec![true; impl_sig.len()];
    // OCaml's inferred-signature path uses Typemod.simplify_signature before
    // Includemod.compunit; simplify_signature only drops earlier duplicate
    // values by name. See compiler/ml/typemod.ml:650-663 and 1768-1770.
    for (idx, item) in impl_sig.iter().enumerate().rev() {
        if let SignatureItem::SigValue(id, _) = item {
            keep[idx] = seen_values.insert(id.name().to_string());
        }
    }

    let mut runtime_pos = 0usize;
    let mut len_impl = 0usize;
    let mut coercions = Vec::new();
    let mut runtime_fields = Vec::new();
    let mut id_pos_list = Vec::new();

    for (idx, item) in impl_sig.iter().enumerate() {
        let current_runtime_pos = runtime_pos;
        if let SignatureItem::SigModule(id, _, _) = item {
            // OCaml builds id_pos_list by consing during a left fold, so the
            // final list is reverse module order. See compiler/ml/includemod.ml:288-293.
            id_pos_list.push((
                id.clone(),
                current_runtime_pos,
                ModuleCoercion::Tcoerce_none,
            ));
        }
        if is_runtime_component(item) {
            runtime_pos += 1;
            len_impl += 1;
        }
        if !keep[idx] {
            continue;
        }
        match item {
            SignatureItem::SigValue(id, desc)
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) =>
            {
                coercions.push((current_runtime_pos, ModuleCoercion::Tcoerce_none));
                runtime_fields.push(id.name().to_string());
            }
            SignatureItem::SigTypext(id, _, _) | SignatureItem::SigModule(id, _, _) => {
                coercions.push((current_runtime_pos, ModuleCoercion::Tcoerce_none));
                runtime_fields.push(id.name().to_string());
            }
            SignatureItem::SigClass => {
                coercions.push((current_runtime_pos, ModuleCoercion::Tcoerce_none));
            }
            _ => {}
        }
    }

    id_pos_list.reverse();

    // Matches Includemod.signatures: it returns Tcoerce_structure when the
    // runtime lengths differ, otherwise simplify_structure_coercion can erase
    // identity coercions. See compiler/ml/includemod.ml:329-342 and 181-188.
    let is_identity = len_impl == coercions.len()
        && coercions
            .iter()
            .enumerate()
            .all(|(expected_pos, (actual_pos, coercion))| {
                *actual_pos == expected_pos && matches!(coercion, ModuleCoercion::Tcoerce_none)
            });

    if is_identity {
        ModuleCoercion::Tcoerce_none
    } else {
        ModuleCoercion::Tcoerce_structure(coercions, id_pos_list, runtime_fields)
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
        return build_inferred_signature_coercion(impl_sig);
    }

    let Some(module_name) = std::path::Path::new(source_file)
        .file_stem()
        .and_then(|s| s.to_str())
        .map(|s| s.to_string())
    else {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    };
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

    match crate::types::includemod::compunit(
        type_ctx,
        env,
        source_file,
        impl_sig,
        "(inferred signature)",
        target_sig.as_ref(),
    ) {
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
pub fn typecheck_interface_source(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> Result<()> {
    // Parse as signature
    let mut parser = Parser::new(filename, source);
    let signature = module::parse_signature(&mut parser);
    if parser.has_errors() {
        return Err(anyhow!(
            "Parse failed with {} error(s)",
            parser.diagnostics().len()
        ));
    }
    let experimental_let_unwrap =
        experimental_let_unwrap_for_signature(&signature, options, parser.arena());
    let signature = preprocess_signature_for_typecheck_with_source(
        signature,
        options,
        parser.arena_mut(),
        source,
        filename,
    )?;

    // Type check
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    type_ctx.set_preserve_canonical_typedtree(options.preserve_canonical_typedtree());
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    tctx.experimental_let_unwrap = experimental_let_unwrap;
    let mut env = initial_env(&type_ctx);

    // Load Pervasives and extend the initial environment
    let mut pers_env = PersistentEnv::new();
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path.clone());
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        options.module_name.as_deref(),
    );

    tctx.set_persistent_env(pers_env);

    let typed_signature = transl_signature(&mut tctx, &env, parser.arena(), &signature)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

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
    let stdlib_dir = options
        .runtime_path
        .as_ref()
        .map(|runtime_path| runtime_path.join("lib").join("ocaml"));
    let cwd = std::env::current_dir().ok();

    let mut paths = options
        .include_paths
        .iter()
        .map(|path| normalize_load_path_entry(path, stdlib_dir.as_deref(), cwd.as_deref()))
        .collect::<Vec<_>>();

    if let Some(stdlib_dir) = stdlib_dir {
        paths.push(stdlib_dir);
    }

    paths
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
    use crate::ident::Ident;

    if !nopervasives {
        // Try to load and open Pervasives
        if pers_env.open_module("Pervasives", env, ctx) {
            // OCaml `Res_compmisc.initial_env` opens implicit modules through
            // `type_open` (compiler/core/res_compmisc.ml:48-63). In in-process
            // builds, the persistent registry remains available for explicit
            // `Pervasives.X` lookup, so avoid cloning the whole raw signature a
            // second time just to add a top-level module binding.
            if !pers_env.is_in_process_mode() {
                if let Some(md) = pers_env.get_module_declaration("Pervasives", ctx) {
                    if let crate::types::decl::ModuleType::MtySignature(ref sig) = md.md_type {
                        ctx.register_raw_module_sig("Pervasives", std::sync::Arc::new(sig.clone()));
                    }
                    env.add_module(Ident::create_persistent("Pervasives"), md);
                }
            }
        }

        // Try to load and open Stdlib
        if pers_env.open_module("Stdlib", env, ctx) {
            // Same implicit-open behavior as above; keep the opened bindings,
            // but let explicit module lookup use the in-process registry.
            if !pers_env.is_in_process_mode() {
                if let Some(md) = pers_env.get_module_declaration("Stdlib", ctx) {
                    if let crate::types::decl::ModuleType::MtySignature(ref sig) = md.md_type {
                        ctx.register_raw_module_sig("Stdlib", std::sync::Arc::new(sig.clone()));
                    }
                    env.add_module(Ident::create_persistent("Stdlib"), md);
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
            // Keep bsc's standalone path unchanged, but in-process builds can
            // resolve explicit `Module.X` lookups through the persistent
            // registry. Creating this binding would clone the full raw
            // signature after `open_module` already added the opened contents.
            if !pers_env.is_in_process_mode() {
                if let Some(md) = pers_env.get_module_declaration(module_name, ctx) {
                    env.add_module(Ident::create_persistent(module_name), md);
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
        let experimental_let_unwrap =
            experimental_let_unwrap_for_signature(&signature, options, parser.arena());
        let signature = preprocess_signature_for_typecheck_with_source(
            signature,
            options,
            parser.arena_mut(),
            source,
            filename,
        )?;

        // Type check
        crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
        let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
        // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
        // at module initialization, consuming stamp 1000 before any compilation.
        let _ = id_gen.next_stamp();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        type_ctx.set_preserve_canonical_typedtree(true);
        let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
        tctx.experimental_let_unwrap = experimental_let_unwrap;
        let mut env = initial_env(&type_ctx);

        let mut pers_env = PersistentEnv::new();
        let load_path = build_load_path(options);
        type_ctx.set_load_paths(load_path.clone());
        pers_env.set_load_path(load_path);
        pers_env.set_open_modules(options.open_modules.clone());
        pers_env.set_jsx_version(options.jsx_version);
        load_pervasives(
            &mut pers_env,
            &mut env,
            &type_ctx,
            &options.open_modules,
            options.nopervasives,
            options.module_name.as_deref(),
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
        let experimental_let_unwrap =
            experimental_let_unwrap_for_structure(&structure, options, parser.arena());

        let jsx_version = jsx_version_for_structure(&structure, options, parser.arena());
        let structure = if let Some(jsx_version) = jsx_version {
            jsx_ppx::transform_structure(structure, jsx_version, parser.arena_mut())
        } else {
            structure
        };

        let structure = ppx::expand_extensions(&structure, parser.arena_mut());
        let structure = ppx::rewrite_structure(&structure, parser.arena_mut())
            .map_err(|e| ppx_error_to_anyhow(e, parser.arena(), source, filename))?;

        // Type check
        crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
        let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        type_ctx.set_preserve_canonical_typedtree(true);
        let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
        tctx.experimental_let_unwrap = experimental_let_unwrap;
        let mut env = initial_env(&type_ctx);

        let mut pers_env = PersistentEnv::new();
        let load_path = build_load_path(options);
        type_ctx.set_load_paths(load_path.clone());
        pers_env.set_load_path(load_path);
        pers_env.set_open_modules(options.open_modules.clone());
        pers_env.set_jsx_version(options.jsx_version);
        load_pervasives(
            &mut pers_env,
            &mut env,
            &type_ctx,
            &options.open_modules,
            options.nopervasives,
            options.module_name.as_deref(),
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
    let module_name = std::path::Path::new(source_file)
        .file_stem()
        .and_then(|s| s.to_str())
        .map(|s| s.to_string());
    let module_name = match module_name {
        Some(n) => n,
        None => return,
    };

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
    let mut debug = Vec::new();

    // Debug: dump all top-level binding names and types
    debug.push(format!(
        "TOTAL TOP-LEVEL ITEMS: {}",
        typed_structure.str_items.len()
    ));
    for item in &typed_structure.str_items {
        match &item.str_desc {
            crate::types::typedtree::StructureItemDesc::Tstr_value(_, bindings) => {
                for binding in bindings {
                    let name = extract_pat_name(&binding.vb_pat);
                    debug.push(format!("TOP-LEVEL VALUE: {:?}", name));
                    if name.as_deref() == Some("wrapJsForReason") {
                        debug.push(format!(
                            "=== wrapJsForReason pat_type={:?} level={}",
                            binding.vb_pat.pat_type,
                            type_ctx.get_level(type_ctx.repr(binding.vb_pat.pat_type))
                        ));
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
                debug.push(format!("TOP-LEVEL MODULE: {}", mb.mb_name.txt));
            }
            _ => {
                debug.push(format!("TOP-LEVEL OTHER"));
            }
        }
    }

    moregen_link_structure(type_ctx, typed_structure, &iface_val_types, &mut debug);
    if !debug.is_empty() {
        use std::io::Write;
        let debug_file = format!("/tmp/moregen_debug_{}.txt", module_name);
        let mut f = std::fs::File::create(&debug_file).unwrap();
        for line in &debug {
            writeln!(f, "{}", line).unwrap();
        }
    }
}

fn moregen_link_structure(
    type_ctx: &TypeContext,
    structure: &crate::types::typedtree::Structure,
    iface_val_types: &ahash::AHashMap<String, crate::types::type_expr::TypeExprRef>,
    debug: &mut Vec<String>,
) {
    for item in &structure.str_items {
        match &item.str_desc {
            crate::types::typedtree::StructureItemDesc::Tstr_value(_, bindings) => {
                for binding in bindings {
                    let name = extract_pat_name(&binding.vb_pat);
                    if let Some(ref name) = name {
                        if let Some(&iface_ty) = iface_val_types.get(name) {
                            debug.push(format!(
                                "moregen_link: {} impl={:?} iface={:?}",
                                name, binding.vb_pat.pat_type, iface_ty
                            ));
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
                                debug.push(format!(
                                    "moregen_link_alias: {} aliased={:?} iface={:?}",
                                    name, desc.val_type, iface_ty
                                ));
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
                            debug.push(format!("no iface match: {}", name));
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
    debug: &mut Vec<String>,
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
    debug: &mut Vec<String>,
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
            debug.push(format!(
                "{}Tvar({:?}) {:?} {} level={}",
                indent, name, ty, generic_str, level
            ));
        }
        TypeDesc::Tconstr { path, args, .. } => {
            debug.push(format!(
                "{}Tconstr({:?}) {:?} level={} args={}",
                indent,
                path,
                ty,
                level,
                args.len()
            ));
            let args = args.clone();
            drop(desc);
            for arg in &args {
                dump_all_tvars(ctx, *arg, debug, seen, depth + 1);
            }
            return;
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            let (at, r) = (arg.typ, *ret);
            drop(desc);
            dump_all_tvars(ctx, at, debug, seen, depth + 1);
            dump_all_tvars(ctx, r, debug, seen, depth + 1);
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
    debug: &mut Vec<String>,
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
    debug: &mut Vec<String>,
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
    debug: &mut Vec<String>,
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
            let iface_summary = match &*iface_desc {
                TypeDesc::Tvar(n) => format!("Tvar({:?})", n),
                TypeDesc::Tconstr { path, .. } => format!("Tconstr({:?})", path),
                _ => "other".to_string(),
            };
            debug.push(format!(
                "  LINK {:?} Tvar({:?}) level={} -> {}",
                impl_ty,
                name,
                ctx.get_level(impl_ty),
                iface_summary
            ));
            drop(impl_desc);
            drop(iface_desc);
            crate::types::ctype::link_type(ctx, impl_ty, iface_ty);
        }
        (TypeDesc::Tvar(name), _) if allow_generic_anonymous && name.is_none() => {
            let iface_summary = match &*iface_desc {
                TypeDesc::Tvar(n) => format!("Tvar({:?})", n),
                TypeDesc::Tconstr { path, .. } => format!("Tconstr({:?})", path),
                _ => "other".to_string(),
            };
            debug.push(format!(
                "  LINK exported generic {:?} Tvar({:?}) level={} -> {}",
                impl_ty,
                name,
                ctx.get_level(impl_ty),
                iface_summary
            ));
            drop(impl_desc);
            drop(iface_desc);
            crate::types::ctype::link_type(ctx, impl_ty, iface_ty);
        }
        (TypeDesc::Tvar(name), _) => {
            debug.push(format!(
                "  SKIP generic {:?} Tvar({:?}) level={}",
                impl_ty,
                name,
                ctx.get_level(impl_ty)
            ));
        }
        (
            TypeDesc::Tconstr {
                path: p1, args: a1, ..
            },
            TypeDesc::Tconstr {
                path: p2, args: a2, ..
            },
        ) if moregen_paths_compatible(p1, p2) && a1.len() == a2.len() => {
            debug.push(format!(
                "  Tconstr match: {:?} ~ {:?} args={}",
                p1,
                p2,
                a1.len()
            ));
            let a1 = a1.clone();
            let a2 = a2.clone();
            drop(impl_desc);
            drop(iface_desc);
            for (a, b) in a1.iter().zip(a2.iter()) {
                moregen_link_impl(ctx, *a, *b, visited, debug, allow_generic_anonymous);
            }
        }
        (
            TypeDesc::Tarrow {
                arg: a1, ret: r1, ..
            },
            TypeDesc::Tarrow {
                arg: a2, ret: r2, ..
            },
        ) => {
            debug.push(format!("  Tarrow match"));
            let (a1t, r1) = (a1.typ, *r1);
            let (a2t, r2) = (a2.typ, *r2);
            drop(impl_desc);
            drop(iface_desc);
            moregen_link_impl(ctx, a1t, a2t, visited, debug, false);
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
            debug.push(format!(
                "  Tconstr MISMATCH: impl={:?}({}) iface={:?}({})",
                p1,
                a1.len(),
                p2,
                a2.len()
            ));
        }
        _ => {
            debug.push(format!("  NO match"));
        }
    }
}

/// Per-file configuration overrides extracted from `@@config({flags: [...]})`.
#[derive(Debug, Default)]
pub struct FileConfigOverrides {
    pub let_unwrap: bool,
    pub jsx_version: Option<i32>,
}

fn parse_config_flags(flags: &[String]) -> FileConfigOverrides {
    let mut overrides = FileConfigOverrides::default();
    let mut i = 0;
    while i < flags.len() {
        match flags[i].as_str() {
            "-enable-experimental" => {
                if i + 1 < flags.len() && flags[i + 1] == "LetUnwrap" {
                    overrides.let_unwrap = true;
                    i += 2;
                    continue;
                }
            }
            "-bs-jsx" => {
                if i + 1 < flags.len() {
                    if let Ok(v) = flags[i + 1].parse::<i32>() {
                        overrides.jsx_version = Some(v);
                    }
                    i += 2;
                    continue;
                }
            }
            _ => {}
        }
        i += 1;
    }
    overrides
}

fn extract_flags_from_config_payload(
    payload: &Payload,
    arena: &crate::parse_arena::ParseArena,
) -> Vec<String> {
    use crate::parser::ast::ExpressionDesc as ED;
    use crate::parser::longident::Longident;
    let mut result = Vec::new();
    if let Payload::PStr(items) = payload {
        for item in items.iter() {
            if let StructureItemDesc::Pstr_eval(inner) = &*item.pstr_desc {
                let (expr_idx, _attrs) = &**inner;
                let expr = arena.get_expr(*expr_idx);
                if let ED::Pexp_record(inner) = &*expr.pexp_desc {
                    let (fields, _spread) = &**inner;
                    for field in fields {
                        let lid = arena.get_longident(field.lid.txt);
                        let is_flags = match lid {
                            Longident::Lident(str_idx) => arena.get_string(*str_idx) == "flags",
                            _ => false,
                        };
                        if is_flags {
                            let field_expr = arena.get_expr(field.expr);
                            if let ED::Pexp_array(elements) = &*field_expr.pexp_desc {
                                for elem_idx in elements.iter() {
                                    let elem = arena.get_expr(*elem_idx);
                                    if let ED::Pexp_constant(c) = &*elem.pexp_desc {
                                        if let Constant::String(s, _) = &**c {
                                            result.push(s.to_string());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    result
}

fn extract_single_string_payload(
    payload: &Payload,
    arena: &crate::parse_arena::ParseArena,
) -> Option<String> {
    use crate::parser::ast::ExpressionDesc as ED;

    let Payload::PStr(items) = payload else {
        return None;
    };
    if items.len() != 1 {
        return None;
    }
    let StructureItemDesc::Pstr_eval(inner) = &*items[0].pstr_desc else {
        return None;
    };
    let (expr_idx, _attrs) = &**inner;
    let expr = arena.get_expr(*expr_idx);
    match &*expr.pexp_desc {
        ED::Pexp_constant(c) => match &**c {
            Constant::String(s, _) => Some(s.to_string()),
            _ => None,
        },
        _ => None,
    }
}

fn extract_file_directives_from_structure(
    structure: &Structure,
    arena: &crate::parse_arena::ParseArena,
) -> Result<Vec<String>> {
    let mut directives = Vec::new();

    for item in structure {
        let StructureItemDesc::Pstr_attribute(attr) = &*item.pstr_desc else {
            continue;
        };
        if arena.get_string(attr.0.txt) != "directive" {
            continue;
        }
        let directive = extract_single_string_payload(&attr.1, arena)
            .ok_or_else(|| anyhow!("Expected string literal payload in @@directive"))?;
        directives.push(directive);
    }

    Ok(directives)
}

/// Extract `@@config({flags: [...]})` overrides from a parsed structure.
pub fn extract_file_config_from_structure(
    structure: &Structure,
    arena: &crate::parse_arena::ParseArena,
) -> FileConfigOverrides {
    for item in structure {
        if let StructureItemDesc::Pstr_attribute(attr) = &*item.pstr_desc {
            let name = arena.get_string(attr.0.txt);
            if name == "config" {
                let flags = extract_flags_from_config_payload(&attr.1, arena);
                if !flags.is_empty() {
                    return parse_config_flags(&flags);
                }
            }
        }
    }
    FileConfigOverrides::default()
}

/// Extract `@@config({flags: [...]})` overrides from a parsed signature.
pub fn extract_file_config_from_signature(
    signature: &Signature,
    arena: &crate::parse_arena::ParseArena,
) -> FileConfigOverrides {
    for item in signature {
        if let SignatureItemDesc::Psig_attribute(attr) = &*item.psig_desc {
            let name = arena.get_string(attr.0.txt);
            if name == "config" {
                let flags = extract_flags_from_config_payload(&attr.1, arena);
                if !flags.is_empty() {
                    return parse_config_flags(&flags);
                }
            }
        }
    }
    FileConfigOverrides::default()
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

    let experimental_let_unwrap =
        experimental_let_unwrap_for_structure(&structure, options, &arena);

    let jsx_version = jsx_version_for_structure(&structure, options, &arena);
    let structure = if let Some(jsx_version) = jsx_version {
        jsx_ppx::transform_structure(structure, jsx_version, &mut arena)
    } else {
        structure
    };

    let structure = ppx::expand_extensions(&structure, &mut arena);
    let structure = ppx::rewrite_structure(&structure, &mut arena)
        .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?;

    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    type_ctx.set_preserve_canonical_typedtree(true);
    let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
    tctx.experimental_let_unwrap = experimental_let_unwrap;
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::new();
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        options.module_name.as_deref(),
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
    arena: crate::parse_arena::ParseArena,
    signature: Signature,
    options: &CompilerOptions,
    writer: &mut W,
) -> Result<()> {
    let experimental_let_unwrap =
        experimental_let_unwrap_for_signature(&signature, options, &arena);

    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    type_ctx.set_preserve_canonical_typedtree(true);
    let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
    tctx.experimental_let_unwrap = experimental_let_unwrap;
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::new();
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        options.module_name.as_deref(),
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
pub(crate) fn normalize_signature_types(
    type_ctx: &TypeContext,
    typed_structure: &crate::types::typedtree::Structure,
    final_env: &crate::types::env::Env,
) {
    use crate::types::ctype::normalize_type;
    use crate::types::decl::SignatureItem;
    use crate::types::typedtree::{ModuleExprDesc, PatternDesc, StructureItemDesc};

    /// Collect bound variable names from a pattern.
    fn collect_bound_names(pat: &crate::types::typedtree::Pattern, names: &mut Vec<String>) {
        match &pat.pat_desc {
            PatternDesc::Tpat_var(id, _) => {
                names.push(id.name().to_string());
            }
            PatternDesc::Tpat_alias(inner, id, _) => {
                collect_bound_names(inner, names);
                names.push(id.name().to_string());
            }
            PatternDesc::Tpat_tuple(pats)
            | PatternDesc::Tpat_construct(_, _, pats)
            | PatternDesc::Tpat_array(pats) => {
                for p in pats {
                    collect_bound_names(p, names);
                }
            }
            PatternDesc::Tpat_record(fields, _) => {
                for (_, _, p, _) in fields {
                    collect_bound_names(p, names);
                }
            }
            PatternDesc::Tpat_variant(_, Some(inner), _) => collect_bound_names(inner, names),
            PatternDesc::Tpat_or(left, _, _) => collect_bound_names(left, names),
            _ => {}
        }
    }

    fn local_sig_values(
        sig: &[SignatureItem],
    ) -> ahash::AHashMap<String, crate::types::type_expr::TypeExprRef> {
        let mut map = ahash::AHashMap::new();
        for item in sig {
            if let SignatureItem::SigValue(id, vd) = item {
                map.insert(id.name().to_string(), vd.val_type);
            }
        }
        map
    }

    fn norm_structure(
        ctx: &TypeContext,
        env: &crate::types::env::Env,
        s: &crate::types::typedtree::Structure,
        allow_local_sig_values: bool,
    ) {
        let local_values = if allow_local_sig_values {
            local_sig_values(&s.str_type)
        } else {
            ahash::AHashMap::new()
        };

        for item in &s.str_items {
            match &item.str_desc {
                StructureItemDesc::Tstr_value(_, bindings) => {
                    for b in bindings {
                        // Look up val_type from env for each bound variable,
                        // matching OCaml's normalize_signature_item(Sig_value).
                        let mut names = Vec::new();
                        collect_bound_names(&b.vb_pat, &mut names);
                        let mut normalized_from_env = false;
                        for name in &names {
                            if let Some(&val_type) = local_values.get(name) {
                                normalize_type(ctx, val_type);
                                normalized_from_env = true;
                            } else if let Ok(vd) = env.find_value(name) {
                                normalize_type(ctx, vd.val_type);
                                normalized_from_env = true;
                            }
                        }
                        // Module-local generated bindings are not visible through
                        // the outer env threaded into nested structures. When no
                        // lookup succeeds, fall back to the binding pattern type
                        // so recursively reachable function/variant types still
                        // get normalized before typedtree sexp printing.
                        if !normalized_from_env {
                            normalize_type(ctx, b.vb_pat.pat_type);
                        }
                    }
                }
                StructureItemDesc::Tstr_primitive(vd) => {
                    if let Some(&val_type) = local_values.get(vd.val_id.name()) {
                        normalize_type(ctx, val_type);
                    } else {
                        normalize_type(ctx, vd.val_desc.ctyp_type);
                    }
                }
                StructureItemDesc::Tstr_module(mb) => {
                    norm_modexpr(ctx, env, &mb.mb_expr);
                }
                _ => {}
            }
        }
    }

    fn norm_modexpr(
        ctx: &TypeContext,
        env: &crate::types::env::Env,
        me: &crate::types::typedtree::ModuleExpr,
    ) {
        match &me.mod_desc {
            ModuleExprDesc::Tmod_structure(s) => {
                norm_structure(ctx, env, s, true);
            }
            ModuleExprDesc::Tmod_constraint(me, _, _, _) => {
                norm_modexpr(ctx, env, me);
            }
            ModuleExprDesc::Tmod_functor(_, _, _, me) => {
                norm_modexpr(ctx, env, me);
            }
            ModuleExprDesc::Tmod_apply(me1, me2, _) => {
                norm_modexpr(ctx, env, me1);
                norm_modexpr(ctx, env, me2);
            }
            _ => {}
        }
    }

    norm_structure(type_ctx, final_env, typed_structure, false);
}

fn rename_ident_for_save_signature(
    type_ctx: &TypeContext,
    id: &crate::ident::Ident,
) -> crate::ident::Ident {
    let fresh = type_ctx.create_ident(id.name());
    if fresh.flags() == id.flags() {
        fresh
    } else {
        crate::ident::Ident::new(id.name(), fresh.stamp(), id.flags())
    }
}

fn consume_module_type_save_signature_renames(
    type_ctx: &TypeContext,
    mty: &crate::types::decl::ModuleType,
) {
    use crate::types::decl::ModuleType;

    match mty {
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        ModuleType::MtySignature(sig) => consume_signature_save_renames(type_ctx, sig),
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            let _ = rename_ident_for_save_signature(type_ctx, param);
            if let Some(param_type) = param_type.as_deref() {
                consume_module_type_save_signature_renames(type_ctx, param_type);
            }
            consume_module_type_save_signature_renames(type_ctx, result);
        }
    }
}

fn consume_signature_save_renames(
    type_ctx: &TypeContext,
    sig: &[crate::types::decl::SignatureItem],
) {
    use crate::types::decl::SignatureItem;

    for item in sig {
        match item {
            SignatureItem::SigType(id, _, _)
            | SignatureItem::SigModule(id, _, _)
            | SignatureItem::SigModtype(id, _)
            | SignatureItem::SigValue(id, _)
            | SignatureItem::SigTypext(id, _, _) => {
                let _ = rename_ident_for_save_signature(type_ctx, id);
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }

    for item in sig {
        match item {
            SignatureItem::SigModule(_, md, _) => {
                consume_module_type_save_signature_renames(type_ctx, &md.md_type);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(mty) = &mtd.mtd_type {
                    consume_module_type_save_signature_renames(type_ctx, mty);
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

fn prepare_inferred_signature_for_saving(
    type_ctx: &TypeContext,
    typed_structure: &crate::types::typedtree::Structure,
    source_filename: Option<&str>,
    has_resi: bool,
) {
    let Some(source_filename) = source_filename else {
        return;
    };
    if has_resi || !source_filename.ends_with(".res") {
        return;
    }

    let simple_sig = crate::types::includemod::simplify_signature(&typed_structure.str_type);
    consume_signature_save_renames(type_ctx, &simple_sig);
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
    /// Intermediate-representation sexps, populated when
    /// `CompilerOptions::capture_intermediates` is true (for the playground).
    pub typed_tree_sexp: String,
    pub raw_lambda_sexp: String,
    pub lambda_sexp: String,
}

/// Owned in-process compilation state after typechecking and Lambda lowering,
/// before JS backend metadata from dependencies is required.
pub struct InProcessPreJsCompileResult {
    pub lowered_lambda: crate::lambda::Lambda,
    pub possible_required_modules: AHashSet<ModuleId>,
    pub file_directives: Vec<String>,
    pub debug: bool,
    pub jsx_preserve: bool,
    pub signature: crate::types::decl::Signature,
    pub pers_struct: Option<PortablePersStruct>,
    pub new_alias_rewrites: ahash::AHashMap<String, crate::types::path::Path>,
    /// Intermediate-representation sexps, populated when
    /// `CompilerOptions::capture_intermediates` is true (for the playground).
    pub typed_tree_sexp: String,
    pub raw_lambda_sexp: String,
    pub lambda_sexp: String,
}

/// Signature payload produced after in-process implementation typechecking but
/// before Lambda/JS compilation. Rewatch uses this to unblock dependent
/// typechecking while preserving OCaml's save-before-translation order
/// (compiler/ml/typemod.ml:1779-1788; compiler/ml/translmod.ml:267).
pub struct InProcessSignatureReady {
    pub signature: crate::types::decl::Signature,
    pub pers_struct: Option<PortablePersStruct>,
    pub new_alias_rewrites: ahash::AHashMap<String, crate::types::path::Path>,
}

pub type InProcessSignatureReadyHook<'a> =
    dyn FnMut(InProcessSignatureReady) -> Result<Option<ModuleRegistry>> + 'a;

pub type InProcessBeforeJsHook<'a> =
    dyn FnMut(&AHashSet<ModuleId>) -> Result<Option<ModuleRegistry>> + 'a;

/// Result of an in-process `.resi` interface type-check.
pub struct InProcessInterfaceResult {
    pub signature: crate::types::decl::Signature,
    pub pers_struct: Option<PortablePersStruct>,
    pub new_alias_rewrites: ahash::AHashMap<String, crate::types::path::Path>,
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
    if parser.has_errors() {
        return Err(anyhow!(
            "Parse failed with {} error(s)",
            parser.diagnostics().len()
        ));
    }
    let experimental_let_unwrap =
        experimental_let_unwrap_for_structure(&structure, options, parser.arena());
    let jsx_version = jsx_version_for_structure(&structure, options, parser.arena());
    let structure = if let Some(jsx_version) = jsx_version {
        jsx_ppx::transform_structure(structure, jsx_version, parser.arena_mut())
    } else {
        structure
    };
    let structure = ppx::rewrite_structure(&structure, parser.arena_mut())
        .map_err(|e| ppx_error_to_anyhow(e, parser.arena(), source, filename))?;
    let structure =
        crate::binary_ast::writer::apply_no_export_config(parser.arena_mut(), structure);

    let mut effective_options = options.clone();
    effective_options.experimental_let_unwrap = experimental_let_unwrap;

    compile_preprocessed_structure_in_process(
        parser.arena(),
        &structure,
        filename,
        module_name,
        &effective_options,
        registry,
        has_interface,
    )
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

fn compile_js_program_for_output(
    lowered_lambda: &crate::lambda::Lambda,
    possible_required_modules: &AHashSet<ModuleId>,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    output_module_format: Option<ModuleFormat>,
    persistent_env: Option<PersistentEnv>,
    jsx_preserve: bool,
) -> (
    DepsProgram,
    ModulePathResolver,
    ahash::AHashMap<String, CmjExportConstant>,
    ahash::AHashMap<String, CmjExportArity>,
) {
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
        Some(module_path_resolver.clone()),
        jsx_preserve,
        options.check_div_by_zero,
        options.cross_module_inline,
    );
    let program = compiler.compile_deps_program_with_possible_required_modules(
        lowered_lambda,
        possible_required_modules,
    );
    let cmj_export_constants = compiler.take_cmj_export_constants();
    let cmj_export_arities = compiler.take_cmj_export_arities();

    (
        program,
        module_path_resolver,
        cmj_export_constants,
        cmj_export_arities,
    )
}

fn compile_js_program_for_output_owned(
    lowered_lambda: crate::lambda::Lambda,
    possible_required_modules: &AHashSet<ModuleId>,
    options: &CompilerOptions,
    output_path: Option<&FsPath>,
    output_module_format: Option<ModuleFormat>,
    persistent_env: Option<PersistentEnv>,
    jsx_preserve: bool,
) -> (
    DepsProgram,
    ModulePathResolver,
    ahash::AHashMap<String, CmjExportConstant>,
    ahash::AHashMap<String, CmjExportArity>,
) {
    let _span = info_span!(
        "compiler.js_backend",
        module = options.module_name.as_deref().unwrap_or(""),
        owned = true,
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
        Some(module_path_resolver.clone()),
        jsx_preserve,
        options.check_div_by_zero,
        options.cross_module_inline,
    );
    let program = compiler.compile_deps_program_with_possible_required_modules_owned(
        lowered_lambda,
        possible_required_modules,
    );
    let cmj_export_constants = compiler.take_cmj_export_constants();
    let cmj_export_arities = compiler.take_cmj_export_arities();

    (
        program,
        module_path_resolver,
        cmj_export_constants,
        cmj_export_arities,
    )
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

pub fn compile_preprocessed_structure_in_process_until_js(
    arena: &crate::parse_arena::ParseArena,
    structure: &Structure,
    filename: &str,
    module_name: &str,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
    has_interface: bool,
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

    log::debug!(
        "[compile_source_in_process] {} type-check start",
        module_name
    );
    let env_setup_span = info_span!("compiler.env_setup").entered();
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    type_ctx.set_preserve_canonical_typedtree(options.preserve_canonical_typedtree());
    let mut tctx = TypeCheckContext::new(&type_ctx, arena);
    tctx.experimental_let_unwrap = options.experimental_let_unwrap;
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::from_registry(registry);
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path.clone());
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_nopervasives(options.nopervasives);
    pers_env.set_compiling_module(options.module_name.clone());
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        options.module_name.as_deref(),
    );

    tctx.set_persistent_env(pers_env);
    drop(env_setup_span);

    let (typed_structure, final_env) =
        crate::timing::measure(crate::timing::Phase::Typecheck, || {
            let _phase = info_span!("compiler.type_structure").entered();
            type_structure(&mut tctx, &env, arena, structure)
                .map_err(|e| anyhow!("Type checking failed: {e:?}"))
        })?;

    let published_signature = {
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

        if !has_interface {
            normalize_signature_types(&type_ctx, &typed_structure, &final_env);
        }

        prepare_inferred_signature_for_saving(
            &type_ctx,
            &typed_structure,
            options.source_filename.as_deref(),
            has_interface,
        );

        crate::types::includemod::simplify_signature(&typed_structure.str_type)
    };

    // OCaml saves the inferred `.cmi` only in the no-interface branch before
    // Lambda translation mutates any shared type nodes
    // (compiler/ml/typemod.ml:1768-1788; translmod.ml:267). With a `.resi`,
    // the already-published interface remains the target signature for
    // `Translmod.transl_implementation`; do not replace it with the
    // implementation signature or the export coercion becomes identity.
    let (pers_struct, new_alias_rewrites, persistent_env_after_signature) = if has_interface {
        (
            None,
            Default::default(),
            tctx.persistent_env
                .take()
                .unwrap_or_else(PersistentEnv::new),
        )
    } else {
        let _phase = info_span!("compiler.signature_extract").entered();
        let mut internal_env = tctx
            .persistent_env
            .take()
            .unwrap_or_else(PersistentEnv::new);

        internal_env.register_in_memory_signature(
            module_name,
            published_signature.clone(),
            filename,
            &type_ctx,
        );
        // OCaml saves the current unit into the persistent table before
        // lambda translation (compiler/ml/typemod.ml:1779-1788). That save
        // also installs `ps_sig` for later lazy component forcing
        // (compiler/ml/env.ml:1960-1977). In-process builds do not write/read
        // the `.cmi`, so keep the just-saved current signature in the
        // TypeContext raw-signature cache before hiding the transient module.
        let current_raw_sig = internal_env.read_raw_sig_shared(module_name, &type_ctx).unwrap_or_else(|| {
            panic!(
                "in-process invariant violated: saved signature for {module_name} was not available"
            )
        });
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
        (pers_struct, new_alias_rewrites, internal_env)
    };
    if !has_interface && let Some(hook) = signature_ready.as_deref_mut() {
        let _ = hook(InProcessSignatureReady {
            signature: published_signature.clone(),
            pers_struct: pers_struct.clone(),
            new_alias_rewrites: new_alias_rewrites.clone(),
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

    let lambda_start_stamp = type_ctx.current_stamp();

    let unit_name = options
        .source_filename
        .as_deref()
        .map(module_name_from_source_filename)
        .unwrap_or_default();
    let (raw_lambda, possible_required_modules, raw_lambda_current_stamp) =
        crate::timing::measure(crate::timing::Phase::Lambda, || {
            let _phase = info_span!("compiler.raw_lambda").entered();
            let implementation_coercion = compute_raw_implementation_coercion(
                &mut tctx,
                &type_ctx,
                &env,
                &typed_structure,
                options,
                Some(has_interface),
            );
            let mut raw_converter =
                crate::raw_lambda::convert::RawLambdaConverter::with_start_stamp_and_unit_name(
                    arena,
                    &type_ctx,
                    &env,
                    lambda_start_stamp,
                    unit_name,
                );
            raw_converter.set_no_assert_false(options.no_assert_false);
            if let Some(persistent_env) = tctx.persistent_env.clone() {
                raw_converter.set_persistent_env(persistent_env);
            }
            let raw_lambda = raw_converter
                .convert_structure_with_coercion(&typed_structure, &implementation_coercion);
            let possible_required_modules = raw_converter.take_possible_required_modules();
            let raw_lambda_current_stamp = raw_converter.current_stamp();
            (
                raw_lambda,
                possible_required_modules,
                raw_lambda_current_stamp,
            )
        });
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
        crate::raw_lambda::lower::lower_to_lambda_with_start_stamp(
            raw_lambda,
            raw_lambda_current_stamp,
        )
    });

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
        file_directives,
        debug,
        jsx_preserve,
        signature: published_signature,
        pers_struct,
        new_alias_rewrites,
        typed_tree_sexp,
        raw_lambda_sexp,
        lambda_sexp,
    })
}

pub fn finish_preprocessed_structure_in_process_from_js_boundary(
    pre_js: InProcessPreJsCompileResult,
    options: &CompilerOptions,
    registry: &ModuleRegistry,
) -> Result<InProcessCompileResult> {
    let _span = info_span!(
        "compiler.in_process_js_finish",
        module = options.module_name.as_deref().unwrap_or(""),
        skip_js_render = options.skip_js_render,
        js_targets = options.js_output_targets.len()
    )
    .entered();
    let mut persistent_env_for_js = PersistentEnv::from_registry(registry);
    let load_path = build_load_path(options);
    persistent_env_for_js.set_load_path(load_path);
    persistent_env_for_js.set_open_modules(options.open_modules.clone());
    persistent_env_for_js.set_jsx_version(options.jsx_version);
    persistent_env_for_js.set_nopervasives(options.nopervasives);
    persistent_env_for_js.set_compiling_module(options.module_name.clone());
    if let Some(module_name) = options.module_name.as_deref() {
        persistent_env_for_js.unregister_in_memory_signature(module_name);
    }
    let persistent_env_for_js = Some(persistent_env_for_js);
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
    let (program, module_path_resolver, cmj_export_constants, cmj_export_arities) = {
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
                &pre_js.possible_required_modules,
                options,
                primary_output_path,
                primary_output_module_format,
                persistent_env_for_js.clone(),
                pre_js.jsx_preserve,
            )
        } else {
            compile_js_program_for_output_owned(
                lowered_lambda
                    .take()
                    .expect("lowered lambda consumed by single JS target"),
                &pre_js.possible_required_modules,
                options,
                primary_output_path,
                primary_output_module_format,
                persistent_env_for_js.clone(),
                pre_js.jsx_preserve,
            )
        }
    };
    let is_pure = program.side_effect.is_none();
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
            let (program, module_path_resolver, _, _) = compile_js_program_for_output(
                lowered_lambda
                    .as_ref()
                    .expect("lowered lambda retained for secondary JS targets"),
                &pre_js.possible_required_modules,
                options,
                Some(&target.path),
                Some(target.module_format),
                persistent_env_for_js.clone(),
                pre_js.jsx_preserve,
            );
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
            let mut primary_js = print_deps_program_with_directives_and_options(
                &primary_program,
                Some(&primary_resolver),
                &pre_js.file_directives,
                pre_js.debug,
                pre_js.jsx_preserve,
                !options.no_version_header,
            );
            let mut js_outputs = Vec::new();
            let js = if let Some(path) = primary_path {
                js_outputs.push(JsOutput {
                    path,
                    code: std::mem::take(&mut primary_js),
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
                let code = print_deps_program_with_directives_and_options(
                    &program,
                    Some(&module_path_resolver),
                    &pre_js.file_directives,
                    pre_js.debug,
                    pre_js.jsx_preserve,
                    !options.no_version_header,
                );
                crate::js_ir::dispose_deps_program_nonrecursive(program);
                js_outputs.push(JsOutput { path, code });
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
        typed_tree_sexp: pre_js.typed_tree_sexp,
        raw_lambda_sexp: pre_js.raw_lambda_sexp,
        lambda_sexp: pre_js.lambda_sexp,
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
    let signature = preprocess_signature_for_typecheck_with_source(
        signature,
        options,
        parser.arena_mut(),
        source,
        filename,
    )?;

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

    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    type_ctx.set_preserve_canonical_typedtree(options.preserve_canonical_typedtree());
    let mut tctx = TypeCheckContext::new(&type_ctx, arena);
    tctx.experimental_let_unwrap = options.experimental_let_unwrap;
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::from_registry(registry);
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_nopervasives(options.nopervasives);
    pers_env.set_compiling_module(options.module_name.clone());
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        options.module_name.as_deref(),
    );

    tctx.set_persistent_env(pers_env);

    let typed_signature = crate::timing::measure(crate::timing::Phase::Typecheck, || {
        let _phase = info_span!("compiler.type_signature").entered();
        transl_signature(&mut tctx, &env, arena, signature)
            .map_err(|e| anyhow!("Type checking failed: {e:?}"))
    })?;
    let decl_signature =
        crate::types::typemod::decl_signature_from_typed_signature(&typed_signature, arena);

    let typed_module_type = crate::types::typedtree::ModuleType {
        mty_desc: crate::types::typedtree::ModuleTypeDesc::Tmty_signature(typed_signature),
        mty_type: crate::types::decl::ModuleType::MtySignature(decl_signature),
        mty_env: crate::types::typedtree::EnvRef(0),
        mty_loc: crate::parse_arena::LocIdx(0),
        mty_attributes: crate::parser::ast::Attributes::new(),
    };
    let published_signature =
        match crate::types::typemod::decl_module_type_from_typed(&typed_module_type) {
            Some(crate::types::decl::ModuleType::MtySignature(sig)) => sig,
            _ => {
                return Err(anyhow!(
                    "Failed to extract interface signature from typed tree"
                ));
            }
        };

    let mut internal_env = tctx
        .persistent_env
        .take()
        .unwrap_or_else(PersistentEnv::new);

    internal_env.register_in_memory_signature(
        module_name,
        published_signature.clone(),
        filename,
        &type_ctx,
    );

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

    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
    type_ctx.set_preserve_canonical_typedtree(options.preserve_canonical_typedtree());
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    tctx.experimental_let_unwrap = options.experimental_let_unwrap;
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::from_registry(registry);
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    pers_env.set_nopervasives(options.nopervasives);
    pers_env.set_compiling_module(options.module_name.clone());
    load_pervasives(
        &mut pers_env,
        &mut env,
        &type_ctx,
        &options.open_modules,
        options.nopervasives,
        options.module_name.as_deref(),
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

    internal_env.register_in_memory_signature(
        module_name,
        published_signature.clone(),
        filename,
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
                ValueDescription {
                    val_type: TypeExprRef::null(),
                    val_kind: ValueKind::ValReg,
                    val_loc: Location::none(),
                    val_attributes: Vec::new(),
                    val_path: None,
                },
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
