//! Compiler driver utilities.
//!
//! This module wires together parsing, type-checking, Lambda conversion, and
//! JS IR codegen to produce JavaScript output.

use std::ffi::OsString;
use std::path::{Component, Path as FsPath, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};

use anyhow::{Context, Result, anyhow};

use crate::binary_ast::ppx;
use crate::cmi::persistent_env::PersistentEnv;
use crate::context::IdGenerator;
use crate::js_ir::{Kind, ModulePathResolver, printer::print_deps_program_with_directives};
use crate::lambda::compile::LambdaCompiler;
use crate::parser::ast::{
    Attribute, Constant, Expression, ModuleExpr, ModuleExprDesc, Payload, Signature,
    SignatureItemDesc, Structure, StructureItemDesc,
};
use crate::parser::{Parser, jsx_ppx, module};
use crate::types::sexp_typedtree::{
    print_typed_signature, print_typed_signature_with_locs, print_typed_structure,
    print_typed_structure_with_locs,
};
use crate::types::{TypeCheckContext, TypeContext, initial_env, transl_signature, type_structure};

// OCaml's Predef sets `Ident.set_current_time 999`. OCaml's Parmatch.extra_pat
// then eagerly creates Ident.create "+" consuming stamp 1000.
// We match this by starting at 999 and consuming one stamp.
const OCAML_NON_PREDEF_STAMP_START: i32 = 999;
static SKIP_CLI_CLEANUP: AtomicBool = AtomicBool::new(false);

pub fn enable_cli_cleanup_skip() {
    SKIP_CLI_CLEANUP.store(true, Ordering::Relaxed);
}

fn module_name_from_source_filename(path: &str) -> String {
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

fn max_lambda_input_stamp(typed_structure: &crate::types::typedtree::Structure) -> i32 {
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
            ExpressionDesc::Texp_constant(_) => {}
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
        ED::Pexp_ident(_) | ED::Pexp_jsx_element(_) => false,
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

/// Compiler options that can be passed to the driver.
#[derive(Default, Clone)]
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
    /// JSX version from CLI `-bs-jsx` (e.g. 4). When set, enables JSX PPX rewrite.
    pub jsx_version: Option<i32>,
    /// Preserve transformed JSX syntax in the final JS dumper.
    pub jsx_preserve: bool,
    /// Enable debug-mode JS emission (like OCaml's -bs-g / Js_config.debug).
    pub debug: bool,
}

pub(crate) fn jsx_version_for_structure(
    structure: &Structure,
    options: &CompilerOptions,
    arena: &crate::parse_arena::ParseArena,
) -> Option<i32> {
    options
        .jsx_version
        .or_else(|| structure_has_config_string(structure, "-bs-jsx", arena).then_some(4))
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
        .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?;

    // Type check
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(&id_gen);
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    let mut env = initial_env(&type_ctx);

    // Load Pervasives and extend the initial environment
    let mut pers_env = PersistentEnv::new();
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);

    // Store persistent env in the type check context for module resolution
    tctx.set_persistent_env(pers_env);

    let (typed_structure, final_env) = type_structure(&mut tctx, &env, parser.arena(), &structure)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

    // Apply interface constraints: moregen linking for non-generic Tvars.
    // OCaml's Includemod.compunit -> moregeneral -> moregen links weak (non-generic)
    // type variables from value-restricted expressions to the corresponding types
    // from the .resi interface. This happens BEFORE sexp serialization.
    apply_moregen_constraints(&mut tctx, &type_ctx, &typed_structure, options);

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

    let lambda_start_stamp = type_ctx
        .current_stamp()
        .max(max_lambda_input_stamp(&typed_structure));

    let raw_trace = std::env::var_os("RUST_DRAWLAMBDA_STAGE_TRACE").is_some();
    if options.dump_lambda && raw_trace {
        eprintln!("[drawlambda-stage] start");
    }
    let unit_name = options
        .source_filename
        .as_deref()
        .map(module_name_from_source_filename)
        .unwrap_or_default();
    let implementation_coercion =
        compute_raw_implementation_coercion(&mut tctx, &type_ctx, &env, &typed_structure, options);
    let mut raw_converter =
        crate::raw_lambda::convert::RawLambdaConverter::with_start_stamp_and_unit_name(
            parser.arena(),
            &type_ctx,
            &env,
            lambda_start_stamp,
            unit_name,
        );
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
        options.runtime_path.as_deref(),
        tctx.persistent_env.clone(),
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
    let mut compiler = LambdaCompiler::with_module_path_resolver_and_jsx_preserve(
        Some(module_path_resolver.clone()),
        jsx_preserve,
    );
    let program = compiler.compile_deps_program_with_possible_required_modules(
        &lowered_lambda,
        &possible_required_modules,
    );

    // JS IR -> JS source
    let js = print_deps_program_with_directives(
        &program,
        Some(&module_path_resolver),
        &file_directives,
        debug,
        jsx_preserve,
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
    use crate::types::includemod::is_runtime_component;
    use crate::types::typedtree::ModuleCoercion;

    // Build name → runtime_position map from the implementation signature.
    // Only runtime components get a position index.
    let mut impl_name_to_pos: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut runtime_pos = 0usize;
    for item in impl_sig {
        if is_runtime_component(item) {
            let name = match item {
                crate::types::decl::SignatureItem::SigValue(id, _)
                | crate::types::decl::SignatureItem::SigModule(id, _, _)
                | crate::types::decl::SignatureItem::SigTypext(id, _, _) => id.name().to_string(),
                _ => {
                    runtime_pos += 1;
                    continue;
                }
            };
            impl_name_to_pos.insert(name, runtime_pos);
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
            crate::types::decl::SignatureItem::SigValue(id, _)
            | crate::types::decl::SignatureItem::SigModule(id, _, _)
            | crate::types::decl::SignatureItem::SigTypext(id, _, _) => id.name().to_string(),
            _ => continue,
        };
        if let Some(&pos) = impl_name_to_pos.get(&name) {
            coercions.push((pos, ModuleCoercion::Tcoerce_none));
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

fn compute_raw_implementation_coercion(
    tctx: &mut TypeCheckContext<'_>,
    type_ctx: &TypeContext<'_>,
    env: &Env,
    typed_structure: &crate::types::typedtree::Structure,
    options: &CompilerOptions,
) -> crate::types::typedtree::ModuleCoercion {
    let Some(source_file) = &options.source_filename else {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    };
    if !source_file.ends_with(".res") {
        return crate::types::typedtree::ModuleCoercion::Tcoerce_none;
    }

    let impl_sig = typed_structure.str_type.clone();
    let has_resi = std::path::Path::new(&format!("{source_file}i")).exists();
    let target_sig = if has_resi {
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
        match pers.read_raw_sig(&module_name, type_ctx) {
            Some(sig) => sig,
            None => return crate::types::typedtree::ModuleCoercion::Tcoerce_none,
        }
    } else {
        crate::types::includemod::simplify_signature(&impl_sig)
    };

    match crate::types::includemod::compunit(
        type_ctx,
        env,
        source_file,
        &impl_sig,
        "(inferred signature)",
        &target_sig,
    ) {
        Ok(cc) => cc,
        Err(_) if has_resi => {
            // compunit can fail when the OCaml-built CMI has different type stamps
            // than what Rust's type-checker produces. In that case, fall back to a
            // name-based structural coercion that at least filters the export block
            // to match the interface's set of exported items. This ensures functors
            // and other implementation-only items are excluded from the module export
            // block, matching OCaml's behavior.
            build_name_based_coercion(&impl_sig, &target_sig)
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

    // Type check
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(&id_gen);
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    let mut env = initial_env(&type_ctx);

    // Load Pervasives and extend the initial environment
    let mut pers_env = PersistentEnv::new();
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);

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
    let source: String = bytes.iter().map(|&b| b as char).collect();
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
    let source: String = bytes.iter().map(|&b| b as char).collect();
    let filename = path.to_string_lossy();
    compile_source_to_js_with_options(&source, &filename, options)
}

/// Build the load path from compiler options.
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
pub(crate) fn load_pervasives<'a>(
    pers_env: &mut PersistentEnv,
    env: &mut Env,
    ctx: &'a TypeContext<'a>,
    open_modules: &[String],
) {
    use crate::ident::Ident;

    // Try to load and open Pervasives (matches OCaml: open_implicit_module "Pervasives")
    if pers_env.open_module("Pervasives", env, ctx) {
        if let Some(md) = pers_env.get_module_declaration("Pervasives", ctx) {
            if let crate::types::decl::ModuleType::MtySignature(ref sig) = md.md_type {
                ctx.register_raw_module_sig("Pervasives", sig.clone());
            }
            env.add_module(Ident::create_persistent("Pervasives"), md);
        }
    }

    // Try to load and open Stdlib (matches OCaml: open_implicit_module "Stdlib")
    if pers_env.open_module("Stdlib", env, ctx) {
        if let Some(md) = pers_env.get_module_declaration("Stdlib", ctx) {
            if let crate::types::decl::ModuleType::MtySignature(ref sig) = md.md_type {
                ctx.register_raw_module_sig("Stdlib", sig.clone());
            }
            env.add_module(Ident::create_persistent("Stdlib"), md);
        }
    }

    // Apply explicit `-open` modules in argument order.
    for module_name in open_modules {
        if pers_env.open_module(module_name, env, ctx) {
            if let Some(md) = pers_env.get_module_declaration(module_name, ctx) {
                env.add_module(Ident::create_persistent(module_name), md);
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

        // Type check
        crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
        let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
        let type_ctx = TypeContext::new(&id_gen);
        let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
        let mut env = initial_env(&type_ctx);

        let mut pers_env = PersistentEnv::new();
        let load_path = build_load_path(options);
        type_ctx.set_load_paths(load_path.clone());
        pers_env.set_load_path(load_path);
        pers_env.set_open_modules(options.open_modules.clone());
        pers_env.set_jsx_version(options.jsx_version);
        load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);
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

        let jsx_version = jsx_version_for_structure(&structure, options, parser.arena());
        let structure = if let Some(jsx_version) = jsx_version {
            jsx_ppx::transform_structure(structure, jsx_version, parser.arena_mut())
        } else {
            structure
        };

        let structure = ppx::expand_extensions(&structure, parser.arena_mut());
        let structure = ppx::rewrite_structure(&structure, parser.arena_mut())
            .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?;

        // Type check
        crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
        let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
        let type_ctx = TypeContext::new(&id_gen);
        let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
        let mut env = initial_env(&type_ctx);

        let mut pers_env = PersistentEnv::new();
        let load_path = build_load_path(options);
        type_ctx.set_load_paths(load_path.clone());
        pers_env.set_load_path(load_path);
        pers_env.set_open_modules(options.open_modules.clone());
        pers_env.set_jsx_version(options.jsx_version);
        load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);
        tctx.set_persistent_env(pers_env);

        let (typed_structure, _final_env) =
            type_structure(&mut tctx, &env, parser.arena(), &structure)
                .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

        apply_moregen_constraints(&mut tctx, &type_ctx, &typed_structure, options);

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
    type_ctx: &TypeContext<'_>,
    typed_structure: &crate::types::typedtree::Structure,
    options: &CompilerOptions,
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
    let resi_file = format!("{}i", source_file);
    if !std::path::Path::new(&resi_file).exists() {
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
        let result = pers.read_raw_sig(&module_name, type_ctx);
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
        for iface_item in &iface_sig {
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
                &iface_sig,
                &stamp_remap,
                type_ctx,
            );
        }
    }

    // Build a map from value name -> interface type
    let mut iface_val_types: ahash::AHashMap<String, TypeExprRef> = ahash::AHashMap::new();
    for item in &iface_sig {
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
    type_ctx: &TypeContext<'_>,
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
    type_ctx: &TypeContext<'_>,
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
    ctx: &TypeContext<'_>,
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
    ctx: &TypeContext<'_>,
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
    ctx: &TypeContext<'_>,
    impl_ty: crate::types::type_expr::TypeExprRef,
    iface_ty: crate::types::type_expr::TypeExprRef,
    visited: &mut ahash::AHashSet<(
        crate::types::type_expr::TypeExprRef,
        crate::types::type_expr::TypeExprRef,
    )>,
    debug: &mut Vec<String>,
) {
    moregen_link_impl(ctx, impl_ty, iface_ty, visited, debug, true);
}

fn moregen_link_impl(
    ctx: &TypeContext<'_>,
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
    let type_ctx = TypeContext::new(&id_gen);
    let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::new();
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);
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
    crate::ident::Ident::set_current_time(OCAML_NON_PREDEF_STAMP_START);
    let id_gen = IdGenerator::with_start_stamp(OCAML_NON_PREDEF_STAMP_START);
    // Match OCaml's Parmatch.extra_pat which eagerly calls Ident.create "+"
    // at module initialization, consuming stamp 1000 before any compilation.
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(&id_gen);
    let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::new();
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
    pers_env.set_open_modules(options.open_modules.clone());
    pers_env.set_jsx_version(options.jsx_version);
    load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);
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
    type_ctx: &TypeContext<'_>,
    typed_structure: &crate::types::typedtree::Structure,
    final_env: &crate::types::env::Env,
) {
    use crate::types::ctype::normalize_type;
    use crate::types::decl::SignatureItem;
    use crate::types::typedtree::{ModuleExprDesc, PatternDesc, StructureItemDesc};
    use ahash::AHashMap;

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
        ctx: &TypeContext<'_>,
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
        ctx: &TypeContext<'_>,
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
    type_ctx: &TypeContext<'_>,
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
    type_ctx: &TypeContext<'_>,
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
    type_ctx: &TypeContext<'_>,
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
    type_ctx: &TypeContext<'_>,
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

#[cfg(test)]
mod tests {
    use super::extract_file_directives_from_structure;
    use super::max_lambda_input_stamp;
    use super::normalize_load_path_entry;
    use crate::ident::{Ident, IdentFlags};
    use crate::location::Location;
    use crate::parse_arena::{LidentIdx, LocIdx, Located};
    use crate::parser::ast::{Attributes, RecFlag};
    use crate::parser::{Parser, module};
    use crate::types::decl::{ModuleDeclaration, ModuleType, RecStatus, SignatureItem, ValueKind};
    use crate::types::path::Path as TypePath;
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
                pat_extra: Vec::new(),
                pat_type: TypeExprRef::null(),
                pat_env: EnvRef(0),
                pat_attributes: Attributes::new(),
            },
            vb_expr: Expression {
                exp_desc: ExpressionDesc::Texp_constant(crate::types::typedtree::Constant::Int(1)),
                exp_loc: LocIdx::none(),
                exp_extra: Vec::new(),
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
            exp_extra: Vec::new(),
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
