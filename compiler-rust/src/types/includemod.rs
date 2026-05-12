//! Module inclusion checking for ReScript.
//!
//! This module implements signature matching, which verifies that a module
//! implementation conforms to a module signature. This is equivalent to
//! OCaml's `includemod.ml`.
//!
//! The main function is `modtypes` which checks if one module type is
//! a subtype of another.

#![allow(unused_variables)]
#![allow(dead_code)]

use crate::ident::Ident;
use crate::types::Path;
use crate::types::ctype;
use crate::types::decl::{
    Attribute, AttributePayload, ConstructorArguments, ConstructorDeclaration,
    ExtensionConstructor, LabelDeclaration, ModtypeDeclaration, ModuleDeclaration, ModuleType,
    Signature, SignatureItem, TypeDeclaration, TypeInlinedType, TypeKind, ValueDescription,
    ValueKind,
};
use crate::types::env::Env;
use crate::types::type_expr::TypeDesc;
use crate::types::typedtree::ModuleCoercion;
use crate::types::{TypeContext, TypeExprRef};
use crate::{parser::code_frame, types::ArgLabel};
use ahash::{AHashMap as HashMap, AHashSet as HashSet};

// ============================================================================
// Error Types
// ============================================================================

/// Result type for inclusion checking.
pub type IncludeModResult<T> = Result<T, IncludeModError>;

/// Errors that can occur during module inclusion checking.
#[derive(Debug, Clone)]
pub enum IncludeModError {
    /// Missing signature field in implementation.
    MissingField {
        id: Ident,
        loc: crate::location::Location,
        kind: &'static str,
    },
    /// Value type mismatch.
    ValueTypeMismatch {
        name: Ident,
        actual: ValueDescription,
        expected: ValueDescription,
    },
    /// Type declaration mismatch.
    TypeMismatch { name: Ident, reason: String },
    /// Type declaration mismatch with enough context to print OCaml's report.
    TypeDeclarationMismatch {
        name: Ident,
        actual: TypeDeclaration,
        expected: TypeDeclaration,
        detail: String,
    },
    /// Module type mismatch.
    ModuleTypeMismatch { name: Ident, reason: String },
    /// Nested module types do not include one another.
    ModuleTypesMismatch {
        actual: Box<ModuleType>,
        expected: Box<ModuleType>,
        error: Box<IncludeModError>,
    },
    /// Nested include error reported in a module context.
    InModule {
        name: Ident,
        error: Box<IncludeModError>,
    },
    /// Functor parameter mismatch.
    FunctorParamMismatch(String),
    /// Functor result mismatch.
    FunctorResultMismatch(String),
    /// Not a functor.
    NotAFunctor,
    /// Signature mismatch with details.
    SignatureMismatch(Vec<IncludeModError>),
}

pub fn format_error(type_ctx: &TypeContext, filename: &str, error: &IncludeModError) -> String {
    let mut output = String::new();
    output.push_str("  Signature mismatch:\n");
    format_include_error(type_ctx, filename, error, &mut output);
    output
}

pub(crate) fn format_error_without_signature_header(
    type_ctx: &TypeContext,
    filename: &str,
    error: &IncludeModError,
) -> String {
    let mut output = String::new();
    format_include_error(type_ctx, filename, error, &mut output);
    output
}

fn format_include_error(
    type_ctx: &TypeContext,
    filename: &str,
    error: &IncludeModError,
    output: &mut String,
) {
    match error {
        IncludeModError::SignatureMismatch(errors) => {
            for error in errors {
                format_include_error(type_ctx, filename, error, output);
            }
        }
        IncludeModError::ModuleTypesMismatch {
            actual,
            expected,
            error,
        } => {
            let actual = format_module_type(type_ctx, actual);
            let expected = format_module_type(type_ctx, expected);
            if should_elide_module_mismatch(&actual, &expected) {
                output.push_str("  ...\n");
            } else {
                output.push_str("  Modules do not match:\n");
                output.push_str("    ");
                output.push_str(&actual);
                output.push('\n');
                output.push_str("  is not included in\n");
                output.push_str("    ");
                output.push_str(&expected);
                output.push('\n');
            }
            format_include_error(type_ctx, filename, error, output);
        }
        IncludeModError::InModule { name, error } => {
            output.push_str("  In module ");
            output.push_str(name.name());
            output.push_str(":\n");
            format_include_error(type_ctx, filename, error, output);
        }
        IncludeModError::TypeDeclarationMismatch {
            name,
            actual,
            expected,
            detail,
        } => {
            output.push_str("  Type declarations do not match:\n");
            output.push_str("    ");
            output.push_str(&format_type_declaration(type_ctx, name, actual));
            output.push('\n');
            output.push_str("  is not included in\n");
            output.push_str("    ");
            output.push_str(&format_type_declaration(type_ctx, name, expected));
            output.push('\n');
            output.push_str("  ");
            output.push_str(&code_frame::format_location(
                filename,
                &expected.type_loc.loc_start,
                &expected.type_loc.loc_end,
            ));
            output.push_str(":\n");
            output.push_str("    Expected declaration\n");
            output.push_str("  ");
            output.push_str(&code_frame::format_location(
                filename,
                &actual.type_loc.loc_start,
                &actual.type_loc.loc_end,
            ));
            output.push_str(":\n");
            output.push_str("    Actual declaration\n");
            for line in detail.lines() {
                output.push_str("  ");
                output.push_str(line);
                output.push('\n');
            }
        }
        IncludeModError::MissingField { id, loc, kind } => {
            output.push_str("  The ");
            output.push_str(kind);
            output.push_str(" `");
            output.push_str(id.name());
            output.push_str("' is required but not provided\n");
            output.push_str("  ");
            output.push_str(&code_frame::format_location(
                filename,
                &loc.loc_start,
                &loc.loc_end,
            ));
            output.push_str(":\n");
            output.push_str("    Expected declaration\n");
        }
        IncludeModError::ValueTypeMismatch {
            name,
            actual,
            expected,
        } => {
            let actual_text = format_value_description(type_ctx, name, actual);
            let expected_text = format_value_description(type_ctx, name, expected);
            output.push_str("  Values do not match: ");
            output.push_str(&actual_text);
            output.push_str(" is not included in ");
            output.push_str(&expected_text);
            output.push('\n');
            output.push_str("  ");
            output.push_str(&code_frame::format_location(
                filename,
                &expected.val_loc.loc_start,
                &expected.val_loc.loc_end,
            ));
            output.push_str(":\n");
            output.push_str("    Expected declaration\n");
            output.push_str("  ");
            output.push_str(&code_frame::format_location(
                filename,
                &actual.val_loc.loc_start,
                &actual.val_loc.loc_end,
            ));
            output.push_str(":\n");
            output.push_str("    Actual declaration\n");
        }
        IncludeModError::TypeMismatch { name, reason } => {
            output.push_str("  Type declarations do not match: ");
            output.push_str(name.name());
            output.push_str("\n  ");
            output.push_str(reason);
            output.push('\n');
        }
        IncludeModError::ModuleTypeMismatch { name, reason } => {
            output.push_str("  Modules do not match: ");
            output.push_str(name.name());
            output.push_str("\n  ");
            output.push_str(reason);
            output.push('\n');
        }
        IncludeModError::FunctorParamMismatch(reason)
        | IncludeModError::FunctorResultMismatch(reason) => {
            output.push_str("  ");
            output.push_str(reason);
            output.push('\n');
        }
        IncludeModError::NotAFunctor => {
            output.push_str("  Not a functor.\n");
        }
    }
}

fn should_elide_module_mismatch(actual: &str, expected: &str) -> bool {
    actual.len() + expected.len() > 120
}

pub(crate) fn format_module_type(type_ctx: &TypeContext, mty: &ModuleType) -> String {
    match mty {
        ModuleType::MtyIdent(path) | ModuleType::MtyAlias(_, path) => path.name(),
        ModuleType::MtySignature(sig) => {
            if sig.is_empty() {
                "{}".to_string()
            } else {
                let items = sig
                    .iter()
                    .map(|item| indent_lines(&format_signature_item(type_ctx, item), "  "))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("{{\n{items}\n}}")
            }
        }
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            let param_type = param_type
                .as_ref()
                .map(|mty| format_module_type(type_ctx, mty))
                .unwrap_or_else(|| "_".to_string());
            let result = format_module_type(type_ctx, result);
            format!("({}: {}) => {}", param.name(), param_type, result)
        }
    }
}

fn format_signature_item(type_ctx: &TypeContext, item: &SignatureItem) -> String {
    match item {
        SignatureItem::SigType(id, decl, _) => format_type_declaration(type_ctx, id, decl),
        SignatureItem::SigValue(id, desc) => format_value_description(type_ctx, id, desc),
        SignatureItem::SigModule(id, decl, _) => {
            format!(
                "module {}: {}",
                id.name(),
                format_module_type(type_ctx, &decl.md_type)
            )
        }
        SignatureItem::SigModtype(id, decl) => match &decl.mtd_type {
            Some(mty) => format!(
                "module type {} = {}",
                id.name(),
                format_module_type(type_ctx, mty)
            ),
            None => format!("module type {}", id.name()),
        },
        SignatureItem::SigTypext(id, _, _) => format!("type {} += ...", id.name()),
        SignatureItem::SigClass => "class ...".to_string(),
        SignatureItem::SigClassType => "class type ...".to_string(),
    }
}

fn indent_lines(text: &str, prefix: &str) -> String {
    text.lines()
        .map(|line| format!("{prefix}{line}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn format_value_description(
    type_ctx: &TypeContext,
    id: &Ident,
    desc: &ValueDescription,
) -> String {
    format!(
        "let {}: {}",
        id.name(),
        TypeExprErrorPrinter::new(type_ctx).format(desc.val_type)
    )
}

fn format_type_declaration(type_ctx: &TypeContext, id: &Ident, decl: &TypeDeclaration) -> String {
    let mut printer = TypeExprErrorPrinter::new(type_ctx);
    let name = id.name();
    let params = format_type_params(&mut printer, &decl.type_params);
    let prefix = if decl.type_unboxed.unboxed {
        "@unboxed "
    } else {
        ""
    };
    let head = if params.is_empty() {
        format!("{prefix}type {name}")
    } else {
        format!("{prefix}type {name}<{params}>")
    };

    match &decl.type_kind {
        TypeKind::TypeAbstract => match decl.type_manifest {
            Some(manifest) => format!("{head} = {}", printer.format(manifest)),
            None => head,
        },
        TypeKind::TypeRecord(labels, _) => {
            let mut fields = Vec::with_capacity(labels.len());
            for label in labels {
                fields.push(format_label_declaration(&mut printer, label));
            }
            let fields = fields.join(", ");
            format!("{head} = {{{fields}}}")
        }
        TypeKind::TypeVariant(constructors) => {
            if constructors.is_empty() {
                format!("{head} = |")
            } else {
                let mut formatted_constructors = Vec::with_capacity(constructors.len());
                for constructor in constructors {
                    formatted_constructors
                        .push(format_constructor_declaration(&mut printer, constructor));
                }
                let constructors = formatted_constructors.join(" | ");
                format!("{head} = {constructors}")
            }
        }
        TypeKind::TypeOpen => format!("{head} = .."),
    }
}

fn format_constructor_declaration(
    printer: &mut TypeExprErrorPrinter<'_>,
    constructor: &ConstructorDeclaration,
) -> String {
    let constructor_prefix = format_constructor_attributes(&constructor.cd_attributes);
    match &constructor.cd_args {
        ConstructorArguments::CstrTuple(args) if args.is_empty() => {
            format!("{constructor_prefix}{}", constructor.cd_id.name())
        }
        ConstructorArguments::CstrTuple(args) => {
            let mut formatted_args = Vec::with_capacity(args.len());
            for arg in args {
                formatted_args.push(printer.format(*arg));
            }
            let args = formatted_args.join(", ");
            format!("{constructor_prefix}{}({args})", constructor.cd_id.name())
        }
        ConstructorArguments::CstrRecord(labels) => {
            let mut fields = Vec::with_capacity(labels.len());
            for label in labels {
                fields.push(format_label_declaration(printer, label));
            }
            let fields = fields.join(", ");
            format!(
                "{constructor_prefix}{}({{{fields}}})",
                constructor.cd_id.name()
            )
        }
    }
}

fn format_constructor_attributes(attrs: &[Attribute]) -> String {
    attrs
        .iter()
        .filter_map(|attr| {
            if attr.attr_name.txt != "as" {
                return None;
            }
            let payload = match &attr.attr_payload {
                AttributePayload::Ident(value) => value.clone(),
                AttributePayload::Str(value) => format!("\"{value}\""),
                AttributePayload::Int(value) => value.to_string(),
                AttributePayload::Float(value) | AttributePayload::BigInt(value) => value.clone(),
                AttributePayload::Bool(true) => "true".to_string(),
                AttributePayload::Bool(false) => "false".to_string(),
                AttributePayload::Deprecated { reason, .. } => format!("\"{reason}\""),
                AttributePayload::Empty | AttributePayload::Structure(_) => return None,
            };
            Some(format!("@as({payload}) "))
        })
        .collect::<String>()
}

fn format_type_params(printer: &mut TypeExprErrorPrinter<'_>, params: &[TypeExprRef]) -> String {
    params
        .iter()
        .map(|param| printer.format(*param))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_label_declaration(
    printer: &mut TypeExprErrorPrinter<'_>,
    label: &LabelDeclaration,
) -> String {
    let optional = if label.ld_optional { "?" } else { "" };
    let field_type = if label.ld_optional {
        optional_field_payload_type(printer.type_ctx, label.ld_type)
    } else {
        label.ld_type
    };
    format!(
        "{}{}: {}",
        label.ld_id.name(),
        optional,
        printer.format(field_type)
    )
}

fn optional_field_payload_type(type_ctx: &TypeContext, ty: TypeExprRef) -> TypeExprRef {
    let repr = type_ctx.repr(ty);
    match &*type_ctx.get_desc(repr) {
        TypeDesc::Tconstr { path, args, .. } if path.last() == "option" && args.len() == 1 => {
            args[0]
        }
        TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => {
            optional_field_payload_type(type_ctx, *next)
        }
        _ => ty,
    }
}

struct TypeExprErrorPrinter<'a> {
    type_ctx: &'a TypeContext,
    vars: HashMap<TypeExprRef, String>,
    next_var: usize,
}

impl<'a> TypeExprErrorPrinter<'a> {
    fn new(type_ctx: &'a TypeContext) -> Self {
        Self {
            type_ctx,
            vars: HashMap::new(),
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
            TypeDesc::Tobject { .. } => "<object>".to_string(),
            TypeDesc::Tfield { .. } => "<object-field>".to_string(),
            TypeDesc::Tnil => "<object-end>".to_string(),
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => self.format(*next),
            TypeDesc::Tvariant(_) => "<variant>".to_string(),
            TypeDesc::Tpoly { body, .. } => self.format(*body),
            TypeDesc::Tpackage { path, .. } => format!("module({})", path.name()),
        }
    }

    fn format_arrow(&mut self, ty: TypeExprRef) -> String {
        let mut args = Vec::new();
        let mut current = ty;
        let mut seen = HashSet::new();

        loop {
            let repr = self.type_ctx.repr(current);
            if !seen.insert(repr) {
                break;
            }

            match &*self.type_ctx.get_desc(repr) {
                TypeDesc::Tarrow { arg, ret, .. } => {
                    args.push(self.format_arrow_arg(&arg.lbl, arg.typ));
                    current = *ret;
                }
                TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => current = *next,
                _ => break,
            }
        }

        let ret = self.format(current);
        if args.len() == 1 {
            format!("{} => {ret}", args[0])
        } else {
            format!("({}) => {ret}", args.join(", "))
        }
    }

    fn format_arrow_arg(&mut self, label: &ArgLabel, ty: TypeExprRef) -> String {
        let ty = self.format(ty);
        match label {
            ArgLabel::Nolabel => ty,
            ArgLabel::Labelled(label) => format!("~{}: {ty}", label.txt),
            ArgLabel::Optional(label) => format!("~{}?: {ty}", label.txt),
        }
    }

    fn format_type_var(&mut self, ty: TypeExprRef, name: &Option<String>) -> String {
        if let Some(name) = name
            && !name.is_empty()
            && name != "_"
        {
            return format!("'{name}");
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

#[derive(Clone, Default)]
struct InclusionSubst {
    type_paths: HashMap<Path, Path>,
    module_paths: HashMap<Path, Path>,
    modtype_paths: HashMap<Path, Path>,
}

impl InclusionSubst {
    fn is_empty(&self) -> bool {
        self.type_paths.is_empty() && self.module_paths.is_empty() && self.modtype_paths.is_empty()
    }
}

fn lookup_path_subst(map: &HashMap<Path, Path>, path: &Path) -> Option<Path> {
    // OCaml compiler/ml/path.ml:27-35 defines `Path.compare` for PathMap and
    // ignores the `Pdot` position hint, so substitution lookups must use
    // `Path.same` rather than Rust's derived Eq/Hash which includes that field.
    map.get(path).cloned().or_else(|| {
        map.iter()
            .find_map(|(key, value)| key.same(path).then(|| value.clone()))
    })
}

// ============================================================================
// Module Type Inclusion
// ============================================================================

/// Check if `mty_impl` is a subtype of `mty_sig` (implementation matches signature).
///
/// Returns a coercion that can be applied to convert the implementation
/// to the signature type.
use std::cell::Cell;

thread_local! {
    static MODTYPES_DEPTH: Cell<usize> = Cell::new(0);
}

fn with_local_pident_module_type<R>(
    env: &Env,
    path: &Path,
    f: impl FnOnce(&ModuleType) -> R,
) -> Option<R> {
    let mut current = path;
    let mut visiting = HashSet::new();
    let f = f;

    loop {
        let Path::Pident(id) = current else {
            return None;
        };

        if id.is_persistent() || id.stamp() == 0 || !visiting.insert(current.clone()) {
            return None;
        }

        if let Ok(md) = env.lookup_module(&Path::pident(id.clone())) {
            match &md.md_type {
                ModuleType::MtyIdent(alias_path) | ModuleType::MtyAlias(_, alias_path)
                    if !alias_path.same(current) =>
                {
                    current = alias_path;
                    continue;
                }
                _ => return Some(f(&md.md_type)),
            }
        }

        if let Ok(mtd) = env.lookup_modtype(&Path::pident(id.clone())) {
            let mty = mtd.mtd_type.as_ref()?;
            match mty {
                ModuleType::MtyIdent(alias_path) | ModuleType::MtyAlias(_, alias_path)
                    if !alias_path.same(current) =>
                {
                    current = alias_path;
                    continue;
                }
                _ => return Some(f(mty)),
            }
        }

        return None;
    }
}

pub fn modtypes<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
) -> IncludeModResult<ModuleCoercion> {
    let subst = InclusionSubst::default();
    modtypes_inner(type_ctx, env, &subst, mty_impl, mty_sig, None, false).map_err(|error| {
        IncludeModError::ModuleTypesMismatch {
            actual: Box::new(mty_impl.clone()),
            expected: Box::new(mty_sig.clone()),
            error: Box::new(error),
        }
    })
}

/// Check if `mty_impl` is a subtype of `mty_sig` with optional aliasability.
fn modtypes_inner<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    subst: &InclusionSubst,
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
    sig_access_path: Option<&Path>,
    aliasable: bool,
) -> IncludeModResult<ModuleCoercion> {
    // Guard against infinite recursion in module type expansion
    let depth = MODTYPES_DEPTH.with(|d| {
        let v = d.get();
        d.set(v + 1);
        v
    });
    struct DepthGuard;
    impl Drop for DepthGuard {
        fn drop(&mut self) {
            MODTYPES_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        }
    }
    let _guard = DepthGuard;
    // Match compiler/ml/includemod.ml:194-267: OCaml dispatches by module-type
    // shape and does not skip structurally equal signatures. Descending here
    // preserves the same lazy signature forcing and bound-ident freshening.
    if depth > 50 {
        return Ok(ModuleCoercion::Tcoerce_none);
    }

    fn expand_module_type_in_env(
        type_ctx: &TypeContext,
        env: &Env,
        path: &Path,
    ) -> Option<ModuleType> {
        use crate::types::decl::SignatureItem as SigItem;

        fn should_try_env_lazy(path: &Path) -> bool {
            match path {
                Path::Pident(id) => id.is_persistent() || id.stamp() == 0,
                Path::Pdot(_, _, _) => true,
                Path::Papply(_, _) => false,
            }
        }

        fn expand_local(
            env: &Env,
            path: &Path,
            visiting: &mut HashSet<Path>,
        ) -> Option<ModuleType> {
            if !visiting.insert(path.clone()) {
                return None;
            }

            match path {
                Path::Pident(id) => {
                    if let Ok(md) = env.lookup_module(&Path::pident(id.clone())) {
                        match &md.md_type {
                            ModuleType::MtyIdent(alias_path)
                            | ModuleType::MtyAlias(_, alias_path)
                                if !alias_path.same(path) =>
                            {
                                if let Some(expanded) = expand_local(env, alias_path, visiting) {
                                    return Some(expanded);
                                }
                            }
                            _ => return Some(md.md_type.clone()),
                        }
                    }
                    if let Ok(mtd) = env.lookup_modtype(&Path::pident(id.clone())) {
                        if let Some(mty) = &mtd.mtd_type {
                            match mty {
                                ModuleType::MtyIdent(alias_path)
                                | ModuleType::MtyAlias(_, alias_path)
                                    if !alias_path.same(path) =>
                                {
                                    if let Some(expanded) = expand_local(env, alias_path, visiting)
                                    {
                                        return Some(expanded);
                                    }
                                }
                                _ => return Some(mty.clone()),
                            }
                        }
                    }
                    None
                }
                Path::Pdot(parent, name, _) => {
                    let parent_mty = expand_local(env, parent, visiting)?;
                    let parent_sig = match &parent_mty {
                        ModuleType::MtySignature(sig) => sig.clone(),
                        ModuleType::MtyIdent(parent_path)
                        | ModuleType::MtyAlias(_, parent_path) => {
                            match expand_local(env, parent_path, visiting)? {
                                ModuleType::MtySignature(sig) => sig,
                                _ => return None,
                            }
                        }
                        _ => return None,
                    };
                    for item in &parent_sig {
                        match item {
                            SigItem::SigModule(id, md, _) if id.name() == name.as_str() => {
                                return Some(md.md_type.clone());
                            }
                            SigItem::SigModtype(id, mtd) if id.name() == name.as_str() => {
                                return mtd.mtd_type.clone();
                            }
                            _ => {}
                        }
                    }
                    None
                }
                Path::Papply(_, _) => None,
            }
        }

        if should_try_env_lazy(path) {
            if let Some(resolved) =
                crate::types::ctype::resolve_module_type_through_env(type_ctx, env, path)
            {
                return Some(resolved);
            }
        }

        let mut visiting = HashSet::new();
        expand_local(env, path, &mut visiting)
    }

    fn normalized_alias_path(env: &Env, path: &Path) -> Path {
        env.normalize_path(path)
    }

    match (mty_impl, mty_sig) {
        (ModuleType::MtyAlias(pres_impl, impl_path), ModuleType::MtyAlias(pres_sig, sig_path)) => {
            let impl_path = normalized_alias_path(env, impl_path);
            let sig_path = normalized_alias_path(env, sig_path);
            if !impl_path.same(&sig_path) {
                return Err(IncludeModError::ModuleTypeMismatch {
                    name: Ident::create_local("module"),
                    reason: "module aliases do not match".to_string(),
                });
            }
            match (pres_impl, pres_sig) {
                (
                    crate::types::decl::AliasPresence::MtaAbsent,
                    crate::types::decl::AliasPresence::MtaPresent,
                ) => Ok(ModuleCoercion::Tcoerce_alias(
                    type_ctx.store_typed_env(env),
                    impl_path,
                    Box::new(ModuleCoercion::Tcoerce_none),
                )),
                _ => Ok(ModuleCoercion::Tcoerce_none),
            }
        }

        (ModuleType::MtyAlias(pres_impl, impl_path), mty_sig) => {
            let impl_path = normalized_alias_path(env, impl_path);
            let coercion = if let Some(coercion) =
                with_local_pident_module_type(env, &impl_path, |expanded| {
                    let expanded = ctype::strengthen_module_type_for_inclusion_path(
                        type_ctx, env, &impl_path, expanded,
                    );
                    modtypes_inner(
                        type_ctx,
                        env,
                        subst,
                        &expanded,
                        mty_sig,
                        sig_access_path,
                        aliasable,
                    )
                }) {
                coercion?
            } else {
                let expanded = expand_module_type_in_env(type_ctx, env, &impl_path)
                    .map(|mty| {
                        ctype::strengthen_module_type_for_inclusion_path(
                            type_ctx, env, &impl_path, &mty,
                        )
                    })
                    .unwrap_or_else(|| ModuleType::MtyAlias(pres_impl.clone(), impl_path.clone()));
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    &expanded,
                    mty_sig,
                    sig_access_path,
                    aliasable,
                )?
            };
            match pres_impl {
                crate::types::decl::AliasPresence::MtaPresent => Ok(coercion),
                crate::types::decl::AliasPresence::MtaAbsent => Ok(ModuleCoercion::Tcoerce_alias(
                    type_ctx.store_typed_env(env),
                    impl_path,
                    Box::new(coercion),
                )),
            }
        }

        // Alias on the signature side - expand and check
        (mty_impl, ModuleType::MtyAlias(_, path)) => {
            if let Some(result) = with_local_pident_module_type(env, path, |expanded| {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    mty_impl,
                    expanded,
                    sig_access_path,
                    aliasable,
                )
            }) {
                return result;
            }
            if let Some(expanded) = expand_module_type_in_env(type_ctx, env, path) {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    mty_impl,
                    &expanded,
                    sig_access_path,
                    aliasable,
                )
            } else {
                Ok(ModuleCoercion::Tcoerce_none)
            }
        }

        // Signature matching
        (ModuleType::MtySignature(sig_impl), ModuleType::MtySignature(sig_sig)) => {
            signatures_with_subst(type_ctx, env, subst, sig_access_path, sig_impl, sig_sig)
        }

        // Functor matching
        (
            ModuleType::MtyFunctor {
                param: param_impl,
                param_type: param_type_impl,
                result: result_impl,
            },
            ModuleType::MtyFunctor {
                param: param_sig,
                param_type: param_type_sig,
                result: result_sig,
            },
        ) => {
            let empty_subst = InclusionSubst::default();
            let expected_param_type = param_type_sig.as_deref().map(|pt_sig| {
                // OCaml compiler/ml/includemod.ml:257-262 computes
                // `arg2' = Subst.modtype subst arg2` before both the
                // contravariant argument check and `Env.add_module`.
                substitute_module_type_paths(type_ctx, pt_sig, subst)
            });

            // Check parameter (contravariant)
            let param_coercion = match (param_type_impl, expected_param_type.as_ref()) {
                (Some(pt_impl), Some(pt_sig)) => {
                    // Note: parameters are contravariant, so we swap impl/sig
                    modtypes_inner(type_ctx, env, &empty_subst, pt_sig, pt_impl, None, true)?
                }
                (None, None) => ModuleCoercion::Tcoerce_none,
                _ => {
                    return Err(IncludeModError::FunctorParamMismatch(
                        "parameter presence mismatch".to_string(),
                    ));
                }
            };

            // OCaml compiler/ml/includemod.ml:257-262 checks the functor
            // result under `Subst.add_module param2 (Pident param1) subst`
            // and an environment extended with the implementation parameter.
            let mut result_env = env.clone();
            let param_binding_type = expected_param_type
                .clone()
                .or_else(|| param_type_impl.as_deref().cloned())
                .unwrap_or_else(|| ModuleType::MtySignature(vec![]));
            result_env.add_module(
                param_impl.clone(),
                ModuleDeclaration {
                    md_type: param_binding_type,
                    md_attributes: vec![],
                    md_loc: crate::location::Location::none(),
                    md_path: None,
                },
            );
            let mut result_subst = subst.clone();
            result_subst.module_paths.insert(
                Path::pident(param_sig.clone()),
                Path::pident(param_impl.clone()),
            );
            let result_coercion = modtypes_inner(
                type_ctx,
                &result_env,
                &result_subst,
                result_impl,
                result_sig,
                sig_access_path,
                false,
            )?;

            // If both parameter and result coercions are identity, return identity
            if matches!(
                (&param_coercion, &result_coercion),
                (ModuleCoercion::Tcoerce_none, ModuleCoercion::Tcoerce_none)
            ) {
                Ok(ModuleCoercion::Tcoerce_none)
            } else {
                Ok(ModuleCoercion::Tcoerce_functor(
                    Box::new(param_coercion),
                    Box::new(result_coercion),
                ))
            }
        }

        // Signature implementation matches identifier signature
        (ModuleType::MtySignature(sig_impl), ModuleType::MtyIdent(path)) => {
            if let Some(result) = with_local_pident_module_type(env, path, |expanded| {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    mty_impl,
                    expanded,
                    sig_access_path,
                    aliasable,
                )
            }) {
                return result;
            }
            if let Some(expanded) = expand_module_type_in_env(type_ctx, env, path) {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    mty_impl,
                    &expanded,
                    sig_access_path,
                    aliasable,
                )
            } else {
                Ok(ModuleCoercion::Tcoerce_none)
            }
        }

        // Identifier implementation matches signature
        (ModuleType::MtyIdent(path), ModuleType::MtySignature(sig_sig)) => {
            if let Some(result) = with_local_pident_module_type(env, path, |expanded| {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    expanded,
                    mty_sig,
                    sig_access_path,
                    aliasable,
                )
            }) {
                return result;
            }
            if let Some(expanded) = expand_module_type_in_env(type_ctx, env, path) {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    &expanded,
                    mty_sig,
                    sig_access_path,
                    aliasable,
                )
            } else {
                Ok(ModuleCoercion::Tcoerce_none)
            }
        }

        (ModuleType::MtyIdent(path), mty_sig) => {
            // Match compiler/ml/includemod.ml:242-244: implementation-side
            // `Mty_ident` expands before OCaml reaches the same-identifier
            // check in `try_modtypes2` at compiler/ml/includemod.ml:269-280.
            if let Some(result) = with_local_pident_module_type(env, path, |expanded| {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    expanded,
                    mty_sig,
                    sig_access_path,
                    aliasable,
                )
            }) {
                return result;
            }
            if let Some(expanded) = expand_module_type_in_env(type_ctx, env, path) {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    &expanded,
                    mty_sig,
                    sig_access_path,
                    aliasable,
                )
            } else {
                Ok(ModuleCoercion::Tcoerce_none)
            }
        }

        (mty_impl, ModuleType::MtyIdent(path)) => {
            if let Some(result) = with_local_pident_module_type(env, path, |expanded| {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    mty_impl,
                    expanded,
                    sig_access_path,
                    aliasable,
                )
            }) {
                return result;
            }
            if let Some(expanded) = expand_module_type_in_env(type_ctx, env, path) {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    mty_impl,
                    &expanded,
                    sig_access_path,
                    aliasable,
                )
            } else {
                Ok(ModuleCoercion::Tcoerce_none)
            }
        }

        // Fallback: incompatible module types
        _ => Err(IncludeModError::ModuleTypeMismatch {
            name: Ident::create_local("module"),
            reason: "incompatible module types".to_string(),
        }),
    }
}

// ============================================================================
// Signature Inclusion
// ============================================================================

pub fn is_runtime_component(item: &SignatureItem) -> bool {
    match item {
        SignatureItem::SigValue(_, desc) => !matches!(desc.val_kind, ValueKind::ValPrim(_)),
        SignatureItem::SigType(_, _, _)
        | SignatureItem::SigModtype(_, _)
        | SignatureItem::SigClassType => false,
        SignatureItem::SigTypext(_, _, _)
        | SignatureItem::SigModule(_, _, _)
        | SignatureItem::SigClass => true,
    }
}

fn runtime_component_name(item: &SignatureItem) -> Option<String> {
    match item {
        SignatureItem::SigValue(id, _)
        | SignatureItem::SigType(id, _, _)
        | SignatureItem::SigTypext(id, _, _)
        | SignatureItem::SigModule(id, _, _)
        | SignatureItem::SigModtype(id, _) => Some(id.name().to_string()),
        SignatureItem::SigClass | SignatureItem::SigClassType => None,
    }
}

fn simplify_structure_coercion(
    coercions: &[(usize, ModuleCoercion)],
    id_pos_list: &[(Ident, usize, ModuleCoercion)],
    runtime_fields: &[String],
) -> ModuleCoercion {
    let is_identity = coercions
        .iter()
        .enumerate()
        .all(|(expected_pos, (actual_pos, coercion))| {
            *actual_pos == expected_pos && matches!(coercion, ModuleCoercion::Tcoerce_none)
        });

    if is_identity {
        ModuleCoercion::Tcoerce_none
    } else {
        ModuleCoercion::Tcoerce_structure(
            coercions.to_vec(),
            id_pos_list.to_vec(),
            runtime_fields.to_vec(),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FieldDesc {
    Value(String),
    Type(String),
    Typext(String),
    Module(String),
    Modtype(String),
}

#[derive(Debug, Clone, Copy)]
struct ComponentEntry<'a> {
    item: &'a SignatureItem,
    runtime_pos: usize,
}

#[derive(Debug, Clone, Copy)]
struct PairedSignatureItem<'a> {
    impl_item: &'a SignatureItem,
    sig_item: &'a SignatureItem,
    runtime_pos: usize,
}

fn item_ident_name(item: &SignatureItem) -> (&Ident, &crate::location::Location, FieldDesc) {
    match item {
        SignatureItem::SigValue(id, desc) => {
            (id, &desc.val_loc, FieldDesc::Value(id.name().into()))
        }
        SignatureItem::SigType(id, decl, _) => {
            (id, &decl.type_loc, FieldDesc::Type(id.name().into()))
        }
        SignatureItem::SigTypext(id, ext, _) => {
            (id, &ext.ext_loc, FieldDesc::Typext(id.name().into()))
        }
        SignatureItem::SigModule(id, md, _) => {
            (id, &md.md_loc, FieldDesc::Module(id.name().into()))
        }
        SignatureItem::SigModtype(id, mtd) => {
            (id, &mtd.mtd_loc, FieldDesc::Modtype(id.name().into()))
        }
        SignatureItem::SigClass | SignatureItem::SigClassType => unreachable!(),
    }
}

fn adjusted_item_field_desc(item: &SignatureItem) -> (FieldDesc, bool) {
    match item {
        SignatureItem::SigType(id, decl, _)
            if decl.type_manifest.is_none() && crate::types::btype::is_row_name(id.name()) =>
        {
            (
                FieldDesc::Type(id.name().trim_end_matches("#row").to_string()),
                false,
            )
        }
        _ => {
            let (_, _, name) = item_ident_name(item);
            (name, true)
        }
    }
}

fn build_component_table<'a>(
    sig_impl: &'a Signature,
) -> (usize, HashMap<FieldDesc, ComponentEntry<'a>>) {
    let mut runtime_pos = 0usize;
    let mut table = HashMap::new();

    for item in sig_impl {
        let (_, _, field_desc) = item_ident_name(item);
        table.insert(
            item_field_desc_to_key(&field_desc),
            ComponentEntry { item, runtime_pos },
        );
        if is_runtime_component(item) {
            runtime_pos += 1;
        }
    }

    (runtime_pos, table)
}

fn item_field_desc_to_key(field_desc: &FieldDesc) -> FieldDesc {
    match field_desc {
        FieldDesc::Value(name) => FieldDesc::Value(name.clone()),
        FieldDesc::Type(name) => FieldDesc::Type(name.clone()),
        FieldDesc::Typext(name) => FieldDesc::Typext(name.clone()),
        FieldDesc::Module(name) => FieldDesc::Module(name.clone()),
        FieldDesc::Modtype(name) => FieldDesc::Modtype(name.clone()),
    }
}

fn register_paired_signature_substitution(
    paired: PairedSignatureItem<'_>,
    sig_access_path: Option<&Path>,
    subst: &mut InclusionSubst,
) {
    match (paired.impl_item, paired.sig_item) {
        (SignatureItem::SigType(impl_id, _, _), SignatureItem::SigType(sig_id, sig_decl, _)) => {
            // OCaml compiler/ml/includemod.ml:348-359 registers paired
            // signature type components with `Subst.add_type id2 (Pident id1)`;
            // compiler/ml/subst.ml:87-95 then rewrites exact type paths before
            // recursively rewriting module prefixes.
            let impl_path = Path::pident(impl_id.clone());
            subst
                .type_paths
                .insert(Path::pident(sig_id.clone()), impl_path.clone());
            if let Some(access_path) = sig_access_path {
                subst.type_paths.insert(
                    Path::pdot(access_path.clone(), sig_id.name()),
                    impl_path.clone(),
                );
            }
            if let Some(sig_path) = &sig_decl.type_path {
                subst.type_paths.insert(sig_path.clone(), impl_path);
            }
        }
        (
            SignatureItem::SigModule(impl_id, _, _),
            SignatureItem::SigModule(sig_id, sig_decl, _),
        ) => {
            // OCaml compiler/ml/includemod.ml:360-362 adds module and
            // module-type substitutions; compiler/ml/subst.ml:69-75 applies
            // them to exact paths before dotted-prefix recursion.
            let impl_path = Path::pident(impl_id.clone());
            subst
                .module_paths
                .insert(Path::pident(sig_id.clone()), impl_path.clone());
            if let Some(access_path) = sig_access_path {
                subst.module_paths.insert(
                    Path::pdot(access_path.clone(), sig_id.name()),
                    impl_path.clone(),
                );
            }
            if let Some(sig_path) = &sig_decl.md_path {
                subst.module_paths.insert(sig_path.clone(), impl_path);
            }
        }
        (SignatureItem::SigModtype(impl_id, _), SignatureItem::SigModtype(sig_id, _)) => {
            subst
                .modtype_paths
                .insert(Path::pident(sig_id.clone()), Path::pident(impl_id.clone()));
        }
        _ => {}
    }
}

fn field_desc_kind(field_desc: &FieldDesc) -> &'static str {
    match field_desc {
        FieldDesc::Value(_) => "value",
        FieldDesc::Type(_) => "type",
        FieldDesc::Typext(_) => "extension constructor",
        FieldDesc::Module(_) => "module",
        FieldDesc::Modtype(_) => "module type",
    }
}

fn missing_signature_item_error(
    id: &Ident,
    loc: &crate::location::Location,
    field_desc: &FieldDesc,
) -> IncludeModError {
    IncludeModError::MissingField {
        id: id.clone(),
        loc: loc.clone(),
        kind: field_desc_kind(field_desc),
    }
}

fn pair_signature_items<'a>(
    sig_impl: &'a Signature,
    sig_sig: &'a Signature,
    sig_access_path: Option<&Path>,
    subst: &mut InclusionSubst,
) -> (usize, Vec<PairedSignatureItem<'a>>, Vec<IncludeModError>) {
    let (len_impl, component_table) = build_component_table(sig_impl);
    let mut paired = Vec::with_capacity(sig_sig.len());
    let mut errors = Vec::new();

    for sig_item in sig_sig {
        let (sig_id, sig_loc, _) = item_ident_name(sig_item);
        let (field_desc, report_missing) = adjusted_item_field_desc(sig_item);
        if let Some(entry) = component_table.get(&field_desc).copied() {
            let pair = PairedSignatureItem {
                impl_item: entry.item,
                sig_item,
                runtime_pos: entry.runtime_pos,
            };
            register_paired_signature_substitution(pair, sig_access_path, subst);
            paired.push(pair);
        } else if report_missing {
            errors.push(missing_signature_item_error(sig_id, sig_loc, &field_desc));
        }
    }

    (len_impl, paired, errors)
}

fn check_paired_signature_items<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    paired: &[PairedSignatureItem<'_>],
    sig_access_path: Option<&Path>,
    subst: &InclusionSubst,
) -> IncludeModResult<Vec<(usize, ModuleCoercion)>> {
    let mut coercions = Vec::new();

    for pair in paired {
        match (pair.impl_item, pair.sig_item) {
            (
                SignatureItem::SigValue(impl_id, impl_val_desc),
                SignatureItem::SigValue(_, sig_val_desc),
            ) => {
                let coercion = value_descriptions(
                    type_ctx,
                    env,
                    impl_id.clone(),
                    impl_val_desc,
                    sig_val_desc,
                    subst,
                )?;
                if !matches!(sig_val_desc.val_kind, ValueKind::ValPrim(_)) {
                    coercions.push((pair.runtime_pos, coercion));
                }
            }
            (
                SignatureItem::SigType(impl_id, impl_type_decl, _),
                SignatureItem::SigType(_, sig_type_decl, _),
            ) => {
                // OCaml compiler/ml/includemod.ml:64-70 applies
                // Subst.type_declaration to the expected declaration. For
                // package types, compiler/ml/subst.ml:180-181 rewrites only
                // the package path and type arguments; it does not freshen the
                // typedtree-only pack_type from typetexp.ml:547-568.
                let expected_type_decl =
                    substitute_type_declaration_paths(type_ctx, sig_type_decl, subst);
                type_declarations(
                    type_ctx,
                    env,
                    impl_id.clone(),
                    impl_type_decl,
                    &expected_type_decl,
                )?;
            }
            (
                SignatureItem::SigTypext(impl_id, impl_ext_constr, _),
                SignatureItem::SigTypext(_, sig_ext_constr, _),
            ) => {
                extension_constructors(
                    type_ctx,
                    env,
                    impl_id.clone(),
                    impl_ext_constr,
                    sig_ext_constr,
                )?;
                coercions.push((pair.runtime_pos, ModuleCoercion::Tcoerce_none));
            }
            (
                SignatureItem::SigModule(impl_id, impl_mod_decl, _),
                SignatureItem::SigModule(sig_id, sig_mod_decl, _),
            ) => {
                // Match compiler/ml/includemod.ml:396-413:
                // `module_declarations` always strengthens the implementation
                // module type and recurses through `modtypes` with the current
                // substitution rather than pre-substituting the declaration.
                let impl_mty = crate::types::ctype::strengthen_module_type_for_inclusion_path(
                    type_ctx,
                    env,
                    &Path::pident(impl_id.clone()),
                    &impl_mod_decl.md_type,
                );
                let nested_sig_access_path =
                    sig_access_path.map(|path| Path::pdot(path.clone(), sig_id.name()));
                let coercion = modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    &impl_mty,
                    &sig_mod_decl.md_type,
                    nested_sig_access_path.as_ref(),
                    false,
                )
                .map_err(|error| {
                    let name = impl_id.clone();
                    IncludeModError::InModule {
                        name: name.clone(),
                        error: Box::new(IncludeModError::ModuleTypesMismatch {
                            actual: Box::new(impl_mty.clone()),
                            expected: Box::new(sig_mod_decl.md_type.clone()),
                            error: Box::new(IncludeModError::InModule {
                                name,
                                error: Box::new(error),
                            }),
                        }),
                    }
                })?;
                coercions.push((pair.runtime_pos, coercion));
            }
            (
                SignatureItem::SigModtype(impl_id, impl_modtype_decl),
                SignatureItem::SigModtype(_, sig_modtype_decl),
            ) => {
                let expected_modtype_decl =
                    substitute_modtype_declaration_paths(type_ctx, sig_modtype_decl, subst);
                modtype_declarations(
                    type_ctx,
                    env,
                    impl_id.clone(),
                    impl_modtype_decl,
                    &expected_modtype_decl,
                )?;
            }
            (SignatureItem::SigClass, SignatureItem::SigClass)
            | (SignatureItem::SigClassType, SignatureItem::SigClassType) => {}
            _ => unreachable!(),
        }
    }

    Ok(coercions)
}

pub fn simplify_signature(sig: &Signature) -> Signature {
    let mut seen_values = HashSet::new();
    let mut simplified = Vec::with_capacity(sig.len());
    for item in sig.iter().rev() {
        match item {
            SignatureItem::SigValue(id, _) => {
                if seen_values.insert(id.name().to_string()) {
                    simplified.push(item.clone());
                }
            }
            _ => simplified.push(item.clone()),
        }
    }
    simplified.reverse();
    simplified
}

pub fn compunit<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    impl_name: &str,
    impl_sig: &Signature,
    _intf_name: &str,
    intf_sig: &Signature,
) -> IncludeModResult<ModuleCoercion> {
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

    // OCaml compiler/ml/includemod.ml:468-475 starts compilation-unit
    // inclusion from `signatures`; Rust additionally carries the persisted
    // compilation-unit access path so Subst.add_* mappings can cover CMI paths
    // like `Unit.Nested.t` that no longer appear as local `Pident`s.
    let subst = InclusionSubst::default();
    let access_path = Path::pident(Ident::create_persistent(module_name_from_source_filename(
        impl_name,
    )));
    signatures_with_subst(
        type_ctx,
        env,
        &subst,
        Some(&access_path),
        impl_sig,
        intf_sig,
    )
}

/// Check if signature `sig_impl` is a subtype of `sig_sig`.
pub fn signatures<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    sig_impl: &Signature,
    sig_sig: &Signature,
) -> IncludeModResult<ModuleCoercion> {
    let subst = InclusionSubst::default();
    signatures_with_subst(type_ctx, env, &subst, None, sig_impl, sig_sig)
}

fn signatures_with_subst<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    incoming_subst: &InclusionSubst,
    sig_access_path: Option<&Path>,
    sig_impl: &Signature,
    sig_sig: &Signature,
) -> IncludeModResult<ModuleCoercion> {
    let mut include_env = env.clone();
    // OCaml compiler/ml/includemod.ml:284-337 threads the current `Subst.t`
    // into nested signature checks, then extends it while pairing components.
    let mut subst = incoming_subst.clone();
    let len_sig = sig_sig
        .iter()
        .filter(|item| is_runtime_component(item))
        .count();
    let runtime_fields = sig_sig
        .iter()
        .filter(|item| is_runtime_component(item))
        .filter_map(runtime_component_name)
        .collect::<Vec<_>>();
    let id_pos_list = sig_impl
        .iter()
        .scan(0usize, |runtime_pos, item| {
            let current = match item {
                SignatureItem::SigModule(id, _, _) => {
                    Some((id.clone(), *runtime_pos, ModuleCoercion::Tcoerce_none))
                }
                _ => None,
            };
            if is_runtime_component(item) {
                *runtime_pos += 1;
            }
            Some(current)
        })
        .flatten()
        .collect::<Vec<_>>();

    for sig_item in sig_impl {
        add_sig_item_to_env(sig_item, &mut include_env);
    }

    let (len_impl, paired, errors) =
        pair_signature_items(sig_impl, sig_sig, sig_access_path, &mut subst);

    if !errors.is_empty() {
        return Err(IncludeModError::SignatureMismatch(errors));
    }

    let coercions =
        check_paired_signature_items(type_ctx, &include_env, &paired, sig_access_path, &subst)?;

    if len_impl == len_sig {
        Ok(simplify_structure_coercion(
            &coercions,
            &id_pos_list,
            &runtime_fields,
        ))
    } else {
        Ok(ModuleCoercion::Tcoerce_structure(
            coercions,
            id_pos_list,
            runtime_fields,
        ))
    }
}

// ============================================================================
// Component Inclusion
// ============================================================================

/// Check if value description `impl_desc` is a subtype of `sig_desc`.
fn value_descriptions<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    id: Ident,
    impl_desc: &ValueDescription,
    sig_desc: &ValueDescription,
    subst: &InclusionSubst,
) -> IncludeModResult<ModuleCoercion> {
    // Check that the value types are compatible
    // The implementation type should be more general than (or equal to) the signature type
    let expected_ty = substitute_value_type_paths(type_ctx, sig_desc.val_type, subst);

    // OCaml compiler/ml/includemod.ml:56-60 only substitutes the expected
    // value description before calling compiler/ml/includecore.ml:43-48,
    // where `Ctype.moregeneral` compares the two value types directly. Forcing
    // manifest aliases up front changes Env.normalize_path side effects and
    // shifts subsequent Ident stamps.
    let moregeneral = ctype::moregeneral(type_ctx, env, true, impl_desc.val_type, expected_ty);
    if !moregeneral {
        let mut expected_desc = sig_desc.clone();
        expected_desc.val_type = expected_ty;
        return Err(IncludeModError::ValueTypeMismatch {
            name: id,
            actual: impl_desc.clone(),
            expected: expected_desc,
        });
    }

    // OCaml: match (vd1.val_kind, vd2.val_kind) with
    // | Val_prim p, _ -> Tcoerce_primitive { pc_desc = p; pc_type = vd2.val_type; ... }
    // | _, Val_prim _ -> raise Dont_match
    // | _, _ -> Tcoerce_none
    match (&impl_desc.val_kind, &sig_desc.val_kind) {
        (ValueKind::ValPrim(p1), ValueKind::ValPrim(_p2)) => {
            // Both are primitives - check compatibility (simplified: just accept)
            Ok(ModuleCoercion::Tcoerce_none)
        }
        (ValueKind::ValPrim(prim), _) => Ok(ModuleCoercion::Tcoerce_primitive(
            crate::types::typedtree::PrimitiveCoercion {
                pc_desc: prim.clone(),
                pc_type: sig_desc.val_type,
                pc_loc: impl_desc.val_loc.clone(),
                pc_id: id,
            },
        )),
        (_, ValueKind::ValPrim(_)) => {
            // Signature expects primitive but implementation is regular - mismatch
            // OCaml raises Dont_match here but we'll allow it for now
            Ok(ModuleCoercion::Tcoerce_none)
        }
        _ => Ok(ModuleCoercion::Tcoerce_none),
    }
}

fn add_sig_item_to_env(item: &SignatureItem, env: &mut Env) {
    match item {
        SignatureItem::SigValue(id, desc) => env.add_value(id.clone(), desc.clone()),
        SignatureItem::SigType(id, decl, _) => env.add_type(id.clone(), decl.clone()),
        SignatureItem::SigModule(id, md, _) => env.add_module(id.clone(), md.clone()),
        SignatureItem::SigModtype(id, mtd) => env.add_modtype(id.clone(), mtd.clone()),
        SignatureItem::SigTypext(_, _, _)
        | SignatureItem::SigClass
        | SignatureItem::SigClassType => {}
    }
}

fn substitute_value_description_paths<'a>(
    type_ctx: &'a TypeContext,
    desc: &ValueDescription,
    subst: &InclusionSubst,
) -> ValueDescription {
    // OCaml compiler/ml/subst.ml:303-309 copies a value description and runs
    // the full current substitution over `val_type`.
    let mut substituted = desc.clone();
    substituted.val_type = substitute_value_type_paths(type_ctx, desc.val_type, subst);
    substituted
}

fn substitute_label_declaration_paths<'a>(
    type_ctx: &'a TypeContext,
    label: &LabelDeclaration,
    subst: &InclusionSubst,
) -> LabelDeclaration {
    let mut substituted = label.clone();
    substituted.ld_type = substitute_value_type_paths(type_ctx, label.ld_type, subst);
    substituted
}

fn substitute_constructor_arguments_paths<'a>(
    type_ctx: &'a TypeContext,
    args: &ConstructorArguments,
    subst: &InclusionSubst,
) -> ConstructorArguments {
    match args {
        ConstructorArguments::CstrTuple(items) => ConstructorArguments::CstrTuple(
            items
                .iter()
                .map(|ty| substitute_value_type_paths(type_ctx, *ty, subst))
                .collect(),
        ),
        ConstructorArguments::CstrRecord(labels) => ConstructorArguments::CstrRecord(
            labels
                .iter()
                .map(|label| substitute_label_declaration_paths(type_ctx, label, subst))
                .collect(),
        ),
    }
}

fn substitute_constructor_declaration_paths<'a>(
    type_ctx: &'a TypeContext,
    constructor: &ConstructorDeclaration,
    subst: &InclusionSubst,
) -> ConstructorDeclaration {
    let mut substituted = constructor.clone();
    substituted.cd_args =
        substitute_constructor_arguments_paths(type_ctx, &constructor.cd_args, subst);
    substituted.cd_res = constructor
        .cd_res
        .map(|ty| substitute_value_type_paths(type_ctx, ty, subst));
    substituted
}

fn substitute_type_kind_paths<'a>(
    type_ctx: &'a TypeContext,
    kind: &TypeKind,
    subst: &InclusionSubst,
) -> TypeKind {
    match kind {
        TypeKind::TypeAbstract => TypeKind::TypeAbstract,
        TypeKind::TypeOpen => TypeKind::TypeOpen,
        TypeKind::TypeRecord(labels, repr) => TypeKind::TypeRecord(
            labels
                .iter()
                .map(|label| substitute_label_declaration_paths(type_ctx, label, subst))
                .collect(),
            repr.clone(),
        ),
        TypeKind::TypeVariant(constructors) => TypeKind::TypeVariant(
            constructors
                .iter()
                .map(|constructor| {
                    substitute_constructor_declaration_paths(type_ctx, constructor, subst)
                })
                .collect(),
        ),
    }
}

fn substitute_type_inlined_paths<'a>(
    type_ctx: &'a TypeContext,
    inlined: &TypeInlinedType,
    subst: &InclusionSubst,
) -> TypeInlinedType {
    match inlined {
        TypeInlinedType::Record { type_name, labels } => TypeInlinedType::Record {
            type_name: type_name.clone(),
            labels: labels
                .iter()
                .map(|label| substitute_label_declaration_paths(type_ctx, label, subst))
                .collect(),
        },
    }
}

fn substitute_type_declaration_paths<'a>(
    type_ctx: &'a TypeContext,
    decl: &TypeDeclaration,
    subst: &InclusionSubst,
) -> TypeDeclaration {
    // OCaml compiler/ml/includemod.ml:66-70 applies
    // `Subst.type_declaration` before comparing a signature declaration;
    // compiler/ml/subst.ml:273-301 copies params, manifest, and kind.
    let mut substituted = decl.clone();
    substituted.type_params = decl
        .type_params
        .iter()
        .map(|ty| substitute_value_type_paths(type_ctx, *ty, subst))
        .collect();
    substituted.type_manifest = decl
        .type_manifest
        .map(|ty| substitute_value_type_paths(type_ctx, ty, subst));
    substituted.type_kind = substitute_type_kind_paths(type_ctx, &decl.type_kind, subst);
    substituted.type_inlined_types = decl
        .type_inlined_types
        .iter()
        .map(|inlined| substitute_type_inlined_paths(type_ctx, inlined, subst))
        .collect();
    substituted
}

fn substitute_extension_constructor_paths<'a>(
    type_ctx: &'a TypeContext,
    ext: &ExtensionConstructor,
    subst: &InclusionSubst,
) -> ExtensionConstructor {
    // OCaml compiler/ml/includemod.ml:77-80 applies
    // `Subst.extension_constructor`; compiler/ml/subst.ml:311-325 copies
    // the extension path, params, arguments, and return type.
    let mut substituted = ext.clone();
    substituted.ext_type_path = substitute_type_constructor_path(&ext.ext_type_path, subst);
    substituted.ext_type_params = ext
        .ext_type_params
        .iter()
        .map(|ty| substitute_value_type_paths(type_ctx, *ty, subst))
        .collect();
    substituted.ext_args = substitute_constructor_arguments_paths(type_ctx, &ext.ext_args, subst);
    substituted.ext_ret_type = ext
        .ext_ret_type
        .map(|ty| substitute_value_type_paths(type_ctx, ty, subst));
    substituted
}

fn substitute_type_constructor_path(path: &Path, subst: &InclusionSubst) -> Path {
    if let Some(replacement) = lookup_path_subst(&subst.type_paths, path) {
        return replacement;
    }
    match path {
        Path::Pident(_) => path.clone(),
        Path::Pdot(prefix, name, pos) => Path::Pdot(
            std::sync::Arc::new(substitute_module_path(prefix, subst)),
            name.clone(),
            *pos,
        ),
        Path::Papply(functor, arg) => Path::Papply(
            std::sync::Arc::new(substitute_type_constructor_path(functor, subst)),
            std::sync::Arc::new(substitute_module_path(arg, subst)),
        ),
    }
}

fn substitute_module_path(path: &Path, subst: &InclusionSubst) -> Path {
    if let Some(replacement) = lookup_path_subst(&subst.module_paths, path) {
        return replacement;
    }
    match path {
        Path::Pident(_) => path.clone(),
        Path::Pdot(prefix, name, pos) => Path::Pdot(
            std::sync::Arc::new(substitute_module_path(prefix, subst)),
            name.clone(),
            *pos,
        ),
        Path::Papply(functor, arg) => Path::Papply(
            std::sync::Arc::new(substitute_module_path(functor, subst)),
            std::sync::Arc::new(substitute_module_path(arg, subst)),
        ),
    }
}

fn substitute_type_path(path: &Path, subst: &InclusionSubst) -> Path {
    if let Some(replacement) = lookup_path_subst(&subst.type_paths, path) {
        return replacement;
    }
    match path {
        Path::Pident(_) => path.clone(),
        Path::Pdot(prefix, name, pos) => Path::Pdot(
            std::sync::Arc::new(substitute_module_path(prefix, subst)),
            name.clone(),
            *pos,
        ),
        Path::Papply(functor, arg) => Path::Papply(
            std::sync::Arc::new(substitute_type_path(functor, subst)),
            std::sync::Arc::new(substitute_module_path(arg, subst)),
        ),
    }
}

fn substitute_modtype_path(path: &Path, subst: &InclusionSubst) -> Path {
    if let Some(replacement) = lookup_path_subst(&subst.modtype_paths, path) {
        return replacement;
    }
    match path {
        Path::Pident(_) => path.clone(),
        Path::Pdot(prefix, name, pos) => Path::Pdot(
            std::sync::Arc::new(substitute_module_path(prefix, subst)),
            name.clone(),
            *pos,
        ),
        Path::Papply(functor, arg) => Path::Papply(
            std::sync::Arc::new(substitute_modtype_path(functor, subst)),
            std::sync::Arc::new(substitute_module_path(arg, subst)),
        ),
    }
}

fn substitute_module_type_paths(
    type_ctx: &TypeContext,
    mty: &ModuleType,
    subst: &InclusionSubst,
) -> ModuleType {
    let mut substituted = substitute_module_type_paths_no_freshen(type_ctx, mty, subst);
    // OCaml compiler/ml/includemod.ml:396-421 checks expected-side module and
    // module-type declarations under a `Subst.t`. That reaches
    // compiler/ml/subst.ml:328-355, where `Subst.modtype` freshens every
    // signature/functor-bound identifier instead of only rewriting paths.
    crate::cmi::persistent_env::freshen_module_type_bound_idents(&mut substituted, type_ctx);
    substituted
}

fn substitute_module_type_paths_no_freshen(
    type_ctx: &TypeContext,
    mty: &ModuleType,
    subst: &InclusionSubst,
) -> ModuleType {
    // Mirrors OCaml Subst.modtype/signature, including functor-result module
    // substitution and nested signature component substitution.
    // See compiler/ml/subst.ml:345-356 and compiler/ml/subst.ml:358-389.
    match mty {
        ModuleType::MtyIdent(path) => ModuleType::MtyIdent(substitute_modtype_path(path, subst)),
        ModuleType::MtyAlias(presence, path) => {
            ModuleType::MtyAlias(*presence, substitute_module_path(path, subst))
        }
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => ModuleType::MtyFunctor {
            param: param.clone(),
            param_type: param_type.as_ref().map(|param_type| {
                Box::new(substitute_module_type_paths_no_freshen(
                    type_ctx, param_type, subst,
                ))
            }),
            result: Box::new(substitute_module_type_paths_no_freshen(
                type_ctx, result, subst,
            )),
        },
        ModuleType::MtySignature(sig) => ModuleType::MtySignature(
            sig.iter()
                .map(|item| match item {
                    SignatureItem::SigValue(id, desc) => SignatureItem::SigValue(
                        id.clone(),
                        substitute_value_description_paths(type_ctx, desc, subst),
                    ),
                    SignatureItem::SigType(id, decl, rec_status) => SignatureItem::SigType(
                        id.clone(),
                        substitute_type_declaration_paths(type_ctx, decl, subst),
                        *rec_status,
                    ),
                    SignatureItem::SigTypext(id, ext, ext_status) => SignatureItem::SigTypext(
                        id.clone(),
                        substitute_extension_constructor_paths(type_ctx, ext, subst),
                        *ext_status,
                    ),
                    SignatureItem::SigModule(id, md, rec_status) => SignatureItem::SigModule(
                        id.clone(),
                        substitute_module_declaration_paths_no_freshen(type_ctx, md, subst),
                        *rec_status,
                    ),
                    SignatureItem::SigModtype(id, mtd) => SignatureItem::SigModtype(
                        id.clone(),
                        substitute_modtype_declaration_paths_no_freshen(type_ctx, mtd, subst),
                    ),
                    _ => item.clone(),
                })
                .collect(),
        ),
    }
}

fn substitute_module_declaration_paths(
    _type_ctx: &TypeContext,
    md: &ModuleDeclaration,
    subst: &InclusionSubst,
) -> ModuleDeclaration {
    // OCaml compiler/ml/includemod.ml:396-413 does not call
    // `Subst.module_declaration` here. It passes the current substitution into
    // the recursive `modtypes` check, so this boundary only rewrites paths that
    // Rust cannot currently thread lazily through the recursion.
    substitute_module_declaration_paths_no_freshen(_type_ctx, md, subst)
}

fn substitute_module_declaration_paths_no_freshen(
    type_ctx: &TypeContext,
    md: &ModuleDeclaration,
    subst: &InclusionSubst,
) -> ModuleDeclaration {
    let mut substituted = md.clone();
    substituted.md_type = substitute_module_type_paths_no_freshen(type_ctx, &md.md_type, subst);
    substituted.md_path = md
        .md_path
        .as_ref()
        .map(|path| substitute_module_path(path, subst));
    substituted
}

fn substitute_modtype_declaration_paths(
    type_ctx: &TypeContext,
    mtd: &ModtypeDeclaration,
    subst: &InclusionSubst,
) -> ModtypeDeclaration {
    let mut substituted = substitute_modtype_declaration_paths_no_freshen(type_ctx, mtd, subst);
    if let Some(module_type) = substituted.mtd_type.as_mut() {
        crate::cmi::persistent_env::freshen_module_type_bound_idents(module_type, type_ctx);
    }
    substituted
}

fn substitute_modtype_declaration_paths_no_freshen(
    type_ctx: &TypeContext,
    mtd: &ModtypeDeclaration,
    subst: &InclusionSubst,
) -> ModtypeDeclaration {
    let mut substituted = mtd.clone();
    substituted.mtd_type = mtd
        .mtd_type
        .as_ref()
        .map(|mty| substitute_module_type_paths_no_freshen(type_ctx, mty, subst));
    substituted
}

fn substitute_value_type_paths<'a>(
    type_ctx: &'a TypeContext,
    ty: TypeExprRef,
    subst: &InclusionSubst,
) -> TypeExprRef {
    use crate::types::type_expr::{RowField, TypeDesc};

    if subst.is_empty() {
        return ty;
    }

    fn rewrite<'a>(
        type_ctx: &'a TypeContext,
        ty: TypeExprRef,
        subst: &InclusionSubst,
        seen: &mut HashSet<TypeExprRef>,
    ) {
        let ty = type_ctx.repr(ty);
        if !seen.insert(ty) {
            return;
        }

        let desc = type_ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, args, abbrev } => {
                for arg in args {
                    rewrite(type_ctx, *arg, subst, seen);
                }
                let new_path = substitute_type_constructor_path(path, subst);
                if new_path != *path {
                    type_ctx.set_desc(
                        ty,
                        TypeDesc::Tconstr {
                            path: new_path,
                            args: args.clone(),
                            abbrev: *abbrev,
                        },
                    );
                }
            }
            TypeDesc::Tarrow { arg, ret, .. } => {
                rewrite(type_ctx, arg.typ, subst, seen);
                rewrite(type_ctx, *ret, subst, seen);
            }
            TypeDesc::Ttuple(items) => {
                for item in items {
                    rewrite(type_ctx, *item, subst, seen);
                }
            }
            TypeDesc::Tobject { fields, .. } => {
                rewrite(type_ctx, *fields, subst, seen);
            }
            TypeDesc::Tfield { typ, rest, .. } => {
                rewrite(type_ctx, *typ, subst, seen);
                rewrite(type_ctx, *rest, subst, seen);
            }
            TypeDesc::Tvariant(row0) => {
                let row = crate::types::btype::row_repr(type_ctx, &row0);
                for (_, field) in &row.row_fields {
                    match field {
                        RowField::Rpresent(Some(arg)) => rewrite(type_ctx, *arg, subst, seen),
                        RowField::Reither { types, .. } => {
                            for ty in types {
                                rewrite(type_ctx, *ty, subst, seen);
                            }
                        }
                        RowField::Rpresent(None) | RowField::Rabsent => {}
                    }
                }
                rewrite(type_ctx, row.row_more, subst, seen);
            }
            TypeDesc::Tpoly { body, vars } => {
                rewrite(type_ctx, *body, subst, seen);
                for var in vars {
                    rewrite(type_ctx, *var, subst, seen);
                }
            }
            TypeDesc::Tpackage { path, args, lids } => {
                for arg in args {
                    rewrite(type_ctx, *arg, subst, seen);
                }
                let new_path = substitute_modtype_path(path, subst);
                if new_path != *path {
                    type_ctx.set_desc(
                        ty,
                        TypeDesc::Tpackage {
                            path: new_path,
                            lids: lids.clone(),
                            args: args.clone(),
                        },
                    );
                }
            }
            TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                rewrite(type_ctx, *target, subst, seen);
            }
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
        }
    }

    // OCaml compiler/ml/includemod.ml:56-60 applies `Subst.value_description`
    // before more-general checking; compiler/ml/subst.ml:303-309 copies and
    // substitutes the value type rather than mutating the original scheme.
    let copied = ctype::subst_identity_copy(type_ctx, ty);
    let mut seen = HashSet::new();
    rewrite(type_ctx, copied, subst, &mut seen);
    copied
}

/// Check if type declaration `impl_decl` is a subtype of `sig_decl`.
pub(crate) fn type_declarations<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    id: Ident,
    impl_decl: &TypeDeclaration,
    sig_decl: &TypeDeclaration,
) -> IncludeModResult<()> {
    // Check arity (number of type parameters)
    if impl_decl.type_params.len() != sig_decl.type_params.len() {
        return Err(IncludeModError::TypeMismatch {
            name: id,
            reason: format!(
                "arity mismatch: expected {} type parameters, found {}",
                sig_decl.type_params.len(),
                impl_decl.type_params.len()
            ),
        });
    }

    force_package_manifest_inclusion_side_effects(type_ctx, env, impl_decl, sig_decl);

    let param_map = build_type_param_map(type_ctx, &impl_decl.type_params, &sig_decl.type_params);
    if let Some(sig_manifest) = sig_decl.type_manifest {
        let manifests_match = impl_decl.type_manifest.is_some_and(|impl_manifest| {
            type_exprs_equal_for_inclusion(type_ctx, &param_map, impl_manifest, sig_manifest)
        });
        if !manifests_match {
            return Err(IncludeModError::TypeDeclarationMismatch {
                name: id,
                actual: impl_decl.clone(),
                expected: sig_decl.clone(),
                detail: String::new(),
            });
        }
    }

    // Match OCaml's Includecore.type_declarations variance check.
    let sig_is_abstract = matches!(
        sig_decl.type_kind,
        crate::types::decl::TypeKind::TypeAbstract
    ) && sig_decl.type_manifest.is_none();
    let need_variance = sig_is_abstract
        || matches!(impl_decl.type_private, crate::types::PrivateFlag::Private)
        || matches!(impl_decl.type_kind, crate::types::decl::TypeKind::TypeOpen);
    if need_variance && impl_decl.type_variance.len() == sig_decl.type_variance.len() {
        let abstract_or_private =
            sig_is_abstract || matches!(sig_decl.type_private, crate::types::PrivateFlag::Private);
        let open_sig = matches!(sig_decl.type_kind, crate::types::decl::TypeKind::TypeOpen)
            && sig_decl.type_manifest.is_none();

        for (i, (sig_param, (impl_var, sig_var))) in sig_decl
            .type_params
            .iter()
            .zip(
                impl_decl
                    .type_variance
                    .iter()
                    .zip(sig_decl.type_variance.iter()),
            )
            .enumerate()
        {
            let implies = |lhs: bool, rhs: bool| !lhs || rhs;
            let constrained = !crate::types::btype::is_tvar(type_ctx, *sig_param);

            let (impl_co, impl_cn) = impl_var.get_upper();
            let (sig_co, sig_cn) = sig_var.get_upper();
            let upper_ok = if abstract_or_private {
                implies(impl_co, sig_co) && implies(impl_cn, sig_cn)
            } else if open_sig || constrained {
                impl_co == sig_co && impl_cn == sig_cn
            } else {
                true
            };

            let (impl_p, impl_n, impl_i, impl_j) = impl_var.get_lower();
            let (sig_p, sig_n, sig_i, sig_j) = sig_var.get_lower();
            let lower_ok = implies(
                abstract_or_private,
                implies(sig_p, impl_p)
                    && implies(sig_n, impl_n)
                    && implies(sig_i, impl_i)
                    && implies(sig_j, impl_j),
            );

            if !(upper_ok && lower_ok) {
                return Err(IncludeModError::TypeMismatch {
                    name: id,
                    reason: format!("variance mismatch at parameter {}", i),
                });
            }
        }
    }

    // Check that the type kinds are compatible
    match (&impl_decl.type_kind, &sig_decl.type_kind) {
        // Abstract in signature allows any implementation
        (_, crate::types::decl::TypeKind::TypeAbstract) => Ok(()),

        _ if impl_decl.type_unboxed.unboxed != sig_decl.type_unboxed.unboxed => {
            let unboxed_decl = if sig_decl.type_unboxed.unboxed {
                "the second"
            } else {
                "the first"
            };
            Err(IncludeModError::TypeDeclarationMismatch {
                name: id,
                actual: impl_decl.clone(),
                expected: sig_decl.clone(),
                detail: format!(
                    "Their internal representations differ:\n{unboxed_decl} declaration uses unboxed representation."
                ),
            })
        }

        (
            crate::types::decl::TypeKind::TypeRecord(impl_labels, _),
            crate::types::decl::TypeKind::TypeRecord(sig_labels, _),
        ) => {
            if let Some(detail) = compare_record_declarations(
                type_ctx,
                &impl_decl.type_params,
                &sig_decl.type_params,
                impl_labels,
                sig_labels,
            ) {
                Err(IncludeModError::TypeDeclarationMismatch {
                    name: id,
                    actual: impl_decl.clone(),
                    expected: sig_decl.clone(),
                    detail,
                })
            } else {
                Ok(())
            }
        }

        (
            crate::types::decl::TypeKind::TypeVariant(impl_constructors),
            crate::types::decl::TypeKind::TypeVariant(sig_constructors),
        ) => {
            if let Some(detail) = compare_variant_declarations(
                type_ctx,
                &impl_decl.type_params,
                &sig_decl.type_params,
                impl_constructors,
                sig_constructors,
            ) {
                Err(IncludeModError::TypeDeclarationMismatch {
                    name: id,
                    actual: impl_decl.clone(),
                    expected: sig_decl.clone(),
                    detail,
                })
            } else {
                Ok(())
            }
        }

        // Same kind is fine
        (k1, k2) if std::mem::discriminant(k1) == std::mem::discriminant(k2) => {
            // Would need deeper checking for record/variant fields
            Ok(())
        }

        _ => Err(IncludeModError::TypeMismatch {
            name: id,
            reason: "incompatible type kinds".to_string(),
        }),
    }
}

fn compare_record_declarations(
    type_ctx: &TypeContext,
    impl_params: &[TypeExprRef],
    sig_params: &[TypeExprRef],
    impl_labels: &[LabelDeclaration],
    sig_labels: &[LabelDeclaration],
) -> Option<String> {
    let param_map = build_type_param_map(type_ctx, impl_params, sig_params);
    let mut index = 0usize;
    let len = impl_labels.len().min(sig_labels.len());

    while index < len {
        let impl_label = &impl_labels[index];
        let sig_label = &sig_labels[index];
        if impl_label.ld_id.name() != sig_label.ld_id.name() {
            return Some(format!(
                "Fields number {} have different names, {} and {}.",
                index,
                impl_label.ld_id.name(),
                sig_label.ld_id.name()
            ));
        }
        if impl_label.ld_mutable != sig_label.ld_mutable {
            return Some(format!(
                "The mutability of field {} is different.",
                impl_label.ld_id.name()
            ));
        }
        if impl_label.ld_optional != sig_label.ld_optional {
            return Some(format!(
                "The optional attribute of field {} is different.",
                impl_label.ld_id.name()
            ));
        }
        if !type_exprs_equal_for_inclusion(
            type_ctx,
            &param_map,
            impl_label.ld_type,
            sig_label.ld_type,
        ) {
            return Some(format!(
                "The types for field {} are not equal.",
                impl_label.ld_id.name()
            ));
        }
        index += 1;
    }

    if let Some(label) = sig_labels.get(index) {
        return Some(format!(
            "The field {} is only present in the second declaration.",
            label.ld_id.name()
        ));
    }
    if let Some(label) = impl_labels.get(index) {
        return Some(format!(
            "The field {} is only present in the first declaration.",
            label.ld_id.name()
        ));
    }

    None
}

fn compare_variant_declarations(
    type_ctx: &TypeContext,
    impl_params: &[TypeExprRef],
    sig_params: &[TypeExprRef],
    impl_constructors: &[ConstructorDeclaration],
    sig_constructors: &[ConstructorDeclaration],
) -> Option<String> {
    let param_map = build_type_param_map(type_ctx, impl_params, sig_params);
    let mut index = 0usize;
    let len = impl_constructors.len().min(sig_constructors.len());

    while index < len {
        let impl_constructor = &impl_constructors[index];
        let sig_constructor = &sig_constructors[index];
        if impl_constructor.cd_id.name() != sig_constructor.cd_id.name() {
            return Some(format!(
                "Fields number {} have different names, {} and {}.",
                index,
                impl_constructor.cd_id.name(),
                sig_constructor.cd_id.name()
            ));
        }

        match (&impl_constructor.cd_args, &sig_constructor.cd_args) {
            (
                ConstructorArguments::CstrRecord(impl_labels),
                ConstructorArguments::CstrRecord(sig_labels),
            ) => {
                if let Some(detail) = compare_record_declarations(
                    type_ctx,
                    impl_params,
                    sig_params,
                    impl_labels,
                    sig_labels,
                ) {
                    return Some(detail);
                }
            }
            (
                ConstructorArguments::CstrTuple(impl_args),
                ConstructorArguments::CstrTuple(sig_args),
            ) if impl_args.len() != sig_args.len() => {
                return Some(format!(
                    "The arities for field {} differ.",
                    impl_constructor.cd_id.name()
                ));
            }
            (
                ConstructorArguments::CstrTuple(impl_args),
                ConstructorArguments::CstrTuple(sig_args),
            ) => {
                for (impl_arg, sig_arg) in impl_args.iter().zip(sig_args.iter()) {
                    if !type_exprs_equal_for_inclusion(type_ctx, &param_map, *impl_arg, *sig_arg) {
                        return Some(format!(
                            "The types for field {} are not equal.",
                            impl_constructor.cd_id.name()
                        ));
                    }
                }
            }
            _ => {
                return Some(format!(
                    "The types for field {} are not equal.",
                    impl_constructor.cd_id.name()
                ));
            }
        }

        index += 1;
    }

    if let Some(constructor) = sig_constructors.get(index) {
        return Some(format!(
            "The field {} is only present in the second declaration.",
            constructor.cd_id.name()
        ));
    }
    if let Some(constructor) = impl_constructors.get(index) {
        return Some(format!(
            "The field {} is only present in the first declaration.",
            constructor.cd_id.name()
        ));
    }

    None
}

fn build_type_param_map(
    type_ctx: &TypeContext,
    impl_params: &[TypeExprRef],
    sig_params: &[TypeExprRef],
) -> HashMap<TypeExprRef, TypeExprRef> {
    impl_params
        .iter()
        .zip(sig_params.iter())
        .map(|(impl_param, sig_param)| (type_ctx.repr(*impl_param), type_ctx.repr(*sig_param)))
        .collect()
}

fn type_exprs_equal_for_inclusion(
    type_ctx: &TypeContext,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
    impl_ty: TypeExprRef,
    sig_ty: TypeExprRef,
) -> bool {
    let mut seen = HashSet::new();
    type_exprs_equal_for_inclusion_inner(type_ctx, param_map, impl_ty, sig_ty, &mut seen)
}

fn type_exprs_equal_for_inclusion_inner(
    type_ctx: &TypeContext,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
    impl_ty: TypeExprRef,
    sig_ty: TypeExprRef,
    seen: &mut HashSet<(TypeExprRef, TypeExprRef)>,
) -> bool {
    let impl_ty = type_ctx.repr(impl_ty);
    let sig_ty = type_ctx.repr(sig_ty);

    if !seen.insert((impl_ty, sig_ty)) {
        return true;
    }

    if let Some(mapped_sig) = param_map.get(&impl_ty) {
        return type_ctx.repr(*mapped_sig) == sig_ty;
    }
    if param_map
        .values()
        .any(|mapped_sig| type_ctx.repr(*mapped_sig) == sig_ty)
    {
        return false;
    }

    match (&*type_ctx.get_desc(impl_ty), &*type_ctx.get_desc(sig_ty)) {
        (TypeDesc::Tvar(impl_name), TypeDesc::Tvar(sig_name))
        | (TypeDesc::Tunivar(impl_name), TypeDesc::Tunivar(sig_name)) => impl_name == sig_name,
        (
            TypeDesc::Tarrow {
                arg: impl_arg,
                ret: impl_ret,
                ..
            },
            TypeDesc::Tarrow {
                arg: sig_arg,
                ret: sig_ret,
                ..
            },
        ) => {
            arg_labels_equal(&impl_arg.lbl, &sig_arg.lbl)
                && type_exprs_equal_for_inclusion_inner(
                    type_ctx,
                    param_map,
                    impl_arg.typ,
                    sig_arg.typ,
                    seen,
                )
                && type_exprs_equal_for_inclusion_inner(
                    type_ctx, param_map, *impl_ret, *sig_ret, seen,
                )
        }
        (TypeDesc::Ttuple(impl_items), TypeDesc::Ttuple(sig_items)) => {
            impl_items.len() == sig_items.len()
                && impl_items
                    .iter()
                    .zip(sig_items.iter())
                    .all(|(impl_item, sig_item)| {
                        type_exprs_equal_for_inclusion_inner(
                            type_ctx, param_map, *impl_item, *sig_item, seen,
                        )
                    })
        }
        (
            TypeDesc::Tconstr {
                path: impl_path,
                args: impl_args,
                ..
            },
            TypeDesc::Tconstr {
                path: sig_path,
                args: sig_args,
                ..
            },
        ) => {
            impl_path.same(sig_path)
                && impl_args.len() == sig_args.len()
                && impl_args
                    .iter()
                    .zip(sig_args.iter())
                    .all(|(impl_arg, sig_arg)| {
                        type_exprs_equal_for_inclusion_inner(
                            type_ctx, param_map, *impl_arg, *sig_arg, seen,
                        )
                    })
        }
        (TypeDesc::Tlink(impl_next), _) | (TypeDesc::Tsubst(impl_next), _) => {
            type_exprs_equal_for_inclusion_inner(type_ctx, param_map, *impl_next, sig_ty, seen)
        }
        (_, TypeDesc::Tlink(sig_next)) | (_, TypeDesc::Tsubst(sig_next)) => {
            type_exprs_equal_for_inclusion_inner(type_ctx, param_map, impl_ty, *sig_next, seen)
        }
        (
            TypeDesc::Tpoly {
                body: impl_body, ..
            },
            TypeDesc::Tpoly { body: sig_body, .. },
        ) => type_exprs_equal_for_inclusion_inner(type_ctx, param_map, *impl_body, *sig_body, seen),
        (
            TypeDesc::Tpackage {
                path: impl_path,
                args: impl_args,
                ..
            },
            TypeDesc::Tpackage {
                path: sig_path,
                args: sig_args,
                ..
            },
        ) => {
            impl_path.same(sig_path)
                && impl_args.len() == sig_args.len()
                && impl_args
                    .iter()
                    .zip(sig_args.iter())
                    .all(|(impl_arg, sig_arg)| {
                        type_exprs_equal_for_inclusion_inner(
                            type_ctx, param_map, *impl_arg, *sig_arg, seen,
                        )
                    })
        }
        (TypeDesc::Tnil, TypeDesc::Tnil) => true,
        _ => impl_ty == sig_ty,
    }
}

fn arg_labels_equal(left: &ArgLabel, right: &ArgLabel) -> bool {
    match (left, right) {
        (ArgLabel::Nolabel, ArgLabel::Nolabel) => true,
        (ArgLabel::Labelled(left), ArgLabel::Labelled(right))
        | (ArgLabel::Optional(left), ArgLabel::Optional(right)) => left.txt == right.txt,
        _ => false,
    }
}

fn force_package_manifest_inclusion_side_effects<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    impl_decl: &TypeDeclaration,
    sig_decl: &TypeDeclaration,
) {
    let (Some(impl_manifest), Some(sig_manifest)) =
        (impl_decl.type_manifest, sig_decl.type_manifest)
    else {
        return;
    };

    let impl_manifest = type_ctx.repr(impl_manifest);
    let sig_manifest = type_ctx.repr(sig_manifest);
    let impl_desc = type_ctx.get_desc(impl_manifest);
    let sig_desc = type_ctx.get_desc(sig_manifest);
    let (
        TypeDesc::Tpackage {
            path: impl_path,
            lids: impl_lids,
            ..
        },
        TypeDesc::Tpackage {
            path: sig_path,
            lids: sig_lids,
            ..
        },
    ) = (&*impl_desc, &*sig_desc)
    else {
        return;
    };
    let impl_path = impl_path.clone();
    let sig_path = sig_path.clone();
    let impl_lids = impl_lids.clone();
    let sig_lids = sig_lids.clone();
    drop(impl_desc);
    drop(sig_desc);

    // OCaml compiler/ml/includecore.ml:87-151 compares manifests with
    // `Ctype.equal`; for package types that reaches compiler/ml/ctype.ml:2237-2238,
    // which calls `complete_type_list` twice. `complete_type_list` allocates
    // a hidden `Pkg` module at compiler/ml/ctype.ml:2199-2201 even when both
    // packages already list the same labels.
    let _ = crate::types::ctype::package_type_lists_have_ocaml_same_label_completion_side_effect(
        type_ctx,
        Some(env),
        ModuleType::MtyIdent(sig_path),
        &impl_lids,
        &sig_lids,
    );
    let _ = crate::types::ctype::package_type_lists_have_ocaml_same_label_completion_side_effect(
        type_ctx,
        Some(env),
        ModuleType::MtyIdent(impl_path),
        &sig_lids,
        &impl_lids,
    );
}

/// Check if extension constructor `impl_ext` is compatible with `sig_ext`.
fn extension_constructors<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    id: Ident,
    impl_ext: &ExtensionConstructor,
    sig_ext: &ExtensionConstructor,
) -> IncludeModResult<()> {
    // Check that the extension type paths match
    if impl_ext.ext_type_path != sig_ext.ext_type_path {
        return Err(IncludeModError::TypeMismatch {
            name: id,
            reason: "extension type path mismatch".to_string(),
        });
    }

    // Check that the argument types match
    // This would require deeper type checking in a full implementation
    Ok(())
}

/// Check if module type declaration `impl_decl` is compatible with `sig_decl`.
fn modtype_declarations<'a>(
    type_ctx: &'a TypeContext,
    env: &Env,
    id: Ident,
    impl_decl: &ModtypeDeclaration,
    sig_decl: &ModtypeDeclaration,
) -> IncludeModResult<()> {
    if impl_decl == sig_decl {
        return Ok(());
    }
    match (&impl_decl.mtd_type, &sig_decl.mtd_type) {
        // Both abstract - compatible
        (None, None) => Ok(()),

        // Signature is abstract - implementation can be anything
        (Some(_), None) => Ok(()),

        // Signature has type but implementation is abstract - error
        (None, Some(_)) => Err(IncludeModError::ModuleTypeMismatch {
            name: id,
            reason: "implementation is abstract but signature requires concrete type".to_string(),
        }),

        // Both have types - check compatibility (bidirectional)
        (Some(impl_mty), Some(sig_mty)) => {
            if impl_mty == sig_mty {
                return Ok(());
            }
            // Module types must be equivalent (both directions)
            modtypes(type_ctx, env, impl_mty, sig_mty)?;
            modtypes(type_ctx, env, sig_mty, impl_mty)?;
            Ok(())
        }
    }
}

// ============================================================================
// Utilities
// ============================================================================

/// Check if a signature is empty.
pub fn is_empty_signature(sig: &Signature) -> bool {
    sig.is_empty()
}

/// Get all value identifiers from a signature.
pub fn signature_values(sig: &Signature) -> Vec<&Ident> {
    sig.iter()
        .filter_map(|item| {
            if let SignatureItem::SigValue(id, _) = item {
                Some(id)
            } else {
                None
            }
        })
        .collect()
}

/// Get all type identifiers from a signature.
pub fn signature_types(sig: &Signature) -> Vec<&Ident> {
    sig.iter()
        .filter_map(|item| {
            if let SignatureItem::SigType(id, _, _) = item {
                Some(id)
            } else {
                None
            }
        })
        .collect()
}

/// Get all module identifiers from a signature.
pub fn signature_modules(sig: &Signature) -> Vec<&Ident> {
    sig.iter()
        .filter_map(|item| {
            if let SignatureItem::SigModule(id, _, _) = item {
                Some(id)
            } else {
                None
            }
        })
        .collect()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::location::Location;
    use crate::types::Path;
    use crate::types::decl::{
        ModtypeDeclaration, ModuleDeclaration, ModuleType, RecStatus, TypeKind, UnboxedStatus,
        ValueKind,
    };
    use crate::types::env::initial_env;

    fn abstract_type_decl(type_path: Option<Path>) -> TypeDeclaration {
        TypeDeclaration {
            type_params: vec![],
            type_arity: 0,
            type_kind: TypeKind::TypeAbstract,
            type_private: crate::types::PrivateFlag::Public,
            type_manifest: None,
            type_variance: vec![],
            type_newtype_level: None,
            type_loc: Location::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_unboxed: UnboxedStatus::FALSE_FALSE,
            type_inlined_types: vec![],
            type_path,
        }
    }

    fn value_desc(val_type: TypeExprRef) -> ValueDescription {
        ValueDescription {
            val_type,
            val_kind: ValueKind::ValReg,
            val_loc: Location::none(),
            val_attributes: vec![],
            val_path: None,
        }
    }

    #[test]
    fn test_empty_signatures_match() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&type_ctx);

        let sig_impl: Signature = vec![];
        let sig_sig: Signature = vec![];

        let result = signatures(&type_ctx, &env, &sig_impl, &sig_sig);
        assert!(result.is_ok());
    }

    #[test]
    fn test_missing_value_error() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&type_ctx);

        let sig_impl: Signature = vec![];
        let val_ty = type_ctx.new_var(None);
        let sig_sig: Signature = vec![SignatureItem::SigValue(
            Ident::create_local("x"),
            ValueDescription {
                val_type: val_ty,
                val_kind: ValueKind::ValReg,
                val_loc: Location::none(),
                val_attributes: vec![],
                val_path: None,
            },
        )];

        let result = signatures(&type_ctx, &env, &sig_impl, &sig_sig);
        assert!(matches!(result, Err(IncludeModError::SignatureMismatch(_))));
    }

    #[test]
    fn test_value_match() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&type_ctx);

        let val_ty = type_ctx.new_var(None);
        let sig_impl: Signature = vec![SignatureItem::SigValue(
            Ident::create_local("x"),
            ValueDescription {
                val_type: val_ty,
                val_kind: ValueKind::ValReg,
                val_loc: Location::none(),
                val_attributes: vec![],
                val_path: None,
            },
        )];
        let sig_sig: Signature = vec![SignatureItem::SigValue(
            Ident::create_local("x"),
            ValueDescription {
                val_type: val_ty,
                val_kind: ValueKind::ValReg,
                val_loc: Location::none(),
                val_attributes: vec![],
                val_path: None,
            },
        )];

        let result = signatures(&type_ctx, &env, &sig_impl, &sig_sig);
        assert!(result.is_ok());
    }

    #[test]
    fn test_signature_pairing_uses_final_type_substitution() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&type_ctx);

        let impl_type_id = Ident::create_local("t");
        let sig_type_id = Ident::create_local("t");
        let impl_mod_id = Ident::create_local("M");
        let sig_mod_id = Ident::create_local("M");

        let impl_ty = type_ctx.new_generic_constr(Path::pident(impl_type_id.clone()), vec![]);
        let sig_ty = type_ctx.new_generic_constr(Path::pident(sig_type_id.clone()), vec![]);

        let sig_impl: Signature = vec![
            SignatureItem::SigModule(
                impl_mod_id,
                ModuleDeclaration {
                    md_type: ModuleType::MtySignature(vec![SignatureItem::SigValue(
                        Ident::create_local("x"),
                        value_desc(impl_ty),
                    )]),
                    md_attributes: vec![],
                    md_loc: Location::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            ),
            SignatureItem::SigType(
                impl_type_id.clone(),
                abstract_type_decl(Some(Path::pident(impl_type_id))),
                RecStatus::TrecNot,
            ),
        ];
        let sig_sig: Signature = vec![
            SignatureItem::SigModule(
                sig_mod_id,
                ModuleDeclaration {
                    md_type: ModuleType::MtySignature(vec![SignatureItem::SigValue(
                        Ident::create_local("x"),
                        value_desc(sig_ty),
                    )]),
                    md_attributes: vec![],
                    md_loc: Location::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            ),
            SignatureItem::SigType(sig_type_id, abstract_type_decl(None), RecStatus::TrecNot),
        ];

        let result = signatures(&type_ctx, &env, &sig_impl, &sig_sig);
        assert!(matches!(result, Ok(ModuleCoercion::Tcoerce_none)));
    }

    #[test]
    fn test_signature_pairing_uses_last_matching_component() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&type_ctx);

        let val_ty = type_ctx.new_var(None);
        let sig_impl: Signature = vec![
            SignatureItem::SigValue(Ident::create_local("x"), value_desc(val_ty)),
            SignatureItem::SigValue(Ident::create_local("x"), value_desc(val_ty)),
        ];
        let sig_sig: Signature = vec![SignatureItem::SigValue(
            Ident::create_local("x"),
            value_desc(val_ty),
        )];

        let result = signatures(&type_ctx, &env, &sig_impl, &sig_sig).unwrap();
        match result {
            ModuleCoercion::Tcoerce_structure(coercions, _, runtime_fields) => {
                assert!(matches!(
                    coercions.as_slice(),
                    [(1, ModuleCoercion::Tcoerce_none)]
                ));
                assert_eq!(runtime_fields, vec!["x".to_string()]);
            }
            other => panic!("expected structure coercion, got {other:?}"),
        }
    }

    #[test]
    fn test_local_modtype_ident_matches_signature() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = initial_env(&type_ctx);

        let val_ty = type_ctx.new_var(None);
        let sig: Signature = vec![SignatureItem::SigValue(
            Ident::create_local("x"),
            value_desc(val_ty),
        )];
        let modtype_id = Ident::create_local("BeltList");
        env.add_modtype(
            modtype_id.clone(),
            ModtypeDeclaration {
                mtd_type: Some(ModuleType::MtySignature(sig.clone())),
                mtd_attributes: vec![],
                mtd_loc: Location::none(),
            },
        );

        let result = modtypes(
            &type_ctx,
            &env,
            &ModuleType::MtySignature(sig),
            &ModuleType::MtyIdent(Path::pident(modtype_id)),
        );
        assert!(matches!(result, Ok(ModuleCoercion::Tcoerce_none)));
    }

    #[test]
    fn test_functor_match() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&type_ctx);

        let param_sig = ModuleType::MtySignature(vec![]);
        let result_sig = ModuleType::MtySignature(vec![]);

        let mty_impl = ModuleType::MtyFunctor {
            param: Ident::create_local("X"),
            param_type: Some(Box::new(param_sig.clone())),
            result: Box::new(result_sig.clone()),
        };

        let mty_sig = ModuleType::MtyFunctor {
            param: Ident::create_local("X"),
            param_type: Some(Box::new(param_sig)),
            result: Box::new(result_sig),
        };

        let result = modtypes(&type_ctx, &env, &mty_impl, &mty_sig);
        assert!(result.is_ok());
    }

    #[test]
    fn test_signature_utilities() {
        let val_ty_placeholder = crate::types::TypeExprRef(0);

        let sig: Signature = vec![
            SignatureItem::SigValue(
                Ident::create_local("x"),
                ValueDescription {
                    val_type: val_ty_placeholder,
                    val_kind: ValueKind::ValReg,
                    val_loc: Location::none(),
                    val_attributes: vec![],
                    val_path: None,
                },
            ),
            SignatureItem::SigType(
                Ident::create_local("t"),
                TypeDeclaration {
                    type_params: vec![],
                    type_arity: 0,
                    type_kind: TypeKind::TypeAbstract,
                    type_private: crate::types::PrivateFlag::Public,
                    type_manifest: None,
                    type_variance: vec![],
                    type_newtype_level: None,
                    type_loc: Location::none(),
                    type_attributes: vec![],
                    type_immediate: false,
                    type_unboxed: UnboxedStatus::FALSE_FALSE,
                    type_inlined_types: vec![],
                    type_path: None,
                },
                RecStatus::TrecNot,
            ),
        ];

        assert!(!is_empty_signature(&sig));
        assert_eq!(signature_values(&sig).len(), 1);
        assert_eq!(signature_types(&sig).len(), 1);
        assert_eq!(signature_modules(&sig).len(), 0);
    }
}
