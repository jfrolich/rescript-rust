//! Module inclusion checking for ReScript.
//!
//! This module implements signature matching, which verifies that a module
//! implementation conforms to a module signature. This is equivalent to
//! OCaml's `includemod.ml`.
//!
//! The main function is `modtypes` which checks if one module type is
//! a subtype of another.

use crate::types::path::PathView;
use std::cell::Cell;

use crate::diagnostics::Warning;
use crate::fast_hash::{AHashMap as HashMap, AHashSet as HashSet};
use crate::ident::Ident;
use crate::location::Location;
use crate::types::Path;
use crate::types::asttypes::MutableFlag as FieldKind;
use crate::types::ctype;
use crate::types::decl::{
    Attribute, AttributePayload, ConstructorArguments, ConstructorDeclaration,
    ExtensionConstructor, LabelDeclaration, ModtypeDeclaration, ModuleDeclaration, ModuleType,
    RecStatus, Signature, SignatureItem, TypeDeclaration, TypeInlinedType, TypeKind,
    ValueDescription, ValueKind,
};
use crate::types::env::Env;
use crate::types::type_expr::{RowDesc, RowField, TypeDesc};
use crate::types::typedtree::ModuleCoercion;
use crate::types::{TypeContext, TypeExprRef};
use crate::parser::code_frame;

// ============================================================================
// Error Types
// ============================================================================

/// Result type for inclusion checking.
pub type IncludeModResult<T> = Result<T, IncludeModError>;

fn deprecated_payload_from_attrs<'a>(
    attrs: &'a [Attribute],
    names: &[&str],
) -> Option<&'a AttributePayload> {
    attrs
        .iter()
        .find(|attr| names.iter().any(|name| attr.attr_name.txt == *name))
        .map(|attr| &attr.attr_payload)
}

fn deprecated_payload_reason(payload: &AttributePayload) -> &str {
    match payload {
        AttributePayload::Deprecated { reason, .. } | AttributePayload::Str(reason) => {
            reason.as_str()
        }
        AttributePayload::Empty => "",
        _ => "",
    }
}

fn deprecated_inclusion_warning(
    type_ctx: &TypeContext,
    name: &str,
    impl_attrs: &[Attribute],
    sig_attrs: &[Attribute],
    def_loc: crate::types::DeclLoc,
    use_loc: crate::types::DeclLoc,
) -> Option<Warning> {
    let impl_payload =
        deprecated_payload_from_attrs(impl_attrs, &["deprecated", "ocaml.deprecated"])?;
    if deprecated_payload_from_attrs(sig_attrs, &["deprecated", "ocaml.deprecated"]).is_some() {
        return None;
    }
    let reason = deprecated_payload_reason(impl_payload);
    let message = if reason.is_empty() {
        name.to_string()
    } else {
        format!("{name}\n  {reason}")
    };
    Some(Warning::Deprecated {
        message,
        def_loc: type_ctx.resolve_loc(def_loc),
        use_loc: type_ctx.resolve_loc(use_loc),
        can_be_automigrated: false,
    })
}

fn deprecated_mutable_inclusion_warning(
    type_ctx: &TypeContext,
    name: &str,
    impl_attrs: &[Attribute],
    sig_attrs: &[Attribute],
    def_loc: crate::types::DeclLoc,
    use_loc: crate::types::DeclLoc,
) -> Option<Warning> {
    let impl_payload = deprecated_payload_from_attrs(
        impl_attrs,
        &["deprecated_mutable", "ocaml.deprecated_mutable"],
    )?;
    if deprecated_payload_from_attrs(
        sig_attrs,
        &["deprecated_mutable", "ocaml.deprecated_mutable"],
    )
    .is_some()
    {
        return None;
    }
    let reason = deprecated_payload_reason(impl_payload);
    let message = if reason.is_empty() {
        format!("mutating field {name}")
    } else {
        format!("mutating field {name}\n  {reason}")
    };
    Some(Warning::Deprecated {
        message,
        def_loc: type_ctx.resolve_loc(def_loc),
        use_loc: type_ctx.resolve_loc(use_loc),
        can_be_automigrated: false,
    })
}

/// Errors that can occur during module inclusion checking.
#[derive(Debug, Clone)]
pub enum IncludeModError {
    /// Missing signature field in implementation.
    MissingField {
        id: Ident,
        loc: crate::types::DeclLoc,
        kind: &'static str,
    },
    /// Value type mismatch.
    ValueTypeMismatch {
        name: Ident,
        actual: ValueDescription,
        expected: ValueDescription,
        arity_mismatch: Option<(usize, usize)>,
    },
    /// Type declaration mismatch.
    TypeMismatch { name: Ident, reason: String },
    /// Type declaration mismatch with enough context to print OCaml's report.
    TypeDeclarationMismatch {
        name: Ident,
        actual: TypeDeclaration,
        expected: TypeDeclaration,
        detail: TypeDeclarationMismatchDetail,
    },
    /// Extension constructor mismatch.
    ExtensionConstructorMismatch {
        name: Ident,
        actual: ExtensionConstructor,
        expected: ExtensionConstructor,
    },
    /// Module type mismatch.
    ModuleTypeMismatch { name: Ident, reason: String },
    /// Module type declaration mismatch.
    ModuleTypeDeclarationMismatch {
        name: Ident,
        actual: ModtypeDeclaration,
        expected: ModtypeDeclaration,
        error: Box<IncludeModError>,
    },
    /// Equivalent module type declarations require a structure-field permutation.
    ModtypePermutation,
    /// Nested module types do not include one another.
    ModuleTypesMismatch {
        actual: Box<ModuleType>,
        expected: Box<ModuleType>,
        error: Box<IncludeModError>,
    },
    /// A module alias normalized to a path whose compiled interface is missing.
    UnboundModulePath { path: Path },
    /// Nested include error reported in a module context.
    InModule {
        name: Ident,
        error: Box<IncludeModError>,
    },
    /// Nested include error reported in a functor result context.
    InFunctorBody {
        param: Ident,
        actual: Box<ModuleType>,
        expected: Box<ModuleType>,
        error: Box<IncludeModError>,
    },
    /// Nested include error reported in a module type position.
    AtModtype {
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

/// Structured counterpart of `Includecore.type_mismatch`.
///
/// Most inclusion checks still produce a pre-rendered detail while they are
/// ported, but semantic mismatches must remain distinguishable from their
/// diagnostic text. In particular, `TagName` originates from the canonical
/// variant layout rather than from a formatted declaration.
#[derive(Debug, Clone)]
pub enum TypeDeclarationMismatchDetail {
    TagName,
    Variance,
    Rendered(String),
}

impl TypeDeclarationMismatchDetail {
    fn message(&self) -> &str {
        match self {
            Self::TagName => "Their @tag annotations differ.",
            Self::Variance => "Their variances do not agree.",
            Self::Rendered(message) => message,
        }
    }
}

impl From<String> for TypeDeclarationMismatchDetail {
    fn from(value: String) -> Self {
        Self::Rendered(value)
    }
}

impl From<&str> for TypeDeclarationMismatchDetail {
    fn from(value: &str) -> Self {
        Self::Rendered(value.to_string())
    }
}

pub fn format_error(type_ctx: &TypeContext, filename: &str, error: &IncludeModError) -> String {
    let mut output = String::new();
    output.push_str("  Signature mismatch:\n");
    format_include_error(type_ctx, filename, error, &mut Vec::new(), &mut output);
    output
}

pub(crate) fn format_error_without_signature_header(
    type_ctx: &TypeContext,
    filename: &str,
    error: &IncludeModError,
) -> String {
    let mut output = String::new();
    format_include_error(type_ctx, filename, error, &mut Vec::new(), &mut output);
    output
}

/// OCaml `Includemod.show_loc` (includemod.ml:489-490):
/// `@\n@[<2>%a:@ %s@]`, which stays on one line when it fits the 78-column
/// margin and otherwise breaks with a 2-space indent.
fn push_show_loc(output: &mut String, location: &str, message: &str) {
    // Width is measured on the plain text; colour codes are Format tags.
    let fits = 2 + location.len() + 2 + message.len() <= 77;
    let location = code_frame::colorize_location(location);
    if fits {
        output.push_str("  ");
        output.push_str(&location);
        output.push_str(": ");
        output.push_str(message);
        output.push('\n');
    } else {
        output.push_str("  ");
        output.push_str(&location);
        output.push_str(":\n    ");
        output.push_str(message);
        output.push('\n');
    }
}

/// One step of `Includemod.error` contexts (includemod.ml:28-32).
#[derive(Clone)]
enum IncludeContext {
    Module(Ident),
    Modtype(Ident),
    Body(Ident),
}

/// `Includemod.context` (includemod.ml:591-631) for a context listed from
/// the outermost step, when it fits on one line.
fn include_context_text(cxt: &[IncludeContext]) -> String {
    fn argname(id: &Ident) -> &str {
        if id.name() == "*" { "" } else { id.name() }
    }
    fn context(cxt: &[IncludeContext]) -> String {
        match cxt {
            [IncludeContext::Module(id), rem @ ..] => format!("module {}{}", id.name(), args(rem)),
            [IncludeContext::Modtype(id), rem @ ..] => {
                format!("module type {} = {}", id.name(), context_mty(rem))
            }
            [IncludeContext::Body(x), rem @ ..] => {
                format!("functor ({}) -> {}", argname(x), context_mty(rem))
            }
            [] => "<here>".to_string(),
        }
    }
    fn context_mty(cxt: &[IncludeContext]) -> String {
        match cxt {
            [IncludeContext::Module(_) | IncludeContext::Modtype(_), ..] => {
                format!("sig {} end", context(cxt))
            }
            _ => context(cxt),
        }
    }
    fn args(cxt: &[IncludeContext]) -> String {
        match cxt {
            [IncludeContext::Body(x), rem @ ..] => format!("({}){}", argname(x), args(rem)),
            _ => format!(" : {}", context_mty(cxt)),
        }
    }
    context(cxt)
}

/// The context part of `include_err` (includemod.ml:633-650): nothing at the
/// top, `In module A.B:` inside plain submodules, otherwise
/// `At position <context>`.
fn push_include_context(cxt: &[IncludeContext], output: &mut String) {
    if cxt.is_empty() {
        return;
    }
    if cxt
        .iter()
        .all(|step| matches!(step, IncludeContext::Module(_)))
    {
        output.push_str("  In module ");
        let names: Vec<&str> = cxt
            .iter()
            .map(|step| match step {
                IncludeContext::Module(id) => id.name(),
                _ => unreachable!(),
            })
            .collect();
        output.push_str(&names.join("."));
        output.push_str(":\n");
    } else {
        output.push_str("  At position ");
        output.push_str(&include_context_text(cxt));
        output.push('\n');
    }
}

/// `Module_types` in `include_symptom`, with the elision that stands in for
/// `is_big` in `report_error`.
fn push_module_types_symptom(
    type_ctx: &TypeContext,
    actual: &ModuleType,
    expected: &ModuleType,
    error: &IncludeModError,
    output: &mut String,
) {
    let actual_text = format_module_type(type_ctx, actual);
    let expected_text = format_module_type(type_ctx, expected);
    if should_elide_module_mismatch(&actual_text, &expected_text)
        || should_elide_type_declaration_module_mismatch(error)
    {
        output.push_str("  ...\n");
    } else if is_compact_type_declaration_mismatch(error) {
        output.push_str("  Modules do not match: ");
        output.push_str(&actual_text);
        output.push_str(" is not included in ");
        output.push_str(&expected_text);
        output.push('\n');
    } else {
        output.push_str(&format_modules_do_not_match(&actual_text, &expected_text));
    }
}

/// `report_error` (includemod.ml:663-676) over Rust's nested error tree: each
/// entry of OCaml's flat error list is printed with its own context.
fn format_include_error(
    type_ctx: &TypeContext,
    filename: &str,
    error: &IncludeModError,
    cxt: &mut Vec<IncludeContext>,
    output: &mut String,
) {
    match error {
        IncludeModError::SignatureMismatch(errors) => {
            for error in errors {
                format_include_error(type_ctx, filename, error, cxt, output);
            }
            return;
        }
        IncludeModError::InModule { name, error } => {
            cxt.push(IncludeContext::Module(*name));
            format_include_error(type_ctx, filename, error, cxt, output);
            cxt.pop();
            return;
        }
        IncludeModError::AtModtype { name, error } => {
            cxt.push(IncludeContext::Modtype(*name));
            format_include_error(type_ctx, filename, error, cxt, output);
            cxt.pop();
            return;
        }
        IncludeModError::InFunctorBody {
            param,
            actual,
            expected,
            error,
        } => {
            // `modtypes` on the functor results (includemod.ml:388-396) runs
            // in `Body param :: cxt`.
            cxt.push(IncludeContext::Body(*param));
            push_include_context(cxt, output);
            push_module_types_symptom(type_ctx, actual, expected, error, output);
            if !matches!(**error, IncludeModError::ModuleTypeMismatch { .. }) {
                format_include_error(type_ctx, filename, error, cxt, output);
            }
            cxt.pop();
            return;
        }
        _ => {}
    }
    push_include_context(cxt, output);
    match error {
        IncludeModError::SignatureMismatch(_)
        | IncludeModError::InModule { .. }
        | IncludeModError::AtModtype { .. }
        | IncludeModError::InFunctorBody { .. } => unreachable!(),
        IncludeModError::ModuleTypesMismatch {
            actual,
            expected,
            error,
        } => {
            push_module_types_symptom(type_ctx, actual, expected, error, output);
            // A bare `ModuleTypeMismatch` below stands for `Dont_match`, which
            // only contributes the `Module_types` entry (includemod.ml:222-229).
            if !matches!(**error, IncludeModError::ModuleTypeMismatch { .. }) {
                format_include_error(type_ctx, filename, error, cxt, output);
            }
        }
        IncludeModError::UnboundModulePath { path } => {
            output.push_str("  Unbound module ");
            output.push_str(&path.name());
            output.push('\n');
        }
        IncludeModError::TypeDeclarationMismatch {
            name,
            actual,
            expected,
            detail,
        } => {
            // includemod.ml:555-561:
            // "@[<hv>%s:@;<1 2>%a@ %s@;<1 2>%a@]" -- one line when it fits.
            let actual_text = format_type_declaration(type_ctx, name, actual);
            let expected_text = format_type_declaration(type_ctx, name, expected);
            if hv_fits_on_one_line(&[
                "Type declarations do not match:",
                &actual_text,
                "is not included in",
                &expected_text,
            ]) {
                output.push_str("  Type declarations do not match: ");
                output.push_str(&actual_text);
                output.push_str(" is not included in ");
                output.push_str(&expected_text);
                output.push('\n');
            } else {
                output.push_str("  Type declarations do not match:\n");
                output.push_str("    ");
                output.push_str(&actual_text);
                output.push('\n');
                output.push_str("  is not included in\n");
                output.push_str("    ");
                output.push_str(&expected_text);
                output.push('\n');
            }
            push_show_loc(
                output,
                &{
                    let loc = type_ctx.resolve_loc(expected.type_loc);
                    code_frame::format_location(
                        &location_filename(type_ctx, filename, &loc),
                        &loc.loc_start,
                        &loc.loc_end,
                    )
                },
                "Expected declaration",
            );
            push_show_loc(
                output,
                &{
                    let loc = type_ctx.resolve_loc(actual.type_loc);
                    code_frame::format_location(
                        &location_filename(type_ctx, filename, &loc),
                        &loc.loc_start,
                        &loc.loc_end,
                    )
                },
                "Actual declaration",
            );
            for line in detail.message().lines() {
                output.push_str("  ");
                output.push_str(line);
                output.push('\n');
            }
        }
        IncludeModError::ExtensionConstructorMismatch {
            name,
            actual,
            expected,
        } => {
            output.push_str("  Extension declarations do not match:\n");
            output.push_str("    ");
            output.push_str(&format_extension_constructor(type_ctx, name, actual));
            output.push('\n');
            output.push_str("  is not included in\n");
            output.push_str("    ");
            output.push_str(&format_extension_constructor(type_ctx, name, expected));
            output.push('\n');
            push_show_loc(
                output,
                &{
                    let loc = type_ctx.resolve_loc(expected.ext_loc);
                    code_frame::format_location(
                        &location_filename(type_ctx, filename, &loc),
                        &loc.loc_start,
                        &loc.loc_end,
                    )
                },
                "Expected declaration",
            );
            push_show_loc(
                output,
                &{
                    let loc = type_ctx.resolve_loc(actual.ext_loc);
                    code_frame::format_location(
                        &location_filename(type_ctx, filename, &loc),
                        &loc.loc_start,
                        &loc.loc_end,
                    )
                },
                "Actual declaration",
            );
        }
        IncludeModError::MissingField { id, loc, kind } => {
            output.push_str("  The ");
            output.push_str(kind);
            output.push_str(" `");
            output.push_str(id.name());
            output.push_str("' is required but not provided\n");
            let loc = type_ctx.resolve_loc(*loc);
            push_show_loc(
                output,
                &code_frame::format_location(
                    &location_filename(type_ctx, filename, &loc),
                    &loc.loc_start,
                    &loc.loc_end,
                ),
                "Expected declaration",
            );
        }
        IncludeModError::ValueTypeMismatch {
            name,
            actual,
            expected,
            arity_mismatch,
        } => {
            let actual_text = format_value_description(type_ctx, name, actual);
            let expected_text = format_value_description(type_ctx, name, expected);
            let inline_width = "  Values do not match: ".len()
                + actual_text.len()
                + " is not included in ".len()
                + expected_text.len();
            // includemod.ml:549-552 prints "@[<hv 2>Values do not match:@ %a@;<1
            // -2>is not included in@ %a@]" from column 2; the hv box stays on
            // one line only when it fits the report's margin (at most 77
            // columns including the indentation).
            if !actual_text.contains('\n') && !expected_text.contains('\n') && inline_width <= 77 {
                output.push_str("  Values do not match: ");
                output.push_str(&actual_text);
                output.push_str(" is not included in ");
                output.push_str(&expected_text);
                output.push('\n');
            } else {
                // The descriptions are emitted with `Format.pp_print_string`
                // (res_outcome_printer.ml:963-965), so their own line breaks
                // are copied verbatim and the box indentation does not apply
                // to continuation lines.
                output.push_str("  Values do not match:\n    ");
                output.push_str(&actual_text);
                output.push_str("\n  is not included in\n    ");
                output.push_str(&expected_text);
                output.push('\n');
            }
            if let Some((actual_arity, expected_arity)) = arity_mismatch {
                let arguments = |arity: usize| {
                    if arity == 1 {
                        "1 argument".to_string()
                    } else {
                        format!("{arity} arguments")
                    }
                };
                output.push_str("  The implementation contains a function taking ");
                output.push_str(&arguments(*actual_arity));
                output.push_str(" where the interface expects one taking ");
                output.push_str(&arguments(*expected_arity));
                output.push_str(".\n");
            }
            push_show_loc(
                output,
                &{
                    let loc = type_ctx.resolve_loc(expected.val_loc);
                    code_frame::format_location(
                        &location_filename(type_ctx, filename, &loc),
                        &loc.loc_start,
                        &loc.loc_end,
                    )
                },
                "Expected declaration",
            );
            push_show_loc(
                output,
                &{
                    let loc = type_ctx.resolve_loc(actual.val_loc);
                    code_frame::format_location(
                        &location_filename(type_ctx, filename, &loc),
                        &loc.loc_start,
                        &loc.loc_end,
                    )
                },
                "Actual declaration",
            );
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
        IncludeModError::ModuleTypeDeclarationMismatch {
            name,
            actual,
            expected,
            error,
        } => {
            output.push_str("  Module type declarations do not match:\n");
            output.push_str("    ");
            output.push_str(&format_modtype_declaration(type_ctx, name, actual));
            output.push('\n');
            output.push_str("  does not match\n");
            output.push_str("    ");
            output.push_str(&format_modtype_declaration(type_ctx, name, expected));
            output.push('\n');
            format_include_error(type_ctx, filename, error, cxt, output);
        }
        IncludeModError::ModtypePermutation => {
            output.push_str("  Illegal permutation of structure fields\n");
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

fn is_compact_type_declaration_mismatch(error: &IncludeModError) -> bool {
    matches!(
        error,
        IncludeModError::TypeDeclarationMismatch {
            detail: TypeDeclarationMismatchDetail::Variance,
            ..
        }
    )
}

pub(crate) fn location_filename(type_ctx: &TypeContext, fallback: &str, loc: &Location) -> String {
    type_ctx
        .resolve_cmi_longident_component(loc.loc_start.file_name)
        .filter(|name| !name.is_empty() && name != "_none_")
        .unwrap_or_else(|| fallback.to_string())
}

fn should_elide_module_mismatch(actual: &str, expected: &str) -> bool {
    actual.len() + expected.len() > 120
}

fn should_elide_type_declaration_module_mismatch(error: &IncludeModError) -> bool {
    // OCaml includemod.ml:637-655 bounds the structured `Module_types`
    // symptom, whose declarations still carry @tag attributes even though
    // Printtyp omits them. `@as` no longer counts: it is decided at typedecl
    // into `cd_runtime_tag`/`ld_runtime_name` and leaves the attributes.
    let has_hidden_tag_layout = matches!(
        error,
        IncludeModError::TypeDeclarationMismatch {
            detail: TypeDeclarationMismatchDetail::TagName,
            ..
        }
    );
    matches!(error, IncludeModError::TypeDeclarationMismatch { .. })
        && !is_compact_type_declaration_mismatch(error)
        && has_hidden_tag_layout
}

/// Whether an `@[<hv>` box at column 2 holding `parts` separated by break
/// hints stays on one line under the Format margin. Multi-line parts contain
/// forced breaks, so the box cannot be horizontal.
fn hv_fits_on_one_line(parts: &[&str]) -> bool {
    if parts.iter().any(|part| part.contains('\n')) {
        return false;
    }
    let mut buf = Vec::new();
    {
        let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
        ppf.string_as(2, "");
        ppf.open_box(crate::parser::formatter::BoxKind::HV, 0);
        for (index, part) in parts.iter().enumerate() {
            if index > 0 {
                ppf.break_(1, 2);
            }
            ppf.string_as(part.chars().count(), part);
        }
        ppf.close_box();
        ppf.flush();
    }
    !buf.contains(&b'\n')
}

// Declarations and module types print through `Printtyp`'s outcome trees and
// `Res_outcome_printer` (printtyp.ml:1007-1192, res_outcome_printer.ml:481-842),
// each rendered as one Doc string at width 80.

/// `Module_types` in `include_symptom` (includemod.ml:566-569):
/// `@[<hv 2>Modules do not match:@ %a@;<1 -2>is not included in@ %a@]`,
/// where each module type is one `pp_print_string` of the outcome printer's
/// rendering (res_outcome_printer.ml:1063-1065), laid out at column 2 of the
/// error's vertical box.
fn format_modules_do_not_match(actual: &str, expected: &str) -> String {
    let mut buf = Vec::new();
    {
        let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
        ppf.string_as(2, "");
        ppf.open_hvbox(2);
        ppf.string("Modules do not match:");
        ppf.break_(1, 0);
        ppf.string(actual);
        ppf.break_(1, -2);
        ppf.string("is not included in");
        ppf.break_(1, 0);
        ppf.string(expected);
        ppf.close_box();
        ppf.flush();
    }
    let mut out = String::from("  ");
    out.push_str(&String::from_utf8_lossy(&buf));
    out.push('\n');
    out
}

pub(crate) fn format_module_type(type_ctx: &TypeContext, mty: &ModuleType) -> String {
    let tree = crate::types::printtyp::Printtyp::new(type_ctx).tree_of_modtype(mty, false);
    crate::types::printtyp::print_out_module_type(&tree)
}

/// Print a signature loaded from the persistent unit `origin` the way OCaml
/// prints its raw `ps_sig`: paths into the unit are relative to it.
pub(crate) fn format_persistent_module_type(
    type_ctx: &TypeContext,
    mty: &ModuleType,
    origin: &crate::types::Path,
) -> String {
    let mut printer = crate::types::printtyp::Printtyp::new(type_ctx);
    let tree = printer.tree_of_modtype_in_unit(mty, origin);
    crate::types::printtyp::print_out_module_type(&tree)
}

pub(crate) fn format_module_type_show_weak(type_ctx: &TypeContext, mty: &ModuleType) -> String {
    format_module_type(type_ctx, mty)
}

pub(crate) fn format_module_type_full_paths(type_ctx: &TypeContext, mty: &ModuleType) -> String {
    format_module_type(type_ctx, mty)
}

fn format_modtype_declaration(
    type_ctx: &TypeContext,
    id: &Ident,
    decl: &ModtypeDeclaration,
) -> String {
    let tree =
        crate::types::printtyp::Printtyp::new(type_ctx).tree_of_modtype_declaration(id, decl);
    crate::types::printtyp::print_out_sig_item(&tree)
}

fn format_value_description(type_ctx: &TypeContext, id: &Ident, desc: &ValueDescription) -> String {
    let tree = crate::types::printtyp::Printtyp::new(type_ctx).tree_of_value_description(id, desc);
    crate::types::printtyp::print_out_sig_item(&tree)
}

fn format_type_declaration(type_ctx: &TypeContext, id: &Ident, decl: &TypeDeclaration) -> String {
    let tree = crate::types::printtyp::Printtyp::new(type_ctx).tree_of_type_declaration(
        id,
        decl,
        RecStatus::TrecNot,
    );
    crate::types::printtyp::print_out_sig_item(&tree)
}

fn format_extension_constructor(
    type_ctx: &TypeContext,
    id: &Ident,
    ext: &ExtensionConstructor,
) -> String {
    let tree = crate::types::printtyp::Printtyp::new(type_ctx).tree_of_extension_constructor(
        id,
        ext,
        crate::types::decl::ExtStatus::TextFirst,
    );
    crate::types::printtyp::print_out_sig_item(&tree)
}

#[derive(Clone, Default)]
struct InclusionSubst {
    type_paths: PathSubstMap,
    module_paths: PathSubstMap,
    modtype_paths: PathSubstMap,
}

impl InclusionSubst {
    fn is_empty(&self) -> bool {
        self.type_paths.is_empty() && self.module_paths.is_empty() && self.modtype_paths.is_empty()
    }
}

/// Path substitution table looked up with `Path.same` semantics.
///
/// OCaml compiler/ml/path.ml:27-35 defines `Path.compare` for PathMap and
/// ignores the `Pdot` position hint, while Rust's derived `Eq` compares it.
/// `Path`'s `Hash` already ignores the hint, so an exact `get` finds every key
/// that is `==`; the remaining `same`-but-not-`==` keys can only exist when the
/// key or the queried path carries a position hint. `any_pos_key` records
/// whether any key has one so the common case needs no full-map scan.
#[derive(Clone, Default)]
struct PathSubstMap {
    map: HashMap<Path, Path>,
    any_pos_key: bool,
}

impl PathSubstMap {
    fn insert(&mut self, key: Path, value: Path) {
        self.any_pos_key |= path_has_pos_hint(&key);
        self.map.insert(key, value);
    }

    fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn get(&self, path: &Path) -> Option<Path> {
        if let Some(value) = self.map.get(path) {
            return Some(value.clone());
        }
        if self.any_pos_key {
            return self
                .map
                .iter()
                .find_map(|(key, value)| key.same(path).then(|| value.clone()));
        }
        if !path_has_pos_hint(path) {
            // No key and not the path carry a position hint, so `same`
            // coincides with `==` and the exact lookup above was complete.
            return None;
        }
        // Keys carry no position hints, so at most one key is `same` as
        // `path`: the one equal to `path` with its hints cleared.
        self.map.get(&strip_pos_hints(path)).cloned()
    }
}

fn path_has_pos_hint(path: &Path) -> bool {
    match path.view() {
        PathView::Pident(_) => false,
        PathView::Pdot(parent, _, pos) => {
            *pos != crate::types::path::NOPOS || path_has_pos_hint(parent)
        }
        PathView::Papply(functor, argument) => {
            path_has_pos_hint(functor) || path_has_pos_hint(argument)
        }
    }
}

fn strip_pos_hints(path: &Path) -> Path {
    match path.view() {
        PathView::Pident(_) => path.clone(),
        PathView::Pdot(parent, name, _) => Path::pdot_pos(strip_pos_hints(parent), *name, crate::types::path::NOPOS),
        PathView::Papply(functor, argument) => Path::papply(strip_pos_hints(functor), strip_pos_hints(argument)),
    }
}

// ============================================================================
// Module Type Inclusion
// ============================================================================

thread_local! {
    static MODTYPES_DEPTH: Cell<usize> = const { Cell::new(0) };
}

/// Which Env table a path names: `Mty_alias` paths are modules
/// (`Env.find_module`), `Mty_ident` paths are module types
/// (`Env.find_modtype_expansion`, compiler/ml/env.ml:970-973).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum PathNamespace {
    Module,
    ModuleType,
}

fn with_local_pident_module_type<R>(
    env: &Env,
    path: &Path,
    namespace: PathNamespace,
    f: impl FnOnce(&ModuleType) -> R,
) -> Option<R> {
    let mut current = path.clone();
    let mut namespace = namespace;
    let mut visiting = HashSet::new();

    loop {
        let PathView::Pident(id) = current.view() else {
            return None;
        };
        if id.is_persistent() || id.stamp() == 0 || !visiting.insert((current.clone(), namespace)) {
            return None;
        }
        let mty = match namespace {
            PathNamespace::Module => env.lookup_module(&current).ok()?.md_type.clone(),
            PathNamespace::ModuleType => env.lookup_modtype(&current).ok()?.mtd_type.clone()?,
        };
        match &mty {
            ModuleType::MtyIdent(next)
                if !(next.same(&current) && namespace == PathNamespace::ModuleType) =>
            {
                current = next.clone();
                namespace = PathNamespace::ModuleType;
            }
            ModuleType::MtyAlias(_, next)
                if !(next.same(&current) && namespace == PathNamespace::Module) =>
            {
                current = next.clone();
                namespace = PathNamespace::Module;
            }
            _ => return Some(f(&mty)),
        }
    }
}

/// Check if `mty_impl` is a subtype of `mty_sig` (implementation matches signature).
///
/// Returns a coercion that can be applied to convert the implementation
/// to the signature type.
pub fn modtypes(
    type_ctx: &TypeContext,
    env: &Env,
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
) -> IncludeModResult<ModuleCoercion> {
    let mut warnings = Vec::new();
    modtypes_with_warnings(type_ctx, env, mty_impl, mty_sig, &mut warnings)
}

pub fn modtypes_with_warnings(
    type_ctx: &TypeContext,
    env: &Env,
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<ModuleCoercion> {
    let subst = InclusionSubst::default();
    modtypes_inner(type_ctx, env, &subst, mty_impl, mty_sig, None, warnings).map_err(|error| {
        if module_type_error_is_alias_unbound_module(mty_impl, mty_sig, &error) {
            error
        } else {
            IncludeModError::ModuleTypesMismatch {
                actual: Box::new(mty_impl.clone()),
                expected: Box::new(mty_sig.clone()),
                error: Box::new(error),
            }
        }
    })
}

fn module_type_error_is_alias_unbound_module(
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
    error: &IncludeModError,
) -> bool {
    matches!(error, IncludeModError::UnboundModulePath { .. })
        && (matches!(mty_impl, ModuleType::MtyAlias(..))
            || matches!(mty_sig, ModuleType::MtyAlias(..)))
}

/// The error half of OCaml `modtypes` (includemod.ml:187-198): `Dont_match`
/// (a bare `ModuleTypeMismatch` here) becomes a `Module_types` entry; other
/// errors from `try_modtypes` get one too unless either side is an alias, in
/// which case the inner comparison already reported it.
fn wrap_modtypes_error(
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
    error: IncludeModError,
) -> IncludeModError {
    if !matches!(error, IncludeModError::ModuleTypeMismatch { .. })
        && (matches!(mty_impl, ModuleType::MtyAlias(..))
            || matches!(mty_sig, ModuleType::MtyAlias(..)))
    {
        return error;
    }
    IncludeModError::ModuleTypesMismatch {
        actual: Box::new(mty_impl.clone()),
        expected: Box::new(mty_sig.clone()),
        error: Box::new(error),
    }
}

/// Check if `mty_impl` is a subtype of `mty_sig` under `subst`.
fn modtypes_inner(
    type_ctx: &TypeContext,
    env: &Env,
    subst: &InclusionSubst,
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
    sig_access_path: Option<&Path>,
    warnings: &mut Vec<Warning>,
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
        namespace: PathNamespace,
    ) -> Option<ModuleType> {
        use crate::types::decl::SignatureItem as SigItem;

        fn should_try_env_lazy(path: &Path) -> bool {
            match path.view() {
                PathView::Pident(id) => id.is_persistent() || id.stamp() == 0,
                PathView::Pdot(_, _, _) => true,
                PathView::Papply(_, _) => false,
            }
        }

        fn expand_local(
            env: &Env,
            path: &Path,
            namespace: PathNamespace,
            visiting: &mut HashSet<(Path, PathNamespace)>,
        ) -> Option<ModuleType> {
            if !visiting.insert((path.clone(), namespace)) {
                return None;
            }

            let mty = match path.view() {
                PathView::Pident(id) => match namespace {
                    PathNamespace::Module => {
                        env.lookup_module(&Path::pident(*id)).ok()?.md_type.clone()
                    }
                    PathNamespace::ModuleType => env
                        .lookup_modtype(&Path::pident(*id))
                        .ok()?
                        .mtd_type
                        .clone()?,
                },
                PathView::Pdot(parent, name, _) => {
                    let parent_mty = expand_local(env, parent, PathNamespace::Module, visiting)?;
                    let parent_sig = match &parent_mty {
                        ModuleType::MtySignature(sig) => sig.clone(),
                        ModuleType::MtyIdent(parent_path) => {
                            match expand_local(
                                env,
                                parent_path,
                                PathNamespace::ModuleType,
                                visiting,
                            )? {
                                ModuleType::MtySignature(sig) => sig,
                                _ => return None,
                            }
                        }
                        ModuleType::MtyAlias(_, parent_path) => {
                            match expand_local(env, parent_path, PathNamespace::Module, visiting)? {
                                ModuleType::MtySignature(sig) => sig,
                                _ => return None,
                            }
                        }
                        _ => return None,
                    };
                    parent_sig.iter().find_map(|item| match (item, namespace) {
                        (SigItem::SigModule(id, md, _), PathNamespace::Module)
                            if id.name() == name.as_str() =>
                        {
                            Some(md.md_type.clone())
                        }
                        (SigItem::SigModtype(id, mtd), PathNamespace::ModuleType)
                            if id.name() == name.as_str() =>
                        {
                            mtd.mtd_type.clone()
                        }
                        _ => None,
                    })?
                }
                PathView::Papply(_, _) => return None,
            };
            match &mty {
                ModuleType::MtyIdent(next) => {
                    expand_local(env, next, PathNamespace::ModuleType, visiting).or(Some(mty))
                }
                ModuleType::MtyAlias(_, next) => {
                    expand_local(env, next, PathNamespace::Module, visiting).or(Some(mty))
                }
                _ => Some(mty),
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
        expand_local(env, path, namespace, &mut visiting)
    }

    fn normalized_alias_path(type_ctx: &TypeContext, env: &Env, path: &Path) -> Path {
        ctype::normalize_path_full(type_ctx, env, path)
    }

    fn strict_normalized_alias_path(
        type_ctx: &TypeContext,
        env: &Env,
        path: &Path,
    ) -> IncludeModResult<Path> {
        // OCaml compiler/ml/env.ml:903-914 follows only Mty_alias while
        // normalizing a module path. A selected module whose declaration is
        // Mty_ident names a module type; it exists at the selected path and is
        // not an alias to that module-type path.
        if env
            .lookup_module(path)
            .is_ok_and(|md| matches!(md.md_type, ModuleType::MtyIdent(_)))
        {
            return Ok(path.clone());
        }
        ctype::normalize_path_full_strict(type_ctx, env, path)
            .map_err(|path| IncludeModError::UnboundModulePath { path })
    }

    match (mty_impl, mty_sig) {
        (ModuleType::MtyAlias(pres_impl, impl_path), ModuleType::MtyAlias(pres_sig, sig_path)) => {
            // OCaml compiler/ml/includemod.ml:202-208 first compares the alias
            // paths directly. Only unequal paths cross Env.normalize_path;
            // forcing equal aliases here materializes component thunks that
            // OCaml leaves delayed until translation.
            let subst_sig_path = substitute_module_path(sig_path, subst);
            if !impl_path.same(&subst_sig_path) {
                let lax_impl_path = normalized_alias_path(type_ctx, env, impl_path);
                let lax_sig_path = normalized_alias_path(type_ctx, env, &subst_sig_path);
                if !lax_impl_path.same(&lax_sig_path) {
                    return Err(IncludeModError::ModuleTypeMismatch {
                        name: Ident::create_local("module"),
                        reason: "module aliases do not match".to_string(),
                    });
                }
            }
            match (pres_impl, pres_sig) {
                (
                    crate::types::decl::AliasPresence::MtaAbsent,
                    crate::types::decl::AliasPresence::MtaPresent,
                ) => {
                    let impl_path = strict_normalized_alias_path(type_ctx, env, impl_path)?;
                    Ok(ModuleCoercion::Tcoerce_alias(
                        type_ctx.store_typed_env(env),
                        impl_path,
                        Box::new(ModuleCoercion::Tcoerce_none),
                    ))
                }
                _ => Ok(ModuleCoercion::Tcoerce_none),
            }
        }

        (ModuleType::MtyAlias(pres_impl, impl_path), mty_sig) => {
            let impl_path = strict_normalized_alias_path(type_ctx, env, impl_path)?;
            let coercion = if let Some(coercion) =
                with_local_pident_module_type(env, &impl_path, PathNamespace::Module, |expanded| {
                    let expanded = ctype::strengthen_module_type_for_inclusion_path(
                        type_ctx, env, &impl_path, expanded,
                    );
                    // includemod.ml:231: `modtypes ~loc env cxt subst mty1 mty2`.
                    modtypes_inner(
                        type_ctx,
                        env,
                        subst,
                        &expanded,
                        mty_sig,
                        sig_access_path,
                        warnings,
                    )
                    .map_err(|error| wrap_modtypes_error(&expanded, mty_sig, error))
                }) {
                coercion?
            } else {
                let expanded =
                    expand_module_type_in_env(type_ctx, env, &impl_path, PathNamespace::Module)
                        .map(|mty| {
                            ctype::strengthen_module_type_for_inclusion_path(
                                type_ctx, env, &impl_path, &mty,
                            )
                        })
                        .unwrap_or_else(|| ModuleType::MtyAlias(*pres_impl, impl_path.clone()));
                // includemod.ml:231: `modtypes ~loc env cxt subst mty1 mty2`.
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    &expanded,
                    mty_sig,
                    sig_access_path,
                    warnings,
                )
                .map_err(|error| wrap_modtypes_error(&expanded, mty_sig, error))?
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

        // Signature matching
        (ModuleType::MtySignature(sig_impl), ModuleType::MtySignature(sig_sig)) => {
            signatures_with_subst(
                type_ctx,
                env,
                subst,
                sig_access_path,
                sig_impl,
                sig_sig,
                warnings,
            )
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
                    modtypes_inner(type_ctx, env, &empty_subst, pt_sig, pt_impl, None, warnings)?
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
                .unwrap_or_else(|| ModuleType::MtySignature(std::sync::Arc::new(vec![])));
            result_env.add_module(
                *param_impl,
                ModuleDeclaration {
                    md_type: param_binding_type,
                    md_attributes: vec![],
                    md_loc: crate::types::DeclLoc::none(),
                    md_path: None,
                },
            );
            let mut result_subst = subst.clone();
            result_subst
                .module_paths
                .insert(Path::pident(*param_sig), Path::pident(*param_impl));
            let result_coercion = modtypes_inner(
                type_ctx,
                &result_env,
                &result_subst,
                result_impl,
                result_sig,
                sig_access_path,
                warnings,
            )
            .map_err(|error| IncludeModError::InFunctorBody {
                param: *param_impl,
                actual: result_impl.clone(),
                expected: result_sig.clone(),
                error: Box::new(error),
            })?;

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

        // A signature against an identifier goes through the generic
        // `_, Mty_ident _` case below, which substitutes the expected path
        // first (includemod.ml:237, 262-273).

        // Identifier implementation matches signature
        (ModuleType::MtyIdent(path), ModuleType::MtySignature(_)) => {
            if let Some(result) =
                with_local_pident_module_type(env, path, PathNamespace::ModuleType, |expanded| {
                    modtypes_inner(
                        type_ctx,
                        env,
                        subst,
                        expanded,
                        mty_sig,
                        sig_access_path,
                        warnings,
                    )
                })
            {
                return result;
            }
            if let Some(expanded) =
                expand_module_type_in_env(type_ctx, env, path, PathNamespace::ModuleType)
            {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    &expanded,
                    mty_sig,
                    sig_access_path,
                    warnings,
                )
            } else {
                // includemod.ml `try_modtypes`: an identifier that cannot be
                // expanded does not match a signature (`Dont_match`).
                Err(IncludeModError::ModuleTypeMismatch {
                    name: Ident::create_local("module"),
                    reason: "incompatible module types".to_string(),
                })
            }
        }

        (ModuleType::MtyIdent(path), mty_sig) => {
            // compiler/ml/includemod.ml:235-236 expands an implementation-side
            // identifier only when Env says that module type path is manifest.
            if let Some(result) =
                with_local_pident_module_type(env, path, PathNamespace::ModuleType, |expanded| {
                    modtypes_inner(
                        type_ctx,
                        env,
                        subst,
                        expanded,
                        mty_sig,
                        sig_access_path,
                        warnings,
                    )
                })
            {
                return result;
            }
            if let Some(expanded) =
                expand_module_type_in_env(type_ctx, env, path, PathNamespace::ModuleType)
            {
                modtypes_inner(
                    type_ctx,
                    env,
                    subst,
                    &expanded,
                    mty_sig,
                    sig_access_path,
                    warnings,
                )
            } else if let ModuleType::MtyIdent(sig_path) = mty_sig {
                // try_modtypes2 receives `Subst.modtype subst mty2`. For an
                // identifier this first applies Subst.modtype_path; if neither
                // side can expand, only normalized prefix identity succeeds.
                let sig_path = substitute_modtype_path(sig_path, subst);
                if env
                    .normalize_path_prefix(path)
                    .same(&env.normalize_path_prefix(&sig_path))
                {
                    Ok(ModuleCoercion::Tcoerce_none)
                } else if let Some(expanded) =
                    expand_module_type_in_env(type_ctx, env, &sig_path, PathNamespace::ModuleType)
                {
                    let identity = InclusionSubst::default();
                    modtypes_inner(
                        type_ctx,
                        env,
                        &identity,
                        mty_impl,
                        &expanded,
                        sig_access_path,
                        warnings,
                    )
                } else {
                    Err(IncludeModError::ModuleTypeMismatch {
                        name: Ident::create_local("module"),
                        reason: "incompatible module types".to_string(),
                    })
                }
            } else {
                Err(IncludeModError::ModuleTypeMismatch {
                    name: Ident::create_local("module"),
                    reason: "incompatible module types".to_string(),
                })
            }
        }

        (mty_impl, ModuleType::MtyIdent(path)) => {
            // compiler/ml/includemod.ml:237 and 262-273 substitute the expected
            // module type before testing/expanding its identifier, and restart
            // expansion with Subst.identity.
            let path = substitute_modtype_path(path, subst);
            if let ModuleType::MtyIdent(impl_path) = mty_impl
                && env
                    .normalize_path_prefix(impl_path)
                    .same(&env.normalize_path_prefix(&path))
            {
                return Ok(ModuleCoercion::Tcoerce_none);
            }
            let identity = InclusionSubst::default();
            if let Some(result) =
                with_local_pident_module_type(env, &path, PathNamespace::ModuleType, |expanded| {
                    modtypes_inner(
                        type_ctx,
                        env,
                        &identity,
                        mty_impl,
                        expanded,
                        sig_access_path,
                        warnings,
                    )
                })
            {
                return result;
            }
            if let Some(expanded) =
                expand_module_type_in_env(type_ctx, env, &path, PathNamespace::ModuleType)
            {
                modtypes_inner(
                    type_ctx,
                    env,
                    &identity,
                    mty_impl,
                    &expanded,
                    sig_access_path,
                    warnings,
                )
            } else {
                Err(IncludeModError::ModuleTypeMismatch {
                    name: Ident::create_local("module"),
                    reason: "incompatible module types".to_string(),
                })
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

fn item_ident_name(item: &SignatureItem) -> (&Ident, crate::types::DeclLoc, FieldDesc) {
    match item {
        SignatureItem::SigValue(id, desc) => (id, desc.val_loc, FieldDesc::Value(id.name().into())),
        SignatureItem::SigType(id, decl, _) => {
            (id, decl.type_loc, FieldDesc::Type(id.name().into()))
        }
        SignatureItem::SigTypext(id, ext, _) => {
            (id, ext.ext_loc, FieldDesc::Typext(id.name().into()))
        }
        SignatureItem::SigModule(id, md, _) => (id, md.md_loc, FieldDesc::Module(id.name().into())),
        SignatureItem::SigModtype(id, mtd) => {
            (id, mtd.mtd_loc, FieldDesc::Modtype(id.name().into()))
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
            let impl_path = Path::pident(*impl_id);
            subst
                .type_paths
                .insert(Path::pident(*sig_id), impl_path.clone());
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
            let impl_path = Path::pident(*impl_id);
            subst
                .module_paths
                .insert(Path::pident(*sig_id), impl_path.clone());
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
            // OCaml compiler/ml/includemod.ml:353-354 records
            // `Subst.add_modtype id2 (Mty_ident (Pident id1))`. Dotted module
            // type paths are handled by Subst.modtype_path through their module
            // prefix (compiler/ml/subst.ml:77-86), not by a dotted modtype map.
            subst
                .modtype_paths
                .insert(Path::pident(*sig_id), Path::pident(*impl_id));
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
    loc: crate::types::DeclLoc,
    field_desc: &FieldDesc,
) -> IncludeModError {
    IncludeModError::MissingField {
        id: *id,
        loc,
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
    // includemod.ml:358-365 conses each missing field onto `unpaired` and
    // raises the list as built, i.e. in reverse signature order.
    errors.reverse();

    (len_impl, paired, errors)
}

fn check_paired_signature_items(
    type_ctx: &TypeContext,
    env: &Env,
    paired: &[PairedSignatureItem<'_>],
    sig_access_path: Option<&Path>,
    subst: &InclusionSubst,
    warnings: &mut Vec<Warning>,
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
                    *impl_id,
                    impl_val_desc,
                    sig_val_desc,
                    subst,
                    warnings,
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
                    *impl_id,
                    impl_type_decl,
                    &expected_type_decl,
                    warnings,
                )?;
            }
            (
                SignatureItem::SigTypext(impl_id, impl_ext_constr, _),
                SignatureItem::SigTypext(_, sig_ext_constr, _),
            ) => {
                extension_constructors(
                    type_ctx,
                    env,
                    *impl_id,
                    impl_ext_constr,
                    sig_ext_constr,
                    subst,
                    warnings,
                )?;
                coercions.push((pair.runtime_pos, ModuleCoercion::Tcoerce_none));
            }
            (
                SignatureItem::SigModule(impl_id, impl_mod_decl, _),
                SignatureItem::SigModule(sig_id, sig_mod_decl, _),
            ) => {
                if let Some(warning) = deprecated_inclusion_warning(
                    type_ctx,
                    impl_id.name(),
                    &impl_mod_decl.md_attributes,
                    &sig_mod_decl.md_attributes,
                    impl_mod_decl.md_loc,
                    sig_mod_decl.md_loc,
                ) {
                    warnings.push(warning);
                }
                // includemod.ml:399: `Env.mark_module_used env (Ident.name
                // id1) md1.md_loc`.
                if !env.is_implicit_coercion() {
                    type_ctx
                        .usage()
                        .mark_module_used(impl_id.name(), type_ctx.resolve_loc(impl_mod_decl.md_loc));
                }
                // Match compiler/ml/includemod.ml:396-413:
                // `module_declarations` always strengthens the implementation
                // module type and recurses through `modtypes` with the current
                // substitution rather than pre-substituting the declaration.
                let impl_mty = crate::types::ctype::strengthen_module_type_for_inclusion_path(
                    type_ctx,
                    env,
                    &Path::pident(*impl_id),
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
                    warnings,
                )
                .map_err(|error| {
                    // `modtypes` in `Module id :: cxt` (includemod.ml:
                    // 396-413): the `Module_types` entry and the errors below
                    // it share that context.
                    IncludeModError::InModule {
                        name: *impl_id,
                        error: Box::new(wrap_modtypes_error(
                            &impl_mty,
                            &sig_mod_decl.md_type,
                            error,
                        )),
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
                    *impl_id,
                    impl_modtype_decl,
                    &expected_modtype_decl,
                    warnings,
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
                if seen_values.insert(id.name()) {
                    simplified.push(item.clone());
                }
            }
            _ => simplified.push(item.clone()),
        }
    }
    simplified.reverse();
    simplified
}

pub fn compunit(
    type_ctx: &TypeContext,
    env: &Env,
    impl_name: &str,
    impl_sig: &Signature,
    _intf_name: &str,
    intf_sig: &Signature,
) -> IncludeModResult<ModuleCoercion> {
    let mut warnings = Vec::new();
    compunit_with_warnings(
        type_ctx,
        env,
        impl_name,
        impl_sig,
        _intf_name,
        intf_sig,
        &mut warnings,
    )
}

pub fn compunit_with_warnings(
    type_ctx: &TypeContext,
    env: &Env,
    impl_name: &str,
    impl_sig: &Signature,
    _intf_name: &str,
    intf_sig: &Signature,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<ModuleCoercion> {
    // OCaml compiler/ml/includemod.ml:468-475 starts compilation-unit
    // inclusion from `signatures`; Rust additionally carries the persisted
    // compilation-unit access path so Subst.add_* mappings can cover CMI paths
    // like `Unit.Nested.t` that no longer appear as local `Pident`s.
    let subst = InclusionSubst::default();
    let access_path = Path::pident(Ident::create_persistent(
        crate::misc::module_name_from_source_filename(impl_name),
    ));
    signatures_with_subst(
        type_ctx,
        env,
        &subst,
        Some(&access_path),
        impl_sig,
        intf_sig,
        warnings,
    )
}

/// Check if signature `sig_impl` is a subtype of `sig_sig`.
pub fn signatures(
    type_ctx: &TypeContext,
    env: &Env,
    sig_impl: &Signature,
    sig_sig: &Signature,
) -> IncludeModResult<ModuleCoercion> {
    let subst = InclusionSubst::default();
    let mut warnings = Vec::new();
    signatures_with_subst(
        type_ctx,
        env,
        &subst,
        None,
        sig_impl,
        sig_sig,
        &mut warnings,
    )
}

fn signatures_with_subst(
    type_ctx: &TypeContext,
    env: &Env,
    incoming_subst: &InclusionSubst,
    sig_access_path: Option<&Path>,
    sig_impl: &Signature,
    sig_sig: &Signature,
    warnings: &mut Vec<Warning>,
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
                    Some((*id, *runtime_pos, ModuleCoercion::Tcoerce_none))
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

    let coercions = check_paired_signature_items(
        type_ctx,
        &include_env,
        &paired,
        sig_access_path,
        &subst,
        warnings,
    )?;

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
/// compiler/ml/includemod.ml:496-529: find the first nested n-ary arrow
/// whose parameter count differs, descending only through equal-label arrows.
fn find_arity_mismatch(
    type_ctx: &TypeContext,
    env: &Env,
    impl_ty: TypeExprRef,
    sig_ty: TypeExprRef,
) -> Option<(usize, usize)> {
    fn loop_(
        type_ctx: &TypeContext,
        env: &Env,
        seen: &mut HashSet<(TypeExprRef, TypeExprRef)>,
        impl_ty: TypeExprRef,
        sig_ty: TypeExprRef,
    ) -> Option<(usize, usize)> {
        let impl_ty = type_ctx.repr(impl_ty);
        let sig_ty = type_ctx.repr(sig_ty);
        if !seen.insert((impl_ty, sig_ty)) {
            return None;
        }
        let impl_ty = type_ctx.repr(ctype::expand_head(type_ctx, env, impl_ty));
        let sig_ty = type_ctx.repr(ctype::expand_head(type_ctx, env, sig_ty));
        let (impl_args, impl_ret, sig_args, sig_ret) =
            match (&*type_ctx.get_desc(impl_ty), &*type_ctx.get_desc(sig_ty)) {
                (
                    TypeDesc::Tarrow {
                        args: impl_args,
                        ret: impl_ret,
                    },
                    TypeDesc::Tarrow {
                        args: sig_args,
                        ret: sig_ret,
                    },
                ) => (impl_args.clone(), *impl_ret, sig_args.clone(), *sig_ret),
                _ => return None,
            };
        if impl_args.len() != sig_args.len() {
            return Some((impl_args.len(), sig_args.len()));
        }
        if !type_ctx.type_args(impl_args)
            .iter()
            .zip(type_ctx.type_args(sig_args).iter())
            .all(|(impl_arg, sig_arg)| impl_arg.label().same_label(sig_arg.label()))
        {
            return None;
        }
        for (impl_arg, sig_arg) in type_ctx.type_args(impl_args).iter().zip(type_ctx.type_args(sig_args).iter()) {
            if let Some(mismatch) = loop_(type_ctx, env, seen, impl_arg.typ, sig_arg.typ) {
                return Some(mismatch);
            }
        }
        loop_(type_ctx, env, seen, impl_ret, sig_ret)
    }

    loop_(type_ctx, env, &mut HashSet::new(), impl_ty, sig_ty)
}

fn value_descriptions(
    type_ctx: &TypeContext,
    env: &Env,
    id: Ident,
    impl_desc: &ValueDescription,
    sig_desc: &ValueDescription,
    subst: &InclusionSubst,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<ModuleCoercion> {
    // includemod.ml:57: `Cmt_format.record_value_dependency vd1 vd2`.
    type_ctx.record_value_dependency(impl_desc, sig_desc);
    // includemod.ml:58: `Env.mark_value_used env (Ident.name id) vd1`.
    if !env.is_implicit_coercion() {
        type_ctx
            .usage()
            .mark_value_used(id.name(), type_ctx.resolve_loc(impl_desc.val_loc));
    }
    if let Some(warning) = deprecated_inclusion_warning(
        type_ctx,
        id.name(),
        &impl_desc.val_attributes,
        &sig_desc.val_attributes,
        impl_desc.val_loc,
        sig_desc.val_loc,
    ) {
        warnings.push(warning);
    }

    // Check that the value types are compatible
    // The implementation type should be more general than (or equal to) the signature type
    // A signature checked against itself (js_implementation.ml:62 marks an
    // interface's declarations used that way) pairs each value with itself,
    // and a type is always more general than itself.
    let same_value = std::ptr::eq(impl_desc, sig_desc);
    let expected_ty = if same_value {
        impl_desc.val_type
    } else {
        substitute_value_type_paths(type_ctx, sig_desc.val_type, subst)
    };

    // OCaml compiler/ml/includemod.ml:56-60 only substitutes the expected
    // value description before calling compiler/ml/includecore.ml:43-48,
    // where `Ctype.moregeneral` compares the two value types directly. Forcing
    // manifest aliases up front changes Env.normalize_path side effects and
    // shifts subsequent Ident stamps.
    let moregeneral =
        same_value || ctype::moregeneral(type_ctx, env, true, impl_desc.val_type, expected_ty);
    let mut expected_desc = sig_desc.clone();
    expected_desc.val_type = expected_ty;
    if !moregeneral {
        let arity_mismatch = find_arity_mismatch(type_ctx, env, impl_desc.val_type, expected_ty);
        return Err(IncludeModError::ValueTypeMismatch {
            name: id,
            actual: impl_desc.clone(),
            expected: expected_desc,
            arity_mismatch,
        });
    }

    // OCaml: match (vd1.val_kind, vd2.val_kind) with
    // | Val_prim p, _ -> Tcoerce_primitive { pc_desc = p; pc_type = vd2.val_type; ... }
    // | _, Val_prim _ -> raise Dont_match
    // | _, _ -> Tcoerce_none
    let dont_match = || {
        Err(IncludeModError::ValueTypeMismatch {
            name: id,
            actual: impl_desc.clone(),
            expected: expected_desc.clone(),
            arity_mismatch: None,
        })
    };
    match (&impl_desc.val_kind, &sig_desc.val_kind) {
        (ValueKind::ValPrim(p1), ValueKind::ValPrim(p2)) => {
            // includecore.ml:49-52: normalize both primitives against their
            // types, then `Primitive.coercible`.
            let p1 = normalize_primitive(type_ctx, env, impl_desc.val_type, p1);
            let p2 = normalize_primitive(type_ctx, env, expected_ty, p2);
            if primitive_coercible(&p1, &p2) {
                Ok(ModuleCoercion::Tcoerce_none)
            } else {
                dont_match()
            }
        }
        (ValueKind::ValPrim(prim), _) => Ok(ModuleCoercion::Tcoerce_primitive(
            crate::types::typedtree::PrimitiveCoercion {
                pc_desc: (**prim).clone(),
                pc_type: sig_desc.val_type,
                pc_loc: impl_desc.val_loc,
                pc_id: id,
            },
        )),
        // includecore.ml:64: a primitive cannot be implemented by a value.
        (_, ValueKind::ValPrim(_)) => dont_match(),
        _ => Ok(ModuleCoercion::Tcoerce_none),
    }
}

/// OCaml `Includecore.normalize_primitive` (includecore.ml:31-41).
fn normalize_primitive(
    type_ctx: &TypeContext,
    env: &Env,
    val_type: TypeExprRef,
    prim: &crate::types::decl::PrimitiveDescription,
) -> crate::types::decl::PrimitiveDescription {
    match crate::types::typemod::get_primitive_arity_from_type(type_ctx, env, val_type) {
        Some(prim_arity) => {
            let is_constr = matches!(
                &*type_ctx.get_desc(type_ctx.repr(val_type)),
                TypeDesc::Tconstr { .. }
            );
            crate::types::decl::PrimitiveDescription {
                prim_arity,
                prim_from_constructor: is_constr || prim.prim_from_constructor,
                ..prim.clone()
            }
        }
        None => prim.clone(),
    }
}

/// `Primitive.coercible impl intf` (primitive.ml:41-52): can an
/// implementation's primitive satisfy an interface's during signature
/// inclusion? The specs must be equal, up to the widening rule in
/// `External_ffi_types.inclusion_compatible`.
fn primitive_coercible(
    impl_: &crate::types::decl::PrimitiveDescription,
    intf: &crate::types::decl::PrimitiveDescription,
) -> bool {
    use crate::types::decl::PrimKind;
    (impl_.prim_name == intf.prim_name
        && impl_.prim_arity == intf.prim_arity
        && impl_.prim_kind == intf.prim_kind)
        || match (&impl_.prim_kind, &intf.prim_kind) {
            (PrimKind::KindExternal(impl_ffi), PrimKind::KindExternal(intf_ffi)) => {
                crate::types::external_ffi_types::inclusion_compatible(impl_ffi, intf_ffi)
            }
            _ => false,
        }
}

pub(crate) fn add_sig_item_to_env(item: &SignatureItem, env: &mut Env) {
    match item {
        SignatureItem::SigValue(id, desc) => env.add_value(*id, desc.clone()),
        SignatureItem::SigType(id, decl, _) => env.add_type(*id, decl.clone()),
        SignatureItem::SigModule(id, md, _) => env.add_module(*id, md.clone()),
        SignatureItem::SigModtype(id, mtd) => env.add_modtype(*id, mtd.clone()),
        SignatureItem::SigTypext(_, _, _)
        | SignatureItem::SigClass
        | SignatureItem::SigClassType => {}
    }
}

fn substitute_value_description_paths(
    type_ctx: &TypeContext,
    desc: &ValueDescription,
    subst: &InclusionSubst,
) -> ValueDescription {
    // OCaml compiler/ml/subst.ml:303-309 copies a value description and runs
    // the full current substitution over `val_type`.
    let mut substituted = desc.clone();
    substituted.val_type = substitute_value_type_paths(type_ctx, desc.val_type, subst);
    substituted
}

fn substitute_label_declaration_paths(
    type_ctx: &TypeContext,
    label: &LabelDeclaration,
    subst: &InclusionSubst,
) -> LabelDeclaration {
    let mut substituted = label.clone();
    substituted.ld_type = substitute_value_type_paths(type_ctx, label.ld_type, subst);
    substituted
}

fn substitute_constructor_arguments_paths(
    type_ctx: &TypeContext,
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

fn collect_constructor_argument_types(args: &ConstructorArguments, types: &mut Vec<TypeExprRef>) {
    match args {
        ConstructorArguments::CstrTuple(items) => types.extend(items.iter().copied()),
        ConstructorArguments::CstrRecord(labels) => {
            types.extend(labels.iter().map(|label| label.ld_type));
        }
    }
}

fn collect_type_kind_types(kind: &TypeKind, types: &mut Vec<TypeExprRef>) {
    match kind {
        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
        TypeKind::TypeRecord(labels, _) => {
            types.extend(labels.iter().map(|label| label.ld_type));
        }
        TypeKind::TypeVariant(constructors, _) => {
            for constructor in constructors {
                collect_constructor_argument_types(&constructor.cd_args, types);
                if let Some(ty) = constructor.cd_res {
                    types.push(ty);
                }
            }
        }
    }
}

fn collect_type_inlined_types(inlined: &TypeInlinedType, types: &mut Vec<TypeExprRef>) {
    match inlined {
        TypeInlinedType::Record { labels, .. } => {
            types.extend(labels.iter().map(|label| label.ld_type));
        }
    }
}

fn next_copied_type(types: &mut std::vec::IntoIter<TypeExprRef>) -> TypeExprRef {
    types
        .next()
        .expect("type declaration substitution slot mismatch")
}

fn substitute_label_declaration_with_copied_type(
    label: &LabelDeclaration,
    types: &mut std::vec::IntoIter<TypeExprRef>,
) -> LabelDeclaration {
    let mut substituted = label.clone();
    substituted.ld_type = next_copied_type(types);
    substituted
}

fn substitute_constructor_arguments_with_copied_types(
    args: &ConstructorArguments,
    types: &mut std::vec::IntoIter<TypeExprRef>,
) -> ConstructorArguments {
    match args {
        ConstructorArguments::CstrTuple(items) => {
            ConstructorArguments::CstrTuple(items.iter().map(|_| next_copied_type(types)).collect())
        }
        ConstructorArguments::CstrRecord(labels) => ConstructorArguments::CstrRecord(
            labels
                .iter()
                .map(|label| substitute_label_declaration_with_copied_type(label, types))
                .collect(),
        ),
    }
}

fn substitute_constructor_declaration_with_copied_types(
    constructor: &ConstructorDeclaration,
    types: &mut std::vec::IntoIter<TypeExprRef>,
) -> ConstructorDeclaration {
    let mut substituted = constructor.clone();
    substituted.cd_args =
        substitute_constructor_arguments_with_copied_types(&constructor.cd_args, types);
    substituted.cd_res = constructor.cd_res.map(|_| next_copied_type(types));
    substituted
}

fn substitute_type_kind_with_copied_types(
    kind: &TypeKind,
    types: &mut std::vec::IntoIter<TypeExprRef>,
) -> TypeKind {
    match kind {
        TypeKind::TypeAbstract => TypeKind::TypeAbstract,
        TypeKind::TypeOpen => TypeKind::TypeOpen,
        TypeKind::TypeRecord(labels, repr) => TypeKind::TypeRecord(
            labels
                .iter()
                .map(|label| substitute_label_declaration_with_copied_type(label, types))
                .collect(),
            repr.clone(),
        ),
        TypeKind::TypeVariant(constructors, layout) => TypeKind::TypeVariant(
            constructors
                .iter()
                .map(|constructor| {
                    substitute_constructor_declaration_with_copied_types(constructor, types)
                })
                .collect(),
            *layout,
        ),
    }
}

fn substitute_type_inlined_with_copied_types(
    inlined: &TypeInlinedType,
    types: &mut std::vec::IntoIter<TypeExprRef>,
) -> TypeInlinedType {
    match inlined {
        TypeInlinedType::Record { type_name, labels } => TypeInlinedType::Record {
            type_name: type_name.clone(),
            labels: labels
                .iter()
                .map(|label| substitute_label_declaration_with_copied_type(label, types))
                .collect(),
        },
    }
}

fn substitute_type_declaration_paths(
    type_ctx: &TypeContext,
    decl: &TypeDeclaration,
    subst: &InclusionSubst,
) -> TypeDeclaration {
    // OCaml compiler/ml/includemod.ml:66-70 applies
    // `Subst.type_declaration` before comparing a signature declaration;
    // compiler/ml/subst.ml:273-301 copies params, kind, and manifest in one
    // `typexp` window, with a single cleanup after the whole declaration.
    let mut substituted = decl.clone();
    let mut slots = Vec::new();
    slots.extend(decl.type_params.iter().copied());
    collect_type_kind_types(&decl.type_kind, &mut slots);
    if let Some(manifest) = decl.type_manifest {
        slots.push(manifest);
    }
    for inlined in &decl.type_inlined_types {
        collect_type_inlined_types(inlined, &mut slots);
    }

    let copied = ctype::subst_identity_copy_many(type_ctx, &slots);
    if !subst.is_empty() {
        let mut seen = HashSet::new();
        for ty in &copied {
            rewrite_substituted_type_paths(type_ctx, *ty, subst, &mut seen);
        }
    }

    let mut copied = copied.into_iter();
    substituted.type_params = decl
        .type_params
        .iter()
        .map(|_| next_copied_type(&mut copied))
        .collect();
    substituted.type_kind = substitute_type_kind_with_copied_types(&decl.type_kind, &mut copied);
    substituted.type_manifest = decl.type_manifest.map(|_| next_copied_type(&mut copied));
    substituted.type_inlined_types = decl
        .type_inlined_types
        .iter()
        .map(|inlined| substitute_type_inlined_with_copied_types(inlined, &mut copied))
        .collect();
    debug_assert!(copied.next().is_none());
    substituted
}

pub(crate) fn substitute_type_declaration_self_path(
    type_ctx: &TypeContext,
    decl: &TypeDeclaration,
    from: &Path,
    to: &Path,
) -> TypeDeclaration {
    let mut subst = InclusionSubst::default();
    subst.type_paths.insert(from.clone(), to.clone());
    substitute_type_declaration_paths(type_ctx, decl, &subst)
}

fn substitute_extension_constructor_paths(
    type_ctx: &TypeContext,
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
    if let Some(replacement) = subst.type_paths.get(path) {
        return replacement;
    }
    match path.view() {
        PathView::Pident(_) => path.clone(),
        PathView::Pdot(prefix, name, pos) => Path::pdot_pos(substitute_module_path(prefix, subst), *name, *pos),
        PathView::Papply(functor, arg) => Path::papply(substitute_type_constructor_path(functor, subst), substitute_module_path(arg, subst)),
    }
}

fn substitute_module_path(path: &Path, subst: &InclusionSubst) -> Path {
    if let Some(replacement) = subst.module_paths.get(path) {
        return replacement;
    }
    match path.view() {
        PathView::Pident(_) => path.clone(),
        PathView::Pdot(prefix, name, pos) => Path::pdot_pos(substitute_module_path(prefix, subst), *name, *pos),
        PathView::Papply(functor, arg) => Path::papply(substitute_module_path(functor, subst), substitute_module_path(arg, subst)),
    }
}

fn substitute_modtype_path(path: &Path, subst: &InclusionSubst) -> Path {
    if let Some(replacement) = subst.modtype_paths.get(path) {
        return replacement;
    }
    match path.view() {
        PathView::Pident(_) => path.clone(),
        PathView::Pdot(prefix, name, pos) => Path::pdot_pos(substitute_module_path(prefix, subst), *name, *pos),
        PathView::Papply(functor, arg) => Path::papply(substitute_modtype_path(functor, subst), substitute_module_path(arg, subst)),
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
            param: *param,
            param_type: param_type.as_ref().map(|param_type| {
                Box::new(substitute_module_type_paths_no_freshen(
                    type_ctx, param_type, subst,
                ))
            }),
            result: Box::new(substitute_module_type_paths_no_freshen(
                type_ctx, result, subst,
            )),
        },
        ModuleType::MtySignature(sig) => ModuleType::MtySignature(std::sync::Arc::new(
            sig.iter()
                .map(|item| match item {
                    SignatureItem::SigValue(id, desc) => SignatureItem::SigValue(
                        *id,
                        substitute_value_description_paths(type_ctx, desc, subst),
                    ),
                    SignatureItem::SigType(id, decl, rec_status) => SignatureItem::SigType(
                        *id,
                        std::sync::Arc::new(substitute_type_declaration_paths(
                            type_ctx, decl, subst,
                        )),
                        *rec_status,
                    ),
                    SignatureItem::SigTypext(id, ext, ext_status) => SignatureItem::SigTypext(
                        *id,
                        substitute_extension_constructor_paths(type_ctx, ext, subst),
                        *ext_status,
                    ),
                    SignatureItem::SigModule(id, md, rec_status) => SignatureItem::SigModule(
                        *id,
                        substitute_module_declaration_paths_no_freshen(type_ctx, md, subst),
                        *rec_status,
                    ),
                    SignatureItem::SigModtype(id, mtd) => SignatureItem::SigModtype(
                        *id,
                        substitute_modtype_declaration_paths_no_freshen(type_ctx, mtd, subst),
                    ),
                    _ => item.clone(),
                })
                .collect(),
        )),
    }
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

fn rewrite_substituted_type_paths(
    type_ctx: &TypeContext,
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
            for arg in type_ctx.type_list(args).iter() {
                rewrite_substituted_type_paths(type_ctx, *arg, subst, seen);
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
        TypeDesc::Tarrow { args, ret } => {
            for arg in type_ctx.type_args(args).iter() {
                rewrite_substituted_type_paths(type_ctx, arg.typ, subst, seen);
            }
            rewrite_substituted_type_paths(type_ctx, *ret, subst, seen);
        }
        TypeDesc::Ttuple(items) => {
            for item in type_ctx.type_list(items).iter() {
                rewrite_substituted_type_paths(type_ctx, *item, subst, seen);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_substituted_type_paths(type_ctx, *fields, subst, seen);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_substituted_type_paths(type_ctx, *typ, subst, seen);
            rewrite_substituted_type_paths(type_ctx, *rest, subst, seen);
        }
        TypeDesc::Tvariant(row0) => {
            let row = crate::types::btype::row_repr(type_ctx, &type_ctx.row_desc(row0));
            for (_, field) in &row.row_fields {
                match field {
                    RowField::Rpresent(Some(arg)) => {
                        rewrite_substituted_type_paths(type_ctx, *arg, subst, seen)
                    }
                    RowField::Reither { types, .. } => {
                        for ty in types {
                            rewrite_substituted_type_paths(type_ctx, *ty, subst, seen);
                        }
                    }
                    RowField::Rpresent(None) | RowField::Rabsent => {}
                }
            }
            rewrite_substituted_type_paths(type_ctx, row.row_more, subst, seen);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_substituted_type_paths(type_ctx, *body, subst, seen);
            for var in type_ctx.type_list(vars).iter() {
                rewrite_substituted_type_paths(type_ctx, *var, subst, seen);
            }
        }
        TypeDesc::Tpackage { path, args, lids } => {
            for arg in type_ctx.type_list(args).iter() {
                rewrite_substituted_type_paths(type_ctx, *arg, subst, seen);
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
            rewrite_substituted_type_paths(type_ctx, *target, subst, seen);
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

fn substitute_value_type_paths(
    type_ctx: &TypeContext,
    ty: TypeExprRef,
    subst: &InclusionSubst,
) -> TypeExprRef {
    // OCaml compiler/ml/includemod.ml:56-60 applies `Subst.value_description`
    // before more-general checking; compiler/ml/subst.ml:303-309 copies and
    // substitutes the value type rather than mutating the original scheme.
    let copied = ctype::subst_identity_copy(type_ctx, ty);
    let mut seen = HashSet::new();
    rewrite_substituted_type_paths(type_ctx, copied, subst, &mut seen);
    copied
}

/// Check if type declaration `impl_decl` is a subtype of `sig_decl`.
pub(crate) fn type_declarations(
    type_ctx: &TypeContext,
    env: &Env,
    id: Ident,
    impl_decl: &TypeDeclaration,
    sig_decl: &TypeDeclaration,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<()> {
    // includemod.ml:66-67: `Env.mark_type_used env (Ident.name id) decl1`.
    crate::types::typecore::mark_type_used(type_ctx, env, id.name(), type_ctx.resolve_loc(impl_decl.type_loc));
    // includecore.ml:384-398 marks the implementation's constructors when both
    // declarations are variants.
    if let (
        crate::types::TypeKind::TypeVariant(impl_cstrs, _),
        crate::types::TypeKind::TypeVariant(_, _),
    ) = (&impl_decl.type_kind, &sig_decl.type_kind)
        && !env.is_implicit_coercion()
    {
        let usage = if impl_decl.type_private == crate::types::PrivateFlag::Private
            || sig_decl.type_private == crate::types::PrivateFlag::Public
        {
            crate::types::usage::ConstructorUsage::Positive
        } else {
            crate::types::usage::ConstructorUsage::Privatize
        };
        let mut usage_tables = type_ctx.usage();
        for cstr in impl_cstrs {
            usage_tables.mark_constructor_used(
                usage,
                id.name(),
                type_ctx.resolve_loc(impl_decl.type_loc),
                cstr.cd_id.name(),
            );
        }
    }
    if let Some(warning) = deprecated_inclusion_warning(
        type_ctx,
        id.name(),
        &impl_decl.type_attributes,
        &sig_decl.type_attributes,
        impl_decl.type_loc,
        sig_decl.type_loc,
    ) {
        warnings.push(warning);
    }

    // Check arity (number of type parameters)
    if impl_decl.type_params.len() != sig_decl.type_params.len() {
        return Err(type_decl_mismatch(
            id,
            impl_decl,
            sig_decl,
            "They have different arities.",
        ));
    }

    if !private_flags(impl_decl, sig_decl) {
        return Err(type_decl_mismatch(
            id,
            impl_decl,
            sig_decl,
            "A private type would be revealed.",
        ));
    }

    let param_map = build_type_param_map(type_ctx, &impl_decl.type_params, &sig_decl.type_params);
    match (impl_decl.type_manifest, sig_decl.type_manifest) {
        (_, None) => {
            if !type_param_lists_equal_for_inclusion(
                type_ctx,
                env,
                &impl_decl.type_params,
                &sig_decl.type_params,
            ) {
                return Err(type_decl_mismatch(
                    id,
                    impl_decl,
                    sig_decl,
                    "Their constraints differ.",
                ));
            }
        }
        (Some(impl_manifest), Some(sig_manifest)) => {
            if !type_manifest_for_inclusion(
                type_ctx,
                env,
                impl_manifest,
                &impl_decl.type_params,
                sig_manifest,
                &sig_decl.type_params,
                sig_decl.type_private,
                &param_map,
            ) {
                return Err(type_decl_mismatch(id, impl_decl, sig_decl, String::new()));
            }
        }
        (None, Some(sig_manifest)) => {
            let manifests_match = type_param_lists_equal_for_inclusion(
                type_ctx,
                env,
                &impl_decl.type_params,
                &sig_decl.type_params,
            ) && impl_decl.type_path.as_ref().is_some_and(|path| {
                let self_ty =
                    type_ctx.new_generic_constr(path.clone(), sig_decl.type_params.clone());
                type_exprs_equal_for_inclusion(
                    type_ctx,
                    Some(env),
                    &param_map,
                    self_ty,
                    sig_manifest,
                )
            });
            if !manifests_match {
                return Err(type_decl_mismatch(
                    id,
                    impl_decl,
                    sig_decl,
                    if type_param_lists_equal_for_inclusion(
                        type_ctx,
                        env,
                        &impl_decl.type_params,
                        &sig_decl.type_params,
                    ) {
                        String::new()
                    } else {
                        "Their constraints differ.".to_string()
                    },
                ));
            }
        }
    }

    let canonical_unboxed = |decl: &TypeDeclaration| {
        decl.type_representation == crate::types::TypeRepresentation::Unboxed
            || decl.variant_layout_ref().is_some_and(|layout_ref| {
                type_ctx.with_variant_layout(layout_ref, |layout| layout.configuration().unboxed)
            })
    };
    if !matches!(sig_decl.type_kind, TypeKind::TypeAbstract)
        && canonical_unboxed(impl_decl) != canonical_unboxed(sig_decl)
    {
        let unboxed_decl = if canonical_unboxed(sig_decl) {
            "the second"
        } else {
            "the first"
        };
        return Err(type_decl_mismatch(
            id,
            impl_decl,
            sig_decl,
            format!(
                "Their internal representations differ:\n{unboxed_decl} declaration uses unboxed representation."
            ),
        ));
    }

    if type_decl_tag_name(type_ctx, impl_decl) != type_decl_tag_name(type_ctx, sig_decl) {
        return Err(type_decl_mismatch(
            id,
            impl_decl,
            sig_decl,
            TypeDeclarationMismatchDetail::TagName,
        ));
    }

    // Check that the type kinds are compatible
    match (&impl_decl.type_kind, &sig_decl.type_kind) {
        // Abstract in signature allows any implementation
        (_, TypeKind::TypeAbstract) => {}

        (
            TypeKind::TypeRecord(impl_labels, impl_rep),
            TypeKind::TypeRecord(sig_labels, sig_rep),
        ) => {
            if let Some(detail) = compare_record_declarations(
                type_ctx,
                env,
                &impl_decl.type_params,
                &sig_decl.type_params,
                impl_labels,
                sig_labels,
                warnings,
            ) {
                return Err(type_decl_mismatch(id, impl_decl, sig_decl, detail));
            }
            if impl_rep != sig_rep {
                return Err(type_decl_mismatch(
                    id,
                    impl_decl,
                    sig_decl,
                    "Their internal representations differ.",
                ));
            }
        }

        (
            TypeKind::TypeVariant(impl_constructors, _),
            TypeKind::TypeVariant(sig_constructors, _),
        ) => {
            if let Some(detail) = compare_variant_declarations(
                type_ctx,
                env,
                &impl_decl.type_params,
                &sig_decl.type_params,
                impl_constructors,
                sig_constructors,
                type_ctx.variant_layout(
                    impl_decl
                        .variant_layout_ref()
                        .expect("variant declaration layout"),
                ),
                type_ctx.variant_layout(
                    sig_decl
                        .variant_layout_ref()
                        .expect("variant declaration layout"),
                ),
                warnings,
            ) {
                return Err(type_decl_mismatch(id, impl_decl, sig_decl, detail));
            }
        }

        (TypeKind::TypeOpen, TypeKind::TypeOpen) => {}

        _ => {
            return Err(type_decl_mismatch(
                id,
                impl_decl,
                sig_decl,
                "Their kinds differ.",
            ));
        }
    }

    if matches!(sig_decl.type_kind, TypeKind::TypeAbstract)
        && sig_decl.type_manifest.is_none()
        && !impl_decl.type_immediate
        && sig_decl.type_immediate
    {
        return Err(type_decl_mismatch(
            id,
            impl_decl,
            sig_decl,
            "the first is not an immediate type.",
        ));
    }

    // Match OCaml's Includecore.type_declarations variance check.
    let sig_is_abstract =
        matches!(sig_decl.type_kind, TypeKind::TypeAbstract) && sig_decl.type_manifest.is_none();
    let need_variance = sig_is_abstract
        || matches!(impl_decl.type_private, crate::types::PrivateFlag::Private)
        || matches!(impl_decl.type_kind, TypeKind::TypeOpen);
    if need_variance && impl_decl.type_variance.len() == sig_decl.type_variance.len() {
        let abstract_or_private =
            sig_is_abstract || matches!(sig_decl.type_private, crate::types::PrivateFlag::Private);
        let open_sig =
            matches!(sig_decl.type_kind, TypeKind::TypeOpen) && sig_decl.type_manifest.is_none();

        for (sig_param, (impl_var, sig_var)) in sig_decl.type_params.iter().zip(
            impl_decl
                .type_variance
                .iter()
                .zip(sig_decl.type_variance.iter()),
        ) {
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
                return Err(type_decl_mismatch(
                    id,
                    impl_decl,
                    sig_decl,
                    TypeDeclarationMismatchDetail::Variance,
                ));
            }
        }
    }

    Ok(())
}

fn compare_record_declarations(
    type_ctx: &TypeContext,
    env: &Env,
    impl_params: &[TypeExprRef],
    sig_params: &[TypeExprRef],
    impl_labels: &[LabelDeclaration],
    sig_labels: &[LabelDeclaration],
    warnings: &mut Vec<Warning>,
) -> Option<String> {
    let param_map = build_type_param_map(type_ctx, impl_params, sig_params);
    compare_record_declarations_with_param_map(
        type_ctx,
        env,
        &param_map,
        impl_params,
        sig_params,
        impl_labels,
        sig_labels,
        warnings,
    )
}

fn compare_record_declarations_with_param_map(
    type_ctx: &TypeContext,
    env: &Env,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
    impl_params: &[TypeExprRef],
    sig_params: &[TypeExprRef],
    impl_labels: &[LabelDeclaration],
    sig_labels: &[LabelDeclaration],
    warnings: &mut Vec<Warning>,
) -> Option<String> {
    // OCaml compiler/ml/includecore.ml:396 starts record comparison at 1,
    // so diagnostics report declaration field positions as 1-based.
    let mut index = 0usize;
    let len = impl_labels.len().min(sig_labels.len());

    while index < len {
        let impl_label = &impl_labels[index];
        let sig_label = &sig_labels[index];
        if impl_label.ld_id.name() != sig_label.ld_id.name() {
            return Some(format!(
                "Fields number {} have different names, {} and {}.",
                index + 1,
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
        if let Some(warning) = deprecated_mutable_inclusion_warning(
            type_ctx,
            impl_label.ld_id.name(),
            &impl_label.ld_attributes,
            &sig_label.ld_attributes,
            impl_label.ld_loc,
            sig_label.ld_loc,
        ) {
            warnings.push(warning);
        }
        let impl_runtime_name = impl_label.declaration_name();
        let sig_runtime_name = sig_label.declaration_name();
        if impl_runtime_name != sig_runtime_name {
            return Some(format!(
                "Fields number {} have different names, {} and {}.",
                index + 1,
                impl_runtime_name,
                sig_runtime_name
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

    // OCaml compiler/ml/includecore.ml:271-313 first compares every record
    // parameter and field in one Ctype.equal call. Fields are consed while
    // traversing, so the final comparison visits them in reverse declaration
    // order before the type parameters.
    let mut impl_types = Vec::with_capacity(impl_labels.len() + impl_params.len());
    let mut sig_types = Vec::with_capacity(sig_labels.len() + sig_params.len());
    impl_types.extend(impl_labels.iter().rev().map(|label| label.ld_type));
    impl_types.extend_from_slice(impl_params);
    sig_types.extend(sig_labels.iter().rev().map(|label| label.ld_type));
    sig_types.extend_from_slice(sig_params);
    if type_expr_lists_equal_for_inclusion(type_ctx, env, param_map, &impl_types, &sig_types) {
        return None;
    }

    // The reference retries field-by-field only after the batched fast path
    // fails, so diagnostics can identify the first incompatible declaration.
    let mut prior_impl = impl_params.to_vec();
    let mut prior_sig = sig_params.to_vec();
    for (impl_label, sig_label) in impl_labels.iter().zip(sig_labels) {
        // The slow pass re-runs `aux` (includecore.ml:284-312), so
        // `check_deprecated_mutable_inclusion` warns again for each field up
        // to the one that is blamed.
        if let Some(warning) = deprecated_mutable_inclusion_warning(
            type_ctx,
            impl_label.ld_id.name(),
            &impl_label.ld_attributes,
            &sig_label.ld_attributes,
            impl_label.ld_loc,
            sig_label.ld_loc,
        ) {
            warnings.push(warning);
        }
        prior_impl.insert(0, impl_label.ld_type);
        prior_sig.insert(0, sig_label.ld_type);
        if !type_expr_lists_equal_for_inclusion(type_ctx, env, param_map, &prior_impl, &prior_sig) {
            return Some(format!(
                "The types for field {} are not equal.",
                impl_label.ld_id.name()
            ));
        }
    }

    None
}

fn type_decl_mismatch(
    name: Ident,
    actual: &TypeDeclaration,
    expected: &TypeDeclaration,
    detail: impl Into<TypeDeclarationMismatchDetail>,
) -> IncludeModError {
    IncludeModError::TypeDeclarationMismatch {
        name,
        actual: actual.clone(),
        expected: expected.clone(),
        detail: detail.into(),
    }
}

fn type_decl_tag_name(type_ctx: &TypeContext, decl: &TypeDeclaration) -> Option<String> {
    decl.variant_layout_ref().and_then(|layout_ref| {
        type_ctx.with_variant_layout(layout_ref, |layout| layout.matching_facts.tag_name.clone())
    })
}

fn private_flags(impl_decl: &TypeDeclaration, sig_decl: &TypeDeclaration) -> bool {
    match (impl_decl.type_private, sig_decl.type_private) {
        (crate::types::PrivateFlag::Private, crate::types::PrivateFlag::Public) => {
            matches!(sig_decl.type_kind, TypeKind::TypeAbstract)
                && (sig_decl.type_manifest.is_none()
                    || !matches!(impl_decl.type_kind, TypeKind::TypeAbstract))
        }
        _ => true,
    }
}

/// `Ctype.equal env true decl1.type_params decl2.type_params`
/// (compiler/ml/includecore.ml:324, 336).
fn type_param_lists_equal_for_inclusion(
    type_ctx: &TypeContext,
    env: &Env,
    impl_params: &[TypeExprRef],
    sig_params: &[TypeExprRef],
) -> bool {
    crate::types::ctype::equal(type_ctx, env, true, impl_params, sig_params)
}

fn type_expr_lists_equal_for_inclusion(
    type_ctx: &TypeContext,
    env: &Env,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
    impl_types: &[TypeExprRef],
    sig_types: &[TypeExprRef],
) -> bool {
    if impl_types.len() != sig_types.len() {
        return false;
    }
    let mut seen = HashSet::new();
    impl_types
        .iter()
        .zip(sig_types.iter())
        .all(|(impl_ty, sig_ty)| {
            type_exprs_equal_for_inclusion_inner(
                type_ctx,
                Some(env),
                param_map,
                *impl_ty,
                *sig_ty,
                &mut seen,
            )
        })
}

fn type_manifest_is_absrow(type_ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> bool {
    let ty = type_ctx.repr(ty);
    let is_pident_constr = {
        let desc = type_ctx.get_desc(ty);
        matches!(
            &*desc,
            TypeDesc::Tconstr { path, .. } if path.as_pident().is_some()
        )
    };
    if !is_pident_constr {
        return false;
    }

    let expanded = type_ctx.repr(crate::types::ctype::expand_head(type_ctx, env, ty));
    let desc = type_ctx.get_desc(expanded);
    matches!(&*desc, TypeDesc::Tobject { .. } | TypeDesc::Tvariant(_))
}

fn row_more_can_match_fixed_private_super(type_ctx: &TypeContext, row_more: TypeExprRef) -> bool {
    let row_more = type_ctx.repr(row_more);
    let desc = type_ctx.get_desc(row_more);
    matches!(
        &*desc,
        TypeDesc::Tvar(_) | TypeDesc::Tconstr { .. } | TypeDesc::Tnil
    )
}

fn fixed_private_row_extra_field_allowed(type_ctx: &TypeContext, field: &RowField) -> bool {
    matches!(
        crate::types::btype::row_field_repr(type_ctx, field),
        RowField::Rabsent | RowField::Reither { .. }
    )
}

fn fixed_private_row_pair_types(
    type_ctx: &TypeContext,
    impl_field: &RowField,
    sig_field: &RowField,
    impl_types: &mut Vec<TypeExprRef>,
    sig_types: &mut Vec<TypeExprRef>,
) -> bool {
    let impl_field = crate::types::btype::row_field_repr(type_ctx, impl_field);
    let sig_field = crate::types::btype::row_field_repr(type_ctx, sig_field);
    match (&impl_field, &sig_field) {
        (RowField::Rpresent(Some(impl_ty)), RowField::Rpresent(Some(sig_ty))) => {
            impl_types.push(*impl_ty);
            sig_types.push(*sig_ty);
            true
        }
        (
            RowField::Rpresent(Some(impl_ty)),
            RowField::Reither {
                constant: false,
                types,
                ..
            },
        ) if types.len() == 1 => {
            impl_types.push(*impl_ty);
            sig_types.push(types[0]);
            true
        }
        (RowField::Rpresent(None), RowField::Rpresent(None)) => true,
        (
            RowField::Rpresent(None),
            RowField::Reither {
                constant: true,
                types,
                ..
            },
        ) if types.is_empty() => true,
        (
            RowField::Reither {
                constant: impl_constant,
                types: impl_field_types,
                ..
            },
            RowField::Reither {
                constant: sig_constant,
                types: sig_field_types,
                ..
            },
        ) if impl_constant == sig_constant && impl_field_types.len() == sig_field_types.len() => {
            impl_types.extend(impl_field_types.iter().copied());
            sig_types.extend(sig_field_types.iter().copied());
            true
        }
        (RowField::Rabsent, RowField::Reither { .. } | RowField::Rabsent) => true,
        _ => false,
    }
}

fn fixed_private_variant_manifest_for_inclusion(
    type_ctx: &TypeContext,
    env: &Env,
    impl_manifest: TypeExprRef,
    impl_params: &[TypeExprRef],
    sig_params: &[TypeExprRef],
    impl_row: &RowDesc,
    sig_row: &RowDesc,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
) -> bool {
    // Direct port of compiler/ml/includecore.ml:87-125:
    // private fixed rows compare the implementation row against the abstract
    // row carried by the signature manifest, while preserving the declaration
    // parameter equality checks in the same Ctype.equal calls.
    let impl_row = crate::types::btype::row_repr(type_ctx, impl_row);
    let sig_row = crate::types::btype::row_repr(type_ctx, sig_row);

    let mut impl_head_and_params = Vec::with_capacity(impl_params.len() + 1);
    impl_head_and_params.push(impl_manifest);
    impl_head_and_params.extend_from_slice(impl_params);
    let mut sig_head_and_params = Vec::with_capacity(sig_params.len() + 1);
    sig_head_and_params.push(sig_row.row_more);
    sig_head_and_params.extend_from_slice(sig_params);
    if !type_expr_lists_equal_for_inclusion(
        type_ctx,
        env,
        param_map,
        &impl_head_and_params,
        &sig_head_and_params,
    ) {
        return false;
    }

    if !row_more_can_match_fixed_private_super(type_ctx, impl_row.row_more) {
        return false;
    }

    let (impl_only, sig_only, pairs) =
        crate::types::ctype::merge_row_fields(&impl_row.row_fields, &sig_row.row_fields);
    let impl_only_is_empty_after_filter = impl_only
        .iter()
        .all(|(_, field)| crate::types::btype::row_field_is_absent(type_ctx, field));
    if sig_row.row_closed && (!impl_row.row_closed || !impl_only_is_empty_after_filter) {
        return false;
    }
    if sig_only
        .iter()
        .any(|(_, field)| !fixed_private_row_extra_field_allowed(type_ctx, field))
    {
        return false;
    }

    let mut impl_types = impl_params.to_vec();
    let mut sig_types = sig_params.to_vec();
    for (_, impl_field, sig_field) in pairs {
        if !fixed_private_row_pair_types(
            type_ctx,
            impl_field,
            sig_field,
            &mut impl_types,
            &mut sig_types,
        ) {
            return false;
        }
    }

    type_expr_lists_equal_for_inclusion(type_ctx, env, param_map, &impl_types, &sig_types)
}

fn fixed_private_object_manifest_for_inclusion(
    type_ctx: &TypeContext,
    env: &Env,
    impl_manifest: TypeExprRef,
    impl_params: &[TypeExprRef],
    sig_params: &[TypeExprRef],
    impl_fields: TypeExprRef,
    sig_fields: TypeExprRef,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
) -> bool {
    // Direct port of compiler/ml/includecore.ml:126-151 for private fixed
    // object rows.
    let (sig_fields_flat, sig_rest) = flatten_object_fields_for_inclusion(type_ctx, sig_fields);
    let mut impl_head_and_params = Vec::with_capacity(impl_params.len() + 1);
    impl_head_and_params.push(impl_manifest);
    impl_head_and_params.extend_from_slice(impl_params);
    let mut sig_head_and_params = Vec::with_capacity(sig_params.len() + 1);
    sig_head_and_params.push(sig_rest);
    sig_head_and_params.extend_from_slice(sig_params);
    if !type_expr_lists_equal_for_inclusion(
        type_ctx,
        env,
        param_map,
        &impl_head_and_params,
        &sig_head_and_params,
    ) {
        return false;
    }

    let (impl_fields_flat, impl_rest) = flatten_object_fields_for_inclusion(type_ctx, impl_fields);
    let rest_ok = {
        let impl_rest = type_ctx.repr(impl_rest);
        let desc = type_ctx.get_desc(impl_rest);
        matches!(
            &*desc,
            TypeDesc::Tnil | TypeDesc::Tvar(_) | TypeDesc::Tconstr { .. }
        )
    };
    if !rest_ok {
        return false;
    }

    let (pairs, _impl_only, sig_only) =
        associate_object_fields_for_inclusion(impl_fields_flat, sig_fields_flat);
    if !sig_only.is_empty() {
        return false;
    }
    // The signature must not grant write capability the implementation
    // lacks; an implementation's settable field may be abstracted to a
    // read-only one.
    if !pairs
        .iter()
        .all(|(_, impl_mut, _, sig_mut, _)| match sig_mut {
            FieldKind::Mutable => *impl_mut == FieldKind::Mutable,
            FieldKind::Immutable => true,
        })
    {
        return false;
    }

    let mut impl_types = impl_params.to_vec();
    let mut sig_types = sig_params.to_vec();
    for (_, _, impl_ty, _, sig_ty) in pairs {
        impl_types.push(impl_ty);
        sig_types.push(sig_ty);
    }
    type_expr_lists_equal_for_inclusion(type_ctx, env, param_map, &impl_types, &sig_types)
}

fn type_manifest_for_inclusion(
    type_ctx: &TypeContext,
    env: &Env,
    impl_manifest: TypeExprRef,
    impl_params: &[TypeExprRef],
    sig_manifest: TypeExprRef,
    sig_params: &[TypeExprRef],
    sig_private: crate::types::PrivateFlag,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
) -> bool {
    // Direct port of compiler/ml/includecore.ml:87-159 `type_manifest`.
    let impl_expanded = type_ctx.repr(crate::types::ctype::expand_head(
        type_ctx,
        env,
        impl_manifest,
    ));
    let sig_expanded = type_ctx.repr(crate::types::ctype::expand_head(
        type_ctx,
        env,
        sig_manifest,
    ));
    let impl_desc = type_ctx.get_desc(impl_expanded).into_desc();
    let sig_desc = type_ctx.get_desc(sig_expanded).into_desc();

    match (&impl_desc, &sig_desc) {
        (TypeDesc::Tvariant(impl_row), TypeDesc::Tvariant(sig_row))
            if type_manifest_is_absrow(type_ctx, env, type_ctx.row_desc(sig_row).row_more) =>
        {
            return fixed_private_variant_manifest_for_inclusion(
                type_ctx,
                env,
                impl_manifest,
                impl_params,
                sig_params,
                &type_ctx.row_desc(impl_row),
                &type_ctx.row_desc(sig_row),
                param_map,
            );
        }
        (
            TypeDesc::Tobject {
                fields: impl_fields,
                ..
            },
            TypeDesc::Tobject {
                fields: sig_fields, ..
            },
        ) if {
            let (_, sig_rest) = flatten_object_fields_for_inclusion(type_ctx, *sig_fields);
            type_manifest_is_absrow(type_ctx, env, sig_rest)
        } =>
        {
            return fixed_private_object_manifest_for_inclusion(
                type_ctx,
                env,
                impl_manifest,
                impl_params,
                sig_params,
                *impl_fields,
                *sig_fields,
                param_map,
            );
        }
        _ => {}
    }

    if type_exprs_equal_for_inclusion(type_ctx, Some(env), param_map, impl_manifest, sig_manifest) {
        return true;
    }

    if sig_private != crate::types::PrivateFlag::Private {
        return false;
    }

    let mut current = impl_expanded;
    let mut seen = HashSet::new();
    while seen.insert(current) {
        // compiler/ml/includecore.ml:157 calls Ctype.try_expand_once_opt,
        // whose ctype.ml:1269-1275 path uses Private expansion. This is what
        // allows inclusion against a private manifest to walk through the
        // implementation's strengthened self constructor.
        let Some(next) = crate::types::ctype::expand_abbrev_opt_once(type_ctx, env, current) else {
            break;
        };
        current = type_ctx.repr(next);
        if type_exprs_equal_for_inclusion(type_ctx, Some(env), param_map, current, sig_manifest) {
            return true;
        }
    }

    false
}

fn compare_variant_declarations(
    type_ctx: &TypeContext,
    env: &Env,
    impl_params: &[TypeExprRef],
    sig_params: &[TypeExprRef],
    impl_constructors: &[ConstructorDeclaration],
    sig_constructors: &[ConstructorDeclaration],
    impl_layout: crate::types::VariantLayout,
    sig_layout: crate::types::VariantLayout,
    warnings: &mut Vec<Warning>,
) -> Option<String> {
    let param_map = build_type_param_map(type_ctx, impl_params, sig_params);
    // OCaml compiler/ml/includecore.ml:392 starts variant comparison at 1,
    // so diagnostics report constructor positions as 1-based.
    let mut index = 0usize;
    let len = impl_constructors.len().min(sig_constructors.len());

    while index < len {
        let impl_constructor = &impl_constructors[index];
        let sig_constructor = &sig_constructors[index];
        if impl_constructor.cd_id.name() != sig_constructor.cd_id.name() {
            return Some(format!(
                "Fields number {} have different names, {} and {}.",
                index + 1,
                impl_constructor.cd_id.name(),
                sig_constructor.cd_id.name()
            ));
        }
        if let Some(warning) = deprecated_inclusion_warning(
            type_ctx,
            impl_constructor.cd_id.name(),
            &impl_constructor.cd_attributes,
            &sig_constructor.cd_attributes,
            impl_constructor.cd_loc,
            sig_constructor.cd_loc,
        ) {
            warnings.push(warning);
        }

        let (arg_param_map, arg_impl_params, arg_sig_params) =
            match (impl_constructor.cd_res, sig_constructor.cd_res) {
                (Some(impl_res), Some(sig_res)) => {
                    if !type_exprs_equal_for_inclusion(
                        type_ctx,
                        Some(env),
                        &param_map,
                        impl_res,
                        sig_res,
                    ) {
                        return Some(format!(
                            "The types for field {} are not equal.",
                            impl_constructor.cd_id.name()
                        ));
                    }
                    (
                        build_type_param_map(type_ctx, &[impl_res], &[sig_res]),
                        vec![impl_res],
                        vec![sig_res],
                    )
                }
                (Some(_), None) | (None, Some(_)) => {
                    return Some(format!(
                        "The types for field {} are not equal.",
                        impl_constructor.cd_id.name()
                    ));
                }
                (None, None) => (param_map.clone(), impl_params.to_vec(), sig_params.to_vec()),
            };

        match (&impl_constructor.cd_args, &sig_constructor.cd_args) {
            (
                ConstructorArguments::CstrRecord(impl_labels),
                ConstructorArguments::CstrRecord(sig_labels),
            ) => {
                if let Some(detail) = compare_record_declarations_with_param_map(
                    type_ctx,
                    env,
                    &arg_param_map,
                    &arg_impl_params,
                    &arg_sig_params,
                    impl_labels,
                    sig_labels,
                    warnings,
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
                    if !type_exprs_equal_for_inclusion(
                        type_ctx,
                        Some(env),
                        &arg_param_map,
                        *impl_arg,
                        *sig_arg,
                    ) {
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

        if constructor_is_nullary(impl_constructor) && {
            let impl_tag = match &impl_layout.constructors[index] {
                crate::types::VariantConstructorCase::Constant(tag) => &tag.literal,
                crate::types::VariantConstructorCase::Block(_) => unreachable!(),
            };
            let sig_tag = match &sig_layout.constructors[index] {
                crate::types::VariantConstructorCase::Constant(tag) => &tag.literal,
                crate::types::VariantConstructorCase::Block(_) => unreachable!(),
            };
            impl_tag != sig_tag
        } {
            return Some(format!(
                "The internal representations for case {} are not equal.",
                impl_constructor.cd_id.name()
            ));
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

fn constructor_is_nullary(constructor: &ConstructorDeclaration) -> bool {
    matches!(
        &constructor.cd_args,
        ConstructorArguments::CstrTuple(args) if args.is_empty()
    )
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
    env: Option<&Env>,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
    impl_ty: TypeExprRef,
    sig_ty: TypeExprRef,
) -> bool {
    let mut seen = HashSet::new();
    type_exprs_equal_for_inclusion_inner(type_ctx, env, param_map, impl_ty, sig_ty, &mut seen)
}

pub(crate) fn type_exprs_equal_for_type_declaration(
    type_ctx: &TypeContext,
    env: &Env,
    expected_params: &[TypeExprRef],
    actual_params: &[TypeExprRef],
    expected_ty: TypeExprRef,
    actual_ty: TypeExprRef,
) -> bool {
    let param_map = build_type_param_map(type_ctx, expected_params, actual_params);
    type_exprs_equal_for_inclusion(type_ctx, Some(env), &param_map, expected_ty, actual_ty)
}

fn type_exprs_equal_for_inclusion_inner(
    type_ctx: &TypeContext,
    env: Option<&Env>,
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

    if let (
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
    ) = (&*type_ctx.get_desc(impl_ty), &*type_ctx.get_desc(sig_ty))
        && impl_path.same(sig_path)
        && impl_args.is_empty()
        && sig_args.is_empty()
    {
        // OCaml compiler/ml/ctype.ml:3008 handles only equal nullary Tconstr
        // paths before `expand_head_rigid`. Parameterized constructors must
        // expand first; aliases can expose package types whose comparison has
        // observable Env/Ident allocation side effects.
        return type_ctx.type_list(impl_args)
            .iter()
            .zip(type_ctx.type_list(sig_args).iter())
            .all(|(impl_arg, sig_arg)| {
                type_exprs_equal_for_inclusion_inner(
                    type_ctx, env, param_map, *impl_arg, *sig_arg, seen,
                )
            });
    }

    if let Some(env) = env {
        let impl_expanded = type_ctx.repr(crate::types::ctype::expand_head(type_ctx, env, impl_ty));
        let sig_expanded = type_ctx.repr(crate::types::ctype::expand_head(type_ctx, env, sig_ty));
        if impl_expanded != impl_ty || sig_expanded != sig_ty {
            return type_exprs_equal_for_inclusion_inner(
                type_ctx,
                Some(env),
                param_map,
                impl_expanded,
                sig_expanded,
                seen,
            );
        }
    }

    match (&*type_ctx.get_desc(impl_ty), &*type_ctx.get_desc(sig_ty)) {
        (TypeDesc::Tvar(impl_name), TypeDesc::Tvar(sig_name))
        | (TypeDesc::Tunivar(impl_name), TypeDesc::Tunivar(sig_name)) => impl_name == sig_name,
        (
            TypeDesc::Tarrow {
                args: impl_args,
                ret: impl_ret,
            },
            TypeDesc::Tarrow {
                args: sig_args,
                ret: sig_ret,
            },
        ) => {
            impl_args.len() == sig_args.len()
                && type_ctx.type_args(impl_args).iter().zip(type_ctx.type_args(sig_args).iter()).all(|(impl_arg, sig_arg)| {
                    arg_labels_equal(impl_arg.label(), sig_arg.label())
                        && type_exprs_equal_for_inclusion_inner(
                            type_ctx,
                            env,
                            param_map,
                            impl_arg.typ,
                            sig_arg.typ,
                            seen,
                        )
                })
                && type_exprs_equal_for_inclusion_inner(
                    type_ctx, env, param_map, *impl_ret, *sig_ret, seen,
                )
        }
        (TypeDesc::Ttuple(impl_items), TypeDesc::Ttuple(sig_items)) => {
            impl_items.len() == sig_items.len()
                && type_ctx.type_list(impl_items)
                    .iter()
                    .zip(type_ctx.type_list(sig_items).iter())
                    .all(|(impl_item, sig_item)| {
                        type_exprs_equal_for_inclusion_inner(
                            type_ctx, env, param_map, *impl_item, *sig_item, seen,
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
                && type_ctx.type_list(impl_args)
                    .iter()
                    .zip(type_ctx.type_list(sig_args).iter())
                    .all(|(impl_arg, sig_arg)| {
                        type_exprs_equal_for_inclusion_inner(
                            type_ctx, env, param_map, *impl_arg, *sig_arg, seen,
                        )
                    })
        }
        (TypeDesc::Tlink(impl_next), _) | (TypeDesc::Tsubst(impl_next), _) => {
            type_exprs_equal_for_inclusion_inner(type_ctx, env, param_map, *impl_next, sig_ty, seen)
        }
        (_, TypeDesc::Tlink(sig_next)) | (_, TypeDesc::Tsubst(sig_next)) => {
            type_exprs_equal_for_inclusion_inner(type_ctx, env, param_map, impl_ty, *sig_next, seen)
        }
        (
            TypeDesc::Tpoly {
                body: impl_body, ..
            },
            TypeDesc::Tpoly { body: sig_body, .. },
        ) => type_exprs_equal_for_inclusion_inner(
            type_ctx, env, param_map, *impl_body, *sig_body, seen,
        ),
        (
            TypeDesc::Tpackage {
                path: impl_path,
                lids: impl_lids,
                args: impl_args,
            },
            TypeDesc::Tpackage {
                path: sig_path,
                lids: sig_lids,
                args: sig_args,
            },
        ) => {
            // OCaml compiler/ml/includecore.ml routes these comparisons through
            // Ctype.equal. Its package branch calls complete_type_list twice
            // (compiler/ml/ctype.ml:3048-3053, 2044-2047), allocating one
            // hidden `Pkg` module per side before comparing package arguments.
            let impl_lids = &type_ctx.package_lids(impl_lids);
            let sig_lids = &type_ctx.package_lids(sig_lids);
            let labels_complete = env.is_none_or(|env| {
                let sig_complete = crate::types::ctype::package_type_lists_have_ocaml_same_label_completion_side_effect(
                    type_ctx,
                    Some(env),
                    ModuleType::MtyIdent(sig_path.clone()),
                    impl_lids,
                    sig_lids,
                );
                let impl_complete = crate::types::ctype::package_type_lists_have_ocaml_same_label_completion_side_effect(
                    type_ctx,
                    Some(env),
                    ModuleType::MtyIdent(impl_path.clone()),
                    sig_lids,
                    impl_lids,
                );
                sig_complete && impl_complete
            });
            labels_complete
                && impl_path.same(sig_path)
                && impl_args.len() == sig_args.len()
                && type_ctx.type_list(impl_args)
                    .iter()
                    .zip(type_ctx.type_list(sig_args).iter())
                    .all(|(impl_arg, sig_arg)| {
                        type_exprs_equal_for_inclusion_inner(
                            type_ctx, env, param_map, *impl_arg, *sig_arg, seen,
                        )
                    })
        }
        (TypeDesc::Tvariant(impl_row), TypeDesc::Tvariant(sig_row)) => {
            // OCaml compiler/ml/includecore.ml:87-151 compares type manifests
            // through `Ctype.equal`; compiler/ml/ctype.ml:3331-3364 handles
            // polymorphic variant rows by row_repr/merge_row_fields and then
            // recursively equal-checks paired payloads under the same parameter
            // renaming map.
            rows_equal_for_inclusion(
                type_ctx,
                env,
                param_map,
                &type_ctx.row_desc(impl_row),
                &type_ctx.row_desc(sig_row),
                seen,
            )
        }
        // OCaml compiler/ml/ctype.ml:3293-3330 compares object
        // manifests through `eqtype_fields`, not physical identity.
        (
            TypeDesc::Tobject {
                fields: impl_fields,
                ..
            },
            TypeDesc::Tobject {
                fields: sig_fields, ..
            },
        ) => object_fields_equal_for_inclusion(
            type_ctx,
            env,
            param_map,
            *impl_fields,
            *sig_fields,
            seen,
        ),
        (TypeDesc::Tfield { .. }, TypeDesc::Tfield { .. }) => {
            object_fields_equal_for_inclusion(type_ctx, env, param_map, impl_ty, sig_ty, seen)
        }
        (TypeDesc::Tnil, TypeDesc::Tnil) => true,
        _ => impl_ty == sig_ty,
    }
}

fn rows_equal_for_inclusion(
    type_ctx: &TypeContext,
    env: Option<&Env>,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
    impl_row: &RowDesc,
    sig_row: &RowDesc,
    seen: &mut HashSet<(TypeExprRef, TypeExprRef)>,
) -> bool {
    let impl_row = crate::types::btype::row_repr(type_ctx, impl_row);
    let sig_row = crate::types::btype::row_repr(type_ctx, sig_row);
    let (impl_only, sig_only, pairs) =
        crate::types::ctype::merge_row_fields(&impl_row.row_fields, &sig_row.row_fields);

    if impl_row.row_closed != sig_row.row_closed
        || (!impl_row.row_closed && (!impl_only.is_empty() || !sig_only.is_empty()))
        || impl_only
            .iter()
            .chain(sig_only.iter())
            .any(|(_, field)| !crate::types::btype::row_field_is_absent(type_ctx, field))
    {
        return false;
    }

    if !crate::types::btype::static_row(type_ctx, &impl_row)
        && !type_exprs_equal_for_inclusion_inner(
            type_ctx,
            env,
            param_map,
            impl_row.row_more,
            sig_row.row_more,
            seen,
        )
    {
        return false;
    }

    pairs.into_iter().all(|(_, impl_field, sig_field)| {
        row_fields_equal_for_inclusion(type_ctx, env, param_map, impl_field, sig_field, seen)
    })
}

fn row_fields_equal_for_inclusion(
    type_ctx: &TypeContext,
    env: Option<&Env>,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
    impl_field: &RowField,
    sig_field: &RowField,
    seen: &mut HashSet<(TypeExprRef, TypeExprRef)>,
) -> bool {
    let impl_field = crate::types::btype::row_field_repr(type_ctx, impl_field);
    let sig_field = crate::types::btype::row_field_repr(type_ctx, sig_field);
    match (&impl_field, &sig_field) {
        (RowField::Rpresent(None), RowField::Rpresent(None))
        | (RowField::Rabsent, RowField::Rabsent) => true,
        (RowField::Rpresent(Some(impl_ty)), RowField::Rpresent(Some(sig_ty))) => {
            type_exprs_equal_for_inclusion_inner(type_ctx, env, param_map, *impl_ty, *sig_ty, seen)
        }
        (
            RowField::Reither {
                constant: impl_constant,
                types: impl_types,
                ..
            },
            RowField::Reither {
                constant: sig_constant,
                types: sig_types,
                ..
            },
        ) if impl_constant == sig_constant && impl_types.is_empty() && sig_types.is_empty() => true,
        (
            RowField::Reither {
                constant: impl_constant,
                types: impl_types,
                ..
            },
            RowField::Reither {
                constant: sig_constant,
                types: sig_types,
                ..
            },
        ) if impl_constant == sig_constant && !impl_types.is_empty() && !sig_types.is_empty() => {
            if !type_exprs_equal_for_inclusion_inner(
                type_ctx,
                env,
                param_map,
                impl_types[0],
                sig_types[0],
                seen,
            ) {
                return false;
            }
            if impl_types.len() == sig_types.len() {
                impl_types
                    .iter()
                    .skip(1)
                    .zip(sig_types.iter().skip(1))
                    .all(|(impl_ty, sig_ty)| {
                        type_exprs_equal_for_inclusion_inner(
                            type_ctx, env, param_map, *impl_ty, *sig_ty, seen,
                        )
                    })
            } else {
                sig_types.iter().skip(1).all(|sig_ty| {
                    type_exprs_equal_for_inclusion_inner(
                        type_ctx,
                        env,
                        param_map,
                        impl_types[0],
                        *sig_ty,
                        seen,
                    )
                }) && impl_types.iter().skip(1).all(|impl_ty| {
                    type_exprs_equal_for_inclusion_inner(
                        type_ctx,
                        env,
                        param_map,
                        *impl_ty,
                        sig_types[0],
                        seen,
                    )
                })
            }
        }
        _ => false,
    }
}

fn flatten_object_fields_for_inclusion(
    type_ctx: &TypeContext,
    fields: TypeExprRef,
) -> (Vec<ObjectFieldForInclusion>, TypeExprRef) {
    let mut flattened = Vec::new();
    let mut current = type_ctx.repr(fields);
    loop {
        let desc = type_ctx.get_desc(current);
        match &*desc {
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => {
                flattened.push((name.clone(), type_ctx.mutability_repr(*mutability), *typ));
                let next = type_ctx.repr(*rest);
                drop(desc);
                current = next;
            }
            _ => {
                drop(desc);
                break;
            }
        }
    }
    flattened.sort_by(|left, right| left.0.cmp(&right.0));
    (flattened, current)
}

type ObjectFieldForInclusion = (crate::name::Name, FieldKind, TypeExprRef);

fn associate_object_fields_for_inclusion(
    impl_fields: Vec<ObjectFieldForInclusion>,
    sig_fields: Vec<ObjectFieldForInclusion>,
) -> (
    Vec<(crate::name::Name, FieldKind, TypeExprRef, FieldKind, TypeExprRef)>,
    Vec<ObjectFieldForInclusion>,
    Vec<ObjectFieldForInclusion>,
) {
    let mut pairs = Vec::new();
    let mut impl_only = Vec::new();
    let mut sig_only = Vec::new();
    let mut impl_index = 0;
    let mut sig_index = 0;

    while impl_index < impl_fields.len() && sig_index < sig_fields.len() {
        let (impl_name, impl_kind, impl_ty) = &impl_fields[impl_index];
        let (sig_name, sig_kind, sig_ty) = &sig_fields[sig_index];
        match impl_name.cmp(sig_name) {
            std::cmp::Ordering::Equal => {
                pairs.push((impl_name.clone(), *impl_kind, *impl_ty, *sig_kind, *sig_ty));
                impl_index += 1;
                sig_index += 1;
            }
            std::cmp::Ordering::Less => {
                impl_only.push(impl_fields[impl_index].clone());
                impl_index += 1;
            }
            std::cmp::Ordering::Greater => {
                sig_only.push(sig_fields[sig_index].clone());
                sig_index += 1;
            }
        }
    }

    impl_only.extend(impl_fields[impl_index..].iter().cloned());
    sig_only.extend(sig_fields[sig_index..].iter().cloned());
    (pairs, impl_only, sig_only)
}

fn object_field_kinds_equal_for_inclusion(left: &FieldKind, right: &FieldKind) -> bool {
    // ctype.ml eqtype_fields: the mutabilities must agree.
    left == right
}

fn object_fields_equal_for_inclusion(
    type_ctx: &TypeContext,
    env: Option<&Env>,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
    impl_fields: TypeExprRef,
    sig_fields: TypeExprRef,
    seen: &mut HashSet<(TypeExprRef, TypeExprRef)>,
) -> bool {
    let (impl_fields_flat, impl_rest) = flatten_object_fields_for_inclusion(type_ctx, impl_fields);
    let (sig_fields_flat, sig_rest) = flatten_object_fields_for_inclusion(type_ctx, sig_fields);
    let same_row = impl_rest == sig_rest || seen.contains(&(impl_rest, sig_rest));

    if !same_row {
        if let Some(env) = env {
            let sig_rest_expanded =
                type_ctx.repr(crate::types::ctype::expand_head(type_ctx, env, sig_rest));
            if let TypeDesc::Tobject { fields, .. } = &*type_ctx.get_desc(sig_rest_expanded) {
                return object_fields_equal_for_inclusion(
                    type_ctx,
                    Some(env),
                    param_map,
                    impl_fields,
                    *fields,
                    seen,
                );
            }
        }
    }

    let (pairs, impl_only, sig_only) =
        associate_object_fields_for_inclusion(impl_fields_flat, sig_fields_flat);
    if !type_exprs_equal_for_inclusion_inner(type_ctx, env, param_map, impl_rest, sig_rest, seen)
        || !impl_only.is_empty()
        || !sig_only.is_empty()
    {
        return false;
    }

    pairs
        .into_iter()
        .all(|(_, impl_kind, impl_ty, sig_kind, sig_ty)| {
            object_field_kinds_equal_for_inclusion(&impl_kind, &sig_kind)
                && type_exprs_equal_for_inclusion_inner(
                    type_ctx, env, param_map, impl_ty, sig_ty, seen,
                )
        })
}

fn arg_labels_equal(
    left: crate::types::type_expr::TypeArgLabel,
    right: crate::types::type_expr::TypeArgLabel,
) -> bool {
    left.same_label(right)
}

/// Check if extension constructor `impl_ext` is compatible with `sig_ext`.
fn extension_constructors(
    type_ctx: &TypeContext,
    env: &Env,
    id: Ident,
    impl_ext: &ExtensionConstructor,
    sig_ext: &ExtensionConstructor,
    subst: &InclusionSubst,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<()> {
    // includecore.ml:461-466: `Env.mark_extension_used usage env ext1
    // (Ident.name id)`.
    if !env.is_implicit_coercion() {
        let usage = if impl_ext.ext_private == crate::types::PrivateFlag::Private
            || sig_ext.ext_private == crate::types::PrivateFlag::Public
        {
            crate::types::usage::ConstructorUsage::Positive
        } else {
            crate::types::usage::ConstructorUsage::Privatize
        };
        type_ctx.usage().mark_constructor_used(
            usage,
            impl_ext.ext_type_path.last(),
            type_ctx.resolve_loc(impl_ext.ext_loc),
            id.name(),
        );
    }
    let sig_ext = substitute_extension_constructor_paths(type_ctx, sig_ext, subst);
    let mismatch = || IncludeModError::ExtensionConstructorMismatch {
        name: id,
        actual: impl_ext.clone(),
        expected: sig_ext.clone(),
    };

    if !impl_ext.ext_type_path.same(&sig_ext.ext_type_path) {
        return Err(mismatch());
    }

    let param_map = build_type_param_map(
        type_ctx,
        &impl_ext.ext_type_params,
        &sig_ext.ext_type_params,
    );
    if impl_ext.ext_type_params.len() != sig_ext.ext_type_params.len()
        || impl_ext
            .ext_type_params
            .iter()
            .zip(sig_ext.ext_type_params.iter())
            .any(|(impl_param, sig_param)| {
                !type_exprs_equal_for_inclusion(
                    type_ctx,
                    Some(env),
                    &param_map,
                    *impl_param,
                    *sig_param,
                )
            })
    {
        return Err(mismatch());
    }

    // OCaml compiler/ml/includecore.ml:470-473 creates an anonymous
    // constructor identifier before comparing extension arguments. The
    // comparison uses it for record-constructor diagnostics; preserve the
    // allocation even when Rust's diagnostic representation does not need the
    // identifier so subsequent binding stamps follow the same typing order.
    let _constructor_id = type_ctx.create_ident("");

    if !constructor_arguments_equal_for_inclusion(
        type_ctx,
        env,
        &param_map,
        &impl_ext.ext_args,
        &sig_ext.ext_args,
        warnings,
    ) {
        return Err(mismatch());
    }

    match (impl_ext.ext_ret_type, sig_ext.ext_ret_type) {
        (Some(impl_ret), Some(sig_ret))
            if !type_exprs_equal_for_inclusion(
                type_ctx,
                Some(env),
                &param_map,
                impl_ret,
                sig_ret,
            ) =>
        {
            return Err(mismatch());
        }
        (Some(_), None) | (None, Some(_)) => return Err(mismatch()),
        _ => {}
    }

    if impl_ext.ext_private == crate::types::asttypes::PrivateFlag::Private
        && sig_ext.ext_private == crate::types::asttypes::PrivateFlag::Public
    {
        return Err(mismatch());
    }

    Ok(())
}

fn constructor_arguments_equal_for_inclusion(
    type_ctx: &TypeContext,
    env: &Env,
    param_map: &HashMap<TypeExprRef, TypeExprRef>,
    impl_args: &ConstructorArguments,
    sig_args: &ConstructorArguments,
    warnings: &mut Vec<Warning>,
) -> bool {
    match (impl_args, sig_args) {
        (
            ConstructorArguments::CstrTuple(impl_items),
            ConstructorArguments::CstrTuple(sig_items),
        ) => {
            impl_items.len() == sig_items.len()
                && impl_items
                    .iter()
                    .zip(sig_items.iter())
                    .all(|(impl_item, sig_item)| {
                        type_exprs_equal_for_inclusion(
                            type_ctx,
                            Some(env),
                            param_map,
                            *impl_item,
                            *sig_item,
                        )
                    })
        }
        (
            ConstructorArguments::CstrRecord(impl_labels),
            ConstructorArguments::CstrRecord(sig_labels),
        ) => {
            compare_record_declarations(type_ctx, env, &[], &[], impl_labels, sig_labels, warnings)
                .is_none()
        }
        _ => false,
    }
}

/// Check if module type declaration `impl_decl` is compatible with `sig_decl`.
fn modtype_declarations(
    type_ctx: &TypeContext,
    env: &Env,
    id: Ident,
    impl_decl: &ModtypeDeclaration,
    sig_decl: &ModtypeDeclaration,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<()> {
    if let Some(warning) = deprecated_inclusion_warning(
        type_ctx,
        id.name(),
        &impl_decl.mtd_attributes,
        &sig_decl.mtd_attributes,
        impl_decl.mtd_loc,
        sig_decl.mtd_loc,
    ) {
        warnings.push(warning);
    }

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

            let mismatch = |error| IncludeModError::ModuleTypeDeclarationMismatch {
                name: id,
                actual: impl_decl.clone(),
                expected: sig_decl.clone(),
                error: Box::new(with_modtype_context(id, error)),
            };

            // Module types must be equivalent (both directions), and OCaml
            // rejects equivalent declarations when either direction needs a
            // structure-field permutation.
            let impl_to_sig = modtypes_with_warnings(type_ctx, env, impl_mty, sig_mty, warnings)
                .map_err(&mismatch)?;
            let sig_to_impl = modtypes_with_warnings(type_ctx, env, sig_mty, impl_mty, warnings)
                .map_err(&mismatch)?;
            if !matches!(impl_to_sig, ModuleCoercion::Tcoerce_none)
                || !matches!(sig_to_impl, ModuleCoercion::Tcoerce_none)
            {
                return Err(mismatch(IncludeModError::ModtypePermutation));
            }
            Ok(())
        }
    }
}

/// `check_modtype_equiv` runs in `Modtype id :: cxt` (includemod.ml:
/// 473-476); every error below it shares that context.
fn with_modtype_context(name: Ident, error: IncludeModError) -> IncludeModError {
    IncludeModError::AtModtype {
        name,
        error: Box::new(error),
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
        ModtypeDeclaration, ModuleDeclaration, ModuleType, RecStatus, TypeKind, TypeRepresentation,
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
            type_loc: crate::types::DeclLoc::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_representation: TypeRepresentation::Boxed,
            type_inlined_types: vec![],
            type_path,
        }
    }

    fn value_desc(val_type: TypeExprRef) -> ValueDescription {
        ValueDescription {
            val_type,
            val_kind: ValueKind::ValReg,
            val_loc: crate::types::DeclLoc::none(),
            val_attributes: Default::default(),
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
                val_loc: crate::types::DeclLoc::none(),
                val_attributes: Default::default(),
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
                val_loc: crate::types::DeclLoc::none(),
                val_attributes: Default::default(),
                val_path: None,
            },
        )];
        let sig_sig: Signature = vec![SignatureItem::SigValue(
            Ident::create_local("x"),
            ValueDescription {
                val_type: val_ty,
                val_kind: ValueKind::ValReg,
                val_loc: crate::types::DeclLoc::none(),
                val_attributes: Default::default(),
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

        let impl_ty = type_ctx.new_generic_constr(Path::pident(impl_type_id), vec![]);
        let sig_ty = type_ctx.new_generic_constr(Path::pident(sig_type_id), vec![]);

        let sig_impl: Signature = vec![
            SignatureItem::SigModule(
                impl_mod_id,
                ModuleDeclaration {
                    md_type: ModuleType::MtySignature(std::sync::Arc::new(vec![
                        SignatureItem::SigValue(Ident::create_local("x"), value_desc(impl_ty)),
                    ])),
                    md_attributes: vec![],
                    md_loc: crate::types::DeclLoc::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            ),
            SignatureItem::SigType(
                impl_type_id,
                std::sync::Arc::new(abstract_type_decl(Some(Path::pident(impl_type_id)))),
                RecStatus::TrecNot,
            ),
        ];
        let sig_sig: Signature = vec![
            SignatureItem::SigModule(
                sig_mod_id,
                ModuleDeclaration {
                    md_type: ModuleType::MtySignature(std::sync::Arc::new(vec![
                        SignatureItem::SigValue(Ident::create_local("x"), value_desc(sig_ty)),
                    ])),
                    md_attributes: vec![],
                    md_loc: crate::types::DeclLoc::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            ),
            SignatureItem::SigType(
                sig_type_id,
                std::sync::Arc::new(abstract_type_decl(None)),
                RecStatus::TrecNot,
            ),
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
            modtype_id,
            ModtypeDeclaration {
                mtd_type: Some(ModuleType::MtySignature(std::sync::Arc::new(sig.clone()))),
                mtd_attributes: vec![],
                mtd_loc: crate::types::DeclLoc::none(),
            },
        );

        let result = modtypes(
            &type_ctx,
            &env,
            &ModuleType::MtySignature(std::sync::Arc::new(sig)),
            &ModuleType::MtyIdent(Path::pident(modtype_id)),
        );
        assert!(matches!(result, Ok(ModuleCoercion::Tcoerce_none)));
    }

    #[test]
    fn test_functor_match() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&type_ctx);

        let param_sig = ModuleType::MtySignature(std::sync::Arc::new(vec![]));
        let result_sig = ModuleType::MtySignature(std::sync::Arc::new(vec![]));

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
    fn extension_inclusion_allocates_ocaml_constructor_id() {
        let id_gen = std::sync::Arc::new(IdGenerator::new());
        let type_ctx = TypeContext::new(id_gen.clone());
        let env = initial_env(&type_ctx);
        let extension = ExtensionConstructor {
            ext_type_path: crate::types::predef::path_exn(),
            ext_type_params: vec![],
            ext_args: ConstructorArguments::CstrTuple(vec![]),
            ext_ret_type: None,
            ext_private: crate::types::PrivateFlag::Public,
            ext_loc: crate::types::DeclLoc::none(),
            ext_attributes: vec![],
            ext_is_exception: true,
        };
        let before = id_gen.current_stamp();

        let result = extension_constructors(
            &type_ctx,
            &env,
            Ident::create_persistent("Exit"),
            &extension,
            &extension,
            &InclusionSubst::default(),
            &mut Vec::new(),
        );

        assert!(result.is_ok());
        assert_eq!(id_gen.current_stamp(), before + 1);
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
                    val_loc: crate::types::DeclLoc::none(),
                    val_attributes: Default::default(),
                    val_path: None,
                },
            ),
            SignatureItem::SigType(
                Ident::create_local("t"),
                std::sync::Arc::new(TypeDeclaration {
                    type_params: vec![],
                    type_arity: 0,
                    type_kind: TypeKind::TypeAbstract,
                    type_private: crate::types::PrivateFlag::Public,
                    type_manifest: None,
                    type_variance: vec![],
                    type_newtype_level: None,
                    type_loc: crate::types::DeclLoc::none(),
                    type_attributes: vec![],
                    type_immediate: false,
                    type_representation: TypeRepresentation::Boxed,
                    type_inlined_types: vec![],
                    type_path: None,
                }),
                RecStatus::TrecNot,
            ),
        ];

        assert!(!is_empty_signature(&sig));
        assert_eq!(signature_values(&sig).len(), 1);
        assert_eq!(signature_types(&sig).len(), 1);
        assert_eq!(signature_modules(&sig).len(), 0);
    }
}
