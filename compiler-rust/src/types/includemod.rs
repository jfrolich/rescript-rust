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
    Attribute, ConstructorArguments, ConstructorDeclaration, ExtensionConstructor,
    LabelDeclaration, ModtypeDeclaration, ModuleDeclaration, ModuleType, RecStatus, Signature,
    SignatureItem, TypeDeclaration, TypeInlinedType, TypeKind, ValueDescription, ValueKind,
};
use crate::types::env::Env;
use crate::types::includecore::TypeMismatch;
use crate::types::type_expr::{RowDesc, RowField, TypeDesc};
use crate::types::typedtree::ModuleCoercion;
use crate::types::{TypeContext, TypeExprRef};
use crate::parser::code_frame;

// ============================================================================
// Error Types
// ============================================================================

/// Result type for inclusion checking.
pub type IncludeModResult<T> = Result<T, IncludeModError>;

// Keep the error of every inclusion-check `Result` small; box declarations.
const _: () = assert!(std::mem::size_of::<IncludeModError>() <= 64);

/// `Builtin_attributes.check_deprecated_inclusion`
/// (builtin_attributes.ml:119-122): `deprecated_of_attrs` of both sides,
/// whose `string_of_opt_payload` reads the record form as `""` and raises
/// on an invalid template. The pair is evaluated right to left, as
/// ocamlopt evaluates tuples: the signature's attributes first.
fn deprecated_inclusion_warning(
    type_ctx: &TypeContext,
    name: &str,
    impl_attrs: &[Attribute],
    sig_attrs: &[Attribute],
    def_loc: crate::types::DeclLoc,
    use_loc: crate::types::DeclLoc,
) -> IncludeModResult<Option<Warning>> {
    let invalid_escape = |loc| IncludeModError::InvalidStringEscape { loc };
    let sig_reason =
        crate::types::typecore::deprecated_of_decl_attrs(sig_attrs).map_err(invalid_escape)?;
    let impl_reason =
        crate::types::typecore::deprecated_of_decl_attrs(impl_attrs).map_err(invalid_escape)?;
    let (Some(reason), None) = (impl_reason, sig_reason) else {
        return Ok(None);
    };
    let message = if reason.is_empty() {
        name.to_string()
    } else {
        format!("{name}\n  {reason}")
    };
    Ok(Some(Warning::Deprecated {
        message,
        def_loc: type_ctx.resolve_loc(def_loc),
        use_loc: type_ctx.resolve_loc(use_loc),
        can_be_automigrated: false,
    }))
}

/// An inclusion check's result, with a payload reader's error taken out:
/// it is a `Location.Error`, not an `Includemod.Error`, so it escapes the
/// check and whatever reports its errors.
pub fn escaped<T>(
    type_ctx: &TypeContext,
    result: IncludeModResult<T>,
) -> Result<IncludeModResult<T>, crate::types::typecore::TypeCoreError> {
    match result
        .as_ref()
        .err()
        .and_then(IncludeModError::invalid_string_escape)
    {
        Some(loc) => Err(crate::types::typecore::invalid_escape_at(type_ctx, loc)),
        None => Ok(result),
    }
}

impl IncludeModError {
    /// The location of the first payload reader's error in checking order,
    /// wherever the error that carries it was nested: OCaml raises it at
    /// once, before any error the check would have reported.
    fn invalid_string_escape(&self) -> Option<crate::types::DeclLoc> {
        match self {
            IncludeModError::InvalidStringEscape { loc } => Some(*loc),
            IncludeModError::ModuleTypeDeclarationMismatch { error, .. }
            | IncludeModError::ModuleTypesMismatch { error, .. }
            | IncludeModError::InModule { error, .. }
            | IncludeModError::InFunctorBody { error, .. }
            | IncludeModError::InFunctorArg { error, .. }
            | IncludeModError::AtModtype { error, .. }
            | IncludeModError::Reversed { error } => error.invalid_string_escape(),
            IncludeModError::SignatureMismatch(errors) => errors
                .iter()
                .find_map(IncludeModError::invalid_string_escape),
            _ => None,
        }
    }
}

/// `Includemod.Error`'s list of `(pos list, Env.t, symptom)` (includemod.ml),
/// as a tree: each node that carries an error below it stands for the
/// position or the entry OCaml conses onto that error's list.
#[derive(Debug, Clone)]
pub enum IncludeModError {
    /// A `@deprecated` payload with an invalid escape: its reader's
    /// `Location.Error` (ast_payload.ml:39-51), which escapes inclusion
    /// checking.
    InvalidStringEscape {
        /// The payload's location.
        loc: crate::types::DeclLoc,
    },
    /// `Dont_match` (includemod.ml): the module types do not match, which
    /// the enclosing `modtypes` reports as their `Module_types` entry.
    DontMatch,
    /// `Missing_field (id, loc, kind, item)`: an expected item the
    /// implementation lacks.
    MissingField {
        /// The missing item.
        id: Ident,
        /// Where the signature declares it.
        loc: crate::types::DeclLoc,
        /// What kind of item it is, as printed (e.g. "value", "type").
        kind: &'static str,
        /// The signature's item.
        item: Box<SignatureItem>,
    },
    /// `Value_descriptions (id, vd1, vd2)`.
    ValueTypeMismatch {
        /// The value.
        name: Ident,
        /// The implementation's declaration.
        actual: Box<ValueDescription>,
        /// The signature's declaration.
        expected: Box<ValueDescription>,
        /// `find_arity_mismatch env vd1.val_type vd2.val_type`: the
        /// implementation's and the signature's arity, when they differ.
        arity_mismatch: Option<(usize, usize)>,
    },
    /// `Type_declarations (id, decl1, decl2, errs)`.
    TypeDeclarationMismatch {
        /// The type.
        name: Ident,
        /// The implementation's declaration.
        actual: Box<TypeDeclaration>,
        /// The signature's declaration.
        expected: Box<TypeDeclaration>,
        /// `Includecore.type_declarations`'s differences, never empty.
        errs: Vec<TypeMismatch>,
    },
    /// `Extension_constructors (id, ext1, ext2)`.
    ExtensionConstructorMismatch {
        /// The constructor.
        name: Ident,
        /// The implementation's constructor.
        actual: Box<ExtensionConstructor>,
        /// The signature's constructor.
        expected: Box<ExtensionConstructor>,
    },
    /// `Modtype_infos (id, info1, info2)` before the errors of the
    /// equivalence check (includemod.ml `modtype_infos`); `expected` is
    /// `Subst.modtype_declaration subst info2`.
    ModuleTypeDeclarationMismatch {
        /// The module type.
        name: Ident,
        /// The implementation's declaration.
        actual: Box<ModtypeDeclaration>,
        /// The signature's declaration.
        expected: Box<ModtypeDeclaration>,
        /// Why they are not equivalent.
        error: Box<IncludeModError>,
    },
    /// `Modtype_permutation`.
    ModtypePermutation,
    /// `Module_types (mty1, Subst.modtype subst mty2)` before the errors of
    /// the comparison (includemod.ml `modtypes`); a `DontMatch` error
    /// stands for none.
    ModuleTypesMismatch {
        /// The implementation's module type.
        actual: Box<ModuleType>,
        /// The signature's module type.
        expected: Box<ModuleType>,
        /// Why the first is not included in the second.
        error: Box<IncludeModError>,
    },
    /// `Unbound_module_path path`.
    UnboundModulePath {
        /// The normalized path.
        path: Path,
    },
    /// The errors under `Module id`.
    InModule {
        /// The module.
        name: Ident,
        /// The error inside it.
        error: Box<IncludeModError>,
    },
    /// The errors under `Body param`, a functor's result.
    InFunctorBody {
        /// The functor's parameter.
        param: Ident,
        /// The error in the result.
        error: Box<IncludeModError>,
    },
    /// The errors under `Arg param`, a functor's parameter, where inclusion
    /// goes the other way.
    InFunctorArg {
        /// The functor's parameter.
        param: Ident,
        /// The error in the parameter.
        error: Box<IncludeModError>,
    },
    /// The errors under `Modtype id`.
    AtModtype {
        /// The module type.
        name: Ident,
        /// The error inside it.
        error: Box<IncludeModError>,
    },
    /// The errors under `Reverse`: the second half of an equivalence check
    /// of module types, compared the other way round.
    Reversed {
        /// The error in the reversed check.
        error: Box<IncludeModError>,
    },
    /// Several errors at the same position, in order.
    SignatureMismatch(Vec<IncludeModError>),
}

/// The formatter an inclusion report prints into.
type Ppf<'b> = crate::parser::formatter::Formatter<&'b mut Vec<u8>>;

/// `Format.pp_print_string`: a string as wide as its bytes (format.ml
/// `pp_print_string` measures `String.length`).
fn pp_text(ppf: &mut Ppf<'_>, s: &str) {
    ppf.string_as(s.len(), s);
}

/// What an inclusion report is printed under.
pub(crate) enum ReportHeading<'a> {
    /// `Typemod.report_error (Not_included errs)`:
    /// `@[<v>Signature mismatch:@,@,%a@]`.
    SignatureMismatch,
    /// `Includemod.compunit`'s errors, whose list starts with
    /// `([], Env.empty, Interface_mismatch (impl_name, intf_name))`.
    Interface {
        impl_name: &'a str,
        intf_name: &'a str,
    },
    /// `Typemod.report_error (With_mismatch (lid, explanation))`.
    WithMismatch { lid: &'a str },
    /// `Typemod.report_error (With_makes_applicative_functor_ill_typed (lid,
    /// path, explanation))`.
    WithMakesApplicativeFunctorIllTyped { lid: &'a str, path: &'a str },
}

/// `Typemod.report_error (Not_included errs)` (typemod.ml).
pub fn format_error(type_ctx: &TypeContext, filename: &str, error: &IncludeModError) -> String {
    format_report(type_ctx, filename, error, ReportHeading::SignatureMismatch)
}

/// An inclusion report under `heading`, printed at column 2, the column of
/// a report's message in its vertical box, ending in a newline.
pub(crate) fn format_report(
    type_ctx: &TypeContext,
    filename: &str,
    error: &IncludeModError,
    heading: ReportHeading<'_>,
) -> String {
    use crate::parser::formatter::BoxKind;
    let mut entries = Vec::new();
    if let ReportHeading::Interface {
        impl_name,
        intf_name,
    } = heading
    {
        entries.push(ReportEntry {
            cxt: Vec::new(),
            symptom: ReportSymptom::Interface {
                impl_name,
                intf_name,
            },
        });
    }
    flatten_error(error, &mut Vec::new(), &mut entries);
    let mut buf = Vec::new();
    {
        let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
        ppf.string_as(2, "");
        let ppf = &mut ppf;
        match heading {
            ReportHeading::Interface { .. } => report_error(ppf, type_ctx, filename, &entries),
            ReportHeading::SignatureMismatch => {
                ppf.open_vbox(0);
                pp_text(ppf, "Signature mismatch:");
                ppf.cut();
                ppf.cut();
                report_error(ppf, type_ctx, filename, &entries);
                ppf.close_box();
            }
            // `@[<v>@[In this `with' constraint, the new definition of %a@
            // does not match its original definition@ in the constrained
            // signature:@]@,@,%a@]`
            ReportHeading::WithMismatch { lid } => {
                ppf.open_vbox(0);
                ppf.open_box(BoxKind::Box, 0);
                pp_text(
                    ppf,
                    &format!("In this `with' constraint, the new definition of {lid}"),
                );
                ppf.space();
                pp_text(ppf, "does not match its original definition");
                ppf.space();
                pp_text(ppf, "in the constrained signature:");
                ppf.close_box();
                ppf.cut();
                ppf.cut();
                report_error(ppf, type_ctx, filename, &entries);
                ppf.close_box();
            }
            // `@[<v>@[This `with' constraint on %a makes the applicative
            // functor @ type %s ill-typed in the constrained signature:@]@,@,%a@]`
            ReportHeading::WithMakesApplicativeFunctorIllTyped { lid, path } => {
                ppf.open_vbox(0);
                ppf.open_box(BoxKind::Box, 0);
                pp_text(
                    ppf,
                    &format!("This `with' constraint on {lid} makes the applicative functor "),
                );
                ppf.space();
                pp_text(
                    ppf,
                    &format!("type {path} ill-typed in the constrained signature:"),
                );
                ppf.close_box();
                ppf.cut();
                ppf.cut();
                report_error(ppf, type_ctx, filename, &entries);
                ppf.close_box();
            }
        }
        ppf.flush();
    }
    if buf.is_empty() {
        return String::new();
    }
    let mut out = String::from("  ");
    out.push_str(&String::from_utf8_lossy(&buf));
    out.push('\n');
    out
}

/// One position of `Includemod.pos` (includemod.ml).
#[derive(Clone, Copy, PartialEq, Debug)]
enum IncludePos {
    Module(Ident),
    Modtype(Ident),
    Arg(Ident),
    Body(Ident),
    Reverse,
}

/// The symptom of an entry of the error list.
enum ReportSymptom<'e> {
    /// `Interface_mismatch (impl_name, intf_name)`.
    Interface {
        impl_name: &'e str,
        intf_name: &'e str,
    },
    /// `Module_types (mty1, mty2)`.
    ModuleTypes {
        actual: &'e ModuleType,
        expected: &'e ModuleType,
    },
    /// `Modtype_infos (id, info1, info2)`.
    ModtypeInfos {
        name: &'e Ident,
        actual: &'e ModtypeDeclaration,
        expected: &'e ModtypeDeclaration,
    },
    /// Any other symptom, the error that is it.
    Leaf(&'e IncludeModError),
}

/// An entry `(cxt, env, symptom)` of `Includemod.Error`'s list; `cxt` is
/// listed from the outermost position, `List.rev` of OCaml's.
struct ReportEntry<'e> {
    cxt: Vec<IncludePos>,
    symptom: ReportSymptom<'e>,
}

/// The list OCaml builds for `error`, in order, each entry under the
/// positions above it.
fn flatten_error<'e>(
    error: &'e IncludeModError,
    cxt: &mut Vec<IncludePos>,
    out: &mut Vec<ReportEntry<'e>>,
) {
    let mut under = |pos, error: &'e IncludeModError, out: &mut Vec<ReportEntry<'e>>| {
        cxt.push(pos);
        flatten_error(error, cxt, out);
        cxt.pop();
    };
    match error {
        IncludeModError::SignatureMismatch(errors) => {
            for error in errors {
                flatten_error(error, cxt, out);
            }
        }
        IncludeModError::InModule { name, error } => under(IncludePos::Module(*name), error, out),
        IncludeModError::AtModtype { name, error } => under(IncludePos::Modtype(*name), error, out),
        IncludeModError::InFunctorBody { param, error } => {
            under(IncludePos::Body(*param), error, out)
        }
        IncludeModError::InFunctorArg { param, error } => {
            under(IncludePos::Arg(*param), error, out)
        }
        IncludeModError::Reversed { error } => under(IncludePos::Reverse, error, out),
        IncludeModError::ModuleTypesMismatch {
            actual,
            expected,
            error,
        } => {
            out.push(ReportEntry {
                cxt: cxt.clone(),
                symptom: ReportSymptom::ModuleTypes { actual, expected },
            });
            if !matches!(**error, IncludeModError::DontMatch) {
                flatten_error(error, cxt, out);
            }
        }
        IncludeModError::ModuleTypeDeclarationMismatch {
            name,
            actual,
            expected,
            error,
        } => {
            out.push(ReportEntry {
                cxt: cxt.clone(),
                symptom: ReportSymptom::ModtypeInfos {
                    name,
                    actual,
                    expected,
                },
            });
            flatten_error(error, cxt, out);
        }
        // `modtypes` turns every `Dont_match` into its `Module_types` entry.
        IncludeModError::DontMatch => {
            debug_assert!(false, "Dont_match escaped its modtypes");
        }
        _ => out.push(ReportEntry {
            cxt: cxt.clone(),
            symptom: ReportSymptom::Leaf(error),
        }),
    }
}

/// Whether a symptom shows the declarations that differ. A permutation of
/// fields doesn't, so the comparison of the module types around it stays
/// (includemod.ml `report_error`).
fn shows_declarations(symptom: &ReportSymptom<'_>) -> bool {
    match symptom {
        ReportSymptom::ModuleTypes { .. } | ReportSymptom::ModtypeInfos { .. } => true,
        ReportSymptom::Interface { .. } => false,
        ReportSymptom::Leaf(error) => matches!(
            error,
            IncludeModError::MissingField { .. }
                | IncludeModError::ValueTypeMismatch { .. }
                | IncludeModError::TypeDeclarationMismatch { .. }
                | IncludeModError::ExtensionConstructorMismatch { .. }
        ),
    }
}

/// `Includemod.report_error` (includemod.ml): the error is a path of
/// symptoms from the whole module down to the items that differ. A module or
/// module type comparison is left out when a later symptom shows the
/// declarations that differ; each entry follows a blank line and, when its
/// position differs from the one before, a line naming where it is.
fn report_error(
    ppf: &mut Ppf<'_>,
    type_ctx: &TypeContext,
    filename: &str,
    entries: &[ReportEntry<'_>],
) {
    ppf.open_vbox(0);
    let mut previous: Option<&[IncludePos]> = None;
    for (index, entry) in entries.iter().enumerate() {
        if matches!(
            entry.symptom,
            ReportSymptom::ModuleTypes { .. } | ReportSymptom::ModtypeInfos { .. }
        ) && entries[index + 1..]
            .iter()
            .any(|later| shows_declarations(&later.symptom))
        {
            continue;
        }
        if previous.is_some() {
            ppf.cut();
            ppf.cut();
        }
        let show_context = previous != Some(entry.cxt.as_slice());
        include_err(ppf, type_ctx, filename, show_context, entry);
        previous = Some(&entry.cxt);
    }
    ppf.close_box();
}

/// `include_err ~show_context` (includemod.ml): `@[<v>%a%a@]` of the
/// position and the symptom. Inclusion is reversed in each functor parameter
/// on the way, and in the second half of an equivalence check of module
/// types.
fn include_err(
    ppf: &mut Ppf<'_>,
    type_ctx: &TypeContext,
    filename: &str,
    show_context: bool,
    entry: &ReportEntry<'_>,
) {
    let swapped = entry
        .cxt
        .iter()
        .filter(|pos| matches!(pos, IncludePos::Arg(_) | IncludePos::Reverse))
        .count()
        % 2
        == 1;
    ppf.open_vbox(0);
    if show_context {
        let cxt: Vec<IncludePos> = entry
            .cxt
            .iter()
            .copied()
            .filter(|pos| *pos != IncludePos::Reverse)
            .collect();
        pp_include_context(ppf, &cxt);
    }
    include_symptom(ppf, type_ctx, filename, swapped, &entry.symptom);
    ppf.close_box();
}

/// `Includemod.context` (includemod.ml) for a context listed from the
/// outermost step.
fn pp_context(ppf: &mut Ppf<'_>, cxt: &[IncludePos]) {
    use crate::parser::formatter::BoxKind;
    match cxt {
        // `@[<2>module %a%a@]`
        [IncludePos::Module(id), rem @ ..] => {
            ppf.open_box(BoxKind::Box, 2);
            pp_text(ppf, "module ");
            pp_text(ppf, id.name());
            pp_context_args(ppf, rem);
            ppf.close_box();
        }
        // `@[<2>module type %a =@ %a@]`
        [IncludePos::Modtype(id), rem @ ..] => {
            ppf.open_box(BoxKind::Box, 2);
            pp_text(ppf, "module type ");
            pp_text(ppf, id.name());
            pp_text(ppf, " =");
            ppf.space();
            pp_context_mty(ppf, rem);
            ppf.close_box();
        }
        // `(%s) =>@ %a`
        [IncludePos::Body(x), rem @ ..] => {
            pp_text(ppf, "(");
            pp_text(ppf, context_argname(x));
            pp_text(ppf, ") =>");
            ppf.space();
            pp_context_mty(ppf, rem);
        }
        // `(%a:@ %a) => ...`
        [IncludePos::Arg(x), rem @ ..] => {
            pp_text(ppf, "(");
            pp_text(ppf, x.name());
            pp_text(ppf, ":");
            ppf.space();
            pp_context_mty(ppf, rem);
            pp_text(ppf, ") => ...");
        }
        [IncludePos::Reverse, rem @ ..] => pp_context(ppf, rem),
        [] => pp_text(ppf, "<here>"),
    }
}

/// `context_mty`: `@[<2>{@ %a@;<1 -2>}@]` around a module step.
fn pp_context_mty(ppf: &mut Ppf<'_>, cxt: &[IncludePos]) {
    match cxt {
        [IncludePos::Module(_) | IncludePos::Modtype(_), ..] => {
            ppf.open_box(crate::parser::formatter::BoxKind::Box, 2);
            pp_text(ppf, "{");
            ppf.space();
            pp_context(ppf, cxt);
            ppf.break_(1, -2);
            pp_text(ppf, "}");
            ppf.close_box();
        }
        _ => pp_context(ppf, cxt),
    }
}

/// `args`: `:@ %a`, the module step's type, a functor's parameters
/// included.
fn pp_context_args(ppf: &mut Ppf<'_>, cxt: &[IncludePos]) {
    pp_text(ppf, ":");
    ppf.space();
    pp_context_mty(ppf, cxt);
}

/// `argname`: the anonymous parameter `*` prints as nothing.
fn context_argname(id: &Ident) -> &str {
    if id.name() == "*" { "" } else { id.name() }
}

/// `path_of_modules` (includemod.ml): the path of the modules a context goes
/// through, outermost first, printed by `Printtyp.path`, when it goes through
/// modules only.
fn path_of_modules(cxt: &[IncludePos]) -> Option<String> {
    if cxt.is_empty() {
        return None;
    }
    let mut names = Vec::with_capacity(cxt.len());
    for pos in cxt {
        match pos {
            IncludePos::Module(id) => names.push(id.name()),
            IncludePos::Modtype(_)
            | IncludePos::Arg(_)
            | IncludePos::Body(_)
            | IncludePos::Reverse => return None,
        }
    }
    Some(names.join("."))
}

/// The `context` of `report_error` (includemod.ml): where in the module an
/// error is, as a line before it. A module type or a functor's result at the
/// end of a module path is named in words; any other position is shown as a
/// module type with `<here>`.
fn pp_include_context(ppf: &mut Ppf<'_>, cxt: &[IncludePos]) {
    if cxt.is_empty() {
        return;
    }
    let line = match path_of_modules(cxt) {
        Some(path) => Some(format!("In module {path}:")),
        None => match cxt.split_last() {
            Some((IncludePos::Modtype(id), [])) => Some(format!("In module type {}:", id.name())),
            Some((IncludePos::Modtype(id), modules)) => {
                path_of_modules(modules).map(|path| format!("In module type {path}.{}:", id.name()))
            }
            Some((IncludePos::Body(_), modules)) => {
                path_of_modules(modules).map(|path| format!("In the result of functor {path}:"))
            }
            Some((IncludePos::Arg(x), modules)) => path_of_modules(modules)
                .map(|path| format!("In the parameter {} of functor {path}:", x.name())),
            _ => None,
        },
    };
    match line {
        Some(line) => pp_text(ppf, &line),
        // `@[<hv 2>At position@ %a@]`
        None => {
            ppf.open_hvbox(2);
            pp_text(ppf, "At position");
            ppf.space();
            pp_context(ppf, cxt);
            ppf.close_box();
        }
    }
    ppf.cut();
    ppf.cut();
}

/// `show_declaration label loc pp ppf x` (includemod.ml):
/// `@[<v 2>%s (%a):@,%a@]`, a declaration under a label naming its side and
/// its location, `Location.print_loc` writing the file name and range in
/// zero-width colour tags.
fn pp_show_declaration(
    ppf: &mut Ppf<'_>,
    type_ctx: &TypeContext,
    filename: &str,
    label: &str,
    loc: crate::types::DeclLoc,
    declaration: &str,
) {
    let loc = type_ctx.resolve_loc(loc);
    let location = code_frame::format_location(
        &location_filename(type_ctx, filename, &loc),
        &loc.loc_start,
        &loc.loc_end,
    );
    ppf.open_vbox(2);
    pp_text(ppf, label);
    pp_text(ppf, " (");
    ppf.string_as(location.len(), &code_frame::colorize_location(&location));
    pp_text(ppf, "):");
    ppf.cut();
    crate::types::printtyp::pp_doc(ppf, declaration);
    ppf.close_box();
}

/// `show_declarations ~swapped pp ppf (x1, loc1, x2, loc2)` (includemod.ml):
/// `x1` is included in `x2`; in a functor's parameter, where inclusion goes
/// the other way, `swapped` is true and `x2` is the actual declaration.
#[allow(clippy::too_many_arguments)]
fn pp_show_declarations(
    ppf: &mut Ppf<'_>,
    type_ctx: &TypeContext,
    filename: &str,
    swapped: bool,
    x1: &str,
    loc1: crate::types::DeclLoc,
    x2: &str,
    loc2: crate::types::DeclLoc,
) {
    let ((actual, actual_loc), (expected, expected_loc)) = if swapped {
        ((x2, loc2), (x1, loc1))
    } else {
        ((x1, loc1), (x2, loc2))
    };
    pp_show_declaration(
        ppf,
        type_ctx,
        filename,
        "Actual declaration",
        actual_loc,
        actual,
    );
    ppf.cut();
    ppf.cut();
    pp_show_declaration(
        ppf,
        type_ctx,
        filename,
        "Expected declaration",
        expected_loc,
        expected,
    );
}

/// `include_symptom ~swapped env ppf symptom` (includemod.ml).
fn include_symptom(
    ppf: &mut Ppf<'_>,
    type_ctx: &TypeContext,
    filename: &str,
    swapped: bool,
    symptom: &ReportSymptom<'_>,
) {
    use crate::parser::formatter::BoxKind;
    let error = match symptom {
        // `@[The implementation %s@ does not match the interface %s:@]`
        ReportSymptom::Interface {
            impl_name,
            intf_name,
        } => {
            ppf.open_box(BoxKind::Box, 0);
            pp_text(ppf, &format!("The implementation {impl_name}"));
            ppf.space();
            pp_text(ppf, &format!("does not match the interface {intf_name}:"));
            ppf.close_box();
            return;
        }
        // `@[<v 2>Actual module type:@,%a@]@,@,@[<v 2>Expected module
        // type:@,%a@]`
        ReportSymptom::ModuleTypes { actual, expected } => {
            let (actual, expected) = if swapped {
                (expected, actual)
            } else {
                (actual, expected)
            };
            ppf.open_vbox(2);
            pp_text(ppf, "Actual module type:");
            ppf.cut();
            crate::types::printtyp::pp_doc(ppf, &format_module_type(type_ctx, actual));
            ppf.close_box();
            ppf.cut();
            ppf.cut();
            ppf.open_vbox(2);
            pp_text(ppf, "Expected module type:");
            ppf.cut();
            crate::types::printtyp::pp_doc(ppf, &format_module_type(type_ctx, expected));
            ppf.close_box();
            return;
        }
        ReportSymptom::ModtypeInfos {
            name,
            actual,
            expected,
        } => {
            pp_show_declarations(
                ppf,
                type_ctx,
                filename,
                swapped,
                &format_modtype_declaration(type_ctx, name, actual),
                actual.mtd_loc,
                &format_modtype_declaration(type_ctx, name, expected),
                expected.mtd_loc,
            );
            return;
        }
        ReportSymptom::Leaf(error) => error,
    };
    match error {
        IncludeModError::MissingField {
            id,
            loc,
            kind,
            item,
        } => {
            // Reversed, the item is one the actual declaration has and the
            // expected one lacks.
            let (sentence, label) = if swapped {
                (
                    "is only present in the actual declaration.",
                    "Actual declaration",
                )
            } else {
                ("is required but not provided.", "Expected declaration")
            };
            pp_text(ppf, &format!("The {kind} `{}` {sentence}", id.name()));
            ppf.cut();
            ppf.cut();
            pp_show_declaration(
                ppf,
                type_ctx,
                filename,
                label,
                *loc,
                &format_signature(type_ctx, std::slice::from_ref(&**item)),
            );
        }
        IncludeModError::ValueTypeMismatch {
            name,
            actual,
            expected,
            arity_mismatch,
        } => {
            pp_show_declarations(
                ppf,
                type_ctx,
                filename,
                swapped,
                &format_value_description(type_ctx, name, actual),
                actual.val_loc,
                &format_value_description(type_ctx, name, expected),
                expected.val_loc,
            );
            // `show_arity_mismatch env ppf d1 d2`, or `d2 d1` when swapped:
            // `@,@,@[The implementation contains a function taking %s where
            // the interface expects one taking %s.@]`.
            let arity_mismatch =
                arity_mismatch.map(|(n1, n2)| if swapped { (n2, n1) } else { (n1, n2) });
            if let Some((actual_arity, expected_arity)) = arity_mismatch {
                let arguments = |arity: usize| {
                    if arity == 1 {
                        "1 argument".to_string()
                    } else {
                        format!("{arity} arguments")
                    }
                };
                ppf.cut();
                ppf.cut();
                ppf.open_box(BoxKind::Box, 0);
                pp_text(
                    ppf,
                    &format!(
                        "The implementation contains a function taking {} where the interface expects one taking {}.",
                        arguments(actual_arity),
                        arguments(expected_arity)
                    ),
                );
                ppf.close_box();
            }
        }
        IncludeModError::TypeDeclarationMismatch {
            name,
            actual,
            expected,
            errs,
        } => {
            let printed1 = format_type_declaration(type_ctx, name, actual);
            let printed2 = format_type_declaration(type_ctx, name, expected);
            pp_show_declarations(
                ppf,
                type_ctx,
                filename,
                swapped,
                &printed1,
                actual.type_loc,
                &printed2,
                expected.type_loc,
            );
            if errs.iter().any(|err| *err != TypeMismatch::Manifest) {
                let (first, second) = if swapped {
                    ("the expected", "the actual")
                } else {
                    ("the actual", "the expected")
                };
                // Declarations can print the same and still differ, when a
                // type they mention differs between the two sides, e.g. a
                // class the interface leaves abstract. The reasons then say
                // that first.
                let read_the_same = printed1 == printed2;
                ppf.cut();
                crate::types::includecore::report_type_mismatch(
                    ppf,
                    read_the_same,
                    first,
                    second,
                    "declaration",
                    errs,
                );
            }
        }
        IncludeModError::ExtensionConstructorMismatch {
            name,
            actual,
            expected,
        } => {
            pp_show_declarations(
                ppf,
                type_ctx,
                filename,
                swapped,
                &format_extension_constructor(type_ctx, name, actual),
                actual.ext_loc,
                &format_extension_constructor(type_ctx, name, expected),
                expected.ext_loc,
            );
        }
        IncludeModError::ModtypePermutation => {
            pp_text(ppf, "Illegal permutation of structure fields");
        }
        IncludeModError::UnboundModulePath { path } => {
            pp_text(ppf, "Unbound module ");
            pp_text(ppf, &path.name());
        }
        // Taken out by `escaped` before an inclusion error is reported.
        IncludeModError::InvalidStringEscape { .. } => {
            unreachable!("an invalid escape escapes inclusion checking")
        }
        IncludeModError::DontMatch
        | IncludeModError::SignatureMismatch(_)
        | IncludeModError::InModule { .. }
        | IncludeModError::AtModtype { .. }
        | IncludeModError::InFunctorBody { .. }
        | IncludeModError::InFunctorArg { .. }
        | IncludeModError::Reversed { .. }
        | IncludeModError::ModuleTypesMismatch { .. }
        | IncludeModError::ModuleTypeDeclarationMismatch { .. } => {
            unreachable!("not a symptom of its own")
        }
    }
}

pub(crate) fn location_filename(type_ctx: &TypeContext, fallback: &str, loc: &Location) -> String {
    type_ctx
        .resolve_cmi_longident_component(loc.loc_start.file_name)
        .filter(|name| !name.is_empty() && name != "_none_")
        .unwrap_or_else(|| fallback.to_string())
}

// Declarations and module types print through `Printtyp`'s outcome trees and
// `Res_outcome_printer` (printtyp.ml:1007-1192, res_outcome_printer.ml:481-842),
// each rendered as one Doc string at width 80 that `pp_doc` prints into a
// report's boxes.

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

/// `Printtyp.signature`: the outcome tree of a signature, printed.
fn format_signature(type_ctx: &TypeContext, sig: &[SignatureItem]) -> String {
    let tree = crate::types::printtyp::Printtyp::new(type_ctx).tree_of_signature(sig);
    crate::types::printtyp::print_out_signature_doc(&tree).to_string(80)
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

/// The substitution `subst` of OCaml's `Includemod.modtypes`.
#[derive(Clone, Default, Debug)]
pub struct InclusionSubst {
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
#[derive(Clone, Default, Debug)]
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
            return Some(*value);
        }
        if self.any_pos_key {
            return self
                .map
                .iter()
                .find_map(|(key, value)| key.same(path).then_some(*value));
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
        PathView::Pident(_) => *path,
        PathView::Pdot(parent, name, _) => {
            Path::pdot_pos(strip_pos_hints(parent), *name, crate::types::path::NOPOS)
        }
        PathView::Papply(functor, argument) => {
            Path::papply(strip_pos_hints(functor), strip_pos_hints(argument))
        }
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
    let mut current = *path;
    let mut namespace = namespace;
    let mut visiting = HashSet::new();

    loop {
        let PathView::Pident(id) = current.view() else {
            return None;
        };
        if id.is_persistent() || id.stamp() == 0 || !visiting.insert((current, namespace)) {
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
                current = *next;
                namespace = PathNamespace::ModuleType;
            }
            ModuleType::MtyAlias(_, next)
                if !(next.same(&current) && namespace == PathNamespace::Module) =>
            {
                current = **next;
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

/// OCaml `Includemod.modtypes`: check that `mty_impl` is included in
/// `mty_sig` and return the coercion, collecting warnings.
pub fn modtypes_with_warnings(
    type_ctx: &TypeContext,
    env: &Env,
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<ModuleCoercion> {
    let subst = InclusionSubst::default();
    modtypes_inner(type_ctx, env, &subst, mty_impl, mty_sig, None, warnings)
        .map_err(|error| wrap_modtypes_error(type_ctx, &subst, mty_impl, mty_sig, error))
}

/// The error half of OCaml `modtypes` (includemod.ml:187-198): `Dont_match`
/// becomes a `Module_types (mty1, Subst.modtype subst mty2)` entry; other
/// errors from `try_modtypes` get one too unless either side is an alias, in
/// which case the inner comparison already reported it.
fn wrap_modtypes_error(
    type_ctx: &TypeContext,
    subst: &InclusionSubst,
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
    error: IncludeModError,
) -> IncludeModError {
    if !matches!(error, IncludeModError::DontMatch)
        && (matches!(mty_impl, ModuleType::MtyAlias(..))
            || matches!(mty_sig, ModuleType::MtyAlias(..)))
    {
        return error;
    }
    IncludeModError::ModuleTypesMismatch {
        actual: Box::new(mty_impl.clone()),
        expected: Box::new(substitute_module_type_paths(type_ctx, mty_sig, subst)),
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
            if !visiting.insert((*path, namespace)) {
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
            return Ok(*path);
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
                    return Err(IncludeModError::DontMatch);
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
                    .map_err(|error| {
                        wrap_modtypes_error(type_ctx, subst, &expanded, mty_sig, error)
                    })
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
                        .unwrap_or_else(|| {
                            ModuleType::MtyAlias(*pres_impl, std::sync::Arc::new(impl_path))
                        });
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
                .map_err(|error| wrap_modtypes_error(type_ctx, subst, &expanded, mty_sig, error))?
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
            match (param_type_impl.as_deref(), param_type_sig.as_deref()) {
                // `Mty_functor (param1, None, res1), Mty_functor (_param2,
                // None, res2)`: the results under `Body param1 :: cxt`.
                (None, None) => {
                    let result_coercion = modtypes_inner(
                        type_ctx,
                        env,
                        subst,
                        result_impl,
                        result_sig,
                        sig_access_path,
                        warnings,
                    )
                    .map_err(|error| IncludeModError::InFunctorBody {
                        param: *param_impl,
                        error: Box::new(wrap_modtypes_error(
                            type_ctx,
                            subst,
                            result_impl,
                            result_sig,
                            error,
                        )),
                    })?;
                    return Ok(match result_coercion {
                        ModuleCoercion::Tcoerce_none => ModuleCoercion::Tcoerce_none,
                        cc => ModuleCoercion::Tcoerce_functor(
                            Box::new(ModuleCoercion::Tcoerce_none),
                            Box::new(cc),
                        ),
                    });
                }
                (Some(_), Some(_)) => {}
                // `_, _ -> raise Dont_match`.
                _ => return Err(IncludeModError::DontMatch),
            }
            let (Some(pt_impl), Some(pt_sig)) = (param_type_impl, param_type_sig) else {
                unreachable!()
            };
            // OCaml compiler/ml/includemod.ml:257-262 computes
            // `arg2' = Subst.modtype subst arg2` before both the
            // contravariant argument check and `Env.add_module`.
            let expected_param_type = substitute_module_type_paths(type_ctx, pt_sig, subst);

            // `modtypes ~loc env (Arg param1 :: cxt) Subst.identity arg2'
            // arg1`: parameters are contravariant.
            let empty_subst = InclusionSubst::default();
            let param_coercion = modtypes_inner(
                type_ctx,
                env,
                &empty_subst,
                &expected_param_type,
                pt_impl,
                None,
                warnings,
            )
            .map_err(|error| IncludeModError::InFunctorArg {
                param: *param_impl,
                error: Box::new(wrap_modtypes_error(
                    type_ctx,
                    &empty_subst,
                    &expected_param_type,
                    pt_impl,
                    error,
                )),
            })?;

            // `modtypes ~loc (Env.add_module param1 arg2' env) (Body param1
            // :: cxt) (Subst.add_module param2 (Pident param1) subst) res1
            // res2`.
            let mut result_env = env.clone();
            result_env.add_module(
                *param_impl,
                ModuleDeclaration {
                    md_type: expected_param_type,
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
                error: Box::new(wrap_modtypes_error(
                    type_ctx,
                    &result_subst,
                    result_impl,
                    result_sig,
                    error,
                )),
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
                Err(IncludeModError::DontMatch)
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
                    .normalize_path_prefix(type_ctx, path)
                    .same(&env.normalize_path_prefix(type_ctx, &sig_path))
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
                    Err(IncludeModError::DontMatch)
                }
            } else {
                Err(IncludeModError::DontMatch)
            }
        }

        (mty_impl, ModuleType::MtyIdent(path)) => {
            // compiler/ml/includemod.ml:237 and 262-273 substitute the expected
            // module type before testing/expanding its identifier, and restart
            // expansion with Subst.identity.
            let path = substitute_modtype_path(path, subst);
            if let ModuleType::MtyIdent(impl_path) = mty_impl
                && env
                    .normalize_path_prefix(type_ctx, impl_path)
                    .same(&env.normalize_path_prefix(type_ctx, &path))
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
                Err(IncludeModError::DontMatch)
            }
        }

        // Fallback: incompatible module types
        _ => Err(IncludeModError::DontMatch),
    }
}

// ============================================================================
// Signature Inclusion
// ============================================================================

/// Whether a signature item has a runtime representation (and so a slot
/// in the module's block).
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
                .insert(Path::pident(*sig_id), impl_path);
            if let Some(access_path) = sig_access_path {
                subst.type_paths.insert(
                    Path::pdot(*access_path, sig_id.name()),
                    impl_path,
                );
            }
            if let Some(sig_path) = &sig_decl.type_path {
                subst.type_paths.insert(*sig_path, impl_path);
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
                .insert(Path::pident(*sig_id), impl_path);
            if let Some(access_path) = sig_access_path {
                subst.module_paths.insert(
                    Path::pdot(*access_path, sig_id.name()),
                    impl_path,
                );
            }
            if let Some(sig_path) = &sig_decl.md_path {
                subst.module_paths.insert(*sig_path, impl_path);
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
    item: &SignatureItem,
) -> IncludeModError {
    IncludeModError::MissingField {
        id: *id,
        loc,
        kind: field_desc_kind(field_desc),
        item: Box::new(item.clone()),
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
            errors.push(missing_signature_item_error(
                sig_id,
                sig_loc,
                &field_desc,
                sig_item,
            ));
        }
    }
    // includemod.ml `pair_components` raises the missing fields in the
    // order of the expected signature.

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
                )? {
                    warnings.push(warning);
                }
                // includemod.ml:399: `Env.mark_module_used env (Ident.name
                // id1) md1.md_loc`.
                if !env.is_implicit_coercion() {
                    type_ctx
                        .usage()
                        .mark_module_used(impl_id.name_atom(), type_ctx.resolve_loc(impl_mod_decl.md_loc));
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
                    sig_access_path.map(|path| Path::pdot(*path, sig_id.name()));
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
                            type_ctx,
                            subst,
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

/// Drop every value declaration that a later one with the same name
/// shadows (OCaml `Typemod.simplify_signature`).
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

/// The coercion of a compilation unit without an interface to its inferred
/// signature (`Includemod.compunits` with `simplify_signature sg`,
/// compiler/ml/typemod.ml:1766-1768), when it can be given without comparing
/// anything: `None` sends the caller to [`compunit`].
///
/// The inferred signature `simple_sig` is `impl_sig` without its shadowed
/// values, so the full check pairs each of its items with that same item of
/// the unit and every comparison succeeds. What the check leaves behind is
/// the coercion and the items it marked as used. Each paired item is exported
/// as it is (see `includes_itself_plainly`), so the coercion only selects
/// the fields that are not shadowed, as `signatures_with_subst` builds it.
pub fn inferred_signature_coercion(
    type_ctx: &TypeContext,
    env: &Env,
    impl_sig: &Signature,
    simple_sig: &Signature,
) -> Option<ModuleCoercion> {
    if !includes_itself_plainly(simple_sig) {
        return None;
    }
    mark_self_included_items_used(type_ctx, env, simple_sig);
    if simple_sig.len() == impl_sig.len() {
        return Some(ModuleCoercion::Tcoerce_none);
    }

    // `simple_sig` is a subsequence of `impl_sig`: walk both, giving each
    // kept runtime component its position among the unit's.
    let mut kept = simple_sig.iter().peekable();
    let mut coercions = Vec::new();
    let mut id_pos_list = Vec::new();
    let mut runtime_fields = Vec::new();
    let mut runtime_pos = 0usize;
    for item in impl_sig {
        let is_kept = kept.peek().is_some_and(|kept_item| {
            std::mem::discriminant(*kept_item) == std::mem::discriminant(item)
                && match (item_ident(item), item_ident(kept_item)) {
                    (Some(id), Some(kept_id)) => id.same(kept_id),
                    _ => false,
                }
        });
        let runtime = is_runtime_component(item);
        if let SignatureItem::SigModule(id, _, _) = item {
            id_pos_list.push((*id, runtime_pos, ModuleCoercion::Tcoerce_none));
        }
        if is_kept {
            kept.next();
            if runtime {
                coercions.push((runtime_pos, ModuleCoercion::Tcoerce_none));
                runtime_fields.extend(runtime_component_name(item));
            }
        }
        if runtime {
            runtime_pos += 1;
        }
    }
    if kept.next().is_some() {
        // Not the subsequence expected: let the full check decide.
        return None;
    }
    if coercions.len() == runtime_pos {
        // Only externals were shadowed; every field keeps its position.
        return Some(ModuleCoercion::Tcoerce_none);
    }
    Some(ModuleCoercion::Tcoerce_structure(
        coercions,
        id_pos_list,
        runtime_fields,
    ))
}

fn item_ident(item: &SignatureItem) -> Option<&Ident> {
    match item {
        SignatureItem::SigValue(id, _)
        | SignatureItem::SigType(id, _, _)
        | SignatureItem::SigTypext(id, _, _)
        | SignatureItem::SigModule(id, _, _)
        | SignatureItem::SigModtype(id, _) => Some(id),
        SignatureItem::SigClass | SignatureItem::SigClassType => None,
    }
}

/// Whether the inclusion of `sig` in itself pairs every item with itself and
/// coerces none of them: no name is declared twice (a repeated name pairs
/// both declarations with the last one), and nested modules are aliases or
/// structures of the same kind, whose own coercion is then the identity.
/// Functors and named module types are left to the full check, and so are
/// module type declarations that are not plain signatures.
fn includes_itself_plainly(sig: &Signature) -> bool {
    let mut seen: HashSet<(std::mem::Discriminant<SignatureItem>, crate::name::Name)> =
        HashSet::with_capacity(sig.len());
    sig.iter().all(|item| {
        let id = match item {
            SignatureItem::SigValue(id, _) | SignatureItem::SigTypext(id, _, _) => id,
            SignatureItem::SigType(id, _, _) => {
                // A row type is paired with the type it belongs to
                // (`adjusted_item_field_desc`).
                if crate::types::btype::is_row_name(id.name()) {
                    return false;
                }
                id
            }
            SignatureItem::SigModule(id, md, _) => {
                let plain = match &md.md_type {
                    ModuleType::MtySignature(nested) => includes_itself_plainly(nested),
                    ModuleType::MtyAlias(..) => true,
                    ModuleType::MtyIdent(_) | ModuleType::MtyFunctor { .. } => false,
                };
                if !plain {
                    return false;
                }
                id
            }
            SignatureItem::SigModtype(id, decl) => {
                // A module type is checked for equivalence with itself
                // (`modtype_declarations`), which a signature that declares
                // a name twice fails as a permutation.
                let plain = match &decl.mtd_type {
                    None => true,
                    Some(ModuleType::MtySignature(nested)) => includes_itself_plainly(nested),
                    Some(
                        ModuleType::MtyAlias(..)
                        | ModuleType::MtyIdent(_)
                        | ModuleType::MtyFunctor { .. },
                    ) => false,
                };
                if !plain {
                    return false;
                }
                id
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => return false,
        };
        seen.insert((std::mem::discriminant(item), id.name_atom()))
    })
}

/// The usage marks of the inclusion of `sig` in itself, for a signature
/// accepted by [`includes_itself_plainly`]: those of `value_descriptions`,
/// `type_declarations`, `extension_constructors` and the module and module
/// type cases of `check_paired_signature_items`, each with an item as both
/// sides.
fn mark_self_included_items_used(type_ctx: &TypeContext, env: &Env, sig: &Signature) {
    if env.is_implicit_coercion() {
        return;
    }
    // Both sides are one declaration, so the usage is `Positive`
    // (includecore.ml:384-398, 461-466).
    let usage = crate::types::usage::ConstructorUsage::Positive;
    for item in sig {
        match item {
            SignatureItem::SigValue(id, desc) => {
                type_ctx
                    .usage()
                    .mark_value_used(id.name_atom(), type_ctx.resolve_loc(desc.val_loc));
            }
            SignatureItem::SigType(id, decl, _) => {
                let loc = type_ctx.resolve_loc(decl.type_loc);
                let mut usage_tables = type_ctx.usage();
                usage_tables.mark_type_used(id.name_atom(), loc);
                if let crate::types::TypeKind::TypeVariant(cstrs, _) = &decl.type_kind {
                    for cstr in cstrs {
                        usage_tables.mark_constructor_used(
                            usage,
                            id.name(),
                            loc,
                            cstr.cd_id.name(),
                        );
                    }
                }
            }
            SignatureItem::SigTypext(id, ext, _) => {
                type_ctx.usage().mark_constructor_used(
                    usage,
                    ext.ext_type_path.last(),
                    type_ctx.resolve_loc(ext.ext_loc),
                    id.name(),
                );
            }
            SignatureItem::SigModule(id, md, _) => {
                type_ctx
                    .usage()
                    .mark_module_used(id.name_atom(), type_ctx.resolve_loc(md.md_loc));
                if let ModuleType::MtySignature(nested) = &md.md_type {
                    mark_self_included_items_used(type_ctx, env, nested);
                }
            }
            SignatureItem::SigModtype(_, decl) => {
                // Both directions of the equivalence check mark the items
                // of the module type's signature.
                if let Some(ModuleType::MtySignature(nested)) = &decl.mtd_type {
                    mark_self_included_items_used(type_ctx, env, nested);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }
}

/// OCaml `Includemod.compunit`: check that a unit's implementation
/// signature is included in its interface.
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

/// [`compunit`], collecting warnings.
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
        add_sig_item_to_env(type_ctx, sig_item, &mut include_env);
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
                ) => (*impl_args, *impl_ret, *sig_args, *sig_ret),
                _ => return None,
            };
        if impl_args.len() != sig_args.len() {
            return Some((impl_args.len(), sig_args.len()));
        }
        if !type_ctx
            .type_args(impl_args)
            .iter()
            .zip(type_ctx.type_args(sig_args).iter())
            .all(|(impl_arg, sig_arg)| impl_arg.label().same_label(sig_arg.label()))
        {
            return None;
        }
        for (impl_arg, sig_arg) in type_ctx
            .type_args(impl_args)
            .iter()
            .zip(type_ctx.type_args(sig_args).iter())
        {
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
            .mark_value_used(id.name_atom(), type_ctx.resolve_loc(impl_desc.val_loc));
    }
    if let Some(warning) = deprecated_inclusion_warning(
        type_ctx,
        id.name(),
        &impl_desc.val_attributes,
        &sig_desc.val_attributes,
        impl_desc.val_loc,
        sig_desc.val_loc,
    )? {
        warnings.push(warning);
    }

    // A signature that declares an effect (`@pure`, `@mutates`) requires it
    // of the value matched against it; the purity check discharges that
    // after typing, on the binding itself. O(1) for a declaration without
    // attributes.
    if !sig_desc.val_attributes.is_empty()
        && !std::ptr::eq(impl_desc, sig_desc)
        && let Some(declared) =
            crate::verify::purity::declared_of_decl_attributes(&sig_desc.val_attributes)
        && crate::verify::purity::declared_of_decl_attributes(&impl_desc.val_attributes)
            != Some(declared)
    {
        type_ctx.require_effect(crate::verify::purity::Obligation {
            stamp: id.stamp(),
            name: id.name(),
            declared,
            signature_loc: sig_desc.val_loc,
            ty: impl_desc.val_type,
        });
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
            actual: Box::new(impl_desc.clone()),
            expected: Box::new(expected_desc),
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
            actual: Box::new(impl_desc.clone()),
            expected: Box::new(expected_desc.clone()),
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

/// `Env.add_item` (env.ml:1757-1768): a type goes through `store_type`.
pub(crate) fn add_sig_item_to_env(ctx: &TypeContext, item: &SignatureItem, env: &mut Env) {
    match item {
        SignatureItem::SigValue(id, desc) => env.add_value(*id, desc.clone()),
        SignatureItem::SigType(id, decl, _) => env.store_type(ctx, *id, decl.clone()),
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
        let mut seen = super::type_marks::visit_set();
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
    subst.type_paths.insert(*from, *to);
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
    match &path.view() {
        PathView::Pident(_) => *path,
        PathView::Pdot(prefix, name, pos) => {
            Path::pdot_pos(substitute_module_path(prefix, subst), *name, *pos)
        }
        PathView::Papply(functor, arg) => Path::papply(
            substitute_type_constructor_path(functor, subst),
            substitute_module_path(arg, subst),
        ),
    }
}

/// `Subst.module_path s p` (subst.ml:69-75) on a shared path block: an
/// unreplaced `Pident` is `p` itself, so its uses keep sharing one block.
fn substitute_module_path_block(
    path: &std::sync::Arc<Path>,
    subst: &InclusionSubst,
) -> std::sync::Arc<Path> {
    match &path.view() {
        PathView::Pident(_) if subst.module_paths.get(path).is_none() => path.clone(),
        _ => std::sync::Arc::new(substitute_module_path(path, subst)),
    }
}

fn substitute_module_path(path: &Path, subst: &InclusionSubst) -> Path {
    if let Some(replacement) = subst.module_paths.get(path) {
        return replacement;
    }
    match &path.view() {
        PathView::Pident(_) => *path,
        PathView::Pdot(prefix, name, pos) => {
            Path::pdot_pos(substitute_module_path(prefix, subst), *name, *pos)
        }
        PathView::Papply(functor, arg) => Path::papply(
            substitute_module_path(functor, subst),
            substitute_module_path(arg, subst),
        ),
    }
}

fn substitute_modtype_path(path: &Path, subst: &InclusionSubst) -> Path {
    if let Some(replacement) = subst.modtype_paths.get(path) {
        return replacement;
    }
    match &path.view() {
        PathView::Pident(_) => *path,
        PathView::Pdot(prefix, name, pos) => {
            Path::pdot_pos(substitute_module_path(prefix, subst), *name, *pos)
        }
        PathView::Papply(functor, arg) => Path::papply(
            substitute_modtype_path(functor, subst),
            substitute_module_path(arg, subst),
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
            // `Subst.module_path` (subst.ml:69-75): an unreplaced `Pident`
            // target is the block itself.
            ModuleType::MtyAlias(*presence, substitute_module_path_block(path, subst))
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
    seen: &mut super::type_marks::TypeVisitSet,
) {
    let ty = type_ctx.repr(ty);
    if !seen.visit(ty) {
        return;
    }

    let desc = type_ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, args, abbrev } => {
            for arg in type_ctx.type_list(args).iter() {
                rewrite_substituted_type_paths(type_ctx, arg, subst, seen);
            }
            let new_path = substitute_type_constructor_path(path, subst);
            if new_path != *path {
                type_ctx.set_desc(
                    ty,
                    TypeDesc::Tconstr {
                        path: new_path,
                        args: *args,
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
                rewrite_substituted_type_paths(type_ctx, item, subst, seen);
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
                rewrite_substituted_type_paths(type_ctx, var, subst, seen);
            }
        }
        TypeDesc::Tpackage { path, args, lids } => {
            for arg in type_ctx.type_list(args).iter() {
                rewrite_substituted_type_paths(type_ctx, arg, subst, seen);
            }
            let new_path = substitute_modtype_path(path, subst);
            if new_path != *path {
                type_ctx.set_desc(
                    ty,
                    TypeDesc::Tpackage {
                        path: new_path,
                        lids: *lids,
                        args: *args,
                    },
                );
            }
        }
        TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
            rewrite_substituted_type_paths(type_ctx, *target, subst, seen);
        }
        TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {}
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
    let mut seen = super::type_marks::visit_set();
    rewrite_substituted_type_paths(type_ctx, copied, subst, &mut seen);
    copied
}

/// Check if type declaration `impl_decl` is a subtype of `sig_decl`.
/// `Includemod.type_declarations` (includemod.ml): mark the implementation's
/// type used, then compare it with the expected declaration (already
/// substituted by the caller).
pub(crate) fn type_declarations(
    type_ctx: &TypeContext,
    env: &Env,
    id: Ident,
    impl_decl: &TypeDeclaration,
    sig_decl: &TypeDeclaration,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<()> {
    // includemod.ml:66-67: `Env.mark_type_used env (Ident.name id) decl1`.
    crate::types::typecore::mark_type_used(
        type_ctx,
        env,
        id.name_atom(),
        type_ctx.resolve_loc(impl_decl.type_loc),
    );
    let errs = includecore_type_declarations(
        type_ctx,
        env,
        id.name(),
        impl_decl,
        id,
        sig_decl,
        false,
        warnings,
    )?;
    if errs.is_empty() {
        Ok(())
    } else {
        Err(type_decl_mismatch(id, impl_decl, sig_decl, errs))
    }
}

/// `Includecore.type_declarations ?equality ~loc env name decl1 id decl2`
/// (includecore.ml): the differences that keep `decl1` from being included
/// in `decl2`, the first failing check's only. `Err` is a payload reader's
/// error, which escapes the check.
#[allow(clippy::too_many_arguments)]
pub(crate) fn includecore_type_declarations(
    type_ctx: &TypeContext,
    env: &Env,
    name: &str,
    impl_decl: &TypeDeclaration,
    id: Ident,
    sig_decl: &TypeDeclaration,
    equality: bool,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<Vec<TypeMismatch>> {
    if let Some(warning) = deprecated_inclusion_warning(
        type_ctx,
        name,
        &impl_decl.type_attributes,
        &sig_decl.type_attributes,
        impl_decl.type_loc,
        sig_decl.type_loc,
    )? {
        warnings.push(warning);
    }

    if impl_decl.type_arity != sig_decl.type_arity {
        return Ok(vec![TypeMismatch::Arity]);
    }

    if !private_flags(impl_decl, sig_decl) {
        return Ok(vec![TypeMismatch::Privacy]);
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
                return Ok(vec![TypeMismatch::Constraint]);
            }
        }
        (Some(impl_manifest), Some(sig_manifest)) => {
            if !type_manifest_for_inclusion(
                type_ctx,
                env,
                &ParamCorrespondence {
                    impl_params: &impl_decl.type_params,
                    sig_params: &sig_decl.type_params,
                    map: &param_map,
                },
                impl_manifest,
                sig_manifest,
                sig_decl.type_private,
            ) {
                return Ok(vec![TypeMismatch::Manifest]);
            }
        }
        (None, Some(sig_manifest)) => {
            if !type_param_lists_equal_for_inclusion(
                type_ctx,
                env,
                &impl_decl.type_params,
                &sig_decl.type_params,
            ) {
                return Ok(vec![TypeMismatch::Constraint]);
            }
            // `let ty1 = Btype.newgenty (Tconstr (Pident id, decl2.type_params,
            // ref Mnil))` and `Ctype.equal env false [ty1] [ty2]`.
            let ty1 = type_ctx.new_generic_constr(Path::pident(id), sig_decl.type_params.clone());
            if !crate::types::ctype::equal(type_ctx, env, false, &[ty1], &[sig_manifest]) {
                return Ok(vec![TypeMismatch::Manifest]);
            }
        }
    }

    // includecore.ml: `compare_runtime_annotations env id decl1 decl2` once
    // the manifests agree.
    if let Some(err) = compare_runtime_annotations(type_ctx, env, id, impl_decl, sig_decl) {
        return Ok(vec![err]);
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
        return Ok(vec![TypeMismatch::UnboxedRepresentation(
            canonical_unboxed(sig_decl),
        )]);
    }

    if type_decl_tag_name(type_ctx, impl_decl) != type_decl_tag_name(type_ctx, sig_decl) {
        return Ok(vec![TypeMismatch::TagName]);
    }

    let err = match (&impl_decl.type_kind, &sig_decl.type_kind) {
        (_, TypeKind::TypeAbstract) => Vec::new(),
        (
            TypeKind::TypeVariant(impl_constructors, _),
            TypeKind::TypeVariant(sig_constructors, _),
        ) => {
            // includecore.ml: `mark cstrs1 usage name decl1; if equality then
            // mark cstrs2 Env.Positive (Ident.name id) decl2`.
            if !env.is_implicit_coercion() {
                let usage = if impl_decl.type_private == crate::types::PrivateFlag::Private
                    || sig_decl.type_private == crate::types::PrivateFlag::Public
                {
                    crate::types::usage::ConstructorUsage::Positive
                } else {
                    crate::types::usage::ConstructorUsage::Privatize
                };
                let mut usage_tables = type_ctx.usage();
                for cstr in impl_constructors {
                    usage_tables.mark_constructor_used(
                        usage,
                        name,
                        type_ctx.resolve_loc(impl_decl.type_loc),
                        cstr.cd_id.name(),
                    );
                }
                if equality {
                    for cstr in sig_constructors {
                        usage_tables.mark_constructor_used(
                            crate::types::usage::ConstructorUsage::Positive,
                            id.name(),
                            type_ctx.resolve_loc(sig_decl.type_loc),
                            cstr.cd_id.name(),
                        );
                    }
                }
            }
            compare_variant_declarations(
                type_ctx,
                env,
                &impl_decl.type_params,
                &sig_decl.type_params,
                (
                    impl_constructors,
                    type_ctx.variant_layout(
                        impl_decl
                            .variant_layout_ref()
                            .expect("variant declaration layout"),
                    ),
                ),
                (
                    sig_constructors,
                    type_ctx.variant_layout(
                        sig_decl
                            .variant_layout_ref()
                            .expect("variant declaration layout"),
                    ),
                ),
                warnings,
            )?
        }
        (
            TypeKind::TypeRecord(impl_labels, impl_rep),
            TypeKind::TypeRecord(sig_labels, sig_rep),
        ) => {
            let err = compare_record_declarations(
                type_ctx,
                env,
                &impl_decl.type_params,
                &sig_decl.type_params,
                impl_labels,
                sig_labels,
            );
            if !err.is_empty() || impl_rep == sig_rep {
                err
            } else {
                vec![TypeMismatch::RecordRepresentation]
            }
        }
        (TypeKind::TypeOpen, TypeKind::TypeOpen) => Vec::new(),
        _ => vec![TypeMismatch::Kind],
    };
    if !err.is_empty() {
        return Ok(err);
    }

    let abstr =
        matches!(sig_decl.type_kind, TypeKind::TypeAbstract) && sig_decl.type_manifest.is_none();
    // If attempt to assign a non-immediate type (e.g. string) to a type that
    // must be immediate, then we error.
    if abstr && !impl_decl.type_immediate && sig_decl.type_immediate {
        return Ok(vec![TypeMismatch::Immediate]);
    }

    let need_variance = abstr
        || matches!(impl_decl.type_private, crate::types::PrivateFlag::Private)
        || matches!(impl_decl.type_kind, TypeKind::TypeOpen);
    if !need_variance {
        return Ok(Vec::new());
    }
    let abstr = abstr || matches!(sig_decl.type_private, crate::types::PrivateFlag::Private);
    let opn = matches!(sig_decl.type_kind, TypeKind::TypeOpen) && sig_decl.type_manifest.is_none();
    let variance_ok = sig_decl
        .type_params
        .iter()
        .zip(
            impl_decl
                .type_variance
                .iter()
                .zip(sig_decl.type_variance.iter()),
        )
        .all(|(sig_param, (impl_var, sig_var))| {
            let imp = |lhs: bool, rhs: bool| !lhs || rhs;
            let constrained = !crate::types::btype::is_tvar(type_ctx, *sig_param);
            let (co1, cn1) = impl_var.get_upper();
            let (co2, cn2) = sig_var.get_upper();
            let upper_ok = if abstr {
                imp(co1, co2) && imp(cn1, cn2)
            } else if opn || constrained {
                co1 == co2 && cn1 == cn2
            } else {
                true
            };
            let (p1, n1, i1, j1) = impl_var.get_lower();
            let (p2, n2, i2, j2) = sig_var.get_lower();
            upper_ok
                && imp(
                    abstr,
                    imp(p2, p1) && imp(n2, n1) && imp(i2, i1) && imp(j2, j1),
                )
        });
    Ok(if variance_ok {
        Vec::new()
    } else {
        vec![TypeMismatch::Variance]
    })
}

/// `'a aligned` (includecore.ml): the entries of two declarations of a
/// record or a variant, lined up by name.
enum Aligned<'a, T> {
    /// An entry in both, with its position in each.
    Both(&'a T, usize, &'a T, usize),
    Renamed(&'a T, &'a T),
    OnlyFirst(&'a T),
    OnlySecond(&'a T),
}

/// The entries both declarations name, in the order of the second, when
/// the first has them in another order.
type AlignedOrder = Option<Vec<String>>;

/// `align name l1 l2` (includecore.ml): declarations that agree on their
/// names, as most do, need no tables.
fn align<'a, T>(
    name: fn(&T) -> &str,
    l1: &'a [T],
    l2: &'a [T],
) -> (Vec<Aligned<'a, T>>, AlignedOrder) {
    if l1.len() == l2.len() && l1.iter().zip(l2).all(|(x1, x2)| name(x1) == name(x2)) {
        let aligned = l1
            .iter()
            .zip(l2)
            .enumerate()
            .map(|(i, (x1, x2))| Aligned::Both(x1, i, x2, i))
            .collect();
        return (aligned, None);
    }
    align_by_name(name, l1, l2)
}

/// `align_by_name name l1 l2` (includecore.ml): the entries of the second
/// declaration in its order, then those only the first has, and the common
/// names in the second's order when the first has them in another. The
/// entries the other declaration lacks fall into gaps, each after an entry
/// both have, or at the start; a gap that holds as many in each declaration
/// holds renamings, paired in order.
fn align_by_name<'a, T>(
    name: fn(&T) -> &str,
    l1: &'a [T],
    l2: &'a [T],
) -> (Vec<Aligned<'a, T>>, AlignedOrder) {
    let positions = |l: &'a [T]| -> HashMap<&'a str, usize> {
        l.iter().enumerate().map(|(i, x)| (name(x), i)).collect()
    };
    let pos1 = positions(l1);
    let pos2 = positions(l2);
    let gaps = |l: &'a [T], other: &HashMap<&'a str, usize>| {
        let mut table: HashMap<Option<&'a str>, Vec<&'a T>> = HashMap::default();
        let mut gap = None;
        for x in l {
            if other.contains_key(name(x)) {
                gap = Some(name(x));
            } else {
                table.entry(gap).or_default().push(x);
            }
        }
        table
    };
    let gaps1 = gaps(l1, &pos2);
    let mut renamings: HashMap<&'a str, &'a T> = HashMap::default();
    let mut renamed: HashSet<&'a str> = HashSet::default();
    for (gap, xs2) in gaps(l2, &pos1) {
        if let Some(xs1) = gaps1.get(&gap)
            && xs1.len() == xs2.len()
        {
            for (x1, x2) in xs1.iter().zip(&xs2) {
                renamings.insert(name(x2), x1);
                renamed.insert(name(x1));
            }
        }
    }
    let mut aligned: Vec<Aligned<'a, T>> = l2
        .iter()
        .enumerate()
        .map(|(i, x2)| match pos1.get(name(x2)) {
            Some(&i1) => Aligned::Both(&l1[i1], i1, x2, i),
            None => match renamings.get(name(x2)) {
                Some(&x1) => Aligned::Renamed(x1, x2),
                None => Aligned::OnlySecond(x2),
            },
        })
        .collect();
    aligned.extend(
        l1.iter()
            .filter(|x1| !pos2.contains_key(name(x1)) && !renamed.contains(name(x1)))
            .map(Aligned::OnlyFirst),
    );
    let common = |l: &'a [T], other: &HashMap<&'a str, usize>| -> Vec<&'a str> {
        l.iter()
            .map(name)
            .filter(|n| other.contains_key(n))
            .collect()
    };
    let order2 = common(l2, &pos1);
    let order = if common(l1, &pos2) == order2 {
        None
    } else {
        Some(order2.into_iter().map(str::to_string).collect())
    };
    (aligned, order)
}

/// `compare_records env params1 params2 labels1 labels2` (includecore.ml):
/// every difference of the fields, lined up by name.
fn compare_record_declarations(
    type_ctx: &TypeContext,
    env: &Env,
    params1: &[TypeExprRef],
    params2: &[TypeExprRef],
    labels1: &[LabelDeclaration],
    labels2: &[LabelDeclaration],
) -> Vec<TypeMismatch> {
    fn name(ld: &LabelDeclaration) -> &str {
        ld.ld_id.name()
    }
    let (aligned, order) = align(name, labels1, labels2);
    let pairs: Vec<(&LabelDeclaration, &LabelDeclaration)> = aligned
        .iter()
        .filter_map(|entry| match entry {
            Aligned::Both(ld1, _, ld2, _) => Some((*ld1, *ld2)),
            Aligned::Renamed(..) | Aligned::OnlyFirst(_) | Aligned::OnlySecond(_) => None,
        })
        .collect();
    // The fields whose types differ. All the types are compared at once
    // first; when that fails, each field with the fields before it that
    // agree, as they are added to the parameters, cf. PR#7378.
    let type_mismatches: Vec<Ident> = {
        let mut all1 = params1.to_vec();
        all1.extend(pairs.iter().map(|(ld1, _)| ld1.ld_type));
        let mut all2 = params2.to_vec();
        all2.extend(pairs.iter().map(|(_, ld2)| ld2.ld_type));
        if crate::types::ctype::equal(type_ctx, env, true, &all1, &all2) {
            Vec::new()
        } else {
            let mut prior1 = params1.to_vec();
            let mut prior2 = params2.to_vec();
            let mut mismatches = Vec::new();
            for (ld1, ld2) in &pairs {
                let mut next1 = Vec::with_capacity(prior1.len() + 1);
                next1.push(ld1.ld_type);
                next1.extend_from_slice(&prior1);
                let mut next2 = Vec::with_capacity(prior2.len() + 1);
                next2.push(ld2.ld_type);
                next2.extend_from_slice(&prior2);
                if crate::types::ctype::equal(type_ctx, env, true, &next1, &next2) {
                    prior1 = next1;
                    prior2 = next2;
                } else {
                    mismatches.push(ld1.ld_id);
                }
            }
            mismatches
        }
    };
    let compare_fields = |ld1: &LabelDeclaration, ld2: &LabelDeclaration| {
        let mut errs = Vec::new();
        if ld1.ld_mutable != ld2.ld_mutable {
            errs.push(TypeMismatch::FieldMutable(ld1.ld_id));
        }
        if ld1.ld_optional != ld2.ld_optional {
            errs.push(TypeMismatch::FieldOptional(ld1.ld_id));
        }
        let name1 = ld1.declaration_name();
        let name2 = ld2.declaration_name();
        if name1 != name2 {
            errs.push(TypeMismatch::FieldRuntimeName(
                ld1.ld_id,
                name1.to_string(),
                name2.to_string(),
            ));
        }
        // The type of an optional field is an option, which `FieldOptional`
        // already reports.
        if ld1.ld_optional == ld2.ld_optional
            && type_mismatches.iter().any(|id| id.same(&ld1.ld_id))
        {
            errs.push(TypeMismatch::FieldType(ld1.ld_id));
        }
        errs
    };
    let mut errs = Vec::new();
    for entry in &aligned {
        match entry {
            Aligned::Both(ld1, _, ld2, _) => errs.extend(compare_fields(ld1, ld2)),
            Aligned::Renamed(ld1, ld2) => errs.push(TypeMismatch::FieldRenamed(
                name(ld1).to_string(),
                name(ld2).to_string(),
            )),
            Aligned::OnlyFirst(ld1) => errs.push(TypeMismatch::FieldMissing(false, ld1.ld_id)),
            Aligned::OnlySecond(ld2) => errs.push(TypeMismatch::FieldMissing(true, ld2.ld_id)),
        }
    }
    if let Some(names) = order {
        errs.push(TypeMismatch::FieldOrder(names));
    }
    errs
}

/// `compare_constructor_arguments env cstr params1 params2 arg1 arg2`
/// (includecore.ml).
fn compare_constructor_arguments(
    type_ctx: &TypeContext,
    env: &Env,
    cstr: Ident,
    params1: &[TypeExprRef],
    params2: &[TypeExprRef],
    arg1: &ConstructorArguments,
    arg2: &ConstructorArguments,
) -> Vec<TypeMismatch> {
    match (arg1, arg2) {
        (ConstructorArguments::CstrTuple(arg1), ConstructorArguments::CstrTuple(arg2)) => {
            if arg1.len() != arg2.len() {
                return vec![TypeMismatch::ConstructorArity(cstr)];
            }
            // Ctype.equal must be called on all arguments at once, cf.
            // PR#7378.
            let mut all1 = params1.to_vec();
            all1.extend_from_slice(arg1);
            let mut all2 = params2.to_vec();
            all2.extend_from_slice(arg2);
            if crate::types::ctype::equal(type_ctx, env, true, &all1, &all2) {
                Vec::new()
            } else {
                vec![TypeMismatch::ConstructorType(cstr)]
            }
        }
        (ConstructorArguments::CstrRecord(l1), ConstructorArguments::CstrRecord(l2)) => {
            let errs = compare_record_declarations(type_ctx, env, params1, params2, l1, l2);
            if errs.is_empty() {
                errs
            } else {
                vec![TypeMismatch::ConstructorRecord(cstr, errs)]
            }
        }
        _ => vec![TypeMismatch::ConstructorType(cstr)],
    }
}

/// A variant declaration's constructors and runtime layout.
type VariantShape<'a> = (&'a [ConstructorDeclaration], crate::types::VariantLayout);

/// `compare_variants ~loc env params1 params2 ~layout1 ~layout2 cstrs1
/// cstrs2` (includecore.ml): every difference of the constructors, lined up
/// by name, each compared at its own position in each layout.
fn compare_variant_declarations(
    type_ctx: &TypeContext,
    env: &Env,
    params1: &[TypeExprRef],
    params2: &[TypeExprRef],
    (cstrs1, layout1): VariantShape<'_>,
    (cstrs2, layout2): VariantShape<'_>,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<Vec<TypeMismatch>> {
    fn name(cd: &ConstructorDeclaration) -> &str {
        cd.cd_id.name()
    }
    let (aligned, order) = align(name, cstrs1, cstrs2);
    let mut errs = Vec::new();
    for entry in aligned {
        match entry {
            Aligned::Both(cd1, i1, cd2, i2) => errs.extend(compare_constructors(
                type_ctx, env, params1, params2, &layout1, &layout2, cd1, i1, cd2, i2, warnings,
            )?),
            Aligned::Renamed(cd1, cd2) => errs.push(TypeMismatch::ConstructorRenamed(
                name(cd1).to_string(),
                name(cd2).to_string(),
            )),
            Aligned::OnlyFirst(cd1) => {
                errs.push(TypeMismatch::ConstructorMissing(false, cd1.cd_id))
            }
            Aligned::OnlySecond(cd2) => {
                errs.push(TypeMismatch::ConstructorMissing(true, cd2.cd_id))
            }
        }
    }
    if let Some(names) = order {
        errs.push(TypeMismatch::ConstructorOrder(names));
    }
    Ok(errs)
}

/// `compare_constructors ~loc env params1 params2 ~layout1 ~layout2 cd1 i1
/// cd2 i2` (includecore.ml): `i1` and `i2` are the positions of the
/// constructors in their layouts.
#[allow(clippy::too_many_arguments)]
fn compare_constructors(
    type_ctx: &TypeContext,
    env: &Env,
    params1: &[TypeExprRef],
    params2: &[TypeExprRef],
    layout1: &crate::types::VariantLayout,
    layout2: &crate::types::VariantLayout,
    cd1: &ConstructorDeclaration,
    i1: usize,
    cd2: &ConstructorDeclaration,
    i2: usize,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<Vec<TypeMismatch>> {
    if let Some(warning) = deprecated_inclusion_warning(
        type_ctx,
        cd1.cd_id.name(),
        &cd1.cd_attributes,
        &cd2.cd_attributes,
        cd1.cd_loc,
        cd2.cd_loc,
    )? {
        warnings.push(warning);
    }
    let r = match (cd1.cd_res, cd2.cd_res) {
        (Some(r1), Some(r2)) => {
            if crate::types::ctype::equal(type_ctx, env, true, &[r1], &[r2]) {
                compare_constructor_arguments(
                    type_ctx,
                    env,
                    cd1.cd_id,
                    &[r1],
                    &[r2],
                    &cd1.cd_args,
                    &cd2.cd_args,
                )
            } else {
                vec![TypeMismatch::ConstructorType(cd1.cd_id)]
            }
        }
        (Some(_), None) | (None, Some(_)) => vec![TypeMismatch::ConstructorType(cd1.cd_id)],
        (None, None) => compare_constructor_arguments(
            type_ctx,
            env,
            cd1.cd_id,
            params1,
            params2,
            &cd1.cd_args,
            &cd2.cd_args,
        ),
    };
    if !r.is_empty() {
        return Ok(r);
    }
    if constructor_is_nullary(cd1) {
        return Ok(
            if layout1.constructor_tag(i1) != layout2.constructor_tag(i2) {
                vec![TypeMismatch::VariantRepresentation(cd1.cd_id)]
            } else {
                Vec::new()
            },
        );
    }
    // A tagged case with a payload carries its tag in the object; an
    // untagged one is its payload, whatever its `@as`, and is compared by
    // its payload kind.
    use crate::types::{VariantBlock, VariantBlockType, VariantConstructorCase};
    Ok(
        match (&layout1.constructors[i1], &layout2.constructors[i2]) {
            (
                VariantConstructorCase::Block(VariantBlock::Tagged(block1)),
                VariantConstructorCase::Block(VariantBlock::Tagged(block2)),
            ) if block1.tag.literal != block2.tag.literal => {
                vec![TypeMismatch::VariantRepresentation(cd1.cd_id)]
            }
            // An unknown payload in the second declaration is the only payload
            // case and has no check, so any first one agrees.
            (
                VariantConstructorCase::Block(VariantBlock::Untagged {
                    block_type: block_type1,
                    ..
                }),
                VariantConstructorCase::Block(VariantBlock::Untagged {
                    block_type: block_type2,
                    ..
                }),
            ) if block_type1 != block_type2 && *block_type2 != VariantBlockType::Unknown => {
                vec![TypeMismatch::VariantRepresentation(cd1.cd_id)]
            }
            _ => Vec::new(),
        },
    )
}

/// includecore.ml `compare_runtime_annotations`: what the second
/// declaration states about its values at run time must hold for the first.
/// Values are recognized by the class or `typeof` the second states, so the
/// first must state the same; stating nothing hides it. `@notUndefined` lets
/// clients unbox `option` of the type, so the first must be a type that
/// cannot hold `undefined` either, or one whose representation the compiler
/// does not see.
fn compare_runtime_annotations(
    type_ctx: &TypeContext,
    env: &Env,
    id: Ident,
    impl_decl: &TypeDeclaration,
    sig_decl: &TypeDeclaration,
) -> Option<TypeMismatch> {
    // The second declaration's shape was resolved in its own environment, so
    // it is what users of the second declaration see.
    let first_type = |env: &mut Env| {
        // `Env.add_type ~check:false id decl1 env` and
        // `Btype.newgenty (Tconstr (Pident id, decl1.type_params, ref Mnil))`.
        env.store_type(type_ctx, id, impl_decl.clone());
        type_ctx.new_generic_constr(Path::pident(id), impl_decl.type_params.clone())
    };
    match &sig_decl.type_shape {
        crate::types::ValueShape::Unstated => None,
        crate::types::ValueShape::NeverUndefined => {
            let mut env = env.clone();
            let ty = first_type(&mut env);
            match crate::raw_lambda::typeopt::undefinedness(type_ctx, &env, ty) {
                crate::raw_lambda::typeopt::Undefinedness::CannotBeUndefined
                | crate::raw_lambda::typeopt::Undefinedness::Unseen => None,
                crate::raw_lambda::typeopt::Undefinedness::StandsForAnother
                | crate::raw_lambda::typeopt::Undefinedness::CanBeUndefined => {
                    Some(TypeMismatch::NotUndefined)
                }
            }
        }
        crate::types::ValueShape::RecognizedAs(shape2) => {
            let declared2 = Some(&shape2.block_type);
            // What the first declaration states, or what its structure gives.
            let mut env = env.clone();
            let ty = first_type(&mut env);
            let declared1 = crate::types::variant_layout::payload_kind(type_ctx, &env, ty);
            if declared1.as_ref() == declared2 {
                None
            } else {
                Some(TypeMismatch::RuntimeAnnotation(
                    crate::types::variant_layout::describe_declared_values(declared1.as_ref()),
                    crate::types::variant_layout::describe_declared_values(declared2),
                ))
            }
        }
    }
}

fn type_decl_mismatch(
    name: Ident,
    actual: &TypeDeclaration,
    expected: &TypeDeclaration,
    errs: Vec<TypeMismatch>,
) -> IncludeModError {
    IncludeModError::TypeDeclarationMismatch {
        name,
        actual: Box::new(actual.clone()),
        expected: Box::new(expected.clone()),
        errs,
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
        TypeDesc::Tvar(..) | TypeDesc::Tconstr { .. } | TypeDesc::Tnil
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

/// How the parameters of an implementation declaration correspond to those
/// of the signature declaration it is checked against.
#[derive(Clone, Copy)]
struct ParamCorrespondence<'a> {
    impl_params: &'a [TypeExprRef],
    sig_params: &'a [TypeExprRef],
    /// Each implementation parameter's signature counterpart.
    map: &'a HashMap<TypeExprRef, TypeExprRef>,
}

fn fixed_private_variant_manifest_for_inclusion(
    type_ctx: &TypeContext,
    env: &Env,
    params: &ParamCorrespondence<'_>,
    impl_manifest: TypeExprRef,
    impl_row: &RowDesc,
    sig_row: &RowDesc,
) -> bool {
    let ParamCorrespondence {
        impl_params,
        sig_params,
        map: param_map,
    } = *params;
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
    params: &ParamCorrespondence<'_>,
    impl_manifest: TypeExprRef,
    impl_fields: TypeExprRef,
    sig_fields: TypeExprRef,
) -> bool {
    let ParamCorrespondence {
        impl_params,
        sig_params,
        map: param_map,
    } = *params;
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
            TypeDesc::Tnil | TypeDesc::Tvar(..) | TypeDesc::Tconstr { .. }
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
    params: &ParamCorrespondence<'_>,
    impl_manifest: TypeExprRef,
    sig_manifest: TypeExprRef,
    sig_private: crate::types::PrivateFlag,
) -> bool {
    let param_map = params.map;
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
                params,
                impl_manifest,
                &type_ctx.row_desc(impl_row),
                &type_ctx.row_desc(sig_row),
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
                params,
                impl_manifest,
                *impl_fields,
                *sig_fields,
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
        return type_ctx
            .type_list(impl_args)
            .iter()
            .zip(type_ctx.type_list(sig_args).iter())
            .all(|(impl_arg, sig_arg)| {
                type_exprs_equal_for_inclusion_inner(
                    type_ctx, env, param_map, impl_arg, sig_arg, seen,
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
        | (TypeDesc::Tunivar(impl_name), TypeDesc::Tunivar(sig_name)) => {
            impl_name == sig_name
        }
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
                && type_ctx
                    .type_list(impl_items)
                    .iter()
                    .zip(type_ctx.type_list(sig_items).iter())
                    .all(|(impl_item, sig_item)| {
                        type_exprs_equal_for_inclusion_inner(
                            type_ctx, env, param_map, impl_item, sig_item, seen,
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
                && type_ctx
                    .type_list(impl_args)
                    .iter()
                    .zip(type_ctx.type_list(sig_args).iter())
                    .all(|(impl_arg, sig_arg)| {
                        type_exprs_equal_for_inclusion_inner(
                            type_ctx, env, param_map, impl_arg, sig_arg, seen,
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
                    ModuleType::MtyIdent(*sig_path),
                    impl_lids,
                    sig_lids,
                );
                let impl_complete = crate::types::ctype::package_type_lists_have_ocaml_same_label_completion_side_effect(
                    type_ctx,
                    Some(env),
                    ModuleType::MtyIdent(*impl_path),
                    sig_lids,
                    impl_lids,
                );
                sig_complete && impl_complete
            });
            labels_complete
                && impl_path.same(sig_path)
                && impl_args.len() == sig_args.len()
                && type_ctx
                    .type_list(impl_args)
                    .iter()
                    .zip(type_ctx.type_list(sig_args).iter())
                    .all(|(impl_arg, sig_arg)| {
                        type_exprs_equal_for_inclusion_inner(
                            type_ctx, env, param_map, impl_arg, sig_arg, seen,
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
                flattened.push((*name, type_ctx.mutability_repr(*mutability), *typ));
                let next = type_ctx.repr(*rest);
                current = next;
            }
            _ => {
                break;
            }
        }
    }
    flattened.sort_by_key(|left| left.0);
    (flattened, current)
}

type ObjectFieldForInclusion = (crate::name::Name, FieldKind, TypeExprRef);

/// A field present on both sides: its name, then the implementation's and
/// the signature's kind and type.
type PairedObjectField = (
    crate::name::Name,
    FieldKind,
    TypeExprRef,
    FieldKind,
    TypeExprRef,
);

fn associate_object_fields_for_inclusion(
    impl_fields: Vec<ObjectFieldForInclusion>,
    sig_fields: Vec<ObjectFieldForInclusion>,
) -> (
    Vec<PairedObjectField>,
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
                pairs.push((*impl_name, *impl_kind, *impl_ty, *sig_kind, *sig_ty));
                impl_index += 1;
                sig_index += 1;
            }
            std::cmp::Ordering::Less => {
                impl_only.push(impl_fields[impl_index]);
                impl_index += 1;
            }
            std::cmp::Ordering::Greater => {
                sig_only.push(sig_fields[sig_index]);
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
        actual: Box::new(impl_ext.clone()),
        expected: Box::new(sig_ext.clone()),
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

    // `compare_constructor_arguments env (Ident.create "")
    // ext1.ext_type_params ext2.ext_type_params ext1.ext_args ext2.ext_args
    // = []` (includecore.ml `extension_constructors`).
    let constructor_id = type_ctx.create_ident("");
    if !compare_constructor_arguments(
        type_ctx,
        env,
        constructor_id,
        &impl_ext.ext_type_params,
        &sig_ext.ext_type_params,
        &impl_ext.ext_args,
        &sig_ext.ext_args,
    )
    .is_empty()
    {
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


/// `modtype_infos ~loc env cxt subst id info1 info2` (includemod.ml), with
/// `sig_decl` already `Subst.modtype_declaration subst info2`: the module
/// types must be equivalent, checked under `Modtype id`.
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
    )? {
        warnings.push(warning);
    }

    let equivalence = match (&impl_decl.mtd_type, &sig_decl.mtd_type) {
        (_, None) => Ok(()),
        (Some(impl_mty), Some(sig_mty)) => {
            check_modtype_equiv(type_ctx, env, impl_mty, sig_mty, warnings)
        }
        // `check_modtype_equiv ~loc env cxt' (Mty_ident (Pident id)) mty2`.
        (None, Some(sig_mty)) => check_modtype_equiv(
            type_ctx,
            env,
            &ModuleType::MtyIdent(Path::pident(id)),
            sig_mty,
            warnings,
        ),
    };
    equivalence.map_err(|error| IncludeModError::ModuleTypeDeclarationMismatch {
        name: id,
        actual: Box::new(impl_decl.clone()),
        expected: Box::new(sig_decl.clone()),
        error: Box::new(IncludeModError::AtModtype {
            name: id,
            error: Box::new(error),
        }),
    })
}

/// `check_modtype_equiv ~loc env cxt mty1 mty2` (includemod.ml): each module
/// type includes the other, without coercion. The reference's build
/// evaluates the pair of `modtypes` left to right: an error of the forward
/// check is the one reported, and the reverse check runs under `Reverse`.
fn check_modtype_equiv(
    type_ctx: &TypeContext,
    env: &Env,
    mty1: &ModuleType,
    mty2: &ModuleType,
    warnings: &mut Vec<Warning>,
) -> IncludeModResult<()> {
    let c1 = modtypes_with_warnings(type_ctx, env, mty1, mty2, warnings)?;
    let c2 = modtypes_with_warnings(type_ctx, env, mty2, mty1, warnings).map_err(|error| {
        IncludeModError::Reversed {
            error: Box::new(error),
        }
    })?;
    match (c1, c2) {
        (ModuleCoercion::Tcoerce_none, ModuleCoercion::Tcoerce_none) => Ok(()),
        _ => Err(IncludeModError::ModtypePermutation),
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
            type_shape: crate::types::ValueShape::Unstated,
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

    fn structure_module(items: Signature) -> ModuleDeclaration {
        ModuleDeclaration {
            md_type: ModuleType::MtySignature(std::sync::Arc::new(items)),
            md_attributes: vec![],
            md_loc: crate::types::DeclLoc::none(),
            md_path: None,
        }
    }

    /// The fast path and the full check on a unit and its inferred signature.
    fn inferred_coercions(
        type_ctx: &TypeContext,
        env: &Env,
        unit: &Signature,
    ) -> (Option<String>, String) {
        let simple = simplify_signature(unit);
        let fast = inferred_signature_coercion(type_ctx, env, unit, &simple)
            .map(|coercion| format!("{coercion:?}"));
        let full = compunit(type_ctx, env, "Unit.res", unit, "(inferred signature)", &simple)
            .expect("a unit includes its inferred signature");
        (fast, format!("{full:?}"))
    }

    #[test]
    fn inferred_signature_coercion_matches_the_full_check() {
        let type_ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let env = initial_env(&type_ctx);
        let value = |name: &str| {
            SignatureItem::SigValue(Ident::create_local(name), value_desc(type_ctx.new_var(None)))
        };
        let ty = |name: &str| {
            SignatureItem::SigType(
                Ident::create_local(name),
                std::sync::Arc::new(abstract_type_decl(None)),
                RecStatus::TrecNot,
            )
        };
        let module = |name: &str, items: Signature| {
            SignatureItem::SigModule(
                Ident::create_local(name),
                structure_module(items),
                RecStatus::TrecNot,
            )
        };

        // Nothing shadowed: the identity.
        let plain: Signature = vec![
            value("a"),
            ty("t"),
            module("M", vec![value("x"), value("y")]),
            value("b"),
        ];
        let (fast, full) = inferred_coercions(&type_ctx, &env, &plain);
        assert_eq!(fast.as_deref(), Some(full.as_str()));
        assert_eq!(full, "Tcoerce_none");

        // A shadowed value: the fields that remain, at their positions in
        // the unit.
        let shadowed: Signature = vec![
            value("a"),
            value("make"),
            ty("t"),
            module("M", vec![value("x")]),
            value("make"),
            value("b"),
        ];
        let (fast, full) = inferred_coercions(&type_ctx, &env, &shadowed);
        assert_eq!(fast.as_deref(), Some(full.as_str()));
        assert!(full.starts_with("Tcoerce_structure"));

        // Left to the full check: a module declared twice, and a nested
        // structure that declares a value twice.
        let twice: Signature = vec![module("M", vec![]), module("M", vec![])];
        assert!(inferred_coercions(&type_ctx, &env, &twice).0.is_none());
        let nested: Signature = vec![module("M", vec![value("x"), value("x")])];
        assert!(inferred_coercions(&type_ctx, &env, &nested).0.is_none());
    }

    #[test]
    fn inferred_signature_coercion_marks_what_the_full_check_marks() {
        // One unit, checked either way; returns which declarations were
        // marked as used: a value, a value of a nested module, and a value
        // of a module type.
        let marked = |fast: bool| {
            let type_ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
            let env = initial_env(&type_ctx);
            let mut next_offset = 0;
            let mut tracked_value = |name: &str| {
                next_offset += 10;
                let loc = Location::new(crate::intern::StrIdx(1), next_offset, next_offset + 5);
                let id = Ident::create_local(name);
                let mut desc = value_desc(type_ctx.new_var(None));
                desc.val_loc = type_ctx.intern_loc(loc);
                let cell = type_ctx
                    .usage()
                    .check_value_usage(id.name_atom(), type_ctx.resolve_loc(desc.val_loc))
                    .expect("a new declaration");
                (SignatureItem::SigValue(id, desc), cell)
            };
            let (top, top_cell) = tracked_value("top");
            let (inner, inner_cell) = tracked_value("inner");
            let (in_modtype, in_modtype_cell) = tracked_value("inModtype");
            let unit: Signature = vec![
                top,
                SignatureItem::SigModule(
                    Ident::create_local("M"),
                    structure_module(vec![inner]),
                    RecStatus::TrecNot,
                ),
                SignatureItem::SigModtype(
                    Ident::create_local("S"),
                    ModtypeDeclaration {
                        mtd_type: Some(ModuleType::MtySignature(std::sync::Arc::new(vec![
                            in_modtype,
                        ]))),
                        mtd_attributes: vec![],
                        mtd_loc: crate::types::DeclLoc::none(),
                    },
                ),
            ];
            let simple = simplify_signature(&unit);
            if fast {
                assert!(inferred_signature_coercion(&type_ctx, &env, &unit, &simple).is_some());
            } else {
                compunit(&type_ctx, &env, "Unit.res", &unit, "(inferred signature)", &simple)
                    .expect("a unit includes its inferred signature");
            }
            let usage = type_ctx.usage();
            [top_cell, inner_cell, in_modtype_cell].map(|cell| usage.is_used(cell))
        };
        assert_eq!(marked(true), marked(false));
        assert_eq!(marked(true), [true, true, true]);
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
                    type_shape: crate::types::ValueShape::Unstated,
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

    /// The position line of `report_error` (includemod.ml `context`),
    /// printed at column 2 as in a report, before a symptom.
    fn include_context_text(cxt: &[IncludePos]) -> String {
        let mut buf = Vec::new();
        {
            let mut ppf = crate::parser::formatter::Formatter::new(&mut buf);
            ppf.string_as(2, "");
            ppf.open_vbox(0);
            pp_include_context(&mut ppf, cxt);
            pp_text(&mut ppf, "Illegal permutation of structure fields");
            ppf.close_box();
            ppf.flush();
        }
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn include_context_names_module_paths_in_words() {
        // The positions of upstream acdf563eef: a module path, a module
        // type, a functor's result or parameter at the end of one, and any
        // other position as a module type with `<here>`.
        let f = Ident::create_local("F");
        let x = Ident::create_local("X");
        let y = Ident::create_local("Y");
        let t = Ident::create_local("T");
        let symptom = "\n  \n  Illegal permutation of structure fields";
        let line = |cxt: &[IncludePos]| {
            include_context_text(cxt)
                .strip_suffix(symptom)
                .expect("a blank line before the symptom")
                .to_string()
        };
        assert_eq!(
            line(&[IncludePos::Module(f), IncludePos::Module(y)]),
            "In module F.Y:"
        );
        assert_eq!(line(&[IncludePos::Modtype(t)]), "In module type T:");
        assert_eq!(
            line(&[IncludePos::Module(f), IncludePos::Modtype(t)]),
            "In module type F.T:"
        );
        assert_eq!(
            line(&[IncludePos::Module(f), IncludePos::Body(x)]),
            "In the result of functor F:"
        );
        assert_eq!(
            line(&[IncludePos::Module(f), IncludePos::Arg(x)]),
            "In the parameter X of functor F:"
        );
        assert_eq!(
            line(&[IncludePos::Body(x), IncludePos::Module(y)]),
            "At position (X) => { module Y: <here> }"
        );
        assert_eq!(
            line(&[IncludePos::Modtype(t), IncludePos::Module(y)]),
            "At position module type T = { module Y: <here> }"
        );
        assert_eq!(
            line(&[
                IncludePos::Module(f),
                IncludePos::Body(x),
                IncludePos::Module(y)
            ]),
            "At position module F: (X) => { module Y: <here> }"
        );
    }
}
