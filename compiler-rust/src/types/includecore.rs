//! The differences between two type declarations, as
//! `Includecore.type_declarations` finds them (includecore.ml), and their
//! report.
//!
//! The comparison itself is `includemod::includecore_type_declarations`; both
//! the inclusion check of a signature (includemod.ml `type_declarations`) and
//! the coherence check of a manifest (typedecl.ml `check_coherence`) read its
//! list.

use crate::ident::Ident;
use crate::parser::formatter::Formatter;

/// `Includecore.type_mismatch` (includecore.ml).
#[derive(Debug, Clone, PartialEq)]
pub enum TypeMismatch {
    Arity,
    Privacy,
    Kind,
    Constraint,
    Manifest,
    Variance,
    FieldType(Ident),
    FieldMutable(Ident),
    FieldOptional(Ident),
    FieldNames(usize, String, String),
    FieldMissing(bool, Ident),
    ConstructorType(Ident),
    ConstructorArity(Ident),
    ConstructorNames(usize, String, String),
    ConstructorMissing(bool, Ident),
    RecordRepresentation,
    /// `true` means the second declaration is unboxed.
    UnboxedRepresentation(bool),
    Immediate,
    TagName,
    VariantRepresentation(Ident),
    /// What each declaration states about its values at run time
    /// (`Ast_untagged_variants.describe_declared_values`).
    RuntimeAnnotation(String, String),
    NotUndefined,
}

/// `Format.pp_print_string`: a string as wide as its bytes.
fn text<W: std::io::Write>(ppf: &mut Formatter<W>, s: &str) {
    ppf.string_as(s.len(), s);
}

/// A side of a comparison as a label: "the actual" and "declaration" make
/// "Actual declaration" (includecore.ml `label`).
fn label(side: &str, decl: &str) -> String {
    let side = side.strip_prefix("the ").unwrap_or(side);
    let mut label = format!("{side} {decl}");
    // `String.capitalize_ascii`
    if let Some(first) = label.get_mut(0..1) {
        first.make_ascii_uppercase();
    }
    label
}

/// `String.capitalize_ascii`
fn capitalize(s: &str) -> String {
    let mut s = s.to_string();
    if let Some(first) = s.get_mut(0..1) {
        first.make_ascii_uppercase();
    }
    s
}

/// `report_type_mismatch0 first second decl ppf err` (includecore.ml).
fn report_type_mismatch0<W: std::io::Write>(
    ppf: &mut Formatter<W>,
    first: &str,
    second: &str,
    decl: &str,
    err: &TypeMismatch,
) {
    match err {
        TypeMismatch::Arity => text(ppf, "They have different arities"),
        TypeMismatch::Privacy => text(ppf, "A private type would be revealed"),
        TypeMismatch::Kind => text(ppf, "Their kinds differ"),
        TypeMismatch::Constraint => text(ppf, "Their constraints differ"),
        TypeMismatch::Manifest => {}
        TypeMismatch::Variance => text(ppf, "Their variances do not agree"),
        TypeMismatch::FieldType(s) => text(
            ppf,
            &format!("The types for field {} are not equal", s.name()),
        ),
        TypeMismatch::FieldMutable(s) => text(
            ppf,
            &format!("The mutability of field {} is different", s.name()),
        ),
        TypeMismatch::FieldOptional(s) => text(
            ppf,
            &format!("The optional attribute of field {} is different", s.name()),
        ),
        TypeMismatch::FieldNames(n, name1, name2) => text(
            ppf,
            &format!("Fields number {n} have different names, {name1} and {name2}"),
        ),
        TypeMismatch::FieldMissing(b, s) => text(
            ppf,
            &format!(
                "The field {} is only present in {} {decl}",
                s.name(),
                if *b { second } else { first }
            ),
        ),
        TypeMismatch::ConstructorType(s) => text(
            ppf,
            &format!("The types for constructor {} are not equal", s.name()),
        ),
        TypeMismatch::ConstructorArity(s) => text(
            ppf,
            &format!("The arities for constructor {} differ", s.name()),
        ),
        TypeMismatch::ConstructorNames(n, name1, name2) => text(
            ppf,
            &format!("Constructors number {n} have different names, {name1} and {name2}"),
        ),
        TypeMismatch::ConstructorMissing(b, s) => text(
            ppf,
            &format!(
                "The constructor {} is only present in {} {decl}",
                s.name(),
                if *b { second } else { first }
            ),
        ),
        TypeMismatch::RecordRepresentation => text(ppf, "Their internal representations differ"),
        // `"@[<v 2>Their internal representations differ:@,%s %s %s@]"`
        TypeMismatch::UnboxedRepresentation(b) => {
            ppf.open_vbox(2);
            text(ppf, "Their internal representations differ:");
            ppf.cut();
            text(
                ppf,
                &format!(
                    "{} {decl} uses unboxed representation",
                    capitalize(if *b { second } else { first })
                ),
            );
            ppf.close_box();
        }
        TypeMismatch::Immediate => text(ppf, &format!("{first} {decl} is not an immediate type")),
        TypeMismatch::TagName => text(ppf, "Their @tag annotations differ"),
        TypeMismatch::VariantRepresentation(s) => text(
            ppf,
            &format!(
                "The internal representations for case {} are not equal",
                s.name()
            ),
        ),
        // `"@[<v 2>Their runtime representations differ:@,%s: can hold
        // undefined@,%s: @notUndefined@]"`
        TypeMismatch::NotUndefined => {
            ppf.open_vbox(2);
            text(ppf, "Their runtime representations differ:");
            ppf.cut();
            text(ppf, &format!("{}: can hold undefined", label(first, decl)));
            ppf.cut();
            text(ppf, &format!("{}: @notUndefined", label(second, decl)));
            ppf.close_box();
        }
        // `"@[<v 2>Their runtime representations differ:@,%s: %s@,%s: %s@]"`
        TypeMismatch::RuntimeAnnotation(declared1, declared2) => {
            ppf.open_vbox(2);
            text(ppf, "Their runtime representations differ:");
            ppf.cut();
            text(ppf, &format!("{}: {declared1}", label(first, decl)));
            ppf.cut();
            text(ppf, &format!("{}: {declared2}", label(second, decl)));
            ppf.close_box();
        }
    }
}

/// `report_type_mismatch first second decl ppf errs` (includecore.ml): each
/// error after a break, followed by a period but for the differences in
/// runtime representation, whose lines are labels; `Manifest` prints
/// nothing.
pub(crate) fn report_type_mismatch<W: std::io::Write>(
    ppf: &mut Formatter<W>,
    first: &str,
    second: &str,
    decl: &str,
    errs: &[TypeMismatch],
) {
    for err in errs {
        if *err == TypeMismatch::Manifest {
            continue;
        }
        ppf.space();
        report_type_mismatch0(ppf, first, second, decl, err);
        if !matches!(
            err,
            TypeMismatch::RuntimeAnnotation(..) | TypeMismatch::NotUndefined
        ) {
            text(ppf, ".");
        }
    }
}
