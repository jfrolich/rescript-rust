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
    /// The declarations have different arities.
    Arity,
    /// A private type would be revealed.
    Privacy,
    /// Their kinds differ.
    Kind,
    /// Their constraints differ.
    Constraint,
    /// Their manifests differ; reported without a message of its own.
    Manifest,
    /// Their variances do not agree.
    Variance,
    /// The types of the field differ.
    FieldType(Ident),
    /// The mutability of the field differs.
    FieldMutable(Ident),
    /// The optional attribute of the field differs.
    FieldOptional(Ident),
    /// A field of the first declaration, named the second way in the
    /// second.
    FieldRenamed(String, String),
    /// A field and its runtime names in the two declarations.
    FieldRuntimeName(Ident, String, String),
    /// A field only one declaration has: the second one when `true`.
    FieldMissing(bool, Ident),
    /// The names in both declarations, in the second one's order.
    FieldOrder(Vec<String>),
    /// The types of the constructor differ.
    ConstructorType(Ident),
    /// The arities of the constructor differ.
    ConstructorArity(Ident),
    /// A constructor of the first declaration, named the second way in the
    /// second.
    ConstructorRenamed(String, String),
    /// A constructor only one declaration has: the second one when `true`.
    ConstructorMissing(bool, Ident),
    /// The names in both declarations, in the second one's order.
    ConstructorOrder(Vec<String>),
    /// The differences of a constructor's inline records.
    ConstructorRecord(Ident, Vec<TypeMismatch>),
    /// Their record representations differ.
    RecordRepresentation,
    /// `true` means the second declaration is unboxed.
    UnboxedRepresentation(bool),
    /// The first declaration is not an immediate type.
    Immediate,
    /// Their `@tag` annotations differ.
    TagName,
    /// The runtime representations of the case differ.
    VariantRepresentation(Ident),
    /// What each declaration states about its values at run time
    /// (`Ast_untagged_variants.describe_declared_values`).
    RuntimeAnnotation(String, String),
    /// The second declaration is `@notUndefined`, the first can hold
    /// `undefined`.
    NotUndefined,
}

/// `%S`: the string in double quotes, `String.escaped`, its characters
/// below 256 read as bytes as the outcome printer reads runtime names.
fn ocaml_quoted(s: &str) -> String {
    crate::types::external_ffi_types::debug::quote(s)
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

/// `report_type_mismatch0 ?lead_in first second decl ppf err`
/// (includecore.ml). `lead_in` introduces the two lines of a difference in
/// runtime representation; without it they stand under a lead-in printed
/// before.
fn report_type_mismatch0<W: std::io::Write>(
    ppf: &mut Formatter<W>,
    lead_in: bool,
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
        TypeMismatch::FieldRenamed(name1, name2) => text(
            ppf,
            &format!("The field {name1} is named {name2} in {second} {decl}"),
        ),
        // `"The field %s has the runtime name %S in %s %s,@ but %S in %s %s"`
        TypeMismatch::FieldRuntimeName(s, name1, name2) => {
            text(
                ppf,
                &format!(
                    "The field {} has the runtime name {} in {first} {decl},",
                    s.name(),
                    ocaml_quoted(name1)
                ),
            );
            ppf.space();
            text(
                ppf,
                &format!("but {} in {second} {decl}", ocaml_quoted(name2)),
            );
        }
        TypeMismatch::FieldMissing(b, s) => text(
            ppf,
            &format!(
                "The field {} is only present in {} {decl}",
                s.name(),
                if *b { second } else { first }
            ),
        ),
        // `"The fields are in another order in %s %s:@ %s"`
        TypeMismatch::FieldOrder(names) => {
            text(
                ppf,
                &format!("The fields are in another order in {second} {decl}:"),
            );
            ppf.space();
            text(ppf, &names.join(", "));
        }
        TypeMismatch::ConstructorType(s) => text(
            ppf,
            &format!("The types for constructor {} are not equal", s.name()),
        ),
        TypeMismatch::ConstructorArity(s) => text(
            ppf,
            &format!("The arities for constructor {} differ", s.name()),
        ),
        TypeMismatch::ConstructorRenamed(name1, name2) => text(
            ppf,
            &format!("The constructor {name1} is named {name2} in {second} {decl}"),
        ),
        TypeMismatch::ConstructorMissing(b, s) => text(
            ppf,
            &format!(
                "The constructor {} is only present in {} {decl}",
                s.name(),
                if *b { second } else { first }
            ),
        ),
        // `"The constructors are in another order in %s %s:@ %s"`
        TypeMismatch::ConstructorOrder(names) => {
            text(
                ppf,
                &format!("The constructors are in another order in {second} {decl}:"),
            );
            ppf.space();
            text(ppf, &names.join(", "));
        }
        // `"@[<v 2>The records of constructor %s differ:%a@]"`
        TypeMismatch::ConstructorRecord(s, errs) => {
            ppf.open_vbox(2);
            text(
                ppf,
                &format!("The records of constructor {} differ:", s.name()),
            );
            report_type_mismatch(ppf, false, first, second, decl, errs);
            ppf.close_box();
        }
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
            if lead_in {
                ppf.open_vbox(2);
                text(ppf, "Their runtime representations differ:");
                ppf.cut();
            }
            text(ppf, &format!("{}: can hold undefined", label(first, decl)));
            ppf.cut();
            text(ppf, &format!("{}: @notUndefined", label(second, decl)));
            if lead_in {
                ppf.close_box();
            }
        }
        // `"@[<v 2>Their runtime representations differ:@,%s: %s@,%s: %s@]"`
        TypeMismatch::RuntimeAnnotation(declared1, declared2) => {
            if lead_in {
                ppf.open_vbox(2);
                text(ppf, "Their runtime representations differ:");
                ppf.cut();
            }
            text(ppf, &format!("{}: {declared1}", label(first, decl)));
            ppf.cut();
            text(ppf, &format!("{}: {declared2}", label(second, decl)));
            if lead_in {
                ppf.close_box();
            }
        }
    }
}

/// `report_type_mismatch ?read_the_same first second decl ppf errs`
/// (includecore.ml): each reason on a line after a break, followed by a
/// period but for the differences in runtime representation, whose lines
/// are labels; `Manifest` prints nothing. `read_the_same` puts them under a
/// note that the declarations print the same, which then replaces the
/// lead-in of a difference in runtime representation.
pub(crate) fn report_type_mismatch<W: std::io::Write>(
    ppf: &mut Formatter<W>,
    read_the_same: bool,
    first: &str,
    second: &str,
    decl: &str,
    errs: &[TypeMismatch],
) {
    if read_the_same {
        // `"@ @[<v 2>The declarations read the same, but a type they mention
        // differs:%a@]"`
        ppf.space();
        ppf.open_vbox(2);
        text(
            ppf,
            "The declarations read the same, but a type they mention differs:",
        );
    }
    for err in errs {
        match err {
            TypeMismatch::Manifest => {}
            // Its lines are labels, or its errors sentences of their own.
            TypeMismatch::RuntimeAnnotation(..) | TypeMismatch::NotUndefined => {
                ppf.space();
                report_type_mismatch0(ppf, !read_the_same, first, second, decl, err);
            }
            TypeMismatch::ConstructorRecord(..) => {
                ppf.space();
                report_type_mismatch0(ppf, true, first, second, decl, err);
            }
            _ => {
                ppf.space();
                report_type_mismatch0(ppf, true, first, second, decl, err);
                text(ppf, ".");
            }
        }
    }
    if read_the_same {
        ppf.close_box();
    }
}
