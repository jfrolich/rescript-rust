//! Port of `compiler/ml/record_runtime.ml`: how a record field is named at
//! run time. A field carries the name it was declared with unless an
//! `@as("...")` renames it, and that choice is made once rather than
//! re-derived wherever a field name is needed. (`declaration_name` is
//! [`LabelDeclaration::declaration_name`](super::decl::LabelDeclaration::declaration_name).)

use crate::ast_payload::PayloadError;
use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::LabelDeclaration;

/// The decoded `@as` rename of a parsetree field
/// (`String_literal.string_semantic` of `pld_runtime_name`).
pub fn parsetree_runtime_name(label: &LabelDeclaration) -> Option<String> {
    label
        .pld_runtime_name
        .as_ref()
        .map(|name| name.txt.semantic().to_string())
}

/// OCaml `Record_runtime.check_duplicated_labels`: the first field that
/// collides with an earlier one, by declared or by runtime name.
pub fn check_duplicated_labels(
    arena: &ParseArena,
    labels: &[LabelDeclaration],
) -> Option<(String, LocIdx)> {
    let mut coll: crate::fast_hash::AHashSet<&str> = crate::fast_hash::AHashSet::default();
    for label in labels {
        let txt = arena.get_string(label.pld_name.txt);
        if coll.contains(txt) && txt != "..." {
            return Some((txt.to_string(), label.pld_name.loc));
        }
        // Checked against the fields seen before this one, so that
        // `@as("x") x` renames a field to the name it already has.
        let clash = label.pld_runtime_name.as_ref().and_then(|name| {
            let semantic = name.txt.semantic();
            coll.contains(semantic)
                .then(|| (semantic.to_string(), name.loc))
        });
        coll.insert(txt);
        if clash.is_some() {
            return clash;
        }
        if let Some(name) = &label.pld_runtime_name {
            coll.insert(name.txt.semantic());
        }
    }
    None
}

/// OCaml `Record_runtime.extra_as_attribute`: the location of a second `@as`
/// naming the field, which is one too many.
pub fn extra_as_attribute(
    arena: &ParseArena,
    label: &LabelDeclaration,
) -> Result<Option<LocIdx>, PayloadError> {
    for attr in label.pld_attributes.iter() {
        if arena.get_string(attr.0.txt) == "as"
            && crate::ast_payload::string_literal_of_payload(arena, &attr.1)?.is_some()
        {
            return Ok(Some(attr.0.loc));
        }
    }
    Ok(None)
}
