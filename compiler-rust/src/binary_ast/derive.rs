//! The single seam for built-in derives. Deleting `spice_ppx` means deleting
//! the bodies here, returning unchanged items and `false` for mapper detection.

use crate::parse_arena::ParseArena;
use crate::parser::ast::{SignatureItem, StructureItem};

/// Detect derives in a structure.
pub fn structure_uses_spice_mapper(items: &[StructureItem], arena: &ParseArena) -> bool {
    super::spice_ppx::structure_uses_spice_mapper(items, arena)
}

/// Detect derives in a signature.
pub fn signature_uses_spice_mapper(items: &[SignatureItem], arena: &ParseArena) -> bool {
    super::spice_ppx::signature_uses_spice_mapper(items, arena)
}

/// Expand built-in derives on a structure item.
pub fn expand_structure_item_with_mapper(
    item: &StructureItem,
    arena: &mut ParseArena,
    active: bool,
) -> Result<Vec<StructureItem>, String> {
    super::spice_ppx::expand_structure_item_with_mapper(item, arena, active)
}

/// Expand built-in derives on a signature item.
pub fn expand_signature_item_with_mapper(
    item: &SignatureItem,
    arena: &mut ParseArena,
    active: bool,
) -> Result<Vec<SignatureItem>, String> {
    super::spice_ppx::expand_signature_item_with_mapper(item, arena, active)
}

/// Record provenance at generation, including derives inside nested modules.
/// All structure items produced by the builtin derive are value groups.
pub(super) fn mark_generated_item(item: &StructureItem, arena: &mut ParseArena) {
    if let crate::parser::ast::StructureItemDesc::Pstr_value((_, bindings)) = item.pstr_desc {
        arena.mark_derived_value_group(bindings);
    }
}

/// Generic provenance query; consumers need not know which derive produced it.
pub fn is_derived_item(item: &StructureItem, arena: &ParseArena) -> bool {
    match item.pstr_desc {
        crate::parser::ast::StructureItemDesc::Pstr_value((_, bindings)) =>
            arena.is_derived_value_group(bindings),
        _ => false,
    }
}
