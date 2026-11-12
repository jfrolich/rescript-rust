//! The single seam for built-in derives. Deleting `spice_ppx` means deleting
//! the bodies here, returning unchanged items and `false` for mapper detection.

/// Optional derived-code measurement, owned by one compilation.
pub mod census;
mod shape;
pub(super) use shape::record as record_shapes;

use crate::parse_arena::ParseArena;
use crate::parser::ast::{SignatureItem, StructureItem};

/// Detect derives in a structure. O(items and visited attributes), delegating to
/// the existing mapper scan; no additional traversal.
pub fn structure_uses_spice_mapper(items: &[StructureItem], arena: &ParseArena) -> bool {
    super::spice_ppx::structure_uses_spice_mapper(items, arena)
}

/// Detect derives in a signature. O(items and visited attributes), delegating to
/// the existing mapper scan; no additional traversal.
pub fn signature_uses_spice_mapper(items: &[SignatureItem], arena: &ParseArena) -> bool {
    super::spice_ppx::signature_uses_spice_mapper(items, arena)
}

/// Expand built-in derives on a structure item. O(generated syntax plus mapper
/// work), with O(1) timing overhead only when the census is enabled.
pub fn expand_structure_item_with_mapper(
    item: &StructureItem,
    arena: &mut ParseArena,
    active: bool,
) -> Result<Vec<StructureItem>, String> {
    // O(1) disabled probe: retain the direct call without saving profiling state
    // across a mapper that mutably borrows the arena.
    if arena.derived_census.is_none() {
        return super::spice_ppx::expand_structure_item_with_mapper(item, arena, active);
    }
    expand_with_census(item, arena, active)
}

/// O(1) census bookkeeping plus the existing expansion and optional key encoder.
/// Keeping this cold leaves no profiling locals in the ordinary mapper's frame.
#[cold]
#[inline(never)]
fn expand_with_census(item: &StructureItem, arena: &mut ParseArena, active: bool) -> Result<Vec<StructureItem>, String> {
    let start = census::start(true);
    let observer_before = arena.derived_census.as_ref().map_or(0, |c| c.observer_ns);
    let result = super::spice_ppx::expand_structure_item_with_mapper(item, arena, active);
    if let (Some(start), Some(census)) = (start, arena.derived_census.as_mut()) {
        census.generation.add(active, census::nanos(start.elapsed()).saturating_sub(census.observer_ns - observer_before));
    }
    result
}

/// Expand built-in derives on a signature item. O(generated declarations plus
/// mapper work); no additional traversal.
pub fn expand_signature_item_with_mapper(
    item: &SignatureItem,
    arena: &mut ParseArena,
    active: bool,
) -> Result<Vec<SignatureItem>, String> {
    super::spice_ppx::expand_signature_item_with_mapper(item, arena, active)
}

/// Record provenance at generation, including derives inside nested modules.
/// All structure items produced by the builtin derive are value groups.
/// Cost: one tag test and one bitmap write; growing the bitmap zeroes only
/// newly reached binding-pool words (one word per 64 binding slots).
pub(super) fn mark_generated_item(item: &StructureItem, arena: &mut ParseArena) {
    if let crate::parser::ast::StructureItemDesc::Pstr_value((_, bindings)) = item.pstr_desc {
        arena.mark_derived_value_group(bindings);
    }
}

/// Generic provenance query; consumers need not know which derive produced it.
/// Cost: O(1), one tag test and at most one bitmap-word read; no allocation,
/// hashing, synchronization or traversal.
pub fn is_derived_item(item: &StructureItem, arena: &ParseArena) -> bool {
    match item.pstr_desc {
        crate::parser::ast::StructureItemDesc::Pstr_value((_, bindings)) =>
            arena.is_derived_value_group(bindings),
        _ => false,
    }
}

#[cfg(test)]
#[test]
fn derive_error_fixture_messages() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/ppx_spice/errors");
    let manifest = std::fs::read_to_string(root.join("cases.tsv")).unwrap();
    for line in manifest.lines() {
        let (name, expected) = line.split_once('\t').unwrap();
        let source = std::fs::read_to_string(root.join(name)).unwrap();
        let mut parser = crate::parser::Parser::new(name, &source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "{name}: fixture must reach the derive");
        let mut arena = parser.into_arena();
        let result: Result<Vec<_>, _> = items.iter().map(|item|
            expand_structure_item_with_mapper(item, &mut arena, true)).collect();
        let error = result.expect_err(name);
        assert!(error.contains(expected), "{name}: expected {expected:?}, got {error:?}");
    }
}
