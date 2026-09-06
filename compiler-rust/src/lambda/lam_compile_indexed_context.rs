//! Native continuation modes with owner-scoped return-label identity. Copying a
//! mode copies a slot, never the mutable return label (lam_compile_context.ml).
use super::*;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ReturnLabelId(pub(super) usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum MaybeTail {
    TailInTry,
    TailWithName { label: Option<ReturnLabelId>, in_staticcatch: bool },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum TailType { NotTail, MaybeTailIsReturn(MaybeTail) }

#[derive(Clone, Debug)]
pub(super) enum Continuation {
    EffectCall(TailType),
    NeedValue(TailType),
    Declare(LetKind, Ident),
    Assign(Ident),
}
impl Continuation {
    pub(super) fn is_return(&self) -> bool {
        matches!(self, Self::EffectCall(TailType::MaybeTailIsReturn(_)) | Self::NeedValue(TailType::MaybeTailIsReturn(_)))
    }
}

// Map_ident uses Ext_ident.compare (stamp then name, NOT flags), unlike
// Set_ident's full structural ordering. Keep original identifiers as payloads.
#[derive(Clone, Debug)]
pub(super) struct MapIdent(pub(super) Ident);
impl PartialEq for MapIdent { fn eq(&self, other: &Self) -> bool { self.cmp(other).is_eq() } }
impl Eq for MapIdent {}
impl PartialOrd for MapIdent { fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(other)) } }
impl Ord for MapIdent { fn cmp(&self, other: &Self) -> std::cmp::Ordering { ext_ident_cmp(&self.0, &other.0) } }

pub(super) struct ReturnLabel {
    pub(super) id: Ident,
    pub(super) params: Vec<Ident>,
    pub(super) immutable_mask: Vec<bool>,
    pub(super) new_params: BTreeMap<MapIdent, Ident>,
    pub(super) triggered: bool,
}
impl ReturnLabel {
    pub(super) fn new(id: Ident, params: Vec<Ident>) -> Self {
        Self { id, immutable_mask: vec![true; params.len()], params, new_params: BTreeMap::new(), triggered: false }
    }
}
