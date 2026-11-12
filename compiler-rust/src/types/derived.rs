//! What the checker records for a derived item (`Tstr_derived`): the
//! identifier, type and environment of each binding, and what each obligation
//! of the plan resolved to. Both are dense tables in the typed arena, indexed
//! by the plan's binding and obligation handles, so the readers of the typed
//! tree reach them without a lookup structure.
//! (`compiler-rust/docs/DERIVED_CODECS.md`, "The cheapest sound path".)

use crate::binary_ast::derive::plan::{BindingIdx, DerivedIdx, ObligationIdx, Plans, Span};
use crate::ident::Ident;
use crate::types::path::Path;
use crate::types::type_expr::TypeExprRef;
use crate::types::typedtree::EnvRef;

/// Why the walks over the structure of a module expression have no case for
/// a derived item: the seam plans an item only at the top level of a unit
/// (`derive::Scope`), and everything nested keeps its value group.
pub(crate) const TOP_LEVEL_ONLY: &str =
    "a derived item is planned only at the top level of a unit";

/// What a discharged obligation resolved to.
#[derive(Debug, Clone, Copy)]
pub struct Resolved {
    /// The path the name resolved to.
    pub path: Path,
    /// For a value, the instance its skeleton was unified with; for a type,
    /// the null reference.
    pub instance: TypeExprRef,
}

/// A binding of a discharged item, as entered in the environment.
#[derive(Debug, Clone, Copy)]
pub struct Bound {
    /// The bound identifier.
    pub ident: Ident,
    /// The generalised type of the binding.
    pub ty: TypeExprRef,
    /// The environment the item was checked in.
    pub env: EnvRef,
}

/// The tables of one typed arena. `reserve` sizes them once per compilation.
#[derive(Debug, Default)]
pub struct DerivedTable {
    resolved: Vec<Option<Resolved>>,
    bound: Vec<Option<Bound>>,
    /// The binding slots of each item, so a reader of the typed tree needs
    /// no parse arena to find them.
    items: Vec<Span>,
}

impl DerivedTable {
    /// Make room for every binding and obligation of `plans`.
    /// Cost: O(1) when the tables already have that size, which is every call
    /// but the first of a compilation; the first is O(bindings + obligations
    /// of the unit), one allocation per table.
    pub fn reserve(&mut self, plans: &Plans) {
        if self.resolved.len() != plans.obligation_count() {
            self.resolved.resize(plans.obligation_count(), None);
        }
        if self.bound.len() != plans.binding_count() {
            self.bound.resize(plans.binding_count(), None);
        }
        if self.items.len() != plans.item_count() {
            self.items.resize(plans.item_count(), Span { start: 0, len: 0 });
        }
    }

    /// Record what an obligation resolved to. Cost: O(1), one slot write.
    #[inline]
    pub fn set_resolved(&mut self, idx: ObligationIdx, resolved: Resolved) {
        self.resolved[idx.index()] = Some(resolved);
    }

    /// Forget what an obligation resolved to. Cost: O(1), one slot write.
    #[inline]
    pub fn clear_resolved(&mut self, idx: ObligationIdx) {
        self.resolved[idx.index()] = None;
    }

    /// Record a binding. Cost: O(1), one slot write.
    #[inline]
    pub fn set_bound(&mut self, idx: BindingIdx, bound: Bound) {
        self.bound[idx.index()] = Some(bound);
    }

    /// What an obligation of a discharged item resolved to. Cost: O(1).
    #[inline]
    pub fn resolved(&self, idx: ObligationIdx) -> Resolved {
        self.resolved[idx.index()].expect("the obligations of a typed derived item are discharged")
    }

    /// Record the binding slots of a discharged item. Cost: O(1).
    #[inline]
    pub fn set_item(&mut self, idx: DerivedIdx, bindings: Span) {
        self.items[idx.index()] = bindings;
    }

    /// The bindings of a discharged item, in declaration order.
    /// Cost: O(1) to obtain; one slot read per binding yielded.
    pub fn bound(&self, idx: DerivedIdx) -> impl Iterator<Item = Bound> + '_ {
        self.bound[self.items[idx.index()].range()]
            .iter()
            .map(|bound| bound.expect("the bindings of a typed derived item are entered"))
    }

    /// The results of the obligations of a discharged item, in typing order.
    /// Cost: O(1) to obtain; one slot read per obligation yielded.
    pub fn resolved_of<'a>(
        &'a self,
        plans: &'a Plans,
        item: DerivedIdx,
    ) -> impl Iterator<Item = Resolved> + 'a {
        let item = plans.item(item);
        plans.bindings(item).iter().flat_map(move |binding| {
            self.resolved[binding.obligations.range()].iter().map(|resolved| {
                resolved.expect("the obligations of a typed derived item are discharged")
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes_are_pinned() {
        assert_eq!(std::mem::size_of::<Option<Resolved>>(), 16);
        assert_eq!(std::mem::size_of::<Option<Bound>>(), 24);
    }
}
