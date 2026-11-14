//! JavaScript occurrence counts, maintained by the arena's existing mutation
//! paths, including normalisation, argument sequencing and statement removal.
//! These are unweighted JS occurrences, not level-L switch-default use weights.
use crate::bir::{Bir, NodeId, VarId, View};

/// Two counts per variable; indexed by VarId, never by identifier or node.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Uses {
    pub(crate) built: u32,
    pub(crate) remaining: u32,
}

/// The position fact of one reference (THREE_TREES 11.4, "T4a as built"):
/// its node and the next site of the same variable. The statement the
/// reference is in and its parent are read from the node when the top level
/// is complete (`lower::export`). A reference to an imported module has a
/// site too (THREE_TREES 11.4, "T5 part B as built"): the naming log reads
/// the sites of a function scope at its close, and a release clears the
/// site of a module reference as it clears a variable's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Site {
    /// The `Var` or `JQualified` node, or `NodeId(u32::MAX)` once it was
    /// released.
    pub(crate) node: NodeId,
    /// The site of the same variable recorded before this one, plus one;
    /// zero ends the chain. Zero for a module reference: no chain is kept
    /// per import (nothing reads the references of one import).
    pub(crate) next: u32,
}

/// What the close of a run reads about one variable besides its counts
/// (THREE_TREES 11.4, "T4c design"). Dense by VarId. The declaration's node
/// and the head of the read sites join it with the decisions that use them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct VarFacts {
    /// The call that is the variable's tail-call site: the last one a
    /// copied run showed with the variable as callee. `NO_SITE` for none.
    pub(crate) site: NodeId,
    /// `EXPORTED`.
    pub(crate) state: u32,
}
impl VarFacts {
    pub(crate) const NO_SITE: NodeId = NodeId(u32::MAX);
    /// The unit exports the variable (written once per export, after the
    /// coercion; read through the variable's origin).
    pub(crate) const EXPORTED: u32 = 1;
}
impl Default for VarFacts {
    fn default() -> Self {
        Self { site: Self::NO_SITE, state: 0 }
    }
}

/// What step A decides for one declaration where its run is copied: the
/// status the legacy tail-call pass would give it, read from `built`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Decision {
    pub(crate) var: VarId,
    /// The status in bits 0..3 (`js_ir::op::UsedStats`), `INLINE` in bit 3,
    /// `built` in the bits above, saturating.
    pub(crate) bits: u32,
}
impl Decision {
    /// An inline candidate with a recorded site.
    pub(crate) const INLINE: u32 = 8;
    const COUNT_SHIFT: u32 = 4;
    /// Constant.
    pub(crate) fn new(var: VarId, status: crate::js_ir::op::UsedStats, inline: bool, built: u32) -> Self {
        let count = built.min(u32::MAX >> Self::COUNT_SHIFT);
        Self { var, bits: status as u32 | if inline { Self::INLINE } else { 0 } | (count << Self::COUNT_SHIFT) }
    }
    /// Constant.
    pub(crate) fn status(self) -> u32 {
        self.bits & 7
    }
    /// Constant.
    pub(crate) fn inline(self) -> bool {
        self.bits & Self::INLINE != 0
    }
    /// Constant.
    pub(crate) fn built(self) -> u32 {
        self.bits >> Self::COUNT_SHIFT
    }
}

/// Enabled only on the lowering's J arena. Source L arenas need no rows.
#[derive(Default)]
pub(crate) struct Scope {
    pub(crate) uses: Vec<Uses>,
    /// One per `Var` and per `JQualified` node ever built, in creation order.
    pub(crate) sites: Vec<Site>,
    /// The last site of each variable plus one, zero for none. Dense by VarId.
    pub(crate) site_heads: Vec<u32>,
    /// Dense by VarId.
    pub(crate) facts: Vec<VarFacts>,
    /// One per declaration of every copied run, last slot first within a run.
    pub(crate) decisions: Vec<Decision>,
    /// Pending operands of the returned expression `return_sites` reads: the
    /// node, and whether a call found there is a site.
    spine: Vec<(NodeId, bool)>,
    /// Steps of `close::decide` and `return_sites`.
    pub(crate) close_steps: usize,
    /// Live `JQualified` references per imported module. Dense by ImportId,
    /// grown where a module is first referenced.
    pub(crate) import_uses: Vec<u32>,
    /// The tables of the external-shadow decision (`globals::decide`).
    pub(crate) globals: super::globals::Globals,
    /// The naming log (`names.rs`, THREE_TREES 11.4, "T5 part B as
    /// redesigned").
    pub(crate) names: super::names::Log,
    #[cfg(test)]
    pub(crate) updates: usize,
}
impl Scope {
    #[cfg(test)]
    pub(super) fn reserve_repeat(&mut self) {
        self.sites.reserve(self.sites.len());
        self.site_heads.reserve(self.site_heads.len());
        self.uses.reserve(self.uses.len());
        self.facts.reserve(self.facts.len());
        self.decisions.reserve(self.decisions.len());
        self.names.reserve_repeat();
    }
    #[cfg(test)]
    pub(super) fn capacities(&self) -> [usize; 6] {
        [self.sites.capacity(), self.site_heads.capacity(), self.uses.capacity(),
         self.facts.capacity(), self.decisions.capacity(), self.spine.capacity()]
    }

    /// Allocate zeroed rows once at lowering entry. Cost: O(variables).
    #[cfg(test)]
    pub(crate) fn new(variables: usize) -> Self {
        Self::with_capacity(variables, variables)
    }

    /// Initialize source rows with reserved room for known generated bindings.
    /// Cost: O(V): initializes V variable rows in each of three columns, with reserved
    /// capacity C >= V; no source nodes or use sites are walked.
    pub(super) fn with_capacity(variables: usize, capacity: usize) -> Self {
        assert!(variables <= capacity);
        let mut uses = Vec::with_capacity(capacity);
        let mut site_heads = Vec::with_capacity(capacity);
        let mut facts = Vec::with_capacity(capacity);
        uses.resize(variables, Uses::default());
        site_heads.resize(variables, 0);
        facts.resize(variables, VarFacts::default());
        Self {
            uses,
            site_heads,
            facts,
            names: super::names::Log::new(variables),
            ..Self::default()
        }
    }

    /// Account for one constructed or released reference to an imported
    /// module. Cost: O(1), amortized over the unit's imports.
    pub(crate) fn import_reference(&mut self, module: crate::bir::ImportId, add: bool) {
        if self.import_uses.len() <= module.index() {
            self.import_uses.resize(module.index() + 1, 0);
        }
        let uses = &mut self.import_uses[module.index()];
        *uses = if add { uses.checked_add(1) } else { uses.checked_sub(1) }.expect("import reference count");
    }

    /// Add a fresh variable's row. Cost: amortized O(1), no node walk.
    pub(crate) fn push(&mut self) {
        self.uses.push(Uses::default());
        self.site_heads.push(0);
        self.facts.push(VarFacts::default());
    }

    /// Record the reference `node` of `var` where it is built. Returns the
    /// site's index, which the node keeps. Cost: one push and two writes.
    pub(crate) fn site(&mut self, var: VarId, node: NodeId) -> u32 {
        let index = u32::try_from(self.sites.len()).expect("site capacity");
        let head = &mut self.site_heads[var.index()];
        self.sites.push(Site { node, next: *head });
        *head = index + 1;
        index
    }

    /// Record the reference `node` to an imported module where it is built.
    /// Returns the site's index, which the node keeps. Cost: one push.
    pub(crate) fn import_site(&mut self, node: NodeId) -> u32 {
        let index = u32::try_from(self.sites.len()).expect("site capacity");
        self.sites.push(Site { node, next: 0 });
        index
    }

    /// Account for one constructed or released Var occurrence. Cost: O(1).
    /// Normalising away an occurrence changes both the pre-substitution JS
    /// count and the remaining count; merely moving a node changes neither.
    pub(crate) fn occurrence(&mut self, var: VarId, add: bool) {
        #[cfg(test)]
        { self.updates += 1; }
        let row = &mut self.uses[var.index()];
        if add {
            row.built = row.built.checked_add(1).expect("JS use count capacity");
            row.remaining = row.remaining.checked_add(1).expect("JS use count capacity");
        } else {
            row.built = row.built.checked_sub(1).expect("released uncounted JS use");
            row.remaining = row.remaining.checked_sub(1).expect("released uncounted JS use");
        }
    }
}

/// The sites of `return value`, read through the flatten pass ("T4c design"
/// (a)): both branches of a conditional, the last operand of a sequence, a
/// call of a variable. `last` says whether the `return` is the last
/// statement of its list; below a conditional every call is a site, because
/// the flatten pass gives each branch a list of its own.
///
/// Cost: one step per conditional and sequence between `value` and its
/// calls, and one per call; a predicate, the head of a sequence and the
/// arguments of a call are not read. Nothing is allocated once the spine
/// has its capacity; nothing is done on an arena without counts.
pub(crate) fn return_sites(bir: &mut Bir, value: NodeId, last: bool) {
    let Some(scope) = &mut bir.js_scope else { return };
    let mut spine = std::mem::take(&mut scope.spine);
    debug_assert!(spine.is_empty());
    spine.push((value, last));
    let mut steps = 0;
    while let Some((node, site)) = spine.pop() {
        steps += 1;
        match bir.view(node) {
            View::JCond { then_, else_, .. } => {
                spine.push((else_, true));
                spine.push((then_, true));
            }
            View::JSeq { second, .. } => spine.push((second, site)),
            View::JCall { callee, .. } if site => {
                if let View::Var { var } = bir.view(callee) {
                    let scope = bir.js_scope.as_mut().expect("lowering scope");
                    scope.facts[var.index()].site = node;
                }
            }
            _ => {}
        }
    }
    let scope = bir.js_scope.as_mut().expect("lowering scope");
    scope.close_steps += steps;
    scope.spine = spine;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::{Bir, View};
    use crate::name::Name;

    #[test]
    fn count_row_size() {
        assert_eq!(std::mem::size_of::<Uses>(), 8);
        assert_eq!(std::mem::size_of::<Site>(), 8);
        assert_eq!(std::mem::size_of::<VarFacts>(), 8);
        assert_eq!(std::mem::size_of::<Decision>(), 8);
    }

    #[test]
    fn ten_thousand_occurrences_are_counted_once_on_creation_and_release() {
        let mut b = Bir::default();
        b.begin_bulk();
        let var = b.new_var_id(Name::new("value"), 0);
        b.js_scope = Some(Scope::new(1));
        let mut nodes = Vec::with_capacity(10_000);
        for _ in 0..10_000 {
            nodes.push(b.new_node(View::Var { var }, 0));
        }
        let scope = b.js_scope.as_ref().unwrap();
        assert_eq!(scope.updates, 10_000);
        assert_eq!(scope.uses[0], Uses { built: 10_000, remaining: 10_000 });
        for node in nodes { b.release(node); }
        let scope = b.js_scope.as_ref().unwrap();
        assert_eq!(scope.updates, 20_000);
        assert_eq!(scope.uses[0], Uses::default());
    }
}
