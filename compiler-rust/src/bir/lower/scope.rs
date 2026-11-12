//! JavaScript occurrence counts, maintained by the arena's existing mutation
//! paths, including normalisation, argument sequencing and statement removal.
//! These are unweighted JS occurrences, not level-L switch-default use weights.
use crate::bir::VarId;

/// Two counts per variable; indexed by VarId, never by identifier or node.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Uses {
    pub(crate) built: u32,
    pub(crate) remaining: u32,
}

/// Enabled only on the lowering's J arena. Source L arenas need no rows.
#[derive(Default)]
pub(crate) struct Scope {
    pub(crate) uses: Vec<Uses>,
    #[cfg(test)]
    pub(crate) updates: usize,
}
impl Scope {
    /// Allocate zeroed rows once at lowering entry. Cost: O(variables).
    pub(crate) fn new(variables: usize) -> Self {
        Self {
            uses: vec![Uses::default(); variables],
            #[cfg(test)]
            updates: 0,
        }
    }

    /// Add a fresh variable's row. Cost: amortized O(1), no node walk.
    pub(crate) fn push(&mut self) {
        self.uses.push(Uses::default());
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::{Bir, View};
    use crate::name::Name;

    #[test]
    fn count_row_size() {
        assert_eq!(std::mem::size_of::<Uses>(), 8);
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
