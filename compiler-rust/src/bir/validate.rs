//! Independent traversal gate for complete trees (not intermediate forests).
use super::*;

/// Validation DFS events. A root uses its own id as the expected parent.
enum Work {
    Enter { id: NodeId, parent: NodeId, weight: u32 },
    Leave(NodeId),
}

impl Bir {
    /// Recount live uses and exits, rebuild parent/binder information and effects,
    /// and check the tree, cached facts, conservative captures and dead bindings.
    /// `None` validates a completely released arena. Detached temporary roots are
    /// rejected: finish constructing/replacing before invoking this gate.
    /// O(allocated nodes + operands + variables + pool headers), with explicit
    /// traversal stacks. Capture checks use preorder intervals and the nearest
    /// capture boundary, never a walk up each variable use's ancestor chain.
    pub fn validate(&self, root: Option<NodeId>) -> Result<(), String> {
        let fail = |message: &str| Err(message.to_owned());
        if self.nodes.len() != self.parents.len()
            || (!self.cold.is_empty() && self.cold.len() != self.nodes.len())
        {
            return fail("parallel node arrays differ in length");
        }
        let nvars = self.vars.len();
        if [
            self.vars.j_origin.len(),
            self.vars.order.len(),
            self.vars.flags.len(),
            self.vars.uses.len(),
            self.vars.binder.len(),
            self.vars.fact.len(),
            self.vars.printed.len(),
        ]
        .into_iter()
        .any(|n| n != nvars)
        {
            return fail("parallel variable arrays differ in length");
        }
        let mut weighted_switches = 0;
        let mut boundaries = 0;
        let mut seen = vec![false; self.nodes.len()];
        let mut free = vec![false; self.nodes.len()];
        for &id in &self.free_nodes {
            if id.index() >= free.len()
                || free[id.index()]
                || self.nodes[id.index()].op() != Op::Free
            {
                return fail("invalid or duplicate free slot");
            }
            free[id.index()] = true;
        }
        let mut uses = vec![0u32; nvars];
        let mut exits = vec![0u32; self.pools.catches.len()];
        let mut binders = vec![None; nvars];
        let mut order = Vec::new();
        let mut entered = vec![0usize; self.nodes.len()];
        let mut ended = vec![0usize; self.nodes.len()];
        let mut capture_root = vec![None; self.nodes.len()];
        let mut functions = vec![false; self.pools.funcs.len()];
        let mut stack: Vec<_> = root.map(|id| Work::Enter { id, parent: id, weight: 1 }).into_iter().collect();
        while let Some(work) = stack.pop() {
            self.visit();
            let (id, parent, weight) = match work {
                Work::Enter { id, parent, weight } => (id, (parent != id).then_some(parent), weight),
                Work::Leave(id) => {
                    ended[id.index()] = order.len();
                    continue;
                }
            };
            if id.index() >= self.nodes.len()
                || free[id.index()]
                || self.nodes[id.index()].op() == Op::Free
            {
                return fail("invalid live child");
            }
            if seen[id.index()] {
                return fail("shared child or cycle");
            }
            seen[id.index()] = true;
            weighted_switches += usize::from(self.is_weighted_switch(self.node(id)));
            boundaries += usize::from(Self::is_capture_kind(self.node(id)));
            let cached = self.weights[id.index()];
            if cached != 0 && cached != weight {
                return fail("stale weight cache");
            }
            entered[id.index()] = order.len();
            order.push(id);
            stack.push(Work::Leave(id));
            if self.parents[id.index()] != parent {
                return fail("stale parent link");
            }
            let has_cold = self.cold.get(id.index()).copied().flatten();
            if has_cold.is_some() != self.node(id).flags().contains(NodeFlags::HAS_LOC) {
                return fail("stale location flag");
            }
            if has_cold.is_some_and(|c| c.index() >= self.pools.cold.len()) {
                return fail("invalid cold handle");
            }
            for var in self.binders(id) {
                if var.index() >= nvars || binders[var.index()].replace(id).is_some() {
                    return fail("invalid or multiply bound variable");
                }
            }
            match self.view(id) {
                View::Fun { header, .. } | View::JFun { header, .. } => {
                    if functions[header.index()] {
                        return fail("shared function header");
                    }
                    functions[header.index()] = true;
                    if self.func_owners[header.index()] != Some(id) {
                        return fail("stale function owner");
                    }
                }
                View::SForOf { parts, .. } | View::SForAwaitOf { parts, .. }
                    if parts.len() != 2 =>
                {
                    return fail("for-of needs iterable and body");
                }
                View::STry {
                    parts,
                    exception: None,
                } if parts.len() != 2 => return fail("finally-only try needs body and finaliser"),
                View::Var { var } => {
                    let Some(count) = uses.get_mut(var.index()) else {
                        return fail("invalid variable");
                    };
                    *count = count.checked_add(weight).ok_or("use count overflow")?;
                }
                View::Exit { label, .. } => {
                    // Labels are arbitrary source u32 values, not dense handles.
                    // Reuse the arena's label-to-CatchId index, then count densely.
                    let Some(header) = self.pools.catch_labels.get(&label) else {
                        return fail("unknown exit label");
                    };
                    let i = header.index();
                    exits[i] = exits[i].checked_add(weight).ok_or("exit count overflow")?;
                }
                View::For { parts, .. } if parts.len() != 3 => {
                    return fail("range loop needs start, finish and body");
                }
                View::SForRange { parts, .. } if !(2..=3).contains(&parts.len()) => {
                    return fail("range loop needs bound and body, with optional start");
                }
                View::STry { parts, .. } if !(2..=3).contains(&parts.len()) => {
                    return fail("try needs body, handler and optional finaliser");
                }
                View::Switch {
                    actions, header, ..
                }
                | View::StrSwitch {
                    actions, header, ..
                }
                | View::SSwitch {
                    actions, header, ..
                } => {
                    let h = self.switch(header);
                    if actions.len() != h.keys.len() + usize::from(h.has_default) {
                        return fail("switch key/action mismatch");
                    }
                }
                _ => {}
            }
            for child in self.view(id).children() {
                if child.index() >= self.nodes.len() {
                    return fail("invalid live child");
                }
                capture_root[child.index()] = if self.capture_boundary(id, child) {
                    Some(id)
                } else {
                    capture_root[id.index()]
                };
                let weight = weight
                    .checked_mul(self.edge_weight(id, child))
                    .ok_or("use weight overflow")?;
                stack.push(Work::Enter { id: child, parent: id, weight });
            }
        }
        for i in 0..self.nodes.len() {
            if !seen[i] && !free[i] {
                return fail("unreachable live node or untracked free slot");
            }
            if free[i] && self.weights[i] != 0 {
                return fail("free node has cached weight");
            }
            if free[i] && self.parents[i].is_some() {
                return fail("free node has parent");
            }
        }
        if weighted_switches != self.weighted_switches || boundaries != self.capture_boundaries {
            return fail("stale boundary counters");
        }
        for (i, live) in functions.iter().enumerate() {
            if !live && self.func_owners[i].is_some() {
                return fail("released function retains owner");
            }
        }
        if uses != self.vars.uses {
            return fail("stale weighted use count");
        }
        if binders != self.vars.binder {
            return fail("stale binder table");
        }
        for (i, h) in self.pools.catches.iter().enumerate() {
            if exits[i] != h.uses {
                return fail("stale exit count");
            }
        }
        let mut effects = vec![(false, false); self.nodes.len()];
        let mut strict = vec![false; self.nodes.len()];
        let mut trivial_unit = vec![false; self.nodes.len()];
        let mut subexpression = vec![false; self.nodes.len()];
        // Leave events completed subtree intervals during the first traversal.
        // Only the nearest boundary matters: a binder inside it is also inside
        // every enclosing boundary, even when the binder followed the use.
        for &id in order.iter().rev() {
            let actual = self.effects(id, |c| effects[c.index()]);
            effects[id.index()] = actual;
            if let Some(actual) = j::facts::purity(self, id, true, |c| strict[c.index()]) {
                strict[id.index()] = actual;
                let sub = j::facts::subexpression(self, id, |c| subexpression[c.index()]);
                subexpression[id.index()] = sub;
                if !matches!(self.view(id), View::Var { .. }) && self.node(id).flags().contains(NodeFlags::J_SUBEXPR) != sub {
                    return fail("stale J subexpression fact");
                }
                if !matches!(self.view(id), View::Var { .. })
                    && self.node(id).flags().contains(NodeFlags::STRICT) != actual
                {
                    return fail("stale strict purity flag");
                }
            }
            let flags = self.node(id).flags();
            trivial_unit[id.index()] = self.trivial_unit_fact(self.view(id), |c| {
                (effects[c.index()].0, trivial_unit[c.index()])
            });
            if matches!(self.view(id), View::Const { .. } | View::Seq { .. } | View::Let { .. })
                && flags.contains(NodeFlags::TRIVIAL_UNIT) != trivial_unit[id.index()]
            {
                return fail("stale trivial unit flag");
            }
            if flags.contains(NodeFlags::PURE) != actual.0
                || flags.contains(NodeFlags::NO_ALLOC) != actual.1
            {
                return fail("stale effect flags");
            }
            for (var, fact) in self.binding_facts(id) {
                if self.vars.fact(var) != fact {
                    return fail("stale binding fact");
                }
                if fact == Fact::Param && !self.vars.flags(var).contains(VarFlags::PARAM) {
                    return fail("missing parameter flag");
                }
            }
            match self.view(id) {
                View::Var { var }
                    if capture_root[id.index()].is_some_and(|boundary| {
                        !binders[var.index()].is_some_and(|binder| {
                            entered[boundary.index()] <= entered[binder.index()]
                                && entered[binder.index()] < ended[boundary.index()]
                        })
                    }) && !self.vars.flags(var).contains(VarFlags::CAPTURED) =>
                {
                    return fail("missing capture flag");
                }
                View::Assign { var, .. } if !self.vars.flags(var).contains(VarFlags::ASSIGNED) => {
                    return fail("missing assigned flag");
                }
                View::Let { var, value, .. } => {
                    if flags.contains(NodeFlags::DEAD) {
                        if uses[var.index()] != 0 || value.is_some() {
                            return fail("dead let retains a use or value");
                        }
                    } else if value.is_none() {
                        return fail("live let has no value");
                    }
                }
                _ if flags.contains(NodeFlags::DEAD) && j::facts::purity(self, id, false, |_| false).is_none() => return fail("DEAD flag on non-let"),
                _ => {}
            }
        }
        for i in 0..nvars {
            if binders[i].is_none() && self.vars.fact[i] != Fact::Unknown {
                return fail("unbound variable has fact");
            }
        }
        for &(var, _) in &self.exports {
            if var.index() >= nvars || !self.vars.flags(var).contains(VarFlags::EXPORTED) {
                return fail("missing export flag");
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn work_frame_size() {
        assert_eq!(std::mem::size_of::<Work>(), 16);
    }

    #[test]
    fn deep_validation_has_linear_visits() {
        for depth in [1_000, 10_000, 100_000] {
            let mut b = Bir::default();
            b.begin_bulk();
            let var = b.new_var_id(Name::new("free"), 0);
            let mut root = b.new_node(View::Var { var }, 0);
            for _ in 0..depth {
                let first = b.new_node(View::Var { var }, 0);
                root = b.new_node(View::Seq { first, second: root }, 0);
            }
            b.finish_bulk(root);
            b.steps.set(0);
            let start = Instant::now();
            b.validate(Some(root)).unwrap();
            let elapsed = start.elapsed();
            let visited = b.steps.get();
            println!("VALIDATE depth={depth} nodes={} visited={visited} elapsed={elapsed:?}", b.nodes.len());
            assert!(visited <= 32 * b.nodes.len() as u64, "{visited} visits");
        }
    }
}
