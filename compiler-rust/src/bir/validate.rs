//! Independent traversal gate for complete trees (not intermediate forests).
use super::*;

impl Bir {
    /// Recount live uses and exits, rebuild parent/binder information and effects,
    /// and check the tree, cached facts, conservative captures and dead bindings.
    /// `None` validates a completely released arena. Detached temporary roots are
    /// rejected: finish constructing/replacing before invoking this gate.
    pub fn validate(&self, root: Option<NodeId>) -> Result<(), String> {
        let fail = |message: &str| Err(message.to_owned());
        if self.nodes.len() != self.parents.len()
            || (!self.cold.is_empty() && self.cold.len() != self.nodes.len())
        {
            return fail("parallel node arrays differ in length");
        }
        let nvars = self.vars.len();
        if [
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
        let mut functions = vec![false; self.pools.funcs.len()];
        let mut stack: Vec<_> = root.map(|id| (id, None, 1u32)).into_iter().collect();
        while let Some((id, parent, weight)) = stack.pop() {
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
            order.push(id);
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
                    let Some(i) = self.pools.catches.iter().position(|h| h.label == label) else {
                        return fail("unknown exit label");
                    };
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
                let weight = weight
                    .checked_mul(self.edge_weight(id, child))
                    .ok_or("use weight overflow")?;
                stack.push((child, Some(id), weight));
            }
        }
        for i in 0..self.nodes.len() {
            if !seen[i] && !free[i] {
                return fail("unreachable live node or untracked free slot");
            }
            if free[i] && self.parents[i].is_some() {
                return fail("free node has parent");
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
        for &id in order.iter().rev() {
            let actual = self.effects(id, |c| effects[c.index()]);
            effects[id.index()] = actual;
            let flags = self.node(id).flags();
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
                    if self.is_captured(id, var)
                        && !self.vars.flags(var).contains(VarFlags::CAPTURED) =>
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
                _ if flags.contains(NodeFlags::DEAD) => return fail("DEAD flag on non-let"),
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
