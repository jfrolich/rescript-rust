//! C: source_loc_of_lam / with_block_source_loc. Only source-map runs allocate
//! this dense cache. A located NONE handle stops the search before filtering,
//! exactly as the legacy source walker does.
use super::*;
use crate::lambda::LamLoc;

#[derive(Clone, Copy, Default)]
pub(super) struct Fact {
    loc: Option<LamLoc>,
    ready: bool,
}

impl State {
    /// O(newly visited source nodes), amortized across all clauses. There is no
    /// recursion, including a source-map-enabled chain of 10,000 switches.
    pub(super) fn switch_location(&mut self, root: NodeId) -> Option<LamLoc> {
        self.locations.as_ref()?;
        self.switch_locations
            .resize(self.source.nodes.len(), Fact::default());
        let mut work = std::mem::take(&mut self.location_work);
        work.push((root, false));
        while let Some((node, done)) = work.pop() {
            if self.switch_locations[node.index()].ready {
                continue;
            }
            let view = self.source.view(node);
            if !done {
                work.push((node, true));
                self.location_children(view, |child| work.push((child, false)));
                continue;
            }
            self.location_steps += 1;
            let loc = match view {
                View::Apply { info, .. } => Some(self.arena.pools.apply[info.index()].loc),
                View::Prim { primitive, .. } => Some(self.arena.primitive(primitive).loc),
                View::Fun { header, .. } => Some(self.arena.function(header).loc),
                _ => {
                    let mut first = None;
                    self.location_children(view, |child| {
                        first = first.or(self.switch_locations[child.index()].loc);
                    });
                    first
                }
            };
            self.switch_locations[node.index()] = Fact { loc, ready: true };
        }
        self.location_work = work;
        self.switch_locations[root.index()].loc.filter(|&loc| {
            self.locations
                .as_ref()
                .and_then(|t| t.get(loc))
                .is_some_and(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0)
        })
    }

    /// C: source_loc_of_lam's search order. O(1), at most three candidates.
    fn location_children(&self, view: View<'_>, mut visit: impl FnMut(NodeId)) {
        match view {
            View::Let { value, body, .. } => {
                if let Some(value) = value {
                    visit(value);
                }
                visit(body);
            }
            View::LetRec { body, .. }
            | View::Catch { body, .. }
            | View::Try { body, .. }
            | View::TryFinally { body, .. }
            | View::While { body, .. }
            | View::ForOf { body, .. }
            | View::ForAwaitOf { body, .. } => visit(body),
            View::Seq { second, .. } => visit(second),
            View::If { then_, .. } => visit(then_),
            View::StrSwitch {
                actions, header, ..
            } => {
                let h = self.arena.switch(header);
                if !h.keys.is_empty() {
                    visit(actions[0]);
                }
                if h.has_default {
                    visit(actions[h.keys.len()]);
                }
            }
            View::Switch {
                actions, header, ..
            } => {
                let h = self.arena.switch(header);
                let n = h.constants as usize;
                if n > 0 {
                    visit(actions[0]);
                }
                if n < h.keys.len() {
                    visit(actions[n]);
                }
                if h.has_default {
                    visit(actions[h.keys.len()]);
                }
            }
            View::Exit { args, .. } => {
                if let Some(&first) = args.first() {
                    visit(first);
                }
            }
            View::For { parts, .. } => visit(*parts.last().unwrap()),
            View::Assign { value, .. } => visit(value),
            // Located nodes stop the search; unlocated leaves contribute none.
            View::Apply { .. }
            | View::Prim { .. }
            | View::Fun { .. }
            | View::Var { .. }
            | View::Global { .. }
            | View::Const { .. }
            | View::Break
            | View::Continue => {}
            _ => unreachable!("source location lookup on an L node"),
        }
    }

    /// C: with_block_source_loc. O(first live slot + new location nodes). Keep
    /// an existing statement location; do not overwrite its comment.
    pub(super) fn locate_switch_run(&mut self, source: NodeId, run: Span) {
        if self.locations.is_none() {
            return;
        }
        if let Some(first) = self.statements.first(run)
            && !self
                .arena
                .node(first)
                .flags()
                .contains(crate::bir::NodeFlags::JS_LOC_PRESENT)
            && let Some(loc) = self.switch_location(source)
        {
            let comment = self.arena.cold(first).and_then(|c| c.comment);
            self.arena
                .set_cold(first, crate::bir::Cold { loc, comment });
            let mut flags = self.arena.node(first).flags();
            flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
            self.arena.nodes[first.index()].set_flags(flags);
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn location_cache_and_walk_sizes() {
        assert_eq!(std::mem::size_of::<super::Fact>(), 8);
        assert_eq!(std::mem::size_of::<(super::NodeId, bool)>(), 8);
    }
}

#[cfg(test)]
mod oracle_tests {
    use super::*;
    use crate::lambda::{
        SwitchDispatch, SwitchKey, arena::LamArena, lam_constant::Constant,
        lam_primitive::Primitive as P,
    };
    use crate::types::{
        VariantBlock, VariantBlockType, VariantConstructorCase as Case,
        VariantLiteralTag as Literal, VariantMatchingFacts, VariantTag,
    };
    #[test]
    fn ten_thousand_nested_location_searches_are_memoized() {
        let mut a = LamArena::new();
        let mut locations = crate::lambda::LamLocTable::located(Default::default());
        let loc = locations.intern(crate::location::Location::new(Default::default(), 1, 8));
        let mut root = a.prim_raw(P::PinitMod, &[], loc);
        let header = a.add_switch(
            true,
            [SwitchKey::Int(0)],
            true,
            [],
            false,
            SwitchDispatch::Direct,
        );
        for _ in 0..10_000 {
            let x = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
            let bodies = a.add_list(&[root]);
            root = a.switch_raw(x, bodies, header);
        }
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        state.locations = Some(locations);
        assert_eq!(state.switch_location(root), Some(loc));
        assert_eq!(state.location_steps, 10_001);
        assert_eq!(state.switch_location(root), Some(loc));
        assert_eq!(state.location_steps, 10_001);
    }

    #[test]
    fn switch_clause_and_fallthrough_mappings_match_legacy() {
        for kind in 0..4 {
            for count in 0..=4 {
                for fallback in [false, true] {
                    let mut a = LamArena::new();
                    let mut locations = crate::lambda::LamLocTable::located(Default::default());
                    let x = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
                    let blocks = if kind == 3 { 2 } else { 0 };
                    let bodies: Vec<_> = (0..count + blocks + usize::from(fallback))
                        .map(|i| {
                            let value = a.const_(Constant::Int {
                                i: (i / 2) as i32,
                                comment: None,
                            });
                            let loc = locations.intern(crate::location::Location::new(
                                Default::default(),
                                i * 10,
                                i * 10 + 5,
                            ));
                            a.prim_raw(P::PinitMod, &[value], loc)
                        })
                        .collect();
                    let root = if kind == 1 {
                        let cases = (0..count)
                            .map(|i| (format!("C{i}"), bodies[i]))
                            .collect::<Vec<_>>();
                        let refs = cases
                            .iter()
                            .map(|(k, v)| (k.as_str(), *v))
                            .collect::<Vec<_>>();
                        a.string_switch(x, &refs, fallback.then(|| bodies[count]))
                    } else {
                        let tag = |i| VariantTag {
                            name: crate::name::Name::new(&format!("C{i}")),
                            literal: Literal::String(format!("C{i}")),
                        };
                        let constants = (0..count)
                            .map(|i| {
                                if kind == 0 {
                                    SwitchKey::Int(i as i32)
                                } else {
                                    SwitchKey::Constructor(Case::Constant(tag(i)))
                                }
                            })
                            .collect::<Vec<_>>();
                        let block_types = if kind == 3 {
                            vec![VariantBlockType::Number, VariantBlockType::String]
                        } else {
                            vec![]
                        };
                        let blocks = block_types
                            .iter()
                            .enumerate()
                            .map(|(i, t)| {
                                SwitchKey::Constructor(Case::Block(VariantBlock::Untagged {
                                    tag: tag(i + count),
                                    block_type: t.clone(),
                                }))
                            })
                            .collect::<Vec<_>>();
                        let dispatch = if kind == 0 {
                            SwitchDispatch::Direct
                        } else {
                            SwitchDispatch::Variant(VariantMatchingFacts {
                                tag_name: None,
                                literal_tags: (0..count).map(|i| tag(i).literal).collect(),
                                block_types,
                            })
                        };
                        let header = a.add_switch(
                            !fallback, constants, !fallback, blocks, fallback, dispatch,
                        );
                        let bodies = a.add_list(&bodies);
                        a.switch_raw(x, bodies, header)
                    };
                    super::super::oracle_tests::compare_mapped(a, root, &locations);
                }
            }
        }
    }
}
