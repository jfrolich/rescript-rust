//! Experimental value namespace of the version-tree environment (H.2.7).
//!
//! Not used by the compiler. The owner holds the pools; snapshots are copyable
//! tips into that owner, and must not be used with another log. Keeping the
//! owner explicit also lets lookups return ordinary payload references without
//! borrowing a RefCell containing the payload pool. Only the path index is
//! interior mutable. No hash iteration order affects lookup results.

use super::decl::ValueDescription;
use crate::fast_hash::AHashMap;
use crate::ident::Ident;
use crate::name::Name;
use std::cell::{Cell, RefCell};

/// A retained version. Copy/clone costs O(1), with no traversal or allocation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Tip(u32);

impl Tip {
    const ROOT: Self = Self(0);
}

struct Entry {
    parent: Tip,
    shadows: Tip,
    id: Ident,
    value: ValueId,
}

#[derive(Clone, Copy)]
struct ValueId(u32);

#[derive(Default)]
struct CurrentPath {
    tip: Tip,
    visible: AHashMap<Name, Tip>,
    on_path: Vec<bool>,
}

#[derive(Default)]
struct Steps {
    probes: Cell<usize>,
    ancestors: Cell<usize>,
    moved: Cell<usize>,
    appended: Cell<usize>,
}

/// Append-only pools plus one movable path index. Root has no entry/payload.
#[derive(Default)]
struct EnvLog {
    entries: Vec<Entry>,
    values: Vec<ValueDescription>,
    current: RefCell<CurrentPath>,
    steps: Steps,
}

impl EnvLog {
    fn entry(&self, tip: Tip) -> &Entry {
        &self.entries[tip.0 as usize - 1]
    }

    /// O(distance through the common ancestor), independent of pool length.
    /// A move to the current tip does no traversal. The target-side walk is
    /// counted separately from undo/redo so tests account for all visited nodes.
    fn make_tip(&self, target: Tip) {
        let mut path = self.current.borrow_mut();
        if target != path.tip {
            let mut redo = Vec::new();
            let mut ancestor = target;
            while ancestor != Tip::ROOT && !path.on_path[ancestor.0 as usize - 1] {
                self.steps.ancestors.set(self.steps.ancestors.get() + 1);
                redo.push(ancestor);
                ancestor = self.entry(ancestor).parent;
            }
            while path.tip != ancestor {
                let old = path.tip;
                let entry = self.entry(old);
                if entry.shadows == Tip::ROOT {
                    path.visible.remove(&entry.id.name_atom());
                } else {
                    path.visible.insert(entry.id.name_atom(), entry.shadows);
                }
                path.on_path[old.0 as usize - 1] = false;
                path.tip = entry.parent;
                self.steps.moved.set(self.steps.moved.get() + 1);
            }
            for tip in redo.into_iter().rev() {
                path.visible.insert(self.entry(tip).id.name_atom(), tip);
                path.on_path[tip.0 as usize - 1] = true;
                self.steps.moved.set(self.steps.moved.get() + 1);
            }
            path.tip = target;
        }
        self.assert_path(&path);
    }

    /// Expected amortized O(1) at the newest tip, plus make_tip's distance
    /// otherwise. Vector growth is amortized; no existing entry is modified.
    fn add_value(&mut self, env: &mut Tip, id: Ident, value: ValueDescription) {
        self.make_tip(*env);
        let next = Tip(u32::try_from(self.entries.len() + 1).expect("environment log overflow"));
        let value_id = ValueId(u32::try_from(self.values.len()).expect("value pool overflow"));
        let path = self.current.get_mut();
        let shadows = path
            .visible
            .insert(id.name_atom(), next)
            .unwrap_or_default();
        self.steps.probes.set(self.steps.probes.get() + 1);
        self.entries.push(Entry {
            parent: *env,
            shadows,
            id,
            value: value_id,
        });
        self.values.push(value);
        path.on_path.push(true);
        path.tip = next;
        *env = next;
        self.steps.appended.set(self.steps.appended.get() + 1);
        self.assert_path(&self.current.borrow());
    }

    /// Expected O(1) at the current tip. An older on-path version skips only
    /// newer bindings of this name; an off-path version first pays make_tip.
    fn head(&self, env: Tip, name: Name) -> Tip {
        if env != Tip::ROOT && !self.current.borrow().on_path[env.0 as usize - 1] {
            self.make_tip(env);
        }
        self.steps.probes.set(self.steps.probes.get() + 1);
        let mut head = self
            .current
            .borrow()
            .visible
            .get(&name)
            .copied()
            .unwrap_or_default();
        while head.0 > env.0 {
            self.steps.ancestors.set(self.steps.ancestors.get() + 1);
            head = self.entry(head).shadows;
        }
        head
    }

    /// Same cost as head; returns the immutable payload, without cloning it.
    fn find_value(&self, env: Tip, name: Name) -> Option<&ValueDescription> {
        let head = self.head(env, name);
        (head != Tip::ROOT).then(|| &self.values[self.entry(head).value.0 as usize])
    }

    /// Head's cost plus the number of same-name bindings examined. Exact
    /// identifier lookup is NOT constant time when many identifiers share a
    /// name; H.2.7 explicitly requires walking the immutable shadows chain.
    fn find_value_by_ident(&self, env: Tip, id: &Ident) -> Option<&ValueDescription> {
        let mut head = self.head(env, id.name_atom());
        while head != Tip::ROOT {
            self.steps.ancestors.set(self.steps.ancestors.get() + 1);
            let entry = self.entry(head);
            if (id.stamp() == 0 && entry.id.is_persistent())
                || (id.stamp() != 0 && entry.id.same(id))
            {
                return Some(&self.values[entry.value.0 as usize]);
            }
            head = entry.shadows;
        }
        None
    }

    /// Bounded debug-only recomputation of invariant H.2.9(2). Deliberately
    /// excluded from algorithmic step counts; never scans a large pool.
    fn assert_path(&self, path: &CurrentPath) {
        if cfg!(debug_assertions) && self.entries.len() <= 128 {
            let mut visible = AHashMap::default();
            let mut on_path = vec![false; self.entries.len()];
            let mut tip = path.tip;
            while tip != Tip::ROOT {
                let entry = self.entry(tip);
                assert!(entry.parent.0 < tip.0);
                on_path[tip.0 as usize - 1] = true;
                visible.entry(entry.id.name_atom()).or_insert(tip);
                tip = entry.parent;
            }
            assert_eq!(on_path, path.on_path);
            assert_eq!(visible.len(), path.visible.len());
            for (name, tip) in visible.iter() {
                assert_eq!(path.visible.get(name), Some(tip));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::types::{DeclLoc, TypeExprRef, ValueKind};

    fn desc(n: u32) -> ValueDescription {
        ValueDescription {
            val_type: TypeExprRef(n),
            val_kind: ValueKind::ValReg,
            val_loc: DeclLoc::none(),
            val_attributes: Default::default(),
            val_path: None,
        }
    }

    #[test]
    fn newest_tip_cost_and_short_branch_moves() {
        let mut log = EnvLog::default();
        let mut tip = Tip::ROOT;
        let name = Name::new("value");
        for n in 0..100_000 {
            log.add_value(
                &mut tip,
                Ident::new(name, n + 1, IdentFlags::NONE),
                desc(n as u32),
            );
        }
        assert_eq!(log.steps.appended.get(), 100_000);
        assert_eq!(log.steps.probes.get(), 100_000);
        assert_eq!(log.steps.ancestors.get(), 0);
        assert_eq!(log.steps.moved.get(), 0);
        for _ in 0..100_000 {
            assert_eq!(log.find_value(tip, name), Some(&desc(99_999)));
        }
        assert_eq!(log.steps.probes.get(), 200_000);
        assert_eq!(log.steps.ancestors.get(), 0);
        assert_eq!(log.steps.moved.get(), 0);
        let mut fork = tip;
        for n in 0..10 {
            log.add_value(
                &mut tip,
                Ident::new(name, n + 1, IdentFlags::NONE),
                desc(n as u32),
            );
        }
        log.make_tip(fork);
        assert_eq!(log.steps.moved.get(), 10);
        for n in 0..10 {
            log.add_value(
                &mut fork,
                Ident::new(name, n + 20, IdentFlags::NONE),
                desc(n as u32 + 20),
            );
        }
        log.steps.moved.set(0);
        log.steps.ancestors.set(0);
        log.make_tip(tip);
        assert_eq!(log.steps.moved.get(), 20);
        assert_eq!(log.steps.ancestors.get(), 10);
        assert_eq!(log.find_value(tip, name), Some(&desc(9)));
        assert_eq!(log.find_value(fork, name), Some(&desc(29)));
    }

    #[test]
    fn snapshot_and_identifier_walk_costs() {
        let mut log = EnvLog::default();
        let mut tip = Tip::ROOT;
        let name = Name::new("shadow");
        let first = Ident::new(name, 1, IdentFlags::NONE);
        log.add_value(&mut tip, first, desc(1));
        let retained = tip;
        for n in 2..=100 {
            log.add_value(
                &mut tip,
                Ident::new(name, n, IdentFlags::NONE),
                desc(n as u32),
            );
        }
        assert_eq!(log.steps.moved.get(), 0);
        assert_eq!(log.steps.ancestors.get(), 0);
        assert_eq!(log.find_value(retained, name), Some(&desc(1)));
        assert_eq!(log.steps.ancestors.get(), 99);
        assert_eq!(log.steps.moved.get(), 0);
        log.steps.ancestors.set(0);
        assert_eq!(log.find_value_by_ident(tip, &first), Some(&desc(1)));
        assert_eq!(log.steps.ancestors.get(), 100);
        assert_eq!(log.steps.moved.get(), 0);
        let mut branch = retained;
        log.add_value(&mut branch, first, desc(101));
        assert_eq!(log.steps.moved.get(), 99);
        assert_eq!(log.find_value(retained, name), Some(&desc(1)));
        assert_eq!(log.find_value(branch, name), Some(&desc(101)));
        assert_eq!(log.find_value(tip, name), Some(&desc(100)));
    }

    #[test]
    fn retained_tips_shadowing_and_identifiers_match_tables() {
        let mut log = EnvLog::default();
        let mut tip = Tip::ROOT;
        let mut env = crate::types::env::Env::empty();
        let name = Name::new("x");
        let first = Ident::new(name, 1, IdentFlags::NONE);
        let second = Ident::new(name, 2, IdentFlags::NONE);
        let persistent = Ident::create_persistent("x");
        let mut snapshots = vec![(tip, env.clone())];
        for (i, id) in [persistent, first, second, first].into_iter().enumerate() {
            log.add_value(&mut tip, id, desc(i as u32));
            env.add_value(id, desc(i as u32));
            snapshots.push((tip, env.clone()));
        }
        let (mut branch, mut branch_env) = snapshots[2].clone();
        log.add_value(&mut branch, second, desc(100));
        branch_env.add_value(second, desc(100));
        snapshots.push((branch, branch_env));
        for (tip, env) in snapshots.iter().rev().chain(snapshots.iter()) {
            assert_eq!(log.find_value(*tip, name), env.find_value(name).ok());
            for id in [first, second, persistent] {
                assert_eq!(
                    log.find_value_by_ident(*tip, &id),
                    env.lookup_value(&super::super::Path::pident(id)).ok()
                );
            }
            log.make_tip(*tip);
        }
    }
}
