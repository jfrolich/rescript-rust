//! The R4 oracle: the old environment's lookups replayed on another scope
//! structure (CHECKER_REWRITE "R4 as designed", decision 4).
//!
//! `tc::scope_trace` records what the old `Env` did while a unit was checked:
//! the tree of its versions, what each version bound or opened, and every
//! lookup by name with the version it ran in and the stamps it found.
//! [`replay`] drives a [`Resolver`] through that tree with a stack discipline
//! (leave to the common ancestor, enter down to the lookup's version) and
//! asks it the same question at every lookup. The first lookup that answers
//! another item is a [`Mismatch`].
//!
//! Three resolvers exist. [`Model`] is a reference: a list of frames scanned
//! backwards, with nothing clever in it. It runs today and proves that the
//! trace carries enough to reproduce the old checker's answers. [`Skewed`] is
//! the same with one rule wrong (a local binding always wins over an opened
//! layer); the oracle must report it. `tc::scope::Scopes` is the third, from
//! slice R4c on (`r4_tests::scopes_answer_what_the_old_environment_answered`).
//!
//! What the oracle covers: every lookup by an unqualified name in the six
//! tables of `Env`, under every binding and every `open` of the unit. What it
//! does not: the members of an opened layer are taken from the old layer, not
//! from a segment (that is `r4_tests::an_import_lists_the_members_of_the_old_layer`,
//! slice R4c), and a qualified path is not a lookup of `Env`'s tables
//! (`r4_tests`, slice R4d, on pinned programs; whole units from R5c on).
//!
//! Nothing here is on a compile path; the oracle allocates freely.

use std::collections::HashMap;

use super::scope_trace::{Event, Ns};

/// A scope structure under test. An item is a number the replay chose; the
/// resolver stores it and gives it back.
pub(crate) trait Resolver {
    /// Enter a scope inside the current one.
    fn enter(&mut self);
    /// Leave the current scope: everything bound or opened in it is gone.
    fn leave(&mut self);
    /// Bind `name` in the current scope.
    fn bind(&mut self, ns: Ns, name: &str, item: u32);
    /// Open one layer in the current scope. Members of one namespace and
    /// name are in candidate order.
    fn open(&mut self, members: &[(Ns, &str, u32)]);
    /// The binding a lookup of `name` finds.
    fn first(&mut self, ns: Ns, name: &str) -> Option<u32>;
    /// Every candidate of `name`, innermost first, appended to `out`.
    fn all(&mut self, ns: Ns, name: &str, out: &mut Vec<u32>);
}

/// The first lookup the resolver answered differently.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Mismatch {
    /// Index of the lookup in the trace.
    pub event: usize,
    pub ns: Ns,
    pub name: String,
    /// `name/stamp` of what each side found, in order.
    pub old: Vec<String>,
    pub new: Vec<String>,
}

/// What a replay did, so that a test can refuse a vacuous one.
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct Replayed {
    pub lookups: usize,
    /// Lookups the old environment answered with an item of the trace.
    pub found: usize,
    /// Lookups answered with an item an opened layer had listed by then.
    pub through_open: usize,
    pub binds: usize,
    pub opens: usize,
}

/// Item numbers by identity, and each number's `name/stamp` text and
/// whether an opened layer has listed it so far.
#[derive(Default)]
struct Items {
    by_identity: HashMap<(Ns, &'static str, i32), u32>,
    names: Vec<String>,
    opened: Vec<bool>,
}

impl Items {
    fn number(&mut self, ns: Ns, name: &'static str, stamp: i32, through_open: bool) -> u32 {
        let next = self.names.len() as u32;
        let number = *self.by_identity.entry((ns, name, stamp)).or_insert(next);
        if number == next {
            self.names.push(format!("{name}/{stamp}"));
            self.opened.push(false);
        }
        // A module's member is bound in the module's body first and listed
        // by the layer later: it is a member from the layer's event on.
        self.opened[number as usize] |= through_open;
        number
    }
}

#[derive(Default)]
struct Version {
    parent: Option<u64>,
    /// Indices of this version's `Bind` and `Open` events.
    adds: Vec<usize>,
}

/// O(events x depth of the version tree): replay `events` on `resolver`.
/// An item the old environment found that no event of the trace bound or
/// opened (a predefined type, a binding of the initial environment) is
/// outside the trace: the resolver must not find anything in its place.
pub(crate) fn replay(events: &[Event], resolver: &mut dyn Resolver) -> Result<Replayed, Mismatch> {
    let mut versions: HashMap<u64, Version> = HashMap::new();
    let mut items = Items::default();
    // The versions on the resolver's stack, root first.
    let mut stack: Vec<u64> = Vec::new();
    let mut path: Vec<u64> = Vec::new();
    let mut done = Replayed::default();
    let mut members_buffer: Vec<(Ns, &str, u32)> = Vec::new();
    for (index, event) in events.iter().enumerate() {
        match event {
            Event::Version { from, to } => {
                versions.entry(*from).or_default();
                versions.entry(*to).or_default().parent = Some(*from);
            }
            Event::Bind {
                env,
                ns,
                name,
                stamp,
            } => {
                items.number(*ns, name, *stamp, false);
                versions.entry(*env).or_default().adds.push(index);
                // A version on the stack never gains a binding: every
                // extension starts with a new version.
                assert!(!stack.contains(env), "binding added to an entered version");
            }
            Event::Open { env, members } => {
                for (ns, name, stamp) in members {
                    items.number(*ns, name, *stamp, true);
                }
                versions.entry(*env).or_default().adds.push(index);
                assert!(!stack.contains(env), "layer added to an entered version");
            }
            Event::Lookup {
                env,
                ns,
                name,
                all,
                found,
            } => {
                // Root-first chain of versions of the lookup's environment.
                path.clear();
                let mut at = Some(*env);
                while let Some(version) = at {
                    path.push(version);
                    at = versions.get(&version).and_then(|v| v.parent);
                }
                path.reverse();
                let common = stack.iter().zip(&path).take_while(|(a, b)| a == b).count();
                while stack.len() > common {
                    resolver.leave();
                    stack.pop();
                }
                for &version in &path[common..] {
                    resolver.enter();
                    stack.push(version);
                    let Some(adds) = versions.get(&version).map(|v| v.adds.as_slice()) else {
                        continue;
                    };
                    for &add in adds {
                        match &events[add] {
                            Event::Bind {
                                ns, name, stamp, ..
                            } => {
                                done.binds += 1;
                                resolver.bind(*ns, name, items.by_identity[&(*ns, *name, *stamp)]);
                            }
                            Event::Open { members, .. } => {
                                done.opens += 1;
                                members_buffer.clear();
                                members_buffer.extend(members.iter().map(|(ns, name, stamp)| {
                                    (*ns, *name, items.by_identity[&(*ns, *name, *stamp)])
                                }));
                                resolver.open(&members_buffer);
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                // Items outside the trace are not the resolver's to find.
                let expected: Vec<u32> = found
                    .iter()
                    .filter_map(|stamp| {
                        items
                            .by_identity
                            .iter()
                            .find(|((item_ns, item_name, item_stamp), _)| {
                                item_ns == ns && *item_name == name.as_str() && item_stamp == stamp
                            })
                            .map(|(_, &number)| number)
                    })
                    .collect();
                let mut actual = Vec::new();
                if *all {
                    resolver.all(*ns, name, &mut actual);
                } else {
                    actual.extend(resolver.first(*ns, name));
                }
                done.lookups += 1;
                if let Some(&first) = expected.first() {
                    done.found += 1;
                    done.through_open += usize::from(items.opened[first as usize]);
                }
                if expected != actual {
                    let text = |list: &[u32]| {
                        list.iter()
                            .map(|&n| items.names[n as usize].clone())
                            .collect()
                    };
                    return Err(Mismatch {
                        event: index,
                        ns: *ns,
                        name: name.clone(),
                        old: text(&expected),
                        new: text(&actual),
                    });
                }
            }
        }
    }
    Ok(done)
}

enum Entry {
    Bind(Ns, String, u32),
    Open(Vec<(Ns, String, u32)>),
}

/// The reference resolver: frames of entries in the order they were added,
/// scanned from the last to the first. A lookup costs O(everything in scope).
#[derive(Default)]
pub(crate) struct Model {
    frames: Vec<Vec<Entry>>,
}

impl Resolver for Model {
    fn enter(&mut self) {
        self.frames.push(Vec::new());
    }

    fn leave(&mut self) {
        self.frames.pop().expect("leave without enter");
    }

    fn bind(&mut self, ns: Ns, name: &str, item: u32) {
        let frame = self.frames.last_mut().expect("bind outside a scope");
        frame.push(Entry::Bind(ns, name.to_string(), item));
    }

    fn open(&mut self, members: &[(Ns, &str, u32)]) {
        let frame = self.frames.last_mut().expect("open outside a scope");
        frame.push(Entry::Open(
            members
                .iter()
                .map(|(ns, name, item)| (*ns, name.to_string(), *item))
                .collect(),
        ));
    }

    fn first(&mut self, ns: Ns, name: &str) -> Option<u32> {
        let mut out = Vec::new();
        self.all(ns, name, &mut out);
        out.first().copied()
    }

    fn all(&mut self, ns: Ns, name: &str, out: &mut Vec<u32>) {
        for entry in self
            .frames
            .iter()
            .rev()
            .flat_map(|frame| frame.iter().rev())
        {
            match entry {
                Entry::Bind(entry_ns, entry_name, item)
                    if *entry_ns == ns && entry_name == name =>
                {
                    out.push(*item)
                }
                Entry::Bind(..) => {}
                Entry::Open(members) => out.extend(
                    members
                        .iter()
                        .filter(|(member_ns, member_name, _)| {
                            *member_ns == ns && member_name == name
                        })
                        .map(|member| member.2),
                ),
            }
        }
    }
}

/// [`Model`] with one rule wrong: an opened layer never hides a binding,
/// however old the binding is.
#[derive(Default)]
pub(crate) struct Skewed(Model);

impl Resolver for Skewed {
    fn enter(&mut self) {
        self.0.enter();
    }

    fn leave(&mut self) {
        self.0.leave();
    }

    fn bind(&mut self, ns: Ns, name: &str, item: u32) {
        self.0.bind(ns, name, item);
    }

    fn open(&mut self, members: &[(Ns, &str, u32)]) {
        self.0.open(members);
    }

    fn first(&mut self, ns: Ns, name: &str) -> Option<u32> {
        let mut out = Vec::new();
        self.all(ns, name, &mut out);
        out.first().copied()
    }

    fn all(&mut self, ns: Ns, name: &str, out: &mut Vec<u32>) {
        let entries = || {
            self.0
                .frames
                .iter()
                .rev()
                .flat_map(|frame| frame.iter().rev())
        };
        for entry in entries() {
            if let Entry::Bind(entry_ns, entry_name, item) = entry
                && *entry_ns == ns
                && entry_name == name
            {
                out.push(*item);
            }
        }
        for entry in entries() {
            if let Entry::Open(members) = entry {
                out.extend(
                    members
                        .iter()
                        .filter(|(member_ns, member_name, _)| {
                            *member_ns == ns && member_name == name
                        })
                        .map(|member| member.2),
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::r4_tests::{OPEN_SHADOWS_A_LOCAL, PROGRAMS, old_checker};

    /// The trace is enough: the reference resolver answers every lookup of
    /// every pinned program as the old environment did, and the replays are
    /// not vacuous (bindings, opened layers, lookups found through a layer).
    #[test]
    fn the_reference_model_answers_what_the_old_environment_answered() {
        let mut total = Replayed::default();
        for program in PROGRAMS {
            let old = old_checker(program);
            let done = replay(&old.events, &mut Model::default())
                .unwrap_or_else(|mismatch| panic!("{mismatch:?}\n{}", program.source));
            assert!(
                done.lookups > 0 && done.binds > 0,
                "{done:?}\n{}",
                program.source
            );
            total.lookups += done.lookups;
            total.found += done.found;
            total.through_open += done.through_open;
            total.binds += done.binds;
            total.opens += done.opens;
        }
        assert!(total.opens >= 4, "{total:?}");
        assert!(total.through_open >= 4, "{total:?}");
        assert!(total.found >= 20, "{total:?}");
    }

    /// The oracle reports a wrong resolution: with a local binding winning
    /// over a younger opened layer, the lookup of `x` after `open M` differs.
    #[test]
    fn a_wrong_resolution_is_reported() {
        let old = old_checker(&OPEN_SHADOWS_A_LOCAL);
        let mismatch = replay(&old.events, &mut Skewed::default())
            .expect_err("the skewed resolver must differ");
        assert_eq!((mismatch.ns, mismatch.name.as_str()), (Ns::Value, "x"));
        assert_eq!((mismatch.old.len(), mismatch.new.len()), (1, 1));
        assert_ne!(mismatch.old, mismatch.new);
    }

    /// A replay on a hand-written trace: leaving to a common ancestor and
    /// entering a sibling version, an item outside the trace, and `all`.
    #[test]
    fn replay_follows_the_version_tree() {
        let events = vec![
            Event::Version { from: 1, to: 2 },
            Event::Bind {
                env: 2,
                ns: Ns::Value,
                name: "x",
                stamp: 10,
            },
            Event::Version { from: 2, to: 3 },
            Event::Bind {
                env: 3,
                ns: Ns::Value,
                name: "x",
                stamp: 11,
            },
            Event::Version { from: 2, to: 4 },
            Event::Open {
                env: 4,
                members: vec![(Ns::Constructor, "A", 20), (Ns::Constructor, "A", 21)],
            },
            Event::Version { from: 4, to: 5 },
            Event::Bind {
                env: 5,
                ns: Ns::Constructor,
                name: "A",
                stamp: 22,
            },
            Event::Lookup {
                env: 3,
                ns: Ns::Value,
                name: "x".into(),
                all: false,
                found: vec![11],
            },
            Event::Lookup {
                env: 5,
                ns: Ns::Value,
                name: "x".into(),
                all: false,
                found: vec![10],
            },
            Event::Lookup {
                env: 5,
                ns: Ns::Constructor,
                name: "A".into(),
                all: true,
                found: vec![22, 20, 21, 99],
            },
            Event::Lookup {
                env: 2,
                ns: Ns::Type,
                name: "int".into(),
                all: false,
                found: vec![1],
            },
        ];
        let done = replay(&events, &mut Model::default()).unwrap();
        assert_eq!(
            done,
            Replayed {
                lookups: 4,
                found: 3,
                through_open: 0,
                binds: 3,
                opens: 1
            }
        );
        let mut wrong = events.clone();
        wrong[9] = Event::Lookup {
            env: 5,
            ns: Ns::Value,
            name: "x".into(),
            all: false,
            found: vec![11],
        };
        let mismatch = replay(&wrong, &mut Model::default()).unwrap_err();
        assert_eq!(mismatch.event, 9);
        assert_eq!(
            (mismatch.old, mismatch.new),
            (vec!["x/11".to_string()], vec!["x/10".to_string()])
        );
    }
}
