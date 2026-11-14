//! What the old checker's environment did, as a list of events (R4 oracle).
//!
//! `types/env.rs` reports here every new environment version, every binding,
//! every opened layer and every lookup by name. The module exists in builds
//! with debug assertions only: a release build has no call, no thread-local
//! and no branch for it, so the default path costs zero instructions. In a
//! debug build a hook is one thread-local load while no capture is running.
//!
//! The old environment is persistent: an extension makes a new version and
//! leaves the old one usable. A version is named by its id; `Version` says
//! which version an extension started from, and the `Bind` and `Open` events
//! that carry the new id say what it added. The versions of one compilation
//! therefore form a tree, and a lookup names the version it ran in.
//! `tc::scope_oracle` replays that tree on a scope structure with a stack
//! discipline.
//!
//! An item's identity is its namespace, name and stamp: both sides can
//! compute it, the old one from the `Ident`, the replaying one from the
//! number it bound.

use std::cell::{Cell, RefCell};

/// The six tables of `Env` a source name is looked up in
/// (compiler/ml/env.ml:416-431).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(crate) enum Ns {
    Value,
    Type,
    Module,
    ModuleType,
    Constructor,
    Label,
}

/// One member of an opened layer. Members of one namespace and name are
/// listed in candidate order: the one a lookup finds first comes first.
pub(crate) type Member = (Ns, &'static str, i32);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Event {
    /// Version `to` was made by extending version `from`.
    Version { from: u64, to: u64 },
    /// Version `env` added this binding.
    Bind {
        env: u64,
        ns: Ns,
        name: &'static str,
        stamp: i32,
    },
    /// Version `env` added one opened layer with these members.
    Open { env: u64, members: Vec<Member> },
    /// A lookup by name in version `env`. `all` is false for a lookup that
    /// returns the first binding (`found` has at most one stamp) and true for
    /// `TycompTbl.find_all` (every candidate, innermost first).
    Lookup {
        env: u64,
        ns: Ns,
        name: String,
        all: bool,
        found: Vec<i32>,
    },
}

thread_local! {
    static ON: Cell<bool> = const { Cell::new(false) };
    static EVENTS: RefCell<Vec<Event>> = const { RefCell::new(Vec::new()) };
}

/// O(1): whether a capture is running on this thread.
#[inline]
pub(crate) fn on() -> bool {
    ON.with(Cell::get)
}

/// Amortized O(1): append one event. The caller tested [`on`].
pub(crate) fn push(event: Event) {
    EVENTS.with(|events| events.borrow_mut().push(event));
}

/// The closure's cost plus O(events): the events the old environment reports
/// on this thread while `f` runs. Captures do not nest; a panic in `f` leaves
/// the capture off for the next one. Tests only until slice R4h wires the
/// capture into `RESCRIPT_CHECKER=both`.
#[cfg(test)]
pub(crate) fn capture<R>(f: impl FnOnce() -> R) -> (R, Vec<Event>) {
    struct Off;
    impl Drop for Off {
        fn drop(&mut self) {
            ON.with(|on| on.set(false));
        }
    }
    assert!(!on(), "scope trace captures do not nest");
    EVENTS.with(|events| events.borrow_mut().clear());
    ON.with(|on| on.set(true));
    let off = Off;
    let result = f();
    drop(off);
    (
        result,
        EVENTS.with(|events| std::mem::take(&mut *events.borrow_mut())),
    )
}
