//! Test-only work counters. No storage or calls are emitted in production.
//!
//! Scopes are thread-local and inclusive: an outer scope counts inner scopes.
//! A panic does not poison future scopes because each takes a fresh baseline.

use std::cell::Cell;

thread_local! {
    static STEPS: Cell<u64> = const { Cell::new(0) };
}

/// O(1): count one test operation on this thread.
pub(crate) fn tick() {
    STEPS.with(|steps| steps.set(steps.get().checked_add(1).expect("step counter overflow")));
}

/// The closure's cost plus O(1); return the inclusive number of ticks it executes.
pub(crate) fn scope(f: impl FnOnce()) -> u64 {
    let before = STEPS.with(Cell::get);
    f();
    STEPS.with(Cell::get) - before
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ten_thousand_steps_nested_scopes_and_thread_isolation() {
        assert_eq!(scope(|| {
            for _ in 0..10000 { tick(); }
            assert_eq!(scope(tick), 1);
            assert_eq!(std::thread::spawn(|| scope(tick)).join().unwrap(), 1);
        }), 10001);
        assert_eq!(scope(|| {}), 0);
        assert!(std::panic::catch_unwind(|| scope(|| { tick(); panic!("test"); })).is_err());
        assert_eq!(scope(tick), 1);
    }
}
