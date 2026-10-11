//! Contention-free seeds for `ahash::RandomState`.
//!
//! ahash's default seed source is one process-wide atomic counter that every
//! `RandomState::new()` (every `AHashMap`/`AHashSet` construction) bumps. The
//! compiler creates many short-lived maps per module, so parallel workers
//! contend on that cache line. A thread-local counter keeps seeds distinct per
//! map without sharing state between threads.

use std::cell::Cell;

struct ThreadLocalSeedSource;

thread_local! {
    static NEXT_SEED: Cell<usize> = const { Cell::new(0) };
}

impl ahash::random_state::RandomSource for ThreadLocalSeedSource {
    fn gen_hasher_seed(&self) -> usize {
        NEXT_SEED.with(|next| {
            let mut seed = next.get();
            if seed == 0 {
                // Distinct starting point per thread, like ahash's default
                // source which mixes in a stack address.
                seed = &seed as *const usize as usize;
            }
            let step = &seed as *const usize as usize | 1;
            next.set(seed.wrapping_add(step));
            seed
        })
    }
}

/// Install the thread-local seed source. Call once at process start, before
/// any `ahash::RandomState` is created; later calls are ignored.
pub fn install_thread_local_hash_seeds() {
    let _ = ahash::random_state::set_random_source(ThreadLocalSeedSource);
}
