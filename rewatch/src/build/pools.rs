//! The worker pools of in-process builds.
//!
//! A build that compiles many modules wants a worker per core and then some
//! (see [`compile_threads`]), but most of a small incremental build is
//! bookkeeping in short parallel loops, and every loop wakes every worker of
//! the pool it runs in; idle workers then spin before they sleep. With the
//! large pool as the global one, a one-module rebuild of a large project
//! spent more time in those wake-ups than in its own work. So the global
//! pool is small, and the phases that can have a lot of work (parsing, each
//! compile round, recording a large build) run in the large pool when they
//! do ([`pool_for`]).

use std::sync::OnceLock;

/// The stack size of every in-process worker: compiling large modules
/// recurses deeply.
pub const STACK_SIZE: usize = 256 * 1024 * 1024;

/// The global pool's size, unless `RAYON_NUM_THREADS` sets both pools'.
const GLOBAL_THREADS: usize = 4;

fn threads_from_env() -> Option<usize> {
    std::env::var("RAYON_NUM_THREADS")
        .ok()?
        .parse()
        .ok()
        .filter(|threads| *threads > 0)
}

/// The size of the global pool.
pub fn global_threads() -> usize {
    threads_from_env().unwrap_or_else(|| GLOBAL_THREADS.min(compile_threads()))
}

/// The size of the pool compiling many modules.
pub fn compile_threads() -> usize {
    if let Some(threads) = threads_from_env() {
        return threads;
    }
    compile_threads_for(num_cpus::get().max(1), super::qos::efficiency_core_count())
}

/// The compile pool's size on a machine with `logical` cores, of which
/// `efficiency` are efficiency cores.
fn compile_threads_for(logical: usize, efficiency: usize) -> usize {
    // With efficiency cores, more workers than cores cost more than the
    // parked workers described below lose: the extra threads move work that
    // was running on a performance core to an efficiency core, which runs
    // it several times slower. On a 4 + 6 core Apple M4, a worker per core
    // builds a 3,700-module project about 2% faster than 16 workers do, and
    // peaks 11% lower in memory.
    if efficiency > 0 {
        return logical;
    }
    let target = logical.saturating_mul(8).div_ceil(5);
    let scaling_cap = logical.saturating_add(8);
    // In-process compilation publishes signatures before JS is emitted so
    // dependents can type-check early. Those workers can later block before JS
    // while waiting for dependency cmj metadata, so a CPU-sized pool leaves
    // runnable modules stranded behind parked workers. A small oversubscription
    // keeps that overlap, while a scaling cap avoids limiting larger builders
    // to the core count of this development machine.
    target.min(scaling_cap)
}

fn compile_pool() -> &'static rayon::ThreadPool {
    static POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    POOL.get_or_init(|| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(compile_threads())
            .thread_name(|index| format!("rewatch-compile-worker-{index}"))
            .stack_size(STACK_SIZE)
            .build()
            .expect("failed to create the in-process compile pool")
    })
}

/// The pool for `work` items (modules to parse or compile): the large pool
/// when there are more than the global pool keeps busy, `None` for the
/// global pool.
pub fn pool_for(work: usize) -> Option<&'static rayon::ThreadPool> {
    (work > 2 * global_threads() && compile_threads() > global_threads()).then(compile_pool)
}

/// Run `op` in the pool for `work` items (see [`pool_for`]).
pub fn with_pool_for<T: Send>(work: usize, op: impl FnOnce() -> T + Send) -> T {
    match pool_for(work) {
        Some(pool) => pool.install(op),
        None => op(),
    }
}

/// `rayon::in_place_scope` in the pool for `work` items: `op` runs on the
/// calling thread and what it spawns runs in that pool.
pub fn in_place_scope_for<'scope, R>(work: usize, op: impl FnOnce(&rayon::Scope<'scope>) -> R) -> R {
    match pool_for(work) {
        Some(pool) => pool.in_place_scope(op),
        None => rayon::in_place_scope(op),
    }
}

/// The number of threads of the pool for `work` items.
pub fn threads_for(work: usize) -> usize {
    pool_for(work).map_or_else(rayon::current_num_threads, rayon::ThreadPool::current_num_threads)
}

#[cfg(test)]
mod tests {
    use super::compile_threads_for;

    #[test]
    fn cores_of_one_class_are_oversubscribed() {
        assert_eq!(compile_threads_for(1, 0), 2);
        assert_eq!(compile_threads_for(4, 0), 7);
        assert_eq!(compile_threads_for(10, 0), 16);
        // The cap: at most eight workers more than cores.
        assert_eq!(compile_threads_for(64, 0), 72);
    }

    #[test]
    fn efficiency_cores_get_a_worker_per_core() {
        assert_eq!(compile_threads_for(10, 6), 10);
        assert_eq!(compile_threads_for(16, 4), 16);
    }
}
