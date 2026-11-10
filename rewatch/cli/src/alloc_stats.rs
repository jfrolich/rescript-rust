//! Allocation statistics, compiled in only with `--features alloc-stats`.
//!
//! [`CountingAlloc`] wraps mimalloc and counts every allocation. Two
//! environment variables read it out (see `scripts/perf/README.md`):
//!
//! * `RESCRIPT_ALLOC_COUNT=1` prints the totals and a size histogram to
//!   stderr when the process exits normally.
//! * `RESCRIPT_ALLOC_SITES=<file>` captures a backtrace for every 8192nd
//!   allocation of each thread and writes them to `<file>` at exit, for
//!   `scripts/perf/alloc_sites.py` to summarize.
//!
//! Counts are kept per thread and flushed to the shared totals every 4096
//! events, so the report misses at most that many events per live worker
//! thread (well under 0.1% of a project build).

use std::alloc::{GlobalAlloc, Layout};
use std::backtrace::Backtrace;
use std::cell::Cell;
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};

use mimalloc::MiMalloc;

/// Size buckets: `<= 8 B`, `<= 16 B`, ... doubling up to `<= 256 KiB`; the
/// last bucket also takes everything larger.
const BUCKETS: usize = 16;
const BYTES: usize = BUCKETS;
const FREES: usize = BUCKETS + 1;
const EVENTS: usize = BUCKETS + 2;
const FLUSH_EVERY: u64 = 4096;
/// Sample one allocation in `SAMPLE_MASK + 1` per thread.
const SAMPLE_MASK: u32 = 8191;

static TOTAL_BUCKETS: [AtomicU64; BUCKETS] = [const { AtomicU64::new(0) }; BUCKETS];
static TOTAL_BYTES: AtomicU64 = AtomicU64::new(0);
static TOTAL_FREES: AtomicU64 = AtomicU64::new(0);
static TOTAL_REALLOCS: AtomicU64 = AtomicU64::new(0);

static SAMPLING: AtomicBool = AtomicBool::new(false);
static SAMPLES: Mutex<Vec<(usize, Backtrace)>> = Mutex::new(Vec::new());

thread_local! {
    /// Unflushed counts: the buckets, then bytes, frees and the event count.
    /// A `Cell` of plain integers needs no destructor, so touching it from
    /// inside the allocator never registers one (which could allocate).
    static LOCAL: Cell<[u64; BUCKETS + 3]> = const { Cell::new([0; BUCKETS + 3]) };
    static SAMPLE_TICK: Cell<u32> = const { Cell::new(0) };
    /// Set while this thread captures a backtrace, whose own allocations
    /// must not be sampled again.
    static IN_SAMPLE: Cell<bool> = const { Cell::new(false) };
}

pub struct CountingAlloc;

// SAFETY: every method forwards to mimalloc with the caller's arguments
// unchanged, so mimalloc's `GlobalAlloc` guarantees carry over. The
// bookkeeping around the calls only touches atomics and thread-local `Cell`s
// (via `try_with`, so it is skipped during thread teardown) and never hands
// out or frees memory itself. `GlobalAlloc` is an `unsafe` trait, so this
// `unsafe impl` cannot be avoided.
unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record_alloc(layout.size());
        // SAFETY: forwarded unchanged; see the impl comment.
        unsafe { MiMalloc.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        record_alloc(layout.size());
        // SAFETY: forwarded unchanged; see the impl comment.
        unsafe { MiMalloc.alloc_zeroed(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        bump(FREES, 1);
        // SAFETY: forwarded unchanged; see the impl comment.
        unsafe { MiMalloc.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        TOTAL_REALLOCS.fetch_add(1, Relaxed);
        // SAFETY: forwarded unchanged; see the impl comment.
        unsafe { MiMalloc.realloc(ptr, layout, new_size) }
    }
}

fn bucket(size: usize) -> usize {
    if size <= 8 {
        0
    } else {
        // ceil(log2(size)) - 3, so 9..=16 B lands in bucket 1.
        ((usize::BITS - (size - 1).leading_zeros()) as usize - 3).min(BUCKETS - 1)
    }
}

#[inline]
fn record_alloc(size: usize) {
    maybe_sample(size);
    bump(bucket(size), 1);
    bump(BYTES, size as u64);
}

#[inline]
fn bump(slot: usize, n: u64) {
    // `try_with` fails only while the thread's locals are being destroyed;
    // those few events go uncounted.
    LOCAL
        .try_with(|cell| {
            let mut counts = cell.get();
            counts[slot] += n;
            counts[EVENTS] += 1;
            if counts[EVENTS] >= FLUSH_EVERY {
                flush(&mut counts);
            }
            cell.set(counts);
        })
        .ok();
}

fn flush(counts: &mut [u64; BUCKETS + 3]) {
    for (total, &n) in TOTAL_BUCKETS.iter().zip(&counts[..BUCKETS]) {
        if n > 0 {
            total.fetch_add(n, Relaxed);
        }
    }
    TOTAL_BYTES.fetch_add(counts[BYTES], Relaxed);
    TOTAL_FREES.fetch_add(counts[FREES], Relaxed);
    *counts = [0; BUCKETS + 3];
}

#[inline]
fn maybe_sample(size: usize) {
    if !SAMPLING.load(Relaxed) {
        return;
    }
    let hit = SAMPLE_TICK
        .try_with(|tick| {
            let next = tick.get().wrapping_add(1);
            tick.set(next);
            next & SAMPLE_MASK == 0
        })
        .unwrap_or(false);
    // `replace(true)` returning true means this thread is already sampling.
    if !hit || IN_SAMPLE.try_with(|busy| busy.replace(true)).unwrap_or(true) {
        return;
    }
    let backtrace = Backtrace::force_capture();
    if let Ok(mut samples) = SAMPLES.lock() {
        samples.push((size, backtrace));
    }
    IN_SAMPLE.try_with(|busy| busy.set(false)).ok();
}

/// Starts sampling allocation sites if `RESCRIPT_ALLOC_SITES` is set. Call
/// first thing in `main`.
pub fn start() {
    if std::env::var_os("RESCRIPT_ALLOC_SITES").is_some() {
        SAMPLING.store(true, Relaxed);
    }
}

/// Writes the reports the environment asks for. Call right before the
/// process exits.
pub fn finish() {
    if std::env::var_os("RESCRIPT_ALLOC_COUNT").is_some() {
        report_totals();
    }
    if let Some(path) = std::env::var_os("RESCRIPT_ALLOC_SITES") {
        write_samples(Path::new(&path));
    }
}

fn report_totals() {
    LOCAL
        .try_with(|cell| {
            let mut counts = cell.get();
            flush(&mut counts);
            cell.set(counts);
        })
        .ok();
    let buckets: Vec<u64> = TOTAL_BUCKETS.iter().map(|n| n.load(Relaxed)).collect();
    let total: u64 = buckets.iter().sum();
    eprintln!(
        "ALLOCS total={} bytes={} frees={} reallocs={}",
        total,
        TOTAL_BYTES.load(Relaxed),
        TOTAL_FREES.load(Relaxed),
        TOTAL_REALLOCS.load(Relaxed)
    );
    for (i, n) in buckets.iter().enumerate() {
        eprintln!("ALLOCS <= {} B: {}", 8usize << i, n);
    }
}

fn write_samples(path: &Path) {
    SAMPLING.store(false, Relaxed);
    let samples = std::mem::take(&mut *SAMPLES.lock().unwrap_or_else(|err| err.into_inner()));
    let mut out = String::new();
    for (size, backtrace) in samples {
        out.push_str(&format!("@@SAMPLE {size}\n{backtrace}\n"));
    }
    if let Err(err) = std::fs::write(path, out) {
        eprintln!("RESCRIPT_ALLOC_SITES: cannot write {}: {err}", path.display());
    }
}
