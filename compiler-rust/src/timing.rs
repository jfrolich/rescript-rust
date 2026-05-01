//! Optional aggregate compiler phase timings.
//!
//! Timings are disabled unless `RESCRIPT_PHASE_TIMINGS` is present in the
//! environment. The counters are process-global so rewatch can aggregate
//! timings across all modules compiled during one build.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

/// Compiler phase buckets reported by the in-process build.
#[derive(Clone, Copy)]
pub enum Phase {
    /// Source read, parsing, PPX rewriting, and dependency extraction.
    Parse,
    /// Type checking into typedtree.
    Typecheck,
    /// Typedtree to raw lambda and raw lambda to lambda lowering.
    Lambda,
    /// Lambda simplification before JavaScript IR generation.
    LambdaOptimization,
    /// JavaScript IR generation and JavaScript text rendering.
    Codegen,
}

/// Snapshot of aggregate phase timings.
#[derive(Clone, Copy, Debug, Default)]
pub struct PhaseTimingSnapshot {
    /// Total wall time since [`reset`] was called.
    pub total: Duration,
    /// Aggregate parse phase time.
    pub parse: Duration,
    /// Aggregate typecheck phase time.
    pub typecheck: Duration,
    /// Aggregate lambda phase time.
    pub lambda: Duration,
    /// Aggregate lambda optimization phase time.
    pub lambda_optimization: Duration,
    /// Aggregate codegen phase time.
    pub codegen: Duration,
}

impl PhaseTimingSnapshot {
    /// Sum of all explicitly recorded phase buckets.
    pub fn recorded(self) -> Duration {
        self.parse
            .saturating_add(self.typecheck)
            .saturating_add(self.lambda)
            .saturating_add(self.lambda_optimization)
            .saturating_add(self.codegen)
    }

    /// Wall time that was not attributed to an explicit phase bucket.
    pub fn overhead(self) -> Duration {
        self.total.saturating_sub(self.recorded())
    }
}

static ENABLED: OnceLock<bool> = OnceLock::new();
static PARSE_NS: AtomicU64 = AtomicU64::new(0);
static TYPECHECK_NS: AtomicU64 = AtomicU64::new(0);
static LAMBDA_NS: AtomicU64 = AtomicU64::new(0);
static LAMBDA_OPT_NS: AtomicU64 = AtomicU64::new(0);
static CODEGEN_NS: AtomicU64 = AtomicU64::new(0);

#[cfg(not(target_arch = "wasm32"))]
mod clock {
    use std::sync::Mutex;
    use std::time::Instant;

    pub(super) static START: Mutex<Option<Instant>> = Mutex::new(None);

    pub(super) fn reset_start() {
        *START.lock().expect("phase timing start lock poisoned") = Some(Instant::now());
    }

    pub(super) fn elapsed() -> std::time::Duration {
        START
            .lock()
            .expect("phase timing start lock poisoned")
            .map(|start| start.elapsed())
            .unwrap_or_default()
    }

    pub(super) fn now() -> Instant {
        Instant::now()
    }
}

/// Returns whether aggregate phase timing is enabled.
#[inline]
pub fn enabled() -> bool {
    #[cfg(target_arch = "wasm32")]
    {
        false
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        *ENABLED.get_or_init(|| std::env::var_os("RESCRIPT_PHASE_TIMINGS").is_some())
    }
}

/// Reset all phase counters and start a new wall-clock measurement window.
pub fn reset() {
    if !enabled() {
        return;
    }

    PARSE_NS.store(0, Ordering::Relaxed);
    TYPECHECK_NS.store(0, Ordering::Relaxed);
    LAMBDA_NS.store(0, Ordering::Relaxed);
    LAMBDA_OPT_NS.store(0, Ordering::Relaxed);
    CODEGEN_NS.store(0, Ordering::Relaxed);

    #[cfg(not(target_arch = "wasm32"))]
    clock::reset_start();
}

/// Record elapsed time for one phase.
#[inline]
pub fn record(phase: Phase, duration: Duration) {
    if !enabled() {
        return;
    }

    let nanos = duration.as_nanos().min(u64::MAX as u128) as u64;
    match phase {
        Phase::Parse => PARSE_NS.fetch_add(nanos, Ordering::Relaxed),
        Phase::Typecheck => TYPECHECK_NS.fetch_add(nanos, Ordering::Relaxed),
        Phase::Lambda => LAMBDA_NS.fetch_add(nanos, Ordering::Relaxed),
        Phase::LambdaOptimization => LAMBDA_OPT_NS.fetch_add(nanos, Ordering::Relaxed),
        Phase::Codegen => CODEGEN_NS.fetch_add(nanos, Ordering::Relaxed),
    };
}

/// Measure a closure and add its elapsed time to the selected phase.
#[inline]
pub fn measure<T>(phase: Phase, f: impl FnOnce() -> T) -> T {
    if !enabled() {
        return f();
    }

    #[cfg(target_arch = "wasm32")]
    {
        f()
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        let start = clock::now();
        let result = f();
        record(phase, start.elapsed());
        result
    }
}

/// Return the current aggregate phase timing snapshot.
pub fn snapshot() -> PhaseTimingSnapshot {
    if !enabled() {
        return PhaseTimingSnapshot::default();
    }

    PhaseTimingSnapshot {
        total: {
            #[cfg(target_arch = "wasm32")]
            {
                Duration::default()
            }
            #[cfg(not(target_arch = "wasm32"))]
            {
                clock::elapsed()
            }
        },
        parse: Duration::from_nanos(PARSE_NS.load(Ordering::Relaxed)),
        typecheck: Duration::from_nanos(TYPECHECK_NS.load(Ordering::Relaxed)),
        lambda: Duration::from_nanos(LAMBDA_NS.load(Ordering::Relaxed)),
        lambda_optimization: Duration::from_nanos(LAMBDA_OPT_NS.load(Ordering::Relaxed)),
        codegen: Duration::from_nanos(CODEGEN_NS.load(Ordering::Relaxed)),
    }
}

/// Print aggregate phase timings to stderr.
pub fn print_report() {
    if !enabled() {
        return;
    }

    let snapshot = snapshot();
    let total = snapshot.total;
    eprintln!(
        "[phase-timing] total_ms={:.3} recorded_ms={:.3} overhead_ms={:.3}",
        ms(total),
        ms(snapshot.recorded()),
        ms(snapshot.overhead())
    );
    print_phase("parse", snapshot.parse, total);
    print_phase("typecheck", snapshot.typecheck, total);
    print_phase("lambda", snapshot.lambda, total);
    print_phase("lambda_optimization", snapshot.lambda_optimization, total);
    print_phase("codegen", snapshot.codegen, total);
    print_phase("overhead", snapshot.overhead(), total);
}

fn print_phase(name: &str, duration: Duration, total: Duration) {
    eprintln!(
        "[phase-timing] phase={} ms={:.3} pct={:.2}",
        name,
        ms(duration),
        pct(duration, total)
    );
}

fn ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn pct(duration: Duration, total: Duration) -> f64 {
    if total.is_zero() {
        0.0
    } else {
        duration.as_secs_f64() * 100.0 / total.as_secs_f64()
    }
}
