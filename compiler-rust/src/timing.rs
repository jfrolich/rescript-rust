//! Optional aggregate compiler phase timings.
//!
//! Timings are disabled unless one of the compiler timing environment flags is
//! present. The aggregate counters are process-global so rewatch can report
//! total work across all modules, while optional thread-local counters let one
//! worker report timings for a single module without parallel-worker pollution.

use std::cell::RefCell;
#[cfg(not(target_arch = "wasm32"))]
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

/// Compiler phase buckets reported by the in-process build.
#[derive(Clone, Copy)]
#[repr(usize)]
pub enum Phase {
    /// Source read, parsing, PPX rewriting, and dependency extraction.
    Parse,
    /// Per-module type context, initial environment, persistent-environment
    /// view and implicit opens (`Pervasives`, `Stdlib`, `-open` modules).
    EnvSetup,
    /// Type checking into typedtree.
    Typecheck,
    /// Inferred-signature registration, current-unit raw signature copy and
    /// portable signature extraction for in-process publication.
    SignaturePublish,
    /// Typedtree to raw lambda and raw lambda to lambda lowering.
    Lambda,
    /// Lambda simplification before JavaScript IR generation.
    LambdaOptimization,
    /// GenType generation from the already-typed artifact.
    Gentype,
    /// JavaScript IR generation and JavaScript text rendering.
    Codegen,
    /// GenType child buckets. They are reported separately, not added again
    /// to the top-level recorded total. Counts are artifact-phase invocations.
    GentypePrepare,
    /// Typed-artifact annotation discovery.
    GentypeAnnotations,
    /// Translation of the declaration cache input.
    GentypeDeclarations,
    /// Conversion of declaration locations to portable handles.
    GentypePortable,
    /// Encoding translated declarations for the cache/store.
    GentypeEncoding,
    /// Translation and text generation for an annotated artifact.
    GentypeEmission,
    /// Output file writes, no-match removal checks, and deletions.
    GentypeFiles,
    /// Annotated output: compare existing contents and write when needed.
    GentypeFileWrite,
    /// Unannotated output: check for and remove an obsolete generated file.
    GentypeFileNoMatch,
}

impl Phase {
    const COUNT: usize = Phase::GentypeFileNoMatch as usize + 1;
}

/// Nanoseconds per phase, indexed by `Phase as usize`.
type PhaseNanos = [u64; Phase::COUNT];

impl PhaseTimingSnapshot {
    fn from_nanos(total: Duration, nanos: PhaseNanos) -> Self {
        let phase = |phase: Phase| Duration::from_nanos(nanos[phase as usize]);
        PhaseTimingSnapshot {
            total,
            parse: phase(Phase::Parse),
            env_setup: phase(Phase::EnvSetup),
            typecheck: phase(Phase::Typecheck),
            signature_publish: phase(Phase::SignaturePublish),
            lambda: phase(Phase::Lambda),
            lambda_optimization: phase(Phase::LambdaOptimization),
            gentype: phase(Phase::Gentype),
            codegen: phase(Phase::Codegen),
        }
    }
}

/// Snapshot of aggregate phase timings.
#[derive(Clone, Copy, Debug, Default)]
pub struct PhaseTimingSnapshot {
    /// Total wall time since [`reset`] was called.
    pub total: Duration,
    /// Aggregate parse phase time.
    pub parse: Duration,
    /// Aggregate per-module environment setup time.
    pub env_setup: Duration,
    /// Aggregate typecheck phase time.
    pub typecheck: Duration,
    /// Aggregate signature publication time.
    pub signature_publish: Duration,
    /// Aggregate lambda phase time.
    pub lambda: Duration,
    /// Aggregate lambda optimization phase time.
    pub lambda_optimization: Duration,
    /// Aggregate GenType generation phase time.
    pub gentype: Duration,
    /// Aggregate codegen phase time.
    pub codegen: Duration,
}

impl PhaseTimingSnapshot {
    /// Sum of all explicitly recorded phase buckets.
    pub fn recorded(self) -> Duration {
        self.parse
            .saturating_add(self.env_setup)
            .saturating_add(self.typecheck)
            .saturating_add(self.signature_publish)
            .saturating_add(self.lambda)
            .saturating_add(self.lambda_optimization)
            .saturating_add(self.gentype)
            .saturating_add(self.codegen)
    }

    /// Wall time that was not attributed to an explicit phase bucket.
    pub fn overhead(self) -> Duration {
        self.total.saturating_sub(self.recorded())
    }
}

#[cfg(not(target_arch = "wasm32"))]
static ENABLED: OnceLock<std::sync::atomic::AtomicBool> = OnceLock::new();
/// Aggregate nanoseconds per phase, indexed by `Phase as usize`.
static PHASE_NS: [AtomicU64; Phase::COUNT] = [const { AtomicU64::new(0) }; Phase::COUNT];
static PHASE_COUNT: [AtomicU64; Phase::COUNT] = [const { AtomicU64::new(0) }; Phase::COUNT];

thread_local! {
    static THREAD_TIMINGS: RefCell<Option<ThreadPhaseCounters>> = const { RefCell::new(None) };
}

#[derive(Clone, Copy, Debug, Default)]
struct ThreadPhaseCounters(PhaseNanos);

impl ThreadPhaseCounters {
    fn record(&mut self, phase: Phase, nanos: u64) {
        let slot = &mut self.0[phase as usize];
        *slot = slot.saturating_add(nanos);
    }

    fn snapshot(self) -> PhaseTimingSnapshot {
        PhaseTimingSnapshot::from_nanos(Duration::default(), self.0)
    }
}

/// Thread-local timing scope for one worker-owned compilation unit.
pub struct ThreadTimingGuard {
    active: bool,
    previous: Option<ThreadPhaseCounters>,
}

impl ThreadTimingGuard {
    /// Start collecting thread-local phase timings for the current thread.
    pub fn start() -> Self {
        let active = enabled();
        let previous = if active {
            THREAD_TIMINGS.with(|timings| timings.replace(Some(ThreadPhaseCounters::default())))
        } else { None };
        Self { active, previous }
    }

    /// Return the phase timings recorded on this thread since the guard started.
    pub fn snapshot(&self) -> PhaseTimingSnapshot {
        if !self.active {
            return PhaseTimingSnapshot::default();
        }

        THREAD_TIMINGS.with(|timings| {
            timings
                .borrow()
                .as_ref()
                .copied()
                .map(ThreadPhaseCounters::snapshot)
                .unwrap_or_default()
        })
    }
}

impl Drop for ThreadTimingGuard {
    fn drop(&mut self) {
        if self.active {
            THREAD_TIMINGS.with(|timings| {
                let mut current = timings.borrow_mut();
                if let (Some(previous), Some(child)) = (&mut self.previous, current.as_ref()) {
                    for (parent, child) in previous.0.iter_mut().zip(child.0) {
                        *parent += child;
                    }
                }
                *current = self.previous.take();
            });
        }
    }
}

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

/// Enable existing phase timers when the compiler options request a census.
/// O(1), once at option creation; no added test in the disabled hot path.
pub fn enable_for_census() {
    #[cfg(not(target_arch = "wasm32"))]
    { ENABLED.get_or_init(|| std::sync::atomic::AtomicBool::new(true)).store(true, Ordering::Relaxed); }
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
        ENABLED.get_or_init(|| std::sync::atomic::AtomicBool::new(
            std::env::var_os("RESCRIPT_PHASE_TIMINGS").is_some()
                || std::env::var_os("RESCRIPT_MODULE_TIMINGS").is_some()
                || std::env::var_os("RESCRIPT_RUNTIME_TIMINGS").is_some()
        )).load(Ordering::Relaxed)
    }
}

/// Reset all phase counters and start a new wall-clock measurement window.
pub fn reset() {
    if !enabled() {
        return;
    }

    for counter in PHASE_NS.iter().chain(PHASE_COUNT.iter()) {
        counter.store(0, Ordering::Relaxed);
    }

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
    PHASE_NS[phase as usize].fetch_add(nanos, Ordering::Relaxed);
    if phase as usize > Phase::Codegen as usize {
        PHASE_COUNT[phase as usize].fetch_add(1, Ordering::Relaxed);
    }
    THREAD_TIMINGS.with(|timings| {
        if let Some(thread_timings) = timings.borrow_mut().as_mut() {
            thread_timings.record(phase, nanos);
        }
    });
}

/// Measure a closure and add its elapsed time to the selected phase.
#[inline]
pub fn measure<T>(phase: Phase, f: impl FnOnce() -> T) -> T {
    #[cfg(target_arch = "wasm32")]
    {
        // Timing is never enabled on wasm.
        let _ = phase;
        f()
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        if !enabled() {
            return f();
        }
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

    let total = {
        #[cfg(target_arch = "wasm32")]
        {
            Duration::default()
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            clock::elapsed()
        }
    };
    PhaseTimingSnapshot::from_nanos(
        total,
        std::array::from_fn(|index| PHASE_NS[index].load(Ordering::Relaxed)),
    )
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
    print_phase("env_setup", snapshot.env_setup, total);
    print_phase("typecheck", snapshot.typecheck, total);
    print_phase("signature_publish", snapshot.signature_publish, total);
    print_phase("lambda", snapshot.lambda, total);
    print_phase("lambda_optimization", snapshot.lambda_optimization, total);
    print_phase("gentype", snapshot.gentype, total);
    print_phase("codegen", snapshot.codegen, total);
    print_phase("overhead", snapshot.overhead(), total);
    for (name, phase) in [
        ("gentype_prepare", Phase::GentypePrepare),
        ("gentype_annotations", Phase::GentypeAnnotations),
        ("gentype_declarations", Phase::GentypeDeclarations),
        ("gentype_portable", Phase::GentypePortable),
        ("gentype_encoding", Phase::GentypeEncoding),
        ("gentype_emission", Phase::GentypeEmission),
        ("gentype_files", Phase::GentypeFiles),
        ("gentype_file_write", Phase::GentypeFileWrite),
        ("gentype_file_no_match", Phase::GentypeFileNoMatch),
    ] {
        eprintln!("[phase-timing] phase={} ms={:.3} artifacts={}", name,
            ms(Duration::from_nanos(PHASE_NS[phase as usize].load(Ordering::Relaxed))),
            PHASE_COUNT[phase as usize].load(Ordering::Relaxed));
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gentype_children_do_not_inflate_recorded_time() {
        let mut nanos = [0; Phase::COUNT];
        nanos[Phase::Gentype as usize] = 100;
        nanos[Phase::GentypeDeclarations as usize] = 70;
        nanos[Phase::GentypeEmission as usize] = 30;
        nanos[Phase::GentypeFiles as usize] = 20;
        nanos[Phase::GentypeFileWrite as usize] = 18;
        nanos[Phase::GentypeFileNoMatch as usize] = 2;
        let snapshot = PhaseTimingSnapshot::from_nanos(Duration::from_nanos(110), nanos);
        assert_eq!(snapshot.recorded(), Duration::from_nanos(100));
        assert_eq!(snapshot.overhead(), Duration::from_nanos(10));
    }
}
