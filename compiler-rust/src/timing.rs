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
    /// Digests prepared for the next process, concurrently with compilation.
    RecordDigests,
    /// Stored-interface encoding prepared for the next process.
    RecordInterfaces,
    /// Package record construction, encoding and SQLite persistence.
    RecordWrite,
    /// Detailed persistence subphase: MetaRows.
    RecordMetaRows,
    /// Detailed persistence subphase: InterfaceRows.
    RecordInterfaceRows,
    /// Detailed persistence subphase: ModuleRows.
    RecordModuleRows,
    /// Detailed persistence subphase: SourceRows.
    RecordSourceRows,
    /// Detailed persistence subphase: DependencyRows.
    RecordDependencyRows,
    /// Detailed persistence subphase: WarningRows.
    RecordWarningRows,
    /// Detailed persistence subphase: ReadRows.
    RecordReadRows,
    /// Detailed persistence subphase: ImportRows.
    RecordImportRows,
    /// Detailed persistence subphase: ItemRows.
    RecordItemRows,
    /// Detailed persistence subphase: ReadsEncode.
    RecordReadsEncode,
    /// Detailed persistence subphase: ItemsEncode.
    RecordItemsEncode,
    /// Detailed persistence subphase: ImportsEncode.
    RecordImportsEncode,
    /// Detailed persistence subphase: DepsEncode.
    RecordDepsEncode,
    /// Detailed persistence subphase: SqlOpen.
    RecordSqlOpen,
    /// Detailed persistence subphase: SqlMeta.
    RecordSqlMeta,
    /// Detailed persistence subphase: SqlSources.
    RecordSqlSources,
    /// Detailed persistence subphase: SqlReads.
    RecordSqlReads,
    /// Detailed persistence subphase: SqlItems.
    RecordSqlItems,
    /// Detailed persistence subphase: SqlInterfaces.
    RecordSqlInterfaces,
    /// Detailed persistence subphase: SqlModules.
    RecordSqlModules,
    /// Detailed persistence subphase: SqlWarnings.
    RecordSqlWarnings,
    /// Detailed persistence subphase: SqlDeps.
    RecordSqlDeps,
    /// Detailed persistence subphase: SqlCommit.
    RecordSqlCommit,
    /// Whole-record publication: rename.
    RecordRename,
    /// Whole-record publication: recover.
    RecordRecover,
    /// Whole-record publication: publish lock.
    RecordPublishLock,
    /// Whole-record preparation: progressive commit.
    RecordBatchCommit,
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
            record_digests: phase(Phase::RecordDigests),
            record_interfaces: phase(Phase::RecordInterfaces),
            record_write: phase(Phase::RecordWrite),
            record_meta_rows: phase(Phase::RecordMetaRows),
            record_interface_rows: phase(Phase::RecordInterfaceRows),
            record_module_rows: phase(Phase::RecordModuleRows),
            record_source_rows: phase(Phase::RecordSourceRows),
            record_dependency_rows: phase(Phase::RecordDependencyRows),
            record_warning_rows: phase(Phase::RecordWarningRows),
            record_read_rows: phase(Phase::RecordReadRows),
            record_import_rows: phase(Phase::RecordImportRows),
            record_item_rows: phase(Phase::RecordItemRows),
            record_reads_encode: phase(Phase::RecordReadsEncode),
            record_items_encode: phase(Phase::RecordItemsEncode),
            record_imports_encode: phase(Phase::RecordImportsEncode),
            record_deps_encode: phase(Phase::RecordDepsEncode),
            record_sql_open: phase(Phase::RecordSqlOpen),
            record_sql_meta: phase(Phase::RecordSqlMeta),
            record_sql_sources: phase(Phase::RecordSqlSources),
            record_sql_reads: phase(Phase::RecordSqlReads),
            record_sql_items: phase(Phase::RecordSqlItems),
            record_sql_interfaces: phase(Phase::RecordSqlInterfaces),
            record_sql_modules: phase(Phase::RecordSqlModules),
            record_sql_warnings: phase(Phase::RecordSqlWarnings),
            record_sql_deps: phase(Phase::RecordSqlDeps),
            record_sql_commit: phase(Phase::RecordSqlCommit),
            record_rename: phase(Phase::RecordRename),
            record_recover: phase(Phase::RecordRecover),
            record_publish_lock: phase(Phase::RecordPublishLock),
            record_batch_commit: phase(Phase::RecordBatchCommit),

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
    /// Aggregate next-process digest preparation time.
    pub record_digests: Duration,
    /// Aggregate stored-interface encoding time.
    pub record_interfaces: Duration,
    /// Aggregate package-record construction and persistence time.
    pub record_write: Duration,
    /// Detailed persistence subphase (MetaRows); nested in record_write.
    pub record_meta_rows: Duration,
    /// Detailed persistence subphase (InterfaceRows); nested in record_write.
    pub record_interface_rows: Duration,
    /// Detailed persistence subphase (ModuleRows); nested in record_write.
    pub record_module_rows: Duration,
    /// Detailed persistence subphase (SourceRows); nested in record_write.
    pub record_source_rows: Duration,
    /// Detailed persistence subphase (DependencyRows); nested in record_write.
    pub record_dependency_rows: Duration,
    /// Detailed persistence subphase (WarningRows); nested in record_write.
    pub record_warning_rows: Duration,
    /// Detailed persistence subphase (ReadRows); nested in record_write.
    pub record_read_rows: Duration,
    /// Detailed persistence subphase (ImportRows); nested in record_write.
    pub record_import_rows: Duration,
    /// Detailed persistence subphase (ItemRows); nested in record_write.
    pub record_item_rows: Duration,
    /// Detailed persistence subphase (ReadsEncode); nested in record_write.
    pub record_reads_encode: Duration,
    /// Detailed persistence subphase (ItemsEncode); nested in record_write.
    pub record_items_encode: Duration,
    /// Detailed persistence subphase (ImportsEncode); nested in record_write.
    pub record_imports_encode: Duration,
    /// Detailed persistence subphase (DepsEncode); nested in record_write.
    pub record_deps_encode: Duration,
    /// Detailed persistence subphase (SqlOpen); nested in record_write.
    pub record_sql_open: Duration,
    /// Detailed persistence subphase (SqlMeta); nested in record_write.
    pub record_sql_meta: Duration,
    /// Detailed persistence subphase (SqlSources); nested in record_write.
    pub record_sql_sources: Duration,
    /// Detailed persistence subphase (SqlReads); nested in record_write.
    pub record_sql_reads: Duration,
    /// Detailed persistence subphase (SqlItems); nested in record_write.
    pub record_sql_items: Duration,
    /// Detailed persistence subphase (SqlInterfaces); nested in record_write.
    pub record_sql_interfaces: Duration,
    /// Detailed persistence subphase (SqlModules); nested in record_write.
    pub record_sql_modules: Duration,
    /// Detailed persistence subphase (SqlWarnings); nested in record_write.
    pub record_sql_warnings: Duration,
    /// Detailed persistence subphase (SqlDeps); nested in record_write.
    pub record_sql_deps: Duration,
    /// Detailed persistence subphase (SqlCommit); nested in record_write.
    pub record_sql_commit: Duration,
    /// Whole-record publication: rename.
    pub record_rename: Duration,
    /// Whole-record publication: recover.
    pub record_recover: Duration,
    /// Whole-record publication: publish lock.
    pub record_publish_lock: Duration,
    /// Whole-record preparation: progressive commit.
    pub record_batch_commit: Duration,

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
            .saturating_add(self.record_digests)
            .saturating_add(self.record_interfaces)
            .saturating_add(self.record_write)
    }

    /// Wall time that was not attributed to an explicit phase bucket.
    pub fn overhead(self) -> Duration {
        self.total.saturating_sub(self.recorded())
    }
}

#[cfg(not(target_arch = "wasm32"))]
static ENABLED: OnceLock<bool> = OnceLock::new();
/// Aggregate nanoseconds per phase, indexed by `Phase as usize`.
static PHASE_NS: [AtomicU64; Phase::COUNT] = [const { AtomicU64::new(0) }; Phase::COUNT];
static PHASE_COUNT: [AtomicU64; Phase::COUNT] = [const { AtomicU64::new(0) }; Phase::COUNT];

thread_local! {
    static THREAD_TIMINGS: RefCell<Option<ThreadPhaseCounters>> = const { RefCell::new(None) };
}

#[derive(Clone, Copy, Debug)]
struct ThreadPhaseCounters(PhaseNanos);

impl Default for ThreadPhaseCounters {
    fn default() -> Self {
        Self([0; Phase::COUNT])
    }
}

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
}

impl ThreadTimingGuard {
    /// Start collecting thread-local phase timings for the current thread.
    pub fn start() -> Self {
        let active = enabled();
        if active {
            THREAD_TIMINGS.with(|timings| {
                *timings.borrow_mut() = Some(ThreadPhaseCounters::default());
            });
        }
        Self { active }
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
                *timings.borrow_mut() = None;
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

/// Returns whether aggregate phase timing is enabled.
#[inline]
pub fn enabled() -> bool {
    #[cfg(target_arch = "wasm32")]
    {
        false
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        *ENABLED.get_or_init(|| {
            std::env::var_os("RESCRIPT_PHASE_TIMINGS").is_some()
                || std::env::var_os("RESCRIPT_MODULE_TIMINGS").is_some()
                || std::env::var_os("RESCRIPT_RUNTIME_TIMINGS").is_some()
        })
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
    print_phase("record_digests", snapshot.record_digests, total);
    print_phase("record_interfaces", snapshot.record_interfaces, total);
    print_phase("record_write", snapshot.record_write, total);
    print_phase("record_meta_rows", snapshot.record_meta_rows, total);
    print_phase("record_interface_rows", snapshot.record_interface_rows, total);
    print_phase("record_module_rows", snapshot.record_module_rows, total);
    print_phase("record_source_rows", snapshot.record_source_rows, total);
    print_phase("record_dependency_rows", snapshot.record_dependency_rows, total);
    print_phase("record_warning_rows", snapshot.record_warning_rows, total);
    print_phase("record_read_rows", snapshot.record_read_rows, total);
    print_phase("record_import_rows", snapshot.record_import_rows, total);
    print_phase("record_item_rows", snapshot.record_item_rows, total);
    print_phase("record_reads_encode", snapshot.record_reads_encode, total);
    print_phase("record_items_encode", snapshot.record_items_encode, total);
    print_phase("record_imports_encode", snapshot.record_imports_encode, total);
    print_phase("record_deps_encode", snapshot.record_deps_encode, total);
    print_phase("record_sql_open", snapshot.record_sql_open, total);
    print_phase("record_sql_meta", snapshot.record_sql_meta, total);
    print_phase("record_sql_sources", snapshot.record_sql_sources, total);
    print_phase("record_sql_reads", snapshot.record_sql_reads, total);
    print_phase("record_sql_items", snapshot.record_sql_items, total);
    print_phase("record_sql_interfaces", snapshot.record_sql_interfaces, total);
    print_phase("record_sql_modules", snapshot.record_sql_modules, total);
    print_phase("record_sql_warnings", snapshot.record_sql_warnings, total);
    print_phase("record_sql_deps", snapshot.record_sql_deps, total);
    print_phase("record_sql_commit", snapshot.record_sql_commit, total);
    print_phase("record_rename", snapshot.record_rename, total);
    print_phase("record_recover", snapshot.record_recover, total);
    print_phase("record_publish_lock", snapshot.record_publish_lock, total);
    print_phase("record_batch_commit", snapshot.record_batch_commit, total);
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
