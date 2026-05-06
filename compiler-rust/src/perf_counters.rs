//! Optional compiler performance counters.
//!
//! Counters are disabled unless `RESCRIPT_COMPILER_COUNTERS` is set. They are
//! process-global so the in-process build can report aggregate behavior across
//! all worker threads.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

static ENABLED: OnceLock<bool> = OnceLock::new();

static VALUE_HITS: AtomicU64 = AtomicU64::new(0);
static VALUE_MISSES: AtomicU64 = AtomicU64::new(0);
static VALUE_SCANS: AtomicU64 = AtomicU64::new(0);
static VALUE_SCANNED_ITEMS: AtomicU64 = AtomicU64::new(0);
static VALUE_RESULTS: AtomicU64 = AtomicU64::new(0);

static TYPE_HITS: AtomicU64 = AtomicU64::new(0);
static TYPE_MISSES: AtomicU64 = AtomicU64::new(0);
static TYPE_SCANS: AtomicU64 = AtomicU64::new(0);
static TYPE_SCANNED_ITEMS: AtomicU64 = AtomicU64::new(0);
static TYPE_RESULTS: AtomicU64 = AtomicU64::new(0);

static MODULE_HITS: AtomicU64 = AtomicU64::new(0);
static MODULE_MISSES: AtomicU64 = AtomicU64::new(0);
static MODULE_SCANS: AtomicU64 = AtomicU64::new(0);
static MODULE_SCANNED_ITEMS: AtomicU64 = AtomicU64::new(0);
static MODULE_RESULTS: AtomicU64 = AtomicU64::new(0);

static CONSTRUCTOR_HITS: AtomicU64 = AtomicU64::new(0);
static CONSTRUCTOR_MISSES: AtomicU64 = AtomicU64::new(0);
static CONSTRUCTOR_SCANS: AtomicU64 = AtomicU64::new(0);
static CONSTRUCTOR_SCANNED_ITEMS: AtomicU64 = AtomicU64::new(0);
static CONSTRUCTOR_RESULTS: AtomicU64 = AtomicU64::new(0);

static LABEL_HITS: AtomicU64 = AtomicU64::new(0);
static LABEL_MISSES: AtomicU64 = AtomicU64::new(0);
static LABEL_SCANS: AtomicU64 = AtomicU64::new(0);
static LABEL_SCANNED_ITEMS: AtomicU64 = AtomicU64::new(0);
static LABEL_RESULTS: AtomicU64 = AtomicU64::new(0);

static CHILD_COMPONENT_HITS: AtomicU64 = AtomicU64::new(0);
static CHILD_COMPONENT_MISSES: AtomicU64 = AtomicU64::new(0);
static CHILD_COMPONENT_SCANS: AtomicU64 = AtomicU64::new(0);
static CHILD_COMPONENT_SCANNED_ITEMS: AtomicU64 = AtomicU64::new(0);
static CHILD_COMPONENT_RESULTS: AtomicU64 = AtomicU64::new(0);

static QUALIFIED_COMPONENT_HITS: AtomicU64 = AtomicU64::new(0);
static QUALIFIED_COMPONENT_MISSES: AtomicU64 = AtomicU64::new(0);
static QUALIFIED_COMPONENT_REGISTERED: AtomicU64 = AtomicU64::new(0);

static REGISTRY_SNAPSHOTS: AtomicU64 = AtomicU64::new(0);
static REGISTRY_SHARED_ENTRIES_TOTAL: AtomicU64 = AtomicU64::new(0);
static REGISTRY_LOCAL_ENTRIES_TOTAL: AtomicU64 = AtomicU64::new(0);
static REGISTRY_MAX_SHARED_ENTRIES: AtomicU64 = AtomicU64::new(0);
static REGISTRY_MAX_LOCAL_ENTRIES: AtomicU64 = AtomicU64::new(0);
static REGISTRY_LOCAL_MODULES_TOTAL: AtomicU64 = AtomicU64::new(0);
static REGISTRY_LOCAL_INFO_TOTAL: AtomicU64 = AtomicU64::new(0);
static REGISTRY_LOCAL_ALIASES_TOTAL: AtomicU64 = AtomicU64::new(0);
static REGISTRY_LOCAL_FALLBACKS_TOTAL: AtomicU64 = AtomicU64::new(0);

/// Lazy lookup buckets tracked by `RESCRIPT_COMPILER_COUNTERS`.
#[derive(Clone, Copy)]
pub(crate) enum LazyLookupKind {
    /// Qualified value lookup inside a shared signature.
    Value,
    /// Qualified type lookup inside a shared signature.
    Type,
    /// Qualified child module lookup inside a shared signature.
    Module,
    /// Constructor bucket lookup derived from a shared signature.
    Constructor,
    /// Record label bucket lookup derived from a shared signature.
    Label,
    /// Lazy child component lookup derived from a shared signature.
    ChildComponent,
}

struct LazyCounters {
    hits: &'static AtomicU64,
    misses: &'static AtomicU64,
    scans: &'static AtomicU64,
    scanned_items: &'static AtomicU64,
    results: &'static AtomicU64,
}

impl LazyLookupKind {
    fn name(self) -> &'static str {
        match self {
            LazyLookupKind::Value => "value",
            LazyLookupKind::Type => "type",
            LazyLookupKind::Module => "module",
            LazyLookupKind::Constructor => "constructor",
            LazyLookupKind::Label => "label",
            LazyLookupKind::ChildComponent => "child_component",
        }
    }

    fn counters(self) -> LazyCounters {
        match self {
            LazyLookupKind::Value => LazyCounters {
                hits: &VALUE_HITS,
                misses: &VALUE_MISSES,
                scans: &VALUE_SCANS,
                scanned_items: &VALUE_SCANNED_ITEMS,
                results: &VALUE_RESULTS,
            },
            LazyLookupKind::Type => LazyCounters {
                hits: &TYPE_HITS,
                misses: &TYPE_MISSES,
                scans: &TYPE_SCANS,
                scanned_items: &TYPE_SCANNED_ITEMS,
                results: &TYPE_RESULTS,
            },
            LazyLookupKind::Module => LazyCounters {
                hits: &MODULE_HITS,
                misses: &MODULE_MISSES,
                scans: &MODULE_SCANS,
                scanned_items: &MODULE_SCANNED_ITEMS,
                results: &MODULE_RESULTS,
            },
            LazyLookupKind::Constructor => LazyCounters {
                hits: &CONSTRUCTOR_HITS,
                misses: &CONSTRUCTOR_MISSES,
                scans: &CONSTRUCTOR_SCANS,
                scanned_items: &CONSTRUCTOR_SCANNED_ITEMS,
                results: &CONSTRUCTOR_RESULTS,
            },
            LazyLookupKind::Label => LazyCounters {
                hits: &LABEL_HITS,
                misses: &LABEL_MISSES,
                scans: &LABEL_SCANS,
                scanned_items: &LABEL_SCANNED_ITEMS,
                results: &LABEL_RESULTS,
            },
            LazyLookupKind::ChildComponent => LazyCounters {
                hits: &CHILD_COMPONENT_HITS,
                misses: &CHILD_COMPONENT_MISSES,
                scans: &CHILD_COMPONENT_SCANS,
                scanned_items: &CHILD_COMPONENT_SCANNED_ITEMS,
                results: &CHILD_COMPONENT_RESULTS,
            },
        }
    }
}

/// Returns whether compiler counters are enabled.
#[inline]
pub fn enabled() -> bool {
    #[cfg(target_arch = "wasm32")]
    {
        false
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        *ENABLED.get_or_init(|| std::env::var_os("RESCRIPT_COMPILER_COUNTERS").is_some())
    }
}

/// Reset all compiler performance counters.
pub fn reset() {
    if !enabled() {
        return;
    }

    for counter in [
        &VALUE_HITS,
        &VALUE_MISSES,
        &VALUE_SCANS,
        &VALUE_SCANNED_ITEMS,
        &VALUE_RESULTS,
        &TYPE_HITS,
        &TYPE_MISSES,
        &TYPE_SCANS,
        &TYPE_SCANNED_ITEMS,
        &TYPE_RESULTS,
        &MODULE_HITS,
        &MODULE_MISSES,
        &MODULE_SCANS,
        &MODULE_SCANNED_ITEMS,
        &MODULE_RESULTS,
        &CONSTRUCTOR_HITS,
        &CONSTRUCTOR_MISSES,
        &CONSTRUCTOR_SCANS,
        &CONSTRUCTOR_SCANNED_ITEMS,
        &CONSTRUCTOR_RESULTS,
        &LABEL_HITS,
        &LABEL_MISSES,
        &LABEL_SCANS,
        &LABEL_SCANNED_ITEMS,
        &LABEL_RESULTS,
        &CHILD_COMPONENT_HITS,
        &CHILD_COMPONENT_MISSES,
        &CHILD_COMPONENT_SCANS,
        &CHILD_COMPONENT_SCANNED_ITEMS,
        &CHILD_COMPONENT_RESULTS,
        &QUALIFIED_COMPONENT_HITS,
        &QUALIFIED_COMPONENT_MISSES,
        &QUALIFIED_COMPONENT_REGISTERED,
        &REGISTRY_SNAPSHOTS,
        &REGISTRY_SHARED_ENTRIES_TOTAL,
        &REGISTRY_LOCAL_ENTRIES_TOTAL,
        &REGISTRY_MAX_SHARED_ENTRIES,
        &REGISTRY_MAX_LOCAL_ENTRIES,
        &REGISTRY_LOCAL_MODULES_TOTAL,
        &REGISTRY_LOCAL_INFO_TOTAL,
        &REGISTRY_LOCAL_ALIASES_TOTAL,
        &REGISTRY_LOCAL_FALLBACKS_TOTAL,
    ] {
        counter.store(0, Ordering::Relaxed);
    }
}

/// Record a cached lazy-signature lookup.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_lazy_hit(kind: LazyLookupKind) {
    kind.counters().hits.fetch_add(1, Ordering::Relaxed);
}

/// Record a lazy-signature scan after a cache miss.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_lazy_scan(kind: LazyLookupKind, scanned_items: usize, result_items: usize) {
    let counters = kind.counters();
    counters.misses.fetch_add(1, Ordering::Relaxed);
    counters.scans.fetch_add(1, Ordering::Relaxed);
    counters
        .scanned_items
        .fetch_add(scanned_items as u64, Ordering::Relaxed);
    counters
        .results
        .fetch_add(result_items as u64, Ordering::Relaxed);
}

/// Record a qualified component-view cache hit.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_component_hit() {
    QUALIFIED_COMPONENT_HITS.fetch_add(1, Ordering::Relaxed);
}

/// Record a qualified component-view cache miss.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_component_miss() {
    QUALIFIED_COMPONENT_MISSES.fetch_add(1, Ordering::Relaxed);
}

/// Record a newly cached qualified component view.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_component_registered() {
    QUALIFIED_COMPONENT_REGISTERED.fetch_add(1, Ordering::Relaxed);
}

/// Record a per-worker in-process module-registry snapshot.
pub(crate) fn record_module_registry_snapshot(
    shared_entries: usize,
    local_modules: usize,
    local_info: usize,
    local_aliases: usize,
    local_fallbacks: usize,
) {
    let local_entries = local_modules + local_info + local_aliases + local_fallbacks;
    REGISTRY_SNAPSHOTS.fetch_add(1, Ordering::Relaxed);
    REGISTRY_SHARED_ENTRIES_TOTAL.fetch_add(shared_entries as u64, Ordering::Relaxed);
    REGISTRY_LOCAL_ENTRIES_TOTAL.fetch_add(local_entries as u64, Ordering::Relaxed);
    REGISTRY_MAX_SHARED_ENTRIES.fetch_max(shared_entries as u64, Ordering::Relaxed);
    REGISTRY_MAX_LOCAL_ENTRIES.fetch_max(local_entries as u64, Ordering::Relaxed);
    REGISTRY_LOCAL_MODULES_TOTAL.fetch_add(local_modules as u64, Ordering::Relaxed);
    REGISTRY_LOCAL_INFO_TOTAL.fetch_add(local_info as u64, Ordering::Relaxed);
    REGISTRY_LOCAL_ALIASES_TOTAL.fetch_add(local_aliases as u64, Ordering::Relaxed);
    REGISTRY_LOCAL_FALLBACKS_TOTAL.fetch_add(local_fallbacks as u64, Ordering::Relaxed);
}

/// Print compiler performance counters to stderr.
pub fn print_report() {
    if !enabled() {
        return;
    }

    for kind in [
        LazyLookupKind::Value,
        LazyLookupKind::Type,
        LazyLookupKind::Module,
        LazyLookupKind::Constructor,
        LazyLookupKind::Label,
        LazyLookupKind::ChildComponent,
    ] {
        print_lazy(kind);
    }
    eprintln!(
        "[compiler-counter] qualified_components hits={} misses={} registered={}",
        QUALIFIED_COMPONENT_HITS.load(Ordering::Relaxed),
        QUALIFIED_COMPONENT_MISSES.load(Ordering::Relaxed),
        QUALIFIED_COMPONENT_REGISTERED.load(Ordering::Relaxed),
    );
    eprintln!(
        "[compiler-counter] module_registry_snapshots count={} shared_entries_total={} local_entries_total={} max_shared_entries={} max_local_entries={} local_modules_total={} local_info_total={} local_aliases_total={} local_fallbacks_total={}",
        REGISTRY_SNAPSHOTS.load(Ordering::Relaxed),
        REGISTRY_SHARED_ENTRIES_TOTAL.load(Ordering::Relaxed),
        REGISTRY_LOCAL_ENTRIES_TOTAL.load(Ordering::Relaxed),
        REGISTRY_MAX_SHARED_ENTRIES.load(Ordering::Relaxed),
        REGISTRY_MAX_LOCAL_ENTRIES.load(Ordering::Relaxed),
        REGISTRY_LOCAL_MODULES_TOTAL.load(Ordering::Relaxed),
        REGISTRY_LOCAL_INFO_TOTAL.load(Ordering::Relaxed),
        REGISTRY_LOCAL_ALIASES_TOTAL.load(Ordering::Relaxed),
        REGISTRY_LOCAL_FALLBACKS_TOTAL.load(Ordering::Relaxed),
    );
}

fn print_lazy(kind: LazyLookupKind) {
    let counters = kind.counters();
    eprintln!(
        "[compiler-counter] lazy_lookup kind={} hits={} misses={} scans={} scanned_items={} result_items={}",
        kind.name(),
        counters.hits.load(Ordering::Relaxed),
        counters.misses.load(Ordering::Relaxed),
        counters.scans.load(Ordering::Relaxed),
        counters.scanned_items.load(Ordering::Relaxed),
        counters.results.load(Ordering::Relaxed),
    );
}
