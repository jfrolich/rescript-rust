//! Optional compiler performance counters.
//!
//! Counters are disabled unless `RESCRIPT_COMPILER_COUNTERS` is set. They are
//! process-global so the in-process build can report aggregate behavior across
//! all worker threads.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

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
static STORED_COMPONENT_CACHED: AtomicU64 = AtomicU64::new(0);
static STORED_COMPONENT_BUILD_FIND_MODULE: AtomicU64 = AtomicU64::new(0);
static STORED_COMPONENT_BUILD_PROBE_MODULE_DESCR: AtomicU64 = AtomicU64::new(0);
static STORED_COMPONENT_PUBLISHED: AtomicU64 = AtomicU64::new(0);
static STORED_COMPONENT_TRANSIENT: AtomicU64 = AtomicU64::new(0);

static QUALIFIED_RECORD_LABEL_HITS: AtomicU64 = AtomicU64::new(0);
static QUALIFIED_RECORD_LABEL_MISSES: AtomicU64 = AtomicU64::new(0);
static QUALIFIED_RECORD_LABEL_REGISTERED: AtomicU64 = AtomicU64::new(0);
static QUALIFIED_RECORD_LABEL_UNCACHED_LOCAL_ROOT: AtomicU64 = AtomicU64::new(0);
static QUALIFIED_RECORD_LABEL_UNCACHED_OTHER: AtomicU64 = AtomicU64::new(0);

static SPARSE_RECORD_LARGE: AtomicU64 = AtomicU64::new(0);
static SPARSE_RECORD_USED: AtomicU64 = AtomicU64::new(0);
static SPARSE_RECORD_SKIPPED: AtomicU64 = AtomicU64::new(0);
static SPARSE_RECORD_TOTAL_LABELS: AtomicU64 = AtomicU64::new(0);
static SPARSE_RECORD_TOTAL_FIELDS: AtomicU64 = AtomicU64::new(0);
static MODULE_SPARSE_RECORDS: OnceLock<Mutex<HashMap<String, SparseRecordSite>>> = OnceLock::new();

static TYPE_ITEM_RESOLVE_CACHE_HITS: AtomicU64 = AtomicU64::new(0);
static TYPE_ITEM_RESOLVE_MISSING_CACHE_HITS: AtomicU64 = AtomicU64::new(0);
static TYPE_ITEM_RESOLVE_SCANS: AtomicU64 = AtomicU64::new(0);
static TYPE_ITEM_RESOLVE_SCANNED_ITEMS: AtomicU64 = AtomicU64::new(0);
static TYPE_ITEM_RESOLVE_TYPE_ITEMS: AtomicU64 = AtomicU64::new(0);
static TYPE_ITEM_RESOLVE_FOUND: AtomicU64 = AtomicU64::new(0);

static SIGNATURE_COPY_CALLS: AtomicU64 = AtomicU64::new(0);
static SIGNATURE_COPY_ITEMS: AtomicU64 = AtomicU64::new(0);
static SIGNATURE_COPY_MAX_ITEMS: AtomicU64 = AtomicU64::new(0);
static SIGNATURE_COPY_SITES: OnceLock<Mutex<HashMap<(&'static str, u32), SignatureCopySite>>> =
    OnceLock::new();
static SIGNATURE_QUALIFICATION_KINDS: OnceLock<Mutex<HashMap<&'static str, SignatureCopySite>>> =
    OnceLock::new();
static SIGNATURE_QUALIFICATION_NAMES: OnceLock<Mutex<HashMap<String, SignatureCopySite>>> =
    OnceLock::new();
static SIGNATURE_FRESHEN_KINDS: OnceLock<Mutex<HashMap<&'static str, SignatureCopySite>>> =
    OnceLock::new();
static SIGNATURE_FRESHEN_NAMES: OnceLock<Mutex<HashMap<String, SignatureCopySite>>> =
    OnceLock::new();
static MODULE_SIGNATURE_COPIES: OnceLock<Mutex<HashMap<String, SignatureCopySite>>> =
    OnceLock::new();
static MODULE_SIGNATURE_FRESHENS: OnceLock<Mutex<HashMap<String, SignatureCopySite>>> =
    OnceLock::new();

static MATCH_ACTION_CLONE_CALLS: AtomicU64 = AtomicU64::new(0);
static MATCH_ACTION_CLONE_NODES: AtomicU64 = AtomicU64::new(0);
static MATCH_ACTION_CLONE_BYTES: AtomicU64 = AtomicU64::new(0);
static MATCH_ACTION_CLONE_NANOS: AtomicU64 = AtomicU64::new(0);
static MATCH_ACTION_CLONE_MAX_REFERENCES: AtomicU64 = AtomicU64::new(0);
static MATCH_ACTION_CLONE_SITES: OnceLock<
    Mutex<HashMap<(&'static str, u32), MatchActionCloneSite>>,
> = OnceLock::new();
static MODULE_MATCH_ACTION_CLONES: OnceLock<Mutex<HashMap<String, MatchActionCloneSite>>> =
    OnceLock::new();

static LAMBDA_VEC_REBUILD_SITES: OnceLock<Mutex<HashMap<&'static str, LambdaVecRebuildSite>>> =
    OnceLock::new();
static MODULE_LAMBDA_VEC_REBUILDS: OnceLock<
    Mutex<HashMap<(String, &'static str), LambdaVecRebuildSite>>,
> = OnceLock::new();
static LAMBDA_OWNED_PASSES: OnceLock<Mutex<HashMap<&'static str, LambdaOwnedPassSite>>> =
    OnceLock::new();
static MODULE_LAMBDA_OWNED_PASSES: OnceLock<
    Mutex<HashMap<(String, &'static str), LambdaOwnedPassSite>>,
> = OnceLock::new();

thread_local! {
    static CURRENT_MODULE: RefCell<Option<String>> = const { RefCell::new(None) };
}

static REGISTRY_SNAPSHOTS: AtomicU64 = AtomicU64::new(0);
static REGISTRY_SHARED_ENTRIES_TOTAL: AtomicU64 = AtomicU64::new(0);
static REGISTRY_LOCAL_ENTRIES_TOTAL: AtomicU64 = AtomicU64::new(0);
static REGISTRY_MAX_SHARED_ENTRIES: AtomicU64 = AtomicU64::new(0);
static REGISTRY_MAX_LOCAL_ENTRIES: AtomicU64 = AtomicU64::new(0);
static REGISTRY_LOCAL_MODULES_TOTAL: AtomicU64 = AtomicU64::new(0);
static REGISTRY_LOCAL_INFO_TOTAL: AtomicU64 = AtomicU64::new(0);
static REGISTRY_LOCAL_ALIASES_TOTAL: AtomicU64 = AtomicU64::new(0);
static REGISTRY_LOCAL_FALLBACKS_TOTAL: AtomicU64 = AtomicU64::new(0);

static TYPE_MUTATION_DESC: AtomicU64 = AtomicU64::new(0);
static TYPE_MUTATION_LEVEL: AtomicU64 = AtomicU64::new(0);
static TYPE_MUTATION_ROW: AtomicU64 = AtomicU64::new(0);
static TYPE_MUTATION_ABBREV: AtomicU64 = AtomicU64::new(0);
static TYPE_MUTATION_STATE: AtomicU64 = AtomicU64::new(0);
static TYPE_MUTATION_SNAPSHOTS: AtomicU64 = AtomicU64::new(0);
static TYPE_MUTATION_BACKTRACKS: AtomicU64 = AtomicU64::new(0);
static TYPE_MUTATION_RESTORES: AtomicU64 = AtomicU64::new(0);
static TYPE_MUTATION_PEAK_DEPTH: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy)]
pub(crate) enum TypeMutationKind {
    Desc,
    Level,
    Row,
    Abbrev,
    State,
}

pub(crate) fn record_type_mutation(kind: TypeMutationKind) {
    let counter = match kind {
        TypeMutationKind::Desc => &TYPE_MUTATION_DESC,
        TypeMutationKind::Level => &TYPE_MUTATION_LEVEL,
        TypeMutationKind::Row => &TYPE_MUTATION_ROW,
        TypeMutationKind::Abbrev => &TYPE_MUTATION_ABBREV,
        TypeMutationKind::State => &TYPE_MUTATION_STATE,
    };
    counter.fetch_add(1, Ordering::Relaxed);
}

pub(crate) fn record_type_mutation_snapshot(depth: usize) {
    TYPE_MUTATION_SNAPSHOTS.fetch_add(1, Ordering::Relaxed);
    TYPE_MUTATION_PEAK_DEPTH.fetch_max(depth as u64, Ordering::Relaxed);
}

pub(crate) fn record_type_mutation_backtrack(restores: usize) {
    TYPE_MUTATION_BACKTRACKS.fetch_add(1, Ordering::Relaxed);
    TYPE_MUTATION_RESTORES.fetch_add(restores as u64, Ordering::Relaxed);
}

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

#[derive(Clone, Copy, Default)]
struct SignatureCopySite {
    calls: u64,
    items: u64,
    max_items: u64,
}

#[derive(Clone, Copy, Default)]
struct MatchActionCloneSite {
    calls: u64,
    nodes: u64,
    bytes: u64,
    nanos: u64,
    max_references: u64,
}

#[derive(Clone, Copy, Default)]
struct SparseRecordSite {
    large: u64,
    used: u64,
    skipped: u64,
    labels: u64,
    fields: u64,
}

#[derive(Clone, Copy, Default)]
struct LambdaVecRebuildSite {
    calls: u64,
    elements: u64,
    logical_bytes: u64,
    reused_allocations: u64,
}

#[derive(Clone, Copy, Default)]
struct LambdaOwnedPassSite {
    calls: u64,
    input_nodes: u64,
    input_logical_bytes: u64,
    nanos: u64,
}

/// Thread-local module attribution guard for compiler counters.
///
/// Normal builds pay no cost because the guard is inactive unless
/// `RESCRIPT_COMPILER_COUNTERS` is set.
pub struct ModuleCounterGuard {
    active: bool,
    previous: Option<String>,
}

impl ModuleCounterGuard {
    /// Attribute subsequent counters on the current worker thread to `module`.
    pub fn start(module: &str) -> Self {
        if !enabled() {
            return Self {
                active: false,
                previous: None,
            };
        }

        let previous = CURRENT_MODULE.with(|current| current.replace(Some(module.to_string())));
        Self {
            active: true,
            previous,
        }
    }
}

impl Drop for ModuleCounterGuard {
    fn drop(&mut self) {
        if self.active {
            CURRENT_MODULE.with(|current| {
                *current.borrow_mut() = self.previous.take();
            });
        }
    }
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
        &STORED_COMPONENT_CACHED,
        &STORED_COMPONENT_BUILD_FIND_MODULE,
        &STORED_COMPONENT_BUILD_PROBE_MODULE_DESCR,
        &STORED_COMPONENT_PUBLISHED,
        &STORED_COMPONENT_TRANSIENT,
        &QUALIFIED_RECORD_LABEL_HITS,
        &QUALIFIED_RECORD_LABEL_MISSES,
        &QUALIFIED_RECORD_LABEL_REGISTERED,
        &QUALIFIED_RECORD_LABEL_UNCACHED_LOCAL_ROOT,
        &QUALIFIED_RECORD_LABEL_UNCACHED_OTHER,
        &SPARSE_RECORD_LARGE,
        &SPARSE_RECORD_USED,
        &SPARSE_RECORD_SKIPPED,
        &SPARSE_RECORD_TOTAL_LABELS,
        &SPARSE_RECORD_TOTAL_FIELDS,
        &TYPE_ITEM_RESOLVE_CACHE_HITS,
        &TYPE_ITEM_RESOLVE_MISSING_CACHE_HITS,
        &TYPE_ITEM_RESOLVE_SCANS,
        &TYPE_ITEM_RESOLVE_SCANNED_ITEMS,
        &TYPE_ITEM_RESOLVE_TYPE_ITEMS,
        &TYPE_ITEM_RESOLVE_FOUND,
        &SIGNATURE_COPY_CALLS,
        &SIGNATURE_COPY_ITEMS,
        &SIGNATURE_COPY_MAX_ITEMS,
        &MATCH_ACTION_CLONE_CALLS,
        &MATCH_ACTION_CLONE_NODES,
        &MATCH_ACTION_CLONE_BYTES,
        &MATCH_ACTION_CLONE_NANOS,
        &MATCH_ACTION_CLONE_MAX_REFERENCES,
        &REGISTRY_SNAPSHOTS,
        &REGISTRY_SHARED_ENTRIES_TOTAL,
        &REGISTRY_LOCAL_ENTRIES_TOTAL,
        &REGISTRY_MAX_SHARED_ENTRIES,
        &REGISTRY_MAX_LOCAL_ENTRIES,
        &REGISTRY_LOCAL_MODULES_TOTAL,
        &REGISTRY_LOCAL_INFO_TOTAL,
        &REGISTRY_LOCAL_ALIASES_TOTAL,
        &REGISTRY_LOCAL_FALLBACKS_TOTAL,
        &TYPE_MUTATION_DESC,
        &TYPE_MUTATION_LEVEL,
        &TYPE_MUTATION_ROW,
        &TYPE_MUTATION_ABBREV,
        &TYPE_MUTATION_STATE,
        &TYPE_MUTATION_SNAPSHOTS,
        &TYPE_MUTATION_BACKTRACKS,
        &TYPE_MUTATION_RESTORES,
        &TYPE_MUTATION_PEAK_DEPTH,
    ] {
        counter.store(0, Ordering::Relaxed);
    }

    if let Some(sites) = SIGNATURE_COPY_SITES.get() {
        sites.lock().unwrap().clear();
    }
    if let Some(kinds) = SIGNATURE_QUALIFICATION_KINDS.get() {
        kinds.lock().unwrap().clear();
    }
    if let Some(names) = SIGNATURE_QUALIFICATION_NAMES.get() {
        names.lock().unwrap().clear();
    }
    if let Some(kinds) = SIGNATURE_FRESHEN_KINDS.get() {
        kinds.lock().unwrap().clear();
    }
    if let Some(names) = SIGNATURE_FRESHEN_NAMES.get() {
        names.lock().unwrap().clear();
    }
    if let Some(modules) = MODULE_SIGNATURE_COPIES.get() {
        modules.lock().unwrap().clear();
    }
    if let Some(modules) = MODULE_SIGNATURE_FRESHENS.get() {
        modules.lock().unwrap().clear();
    }
    if let Some(modules) = MODULE_SPARSE_RECORDS.get() {
        modules.lock().unwrap().clear();
    }
    if let Some(sites) = MATCH_ACTION_CLONE_SITES.get() {
        sites.lock().unwrap().clear();
    }
    if let Some(modules) = MODULE_MATCH_ACTION_CLONES.get() {
        modules.lock().unwrap().clear();
    }
    if let Some(sites) = LAMBDA_VEC_REBUILD_SITES.get() {
        sites.lock().unwrap().clear();
    }
    if let Some(modules) = MODULE_LAMBDA_VEC_REBUILDS.get() {
        modules.lock().unwrap().clear();
    }
    if let Some(passes) = LAMBDA_OWNED_PASSES.get() {
        passes.lock().unwrap().clear();
    }
    if let Some(modules) = MODULE_LAMBDA_OWNED_PASSES.get() {
        modules.lock().unwrap().clear();
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

/// Record use of an already-built stored component view.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_stored_component_cached() {
    STORED_COMPONENT_CACHED.fetch_add(1, Ordering::Relaxed);
}

/// Record a stored component view built for a specific lookup mode.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_stored_component_build(mode: &'static str, published: bool) {
    match mode {
        "find_module" => {
            STORED_COMPONENT_BUILD_FIND_MODULE.fetch_add(1, Ordering::Relaxed);
        }
        "probe_module_descr" => {
            STORED_COMPONENT_BUILD_PROBE_MODULE_DESCR.fetch_add(1, Ordering::Relaxed);
        }
        _ => {}
    }
    if published {
        STORED_COMPONENT_PUBLISHED.fetch_add(1, Ordering::Relaxed);
    } else {
        STORED_COMPONENT_TRANSIENT.fetch_add(1, Ordering::Relaxed);
    }
}

/// Record a qualified record-label cache hit.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_record_label_hit() {
    QUALIFIED_RECORD_LABEL_HITS.fetch_add(1, Ordering::Relaxed);
}

/// Record a qualified record-label cache miss.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_record_label_miss() {
    QUALIFIED_RECORD_LABEL_MISSES.fetch_add(1, Ordering::Relaxed);
}

/// Record a newly cached qualified record label.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_record_label_registered() {
    QUALIFIED_RECORD_LABEL_REGISTERED.fetch_add(1, Ordering::Relaxed);
}

/// Record a local-root record label that is currently not cacheable.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_record_label_uncached_local_root() {
    QUALIFIED_RECORD_LABEL_UNCACHED_LOCAL_ROOT.fetch_add(1, Ordering::Relaxed);
}

/// Record a record label that is not eligible for the qualified-label cache.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_record_label_uncached_other() {
    QUALIFIED_RECORD_LABEL_UNCACHED_OTHER.fetch_add(1, Ordering::Relaxed);
}

/// Record a large record literal that can use the sparse internal representation.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
pub(crate) fn record_sparse_record(used: bool, label_count: usize, field_count: usize) {
    SPARSE_RECORD_LARGE.fetch_add(1, Ordering::Relaxed);
    SPARSE_RECORD_TOTAL_LABELS.fetch_add(label_count as u64, Ordering::Relaxed);
    SPARSE_RECORD_TOTAL_FIELDS.fetch_add(field_count as u64, Ordering::Relaxed);
    if used {
        SPARSE_RECORD_USED.fetch_add(1, Ordering::Relaxed);
    } else {
        SPARSE_RECORD_SKIPPED.fetch_add(1, Ordering::Relaxed);
    }

    CURRENT_MODULE.with(|current| {
        let current = current.borrow();
        let Some(module) = current.as_ref() else {
            return;
        };
        let modules = MODULE_SPARSE_RECORDS.get_or_init(|| Mutex::new(HashMap::new()));
        let mut modules = modules.lock().unwrap();
        let entry = modules
            .entry(module.clone())
            .or_insert_with(SparseRecordSite::default);
        entry.large += 1;
        if used {
            entry.used += 1;
        } else {
            entry.skipped += 1;
        }
        entry.labels += label_count as u64;
        entry.fields += field_count as u64;
    });
}

/// Record a cached type-item path lookup.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_type_item_resolve_cache_hit() {
    TYPE_ITEM_RESOLVE_CACHE_HITS.fetch_add(1, Ordering::Relaxed);
}

/// Record a cached missing type-item path lookup.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_type_item_resolve_missing_cache_hit() {
    TYPE_ITEM_RESOLVE_MISSING_CACHE_HITS.fetch_add(1, Ordering::Relaxed);
}

/// Record a type-item signature scan.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_type_item_resolve_scan(scanned_items: usize, type_items: usize, found: bool) {
    TYPE_ITEM_RESOLVE_SCANS.fetch_add(1, Ordering::Relaxed);
    TYPE_ITEM_RESOLVE_SCANNED_ITEMS.fetch_add(scanned_items as u64, Ordering::Relaxed);
    TYPE_ITEM_RESOLVE_TYPE_ITEMS.fetch_add(type_items as u64, Ordering::Relaxed);
    if found {
        TYPE_ITEM_RESOLVE_FOUND.fetch_add(1, Ordering::Relaxed);
    }
}

/// Record a full signature copy, grouped by call site.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_copy(
    location: &'static std::panic::Location<'static>,
    item_count: usize,
) {
    SIGNATURE_COPY_CALLS.fetch_add(1, Ordering::Relaxed);
    SIGNATURE_COPY_ITEMS.fetch_add(item_count as u64, Ordering::Relaxed);
    SIGNATURE_COPY_MAX_ITEMS.fetch_max(item_count as u64, Ordering::Relaxed);

    let sites = SIGNATURE_COPY_SITES.get_or_init(|| Mutex::new(HashMap::new()));
    let mut sites = sites.lock().unwrap();
    let entry = sites
        .entry((location.file(), location.line()))
        .or_insert_with(SignatureCopySite::default);
    entry.calls += 1;
    entry.items += item_count as u64;
    entry.max_items = entry.max_items.max(item_count as u64);
    record_current_module_signature_copy(item_count);
}

/// Record a signature qualification before the current full-copy path.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_qualification(kind: &'static str, item_count: usize) {
    let kinds = SIGNATURE_QUALIFICATION_KINDS.get_or_init(|| Mutex::new(HashMap::new()));
    let mut kinds = kinds.lock().unwrap();
    let entry = kinds.entry(kind).or_insert_with(SignatureCopySite::default);
    entry.calls += 1;
    entry.items += item_count as u64;
    entry.max_items = entry.max_items.max(item_count as u64);
}

/// Record a named signature qualification entry.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_qualification_name(
    kind: &'static str,
    name: &str,
    item_count: usize,
) {
    let names = SIGNATURE_QUALIFICATION_NAMES.get_or_init(|| Mutex::new(HashMap::new()));
    let mut names = names.lock().unwrap();
    let key = format!("{kind}:{name}");
    let entry = names.entry(key).or_insert_with(SignatureCopySite::default);
    entry.calls += 1;
    entry.items += item_count as u64;
    entry.max_items = entry.max_items.max(item_count as u64);
}

/// Record a signature freshening entry point before it performs full-copy work.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_freshen(kind: &'static str, item_count: usize) {
    let kinds = SIGNATURE_FRESHEN_KINDS.get_or_init(|| Mutex::new(HashMap::new()));
    let mut kinds = kinds.lock().unwrap();
    let entry = kinds.entry(kind).or_insert_with(SignatureCopySite::default);
    entry.calls += 1;
    entry.items += item_count as u64;
    entry.max_items = entry.max_items.max(item_count as u64);
    record_current_module_signature_freshen(item_count);
}

/// Record a named signature freshening entry.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_freshen_name(kind: &'static str, name: &str, item_count: usize) {
    let names = SIGNATURE_FRESHEN_NAMES.get_or_init(|| Mutex::new(HashMap::new()));
    let mut names = names.lock().unwrap();
    let key = format!("{kind}:{name}");
    let entry = names.entry(key).or_insert_with(SignatureCopySite::default);
    entry.calls += 1;
    entry.items += item_count as u64;
    entry.max_items = entry.max_items.max(item_count as u64);
}

fn record_current_module_signature_copy(item_count: usize) {
    CURRENT_MODULE.with(|current| {
        let current = current.borrow();
        let Some(module) = current.as_ref() else {
            return;
        };
        let modules = MODULE_SIGNATURE_COPIES.get_or_init(|| Mutex::new(HashMap::new()));
        let mut modules = modules.lock().unwrap();
        let entry = modules
            .entry(module.clone())
            .or_insert_with(SignatureCopySite::default);
        entry.calls += 1;
        entry.items += item_count as u64;
        entry.max_items = entry.max_items.max(item_count as u64);
    });
}

fn record_current_module_signature_freshen(item_count: usize) {
    CURRENT_MODULE.with(|current| {
        let current = current.borrow();
        let Some(module) = current.as_ref() else {
            return;
        };
        let modules = MODULE_SIGNATURE_FRESHENS.get_or_init(|| Mutex::new(HashMap::new()));
        let mut modules = modules.lock().unwrap();
        let entry = modules
            .entry(module.clone())
            .or_insert_with(SignatureCopySite::default);
        entry.calls += 1;
        entry.items += item_count as u64;
        entry.max_items = entry.max_items.max(item_count as u64);
    });
}

/// Record one recursive materialization of a shared match action.
///
/// `bytes` is the estimated owned RawLambda footprint cloned at this site;
/// `references` is the number of Arc handles or logical output uses that require the clone.
pub(crate) fn record_match_action_clone(
    location: &'static std::panic::Location<'static>,
    nodes: usize,
    bytes: usize,
    elapsed_nanos: u64,
    references: usize,
) {
    MATCH_ACTION_CLONE_CALLS.fetch_add(1, Ordering::Relaxed);
    MATCH_ACTION_CLONE_NODES.fetch_add(nodes as u64, Ordering::Relaxed);
    MATCH_ACTION_CLONE_BYTES.fetch_add(bytes as u64, Ordering::Relaxed);
    MATCH_ACTION_CLONE_NANOS.fetch_add(elapsed_nanos, Ordering::Relaxed);
    MATCH_ACTION_CLONE_MAX_REFERENCES.fetch_max(references as u64, Ordering::Relaxed);

    let update = |entry: &mut MatchActionCloneSite| {
        entry.calls += 1;
        entry.nodes += nodes as u64;
        entry.bytes += bytes as u64;
        entry.nanos += elapsed_nanos;
        entry.max_references = entry.max_references.max(references as u64);
    };

    let sites = MATCH_ACTION_CLONE_SITES.get_or_init(|| Mutex::new(HashMap::new()));
    update(
        sites
            .lock()
            .unwrap()
            .entry((location.file(), location.line()))
            .or_default(),
    );

    CURRENT_MODULE.with(|current| {
        let current = current.borrow();
        let Some(module) = current.as_ref() else {
            return;
        };
        let modules = MODULE_MATCH_ACTION_CLONES.get_or_init(|| Mutex::new(HashMap::new()));
        update(modules.lock().unwrap().entry(module.clone()).or_default());
    });
}

/// Attribute one owned Lambda vector rebuild to its pass and current module.
///
/// `logical_bytes` is the vector element storage traversed by the rebuild. A
/// reused allocation means `collect` kept the source vector buffer; otherwise
/// the same bytes were moved into a fresh allocation.
pub(crate) fn record_lambda_vec_rebuild(
    site: &'static str,
    elements: usize,
    logical_bytes: usize,
    reused_allocation: bool,
) {
    let update = |entry: &mut LambdaVecRebuildSite| {
        entry.calls += 1;
        entry.elements += elements as u64;
        entry.logical_bytes += logical_bytes as u64;
        entry.reused_allocations += u64::from(reused_allocation);
    };

    let sites = LAMBDA_VEC_REBUILD_SITES.get_or_init(|| Mutex::new(HashMap::new()));
    update(sites.lock().unwrap().entry(site).or_default());

    CURRENT_MODULE.with(|current| {
        let current = current.borrow();
        let Some(module) = current.as_ref() else {
            return;
        };
        let modules = MODULE_LAMBDA_VEC_REBUILDS.get_or_init(|| Mutex::new(HashMap::new()));
        update(
            modules
                .lock()
                .unwrap()
                .entry((module.clone(), site))
                .or_default(),
        );
    });
}

/// Attribute one complete owned Lambda pass to its pass and current module.
pub(crate) fn record_lambda_owned_pass(
    pass: &'static str,
    input_nodes: usize,
    input_logical_bytes: usize,
    elapsed_nanos: u64,
) {
    let update = |entry: &mut LambdaOwnedPassSite| {
        entry.calls += 1;
        entry.input_nodes += input_nodes as u64;
        entry.input_logical_bytes += input_logical_bytes as u64;
        entry.nanos += elapsed_nanos;
    };

    let passes = LAMBDA_OWNED_PASSES.get_or_init(|| Mutex::new(HashMap::new()));
    update(passes.lock().unwrap().entry(pass).or_default());

    CURRENT_MODULE.with(|current| {
        let current = current.borrow();
        let Some(module) = current.as_ref() else {
            return;
        };
        let modules = MODULE_LAMBDA_OWNED_PASSES.get_or_init(|| Mutex::new(HashMap::new()));
        update(
            modules
                .lock()
                .unwrap()
                .entry((module.clone(), pass))
                .or_default(),
        );
    });
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
        "[compiler-counter] stored_components cached={} build_find_module={} build_probe_module_descr={} published={} transient={}",
        STORED_COMPONENT_CACHED.load(Ordering::Relaxed),
        STORED_COMPONENT_BUILD_FIND_MODULE.load(Ordering::Relaxed),
        STORED_COMPONENT_BUILD_PROBE_MODULE_DESCR.load(Ordering::Relaxed),
        STORED_COMPONENT_PUBLISHED.load(Ordering::Relaxed),
        STORED_COMPONENT_TRANSIENT.load(Ordering::Relaxed),
    );
    eprintln!(
        "[compiler-counter] qualified_record_labels hits={} misses={} registered={} uncached_local_root={} uncached_other={}",
        QUALIFIED_RECORD_LABEL_HITS.load(Ordering::Relaxed),
        QUALIFIED_RECORD_LABEL_MISSES.load(Ordering::Relaxed),
        QUALIFIED_RECORD_LABEL_REGISTERED.load(Ordering::Relaxed),
        QUALIFIED_RECORD_LABEL_UNCACHED_LOCAL_ROOT.load(Ordering::Relaxed),
        QUALIFIED_RECORD_LABEL_UNCACHED_OTHER.load(Ordering::Relaxed),
    );
    eprintln!(
        "[compiler-counter] sparse_records large={} used={} skipped={} labels={} fields={}",
        SPARSE_RECORD_LARGE.load(Ordering::Relaxed),
        SPARSE_RECORD_USED.load(Ordering::Relaxed),
        SPARSE_RECORD_SKIPPED.load(Ordering::Relaxed),
        SPARSE_RECORD_TOTAL_LABELS.load(Ordering::Relaxed),
        SPARSE_RECORD_TOTAL_FIELDS.load(Ordering::Relaxed),
    );
    print_module_sparse_records();
    eprintln!(
        "[compiler-counter] type_item_resolve positive_cache_hits={} missing_cache_hits={} scans={} scanned_items={} type_items={} found={}",
        TYPE_ITEM_RESOLVE_CACHE_HITS.load(Ordering::Relaxed),
        TYPE_ITEM_RESOLVE_MISSING_CACHE_HITS.load(Ordering::Relaxed),
        TYPE_ITEM_RESOLVE_SCANS.load(Ordering::Relaxed),
        TYPE_ITEM_RESOLVE_SCANNED_ITEMS.load(Ordering::Relaxed),
        TYPE_ITEM_RESOLVE_TYPE_ITEMS.load(Ordering::Relaxed),
        TYPE_ITEM_RESOLVE_FOUND.load(Ordering::Relaxed),
    );
    eprintln!(
        "[compiler-counter] signature_copies calls={} items={} max_items={}",
        SIGNATURE_COPY_CALLS.load(Ordering::Relaxed),
        SIGNATURE_COPY_ITEMS.load(Ordering::Relaxed),
        SIGNATURE_COPY_MAX_ITEMS.load(Ordering::Relaxed),
    );
    print_signature_copy_sites();
    print_signature_qualification_kinds();
    print_signature_qualification_names();
    print_signature_freshen_kinds();
    print_signature_freshen_names();
    print_module_signature_copies();
    print_module_signature_freshens();
    print_match_action_clones();
    print_lambda_vec_rebuilds();
    print_lambda_owned_passes();
    eprintln!(
        "[compiler-counter] type_mutations desc={} level={} row={} abbrev={} state={} snapshots={} backtracks={} restores={} peak_depth={}",
        TYPE_MUTATION_DESC.load(Ordering::Relaxed),
        TYPE_MUTATION_LEVEL.load(Ordering::Relaxed),
        TYPE_MUTATION_ROW.load(Ordering::Relaxed),
        TYPE_MUTATION_ABBREV.load(Ordering::Relaxed),
        TYPE_MUTATION_STATE.load(Ordering::Relaxed),
        TYPE_MUTATION_SNAPSHOTS.load(Ordering::Relaxed),
        TYPE_MUTATION_BACKTRACKS.load(Ordering::Relaxed),
        TYPE_MUTATION_RESTORES.load(Ordering::Relaxed),
        TYPE_MUTATION_PEAK_DEPTH.load(Ordering::Relaxed),
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

fn print_lambda_owned_passes() {
    if let Some(passes) = LAMBDA_OWNED_PASSES.get() {
        let mut passes: Vec<_> = passes
            .lock()
            .unwrap()
            .iter()
            .map(|(pass, counters)| (*pass, *counters))
            .collect();
        passes.sort_by_key(|(_, counters)| std::cmp::Reverse(counters.nanos));
        for (pass, counters) in passes {
            eprintln!(
                "[compiler-counter] lambda_owned_pass pass={} calls={} input_nodes={} input_logical_bytes={} nanos={}",
                pass,
                counters.calls,
                counters.input_nodes,
                counters.input_logical_bytes,
                counters.nanos,
            );
        }
    }

    if let Some(modules) = MODULE_LAMBDA_OWNED_PASSES.get() {
        let mut modules: Vec<_> = modules
            .lock()
            .unwrap()
            .iter()
            .map(|((module, pass), counters)| (module.clone(), *pass, *counters))
            .collect();
        modules.sort_by_key(|(_, _, counters)| std::cmp::Reverse(counters.nanos));
        for (module, pass, counters) in modules.into_iter().take(30) {
            eprintln!(
                "[compiler-counter] module_lambda_owned_pass module={} pass={} calls={} input_nodes={} input_logical_bytes={} nanos={}",
                module,
                pass,
                counters.calls,
                counters.input_nodes,
                counters.input_logical_bytes,
                counters.nanos,
            );
        }
    }
}

fn print_lambda_vec_rebuilds() {
    if let Some(sites) = LAMBDA_VEC_REBUILD_SITES.get() {
        let mut sites: Vec<_> = sites
            .lock()
            .unwrap()
            .iter()
            .map(|(site, counters)| (*site, *counters))
            .collect();
        sites.sort_by_key(|(_, counters)| std::cmp::Reverse(counters.logical_bytes));
        for (site, counters) in sites {
            eprintln!(
                "[compiler-counter] lambda_vec_rebuild site={} calls={} elements={} logical_bytes={} reused_allocations={}",
                site,
                counters.calls,
                counters.elements,
                counters.logical_bytes,
                counters.reused_allocations,
            );
        }
    }

    if let Some(modules) = MODULE_LAMBDA_VEC_REBUILDS.get() {
        let mut modules: Vec<_> = modules
            .lock()
            .unwrap()
            .iter()
            .map(|((module, site), counters)| (module.clone(), *site, *counters))
            .collect();
        modules.sort_by_key(|(_, _, counters)| std::cmp::Reverse(counters.logical_bytes));
        for (module, site, counters) in modules.into_iter().take(30) {
            eprintln!(
                "[compiler-counter] module_lambda_vec_rebuild module={} site={} calls={} elements={} logical_bytes={} reused_allocations={}",
                module,
                site,
                counters.calls,
                counters.elements,
                counters.logical_bytes,
                counters.reused_allocations,
            );
        }
    }
}

fn print_match_action_clones() {
    eprintln!(
        "[compiler-counter] match_action_clones calls={} nodes={} estimated_bytes={} nanos={} max_references={}",
        MATCH_ACTION_CLONE_CALLS.load(Ordering::Relaxed),
        MATCH_ACTION_CLONE_NODES.load(Ordering::Relaxed),
        MATCH_ACTION_CLONE_BYTES.load(Ordering::Relaxed),
        MATCH_ACTION_CLONE_NANOS.load(Ordering::Relaxed),
        MATCH_ACTION_CLONE_MAX_REFERENCES.load(Ordering::Relaxed),
    );

    if let Some(sites) = MATCH_ACTION_CLONE_SITES.get() {
        let mut sites: Vec<_> = sites
            .lock()
            .unwrap()
            .iter()
            .map(|(k, v)| (*k, *v))
            .collect();
        sites.sort_by_key(|(_, site)| std::cmp::Reverse(site.nodes));
        for ((file, line), site) in sites.into_iter().take(12) {
            eprintln!(
                "[compiler-counter] match_action_clone_site file={file}:{line} calls={} nodes={} estimated_bytes={} nanos={} max_references={}",
                site.calls, site.nodes, site.bytes, site.nanos, site.max_references,
            );
        }
    }

    if let Some(modules) = MODULE_MATCH_ACTION_CLONES.get() {
        let mut modules: Vec<_> = modules
            .lock()
            .unwrap()
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect();
        modules.sort_by_key(|(_, site)| std::cmp::Reverse(site.nodes));
        for (module, site) in modules.into_iter().take(20) {
            eprintln!(
                "[compiler-counter] module_match_action_clones module={module} calls={} nodes={} estimated_bytes={} nanos={} max_references={}",
                site.calls, site.nodes, site.bytes, site.nanos, site.max_references,
            );
        }
    }
}

fn print_module_sparse_records() {
    let Some(modules) = MODULE_SPARSE_RECORDS.get() else {
        return;
    };

    let mut modules = modules
        .lock()
        .unwrap()
        .iter()
        .map(|(module, site)| (module.clone(), *site))
        .collect::<Vec<_>>();
    modules.sort_by(|a, b| {
        b.1.labels
            .cmp(&a.1.labels)
            .then_with(|| b.1.large.cmp(&a.1.large))
    });

    for (module, site) in modules.into_iter().take(20) {
        eprintln!(
            "[compiler-counter] module_sparse_records module={} large={} used={} skipped={} labels={} fields={}",
            module, site.large, site.used, site.skipped, site.labels, site.fields,
        );
    }
}

fn print_module_signature_copies() {
    let Some(modules) = MODULE_SIGNATURE_COPIES.get() else {
        return;
    };

    let mut modules = modules
        .lock()
        .unwrap()
        .iter()
        .map(|(module, site)| (module.clone(), *site))
        .collect::<Vec<_>>();
    modules.sort_by(|a, b| {
        b.1.items
            .cmp(&a.1.items)
            .then_with(|| b.1.calls.cmp(&a.1.calls))
    });

    for (module, site) in modules.into_iter().take(20) {
        eprintln!(
            "[compiler-counter] module_signature_copies module={} calls={} items={} max_items={}",
            module, site.calls, site.items, site.max_items
        );
    }
}

fn print_module_signature_freshens() {
    let Some(modules) = MODULE_SIGNATURE_FRESHENS.get() else {
        return;
    };

    let mut modules = modules
        .lock()
        .unwrap()
        .iter()
        .map(|(module, site)| (module.clone(), *site))
        .collect::<Vec<_>>();
    modules.sort_by(|a, b| {
        b.1.items
            .cmp(&a.1.items)
            .then_with(|| b.1.calls.cmp(&a.1.calls))
    });

    for (module, site) in modules.into_iter().take(20) {
        eprintln!(
            "[compiler-counter] module_signature_freshens module={} calls={} items={} max_items={}",
            module, site.calls, site.items, site.max_items
        );
    }
}

fn print_signature_qualification_names() {
    let Some(names) = SIGNATURE_QUALIFICATION_NAMES.get() else {
        return;
    };

    let mut names = names
        .lock()
        .unwrap()
        .iter()
        .map(|(name, counters)| (name.clone(), *counters))
        .collect::<Vec<_>>();
    names.sort_by(|a, b| {
        b.1.items
            .cmp(&a.1.items)
            .then_with(|| b.1.calls.cmp(&a.1.calls))
    });

    for (name, counters) in names.into_iter().take(20) {
        eprintln!(
            "[compiler-counter] signature_qualification_name name={} calls={} items={} max_items={}",
            name, counters.calls, counters.items, counters.max_items,
        );
    }
}

fn print_signature_freshen_names() {
    let Some(names) = SIGNATURE_FRESHEN_NAMES.get() else {
        return;
    };

    let mut names = names
        .lock()
        .unwrap()
        .iter()
        .map(|(name, counters)| (name.clone(), *counters))
        .collect::<Vec<_>>();
    names.sort_by(|a, b| {
        b.1.items
            .cmp(&a.1.items)
            .then_with(|| b.1.calls.cmp(&a.1.calls))
    });

    for (name, counters) in names.into_iter().take(20) {
        eprintln!(
            "[compiler-counter] signature_freshen_name name={} calls={} items={} max_items={}",
            name, counters.calls, counters.items, counters.max_items,
        );
    }
}

fn print_signature_freshen_kinds() {
    let Some(kinds) = SIGNATURE_FRESHEN_KINDS.get() else {
        return;
    };

    let mut kinds = kinds
        .lock()
        .unwrap()
        .iter()
        .map(|(kind, counters)| (*kind, *counters))
        .collect::<Vec<_>>();
    kinds.sort_by(|a, b| {
        b.1.items
            .cmp(&a.1.items)
            .then_with(|| b.1.calls.cmp(&a.1.calls))
    });

    for (kind, counters) in kinds.into_iter().take(20) {
        eprintln!(
            "[compiler-counter] signature_freshen kind={} calls={} items={} max_items={}",
            kind, counters.calls, counters.items, counters.max_items,
        );
    }
}

fn print_signature_qualification_kinds() {
    let Some(kinds) = SIGNATURE_QUALIFICATION_KINDS.get() else {
        return;
    };

    let mut kinds = kinds
        .lock()
        .unwrap()
        .iter()
        .map(|(kind, counters)| (*kind, *counters))
        .collect::<Vec<_>>();
    kinds.sort_by(|a, b| {
        b.1.items
            .cmp(&a.1.items)
            .then_with(|| b.1.calls.cmp(&a.1.calls))
    });

    for (kind, counters) in kinds.into_iter().take(20) {
        eprintln!(
            "[compiler-counter] signature_qualification kind={} calls={} items={} max_items={}",
            kind, counters.calls, counters.items, counters.max_items,
        );
    }
}

fn print_signature_copy_sites() {
    let Some(sites) = SIGNATURE_COPY_SITES.get() else {
        return;
    };

    let mut sites = sites
        .lock()
        .unwrap()
        .iter()
        .map(|((file, line), counters)| (*file, *line, *counters))
        .collect::<Vec<_>>();
    sites.sort_by(|a, b| {
        b.2.items
            .cmp(&a.2.items)
            .then_with(|| b.2.calls.cmp(&a.2.calls))
    });

    for (file, line, counters) in sites.into_iter().take(20) {
        eprintln!(
            "[compiler-counter] signature_copy_site file={} line={} calls={} items={} max_items={}",
            file, line, counters.calls, counters.items, counters.max_items,
        );
    }
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
