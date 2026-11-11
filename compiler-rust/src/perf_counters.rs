//! Optional compiler performance counters.
//!
//! Counters are disabled unless `RESCRIPT_COMPILER_COUNTERS` is set. They are
//! process-global so the in-process build can report aggregate behavior across
//! all worker threads.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

use crate::types::typecore::ComponentLookupApi;

#[cfg(not(target_arch = "wasm32"))]
static ENABLED: OnceLock<bool> = OnceLock::new();

static PUBLISHED_SIGNATURE_DECODES: AtomicU64 = AtomicU64::new(0);

/// A main-signature decode on loading a unit published in this build.
pub fn record_published_signature_decode() {
    if enabled() {
        PUBLISHED_SIGNATURE_DECODES.fetch_add(1, Ordering::Relaxed);
    }
}

#[cfg(debug_assertions)]
thread_local! {
    static SIGNATURE_PUBLICATION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Debug-only guard for the interval before a signature is released.
pub struct SignaturePublication;
impl SignaturePublication {
    /// Begin the checking worker's pre-release interval.
    pub fn begin() -> Self {
        #[cfg(debug_assertions)]
        SIGNATURE_PUBLICATION.with(|active| assert!(!active.replace(true)));
        Self
    }
}
impl Drop for SignaturePublication {
    fn drop(&mut self) {
        #[cfg(debug_assertions)]
        SIGNATURE_PUBLICATION.with(|active| active.set(false));
    }
}

/// Encoding and summary construction must stay off the release path.
#[inline]
pub fn assert_signature_released() {
    #[cfg(debug_assertions)]
    SIGNATURE_PUBLICATION.with(|active| {
        assert!(
            !active.get(),
            "encoding or summary before signature release"
        )
    });
}

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
    State,
}

pub(crate) fn record_type_mutation(kind: TypeMutationKind) {
    let counter = match kind {
        TypeMutationKind::Desc => &TYPE_MUTATION_DESC,
        TypeMutationKind::Level => &TYPE_MUTATION_LEVEL,
        TypeMutationKind::Row => &TYPE_MUTATION_ROW,
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

impl SignatureCopySite {
    fn record(&mut self, item_count: usize) {
        self.calls += 1;
        self.items += item_count as u64;
        self.max_items = self.max_items.max(item_count as u64);
    }
}

/// Print the 20 entries of `map` with the most items (then calls).
fn print_top_signature_sites<K: Clone>(
    map: &OnceLock<Mutex<HashMap<K, SignatureCopySite>>>,
    mut print: impl FnMut(&K, &SignatureCopySite),
) {
    let Some(map) = map.get() else {
        return;
    };
    let mut entries = map
        .lock()
        .unwrap()
        .iter()
        .map(|(key, site)| (key.clone(), *site))
        .collect::<Vec<_>>();
    entries.sort_by(|a, b| {
        b.1.items
            .cmp(&a.1.items)
            .then_with(|| b.1.calls.cmp(&a.1.calls))
    });
    for (key, site) in entries.into_iter().take(20) {
        print(&key, &site);
    }
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
        &TYPE_ITEM_RESOLVE_SCANS,
        &TYPE_ITEM_RESOLVE_SCANNED_ITEMS,
        &TYPE_ITEM_RESOLVE_TYPE_ITEMS,
        &TYPE_ITEM_RESOLVE_FOUND,
        &SIGNATURE_COPY_CALLS,
        &SIGNATURE_COPY_ITEMS,
        &SIGNATURE_COPY_MAX_ITEMS,
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
pub(crate) fn record_stored_component_build(mode: ComponentLookupApi) {
    match mode {
        ComponentLookupApi::FindModule => {
            STORED_COMPONENT_BUILD_FIND_MODULE.fetch_add(1, Ordering::Relaxed);
        }
        ComponentLookupApi::LookupModule
        | ComponentLookupApi::FindModuleDescr
        | ComponentLookupApi::FindType
        | ComponentLookupApi::FindModtype
        | ComponentLookupApi::OpenSignature => {}
    }
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
    sites
        .entry((location.file(), location.line()))
        .or_default()
        .record(item_count);
    record_current_module_signature_copy(item_count);
}

/// Record a signature qualification before the current full-copy path.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_qualification(kind: &'static str, item_count: usize) {
    let kinds = SIGNATURE_QUALIFICATION_KINDS.get_or_init(|| Mutex::new(HashMap::new()));
    let mut kinds = kinds.lock().unwrap();
    kinds.entry(kind).or_default().record(item_count);
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
    names
        .entry(format!("{kind}:{name}"))
        .or_default()
        .record(item_count);
}

/// Record a signature freshening entry point before it performs full-copy work.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_freshen(kind: &'static str, item_count: usize) {
    let kinds = SIGNATURE_FRESHEN_KINDS.get_or_init(|| Mutex::new(HashMap::new()));
    let mut kinds = kinds.lock().unwrap();
    kinds.entry(kind).or_default().record(item_count);
    record_current_module_signature_freshen(item_count);
}

/// Record a named signature freshening entry.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_freshen_name(kind: &'static str, name: &str, item_count: usize) {
    let names = SIGNATURE_FRESHEN_NAMES.get_or_init(|| Mutex::new(HashMap::new()));
    let mut names = names.lock().unwrap();
    names
        .entry(format!("{kind}:{name}"))
        .or_default()
        .record(item_count);
}

fn record_current_module_signature_copy(item_count: usize) {
    CURRENT_MODULE.with(|current| {
        let current = current.borrow();
        let Some(module) = current.as_ref() else {
            return;
        };
        let modules = MODULE_SIGNATURE_COPIES.get_or_init(|| Mutex::new(HashMap::new()));
        let mut modules = modules.lock().unwrap();
        modules
            .entry(module.clone())
            .or_default()
            .record(item_count);
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
        modules
            .entry(module.clone())
            .or_default()
            .record(item_count);
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

    eprintln!(
        "[compiler-counter] published_signature_decodes={}",
        PUBLISHED_SIGNATURE_DECODES.load(Ordering::Relaxed)
    );
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
        "[compiler-counter] stored_components cached={} build_find_module={}",
        STORED_COMPONENT_CACHED.load(Ordering::Relaxed),
        STORED_COMPONENT_BUILD_FIND_MODULE.load(Ordering::Relaxed),
    );
    eprintln!(
        "[compiler-counter] type_item_resolve scans={} scanned_items={} type_items={} found={}",
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

fn print_module_signature_copies() {
    print_top_signature_sites(&MODULE_SIGNATURE_COPIES, |module, site| {
        eprintln!(
            "[compiler-counter] module_signature_copies module={} calls={} items={} max_items={}",
            module, site.calls, site.items, site.max_items
        );
    });
}

fn print_module_signature_freshens() {
    print_top_signature_sites(&MODULE_SIGNATURE_FRESHENS, |module, site| {
        eprintln!(
            "[compiler-counter] module_signature_freshens module={} calls={} items={} max_items={}",
            module, site.calls, site.items, site.max_items
        );
    });
}

fn print_signature_qualification_names() {
    print_top_signature_sites(&SIGNATURE_QUALIFICATION_NAMES, |name, counters| {
        eprintln!(
            "[compiler-counter] signature_qualification_name name={} calls={} items={} max_items={}",
            name, counters.calls, counters.items, counters.max_items,
        );
    });
}

fn print_signature_freshen_names() {
    print_top_signature_sites(&SIGNATURE_FRESHEN_NAMES, |name, counters| {
        eprintln!(
            "[compiler-counter] signature_freshen_name name={} calls={} items={} max_items={}",
            name, counters.calls, counters.items, counters.max_items,
        );
    });
}

fn print_signature_freshen_kinds() {
    print_top_signature_sites(&SIGNATURE_FRESHEN_KINDS, |kind, counters| {
        eprintln!(
            "[compiler-counter] signature_freshen kind={} calls={} items={} max_items={}",
            kind, counters.calls, counters.items, counters.max_items,
        );
    });
}

fn print_signature_qualification_kinds() {
    print_top_signature_sites(&SIGNATURE_QUALIFICATION_KINDS, |kind, counters| {
        eprintln!(
            "[compiler-counter] signature_qualification kind={} calls={} items={} max_items={}",
            kind, counters.calls, counters.items, counters.max_items,
        );
    });
}

fn print_signature_copy_sites() {
    print_top_signature_sites(&SIGNATURE_COPY_SITES, |(file, line), counters| {
        eprintln!(
            "[compiler-counter] signature_copy_site file={} line={} calls={} items={} max_items={}",
            file, line, counters.calls, counters.items, counters.max_items,
        );
    });
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
