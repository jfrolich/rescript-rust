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

pub(crate) use checker::{
    CopyCause, ExpectedVar, census_exported_signature, census_generalize, census_instance,
    census_unify, census_update_level, record_copy, record_expected_var, record_fresh_var,
    record_local_type_nodes, record_store_build_nodes,
};

#[cfg(not(target_arch = "wasm32"))]
static ENABLED: OnceLock<bool> = OnceLock::new();

static EXPLAIN_RERUNS: AtomicU64 = AtomicU64::new(0);
static CHECK_ATTEMPTS: AtomicU64 = AtomicU64::new(0);

/// The CLI has finished preparing dependencies; subsequent attempts belong to
/// its selected source unit. Build commands retain the process-wide totals.
pub(crate) fn begin_cli_unit() {
    if enabled() {
        CHECK_ATTEMPTS.store(0, Ordering::Relaxed);
        EXPLAIN_RERUNS.store(0, Ordering::Relaxed);
    }
}


/// O(1) per whole-unit attempt, including attempts subsequently discarded.
pub(crate) fn record_check_attempt() {
    if enabled() { CHECK_ATTEMPTS.fetch_add(1, Ordering::Relaxed); }
}


/// O(1), at most one atomic increment per unit, and only with counters enabled.
pub(crate) fn record_explain_rerun() {
    if enabled() {
        EXPLAIN_RERUNS.fetch_add(1, Ordering::Relaxed);
    }
}

static SNAPSHOT_MODULE_DECODES: AtomicU64 = AtomicU64::new(0);

/// O(1), one optional counter write per decoded module, not per node/lookup.
pub fn record_snapshot_module_decode() {
    if enabled() { SNAPSHOT_MODULE_DECODES.fetch_add(1, Ordering::Relaxed); }
}

static PUBLISHED_SIGNATURE_DECODES: AtomicU64 = AtomicU64::new(0);

static SIGNATURE_NONSHAREABLE: AtomicU64 = AtomicU64::new(0);
static SIGNATURE_POOL_FULL: AtomicU64 = AtomicU64::new(0);

pub(crate) fn record_signature_fallback(pool_full: bool) {
    if enabled() {
        let counter = if pool_full { &SIGNATURE_POOL_FULL } else { &SIGNATURE_NONSHAREABLE };
        counter.fetch_add(1, Ordering::Relaxed);
    }
}

#[derive(Default)]
struct SignatureCounts {
    published: std::collections::HashSet<(u64, usize)>,
    imported: std::collections::HashSet<(u64, usize)>,
}

impl SignatureCounts {
    fn record(&mut self, key: (u64, usize), imported: bool) {
        if imported {
            if self.published.contains(&key) {
                self.imported.insert(key);
            }
        } else {
            self.published.insert(key);
        }
    }
}

#[cfg(test)]
#[test]
fn signature_counts_distinguish_imported_publications_and_generations() {
    let mut counts = SignatureCounts::default();
    counts.record((1, 7), true); // A stored interface is not this build's publication.
    assert!(counts.imported.is_empty());
    counts.record((1, 7), false);
    counts.record((1, 8), false); // A leaf.
    counts.record((1, 7), true);
    counts.record((1, 7), true); // Repeated worker acquisitions count once.
    counts.record((2, 7), false); // Address reuse in another build is a new unit.
    assert_eq!(counts.published.len(), 3);
    assert_eq!(counts.imported.len(), 1);
}

static SIGNATURE_NEXT_ID: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(1);

/// Diagnostic identity independent of allocation-address reuse by unread leaves.
pub(crate) fn signature_publication_id() -> usize {
    if enabled() { SIGNATURE_NEXT_ID.fetch_add(1, Ordering::Relaxed) } else { 0 }
}

static SIGNATURE_COUNTS: OnceLock<Mutex<SignatureCounts>> = OnceLock::new();
static SIGNATURE_NODES_FROZEN: AtomicU64 = AtomicU64::new(0);
static SIGNATURE_NODES_HASHED: AtomicU64 = AtomicU64::new(0);
static SIGNATURE_HASH_WALKS: AtomicU64 = AtomicU64::new(0);

/// A publication ID distinguishes objects even after an unread leaf is freed.
/// Import counts exclude stored/embedded interfaces and count a signature
/// acquisition, not each individual node read or repeated worker lookup.
pub(crate) fn record_signature_access(id: usize, generation: u64, imported: bool) {
    if enabled() {
        let mut counts = SIGNATURE_COUNTS.get_or_init(Default::default).lock().unwrap();
        counts.record((generation, id), imported);
    }
}

pub(crate) fn record_signature_nodes_frozen(nodes: usize) {
    if enabled() {
        SIGNATURE_NODES_FROZEN.fetch_add(nodes as u64, Ordering::Relaxed);
    }
}

pub(crate) fn record_signature_nodes_hashed(nodes: u64) {
    if enabled() {
        SIGNATURE_HASH_WALKS.fetch_add(1, Ordering::Relaxed);
        SIGNATURE_NODES_HASHED.fetch_add(nodes, Ordering::Relaxed);
    }
}

struct GentypeCounts {
    modules: AtomicU64,
    declarations: AtomicU64,
}

impl GentypeCounts {
    const fn new() -> Self {
        Self {
            modules: AtomicU64::new(0),
            declarations: AtomicU64::new(0),
        }
    }

    fn record(&self, declarations: usize) {
        self.modules.fetch_add(1, Ordering::Relaxed);
        self.declarations
            .fetch_add(declarations as u64, Ordering::Relaxed);
    }

    fn snapshot(&self) -> (u64, u64) {
        (
            self.modules.load(Ordering::Relaxed),
            self.declarations.load(Ordering::Relaxed),
        )
    }
}

static GENTYPE_COUNTS: [GentypeCounts; 2] = [GentypeCounts::new(), GentypeCounts::new()];

#[cfg(test)]
thread_local! {
    static GENTYPE_TEST_COUNTS: std::cell::Cell<[u64; 4]> = const { std::cell::Cell::new([0; 4]) };
}

#[cfg(test)]
pub(crate) fn gentype_counts_for_test() -> [u64; 4] {
    GENTYPE_TEST_COUNTS.with(std::cell::Cell::get)
}

/// Successful declaration-cache translations and the declarations they produce.
/// This excludes the separate translation for an annotated module's own output.
pub(crate) fn record_gentype_translation(annotated: bool, declarations: usize) {
    #[cfg(test)]
    GENTYPE_TEST_COUNTS.with(|counts| {
        let mut values = counts.get();
        let offset = usize::from(annotated) * 2;
        values[offset] += 1;
        values[offset + 1] += declarations as u64;
        counts.set(values);
    });
    if enabled() {
        GENTYPE_COUNTS[usize::from(annotated)].record(declarations);
    }
}

#[cfg(test)]
#[test]
fn gentype_counts_include_empty_translations_and_separate_annotation_classes() {
    let counts = [GentypeCounts::new(), GentypeCounts::new()];
    assert_eq!(counts[0].snapshot(), (0, 0));
    counts[0].record(0);
    counts[0].record(3);
    counts[1].record(5);
    assert_eq!(counts[0].snapshot(), (2, 3));
    assert_eq!(counts[1].snapshot(), (1, 5));
}

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

/// Attempt-local journal counters. Dense fields, no atomic or TLS operations.
/// One instance per speculative unit, never per node.
#[derive(Default)]
pub(crate) struct AttemptCounters {
    mutations: [u64; 4],
    snapshots: u64,
    backtracks: u64,
    restores: u64,
    peak_depth: u64,
}

impl AttemptCounters {
    /// O(1): add one write to the counter indexed by its mutation kind.
    pub(crate) fn mutation(&mut self, kind: TypeMutationKind) {
        self.mutations[kind as usize] += 1;
    }

    /// O(1): count one snapshot, retaining the maximum live depth.
    pub(crate) fn snapshot(&mut self, depth: usize) {
        self.snapshots += 1;
        self.peak_depth = self.peak_depth.max(depth as u64);
    }

    /// O(1): count one rollback and its already-known number of restorations.
    pub(crate) fn backtrack(&mut self, restores: usize) {
        self.backtracks += 1;
        self.restores += restores as u64;
    }

    /// O(1), eight atomic updates once per retained attempt, not per mutation.
    pub(crate) fn publish(self) {
        for (counter, count) in [
            &TYPE_MUTATION_DESC, &TYPE_MUTATION_LEVEL,
            &TYPE_MUTATION_ROW, &TYPE_MUTATION_STATE,
        ].into_iter().zip(self.mutations) {
            counter.fetch_add(count, Ordering::Relaxed);
        }
        TYPE_MUTATION_SNAPSHOTS.fetch_add(self.snapshots, Ordering::Relaxed);
        TYPE_MUTATION_BACKTRACKS.fetch_add(self.backtracks, Ordering::Relaxed);
        TYPE_MUTATION_RESTORES.fetch_add(self.restores, Ordering::Relaxed);
        TYPE_MUTATION_PEAK_DEPTH.fetch_max(self.peak_depth, Ordering::Relaxed);
    }
}

/// O(1): update the unit's plain fields, or publish for non-attempt callers.
pub(crate) fn record_type_mutation(ctx: &crate::types::TypeContext, kind: TypeMutationKind) {
    ctx.record_attempt_counter(|c| c.mutation(kind));
}

/// O(1): count one snapshot in the active unit attempt.
pub(crate) fn record_type_mutation_snapshot(ctx: &crate::types::TypeContext, depth: usize) {
    ctx.record_attempt_counter(|c| c.snapshot(depth));
}

/// O(1): count one backtrack in the active unit attempt.
pub(crate) fn record_type_mutation_backtrack(ctx: &crate::types::TypeContext, restores: usize) {
    ctx.record_attempt_counter(|c| c.backtrack(restores));
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

/// Counters of shared store data (stage P4 of `docs/CHECKER_REDESIGN.md`):
/// how often persistent-rooted component views are built against how many
/// distinct views exist, and what replaying their pieces costs.
pub(crate) mod store_views {
    use std::sync::atomic::{AtomicU64, Ordering};

    static PIECES_BUILT: AtomicU64 = AtomicU64::new(0);
    static PIECES_EMPTY: AtomicU64 = AtomicU64::new(0);
    static PIECES_POISONED: AtomicU64 = AtomicU64::new(0);
    static BINDERS: AtomicU64 = AtomicU64::new(0);
    static PIECES_REPLAYED: AtomicU64 = AtomicU64::new(0);
    /// Replayed effects: unit preparations.
    static EFFECTS_REPLAYED: [AtomicU64; 1] = [const { AtomicU64::new(0) }; 1];

    /// A store build ended: with effects or guards, with none, or poisoned.
    pub(crate) fn record_piece(poisoned: bool, empty: bool) {
        let counter = if poisoned {
            &PIECES_POISONED
        } else if empty {
            &PIECES_EMPTY
        } else {
            &PIECES_BUILT
        };
        counter.fetch_add(1, Ordering::Relaxed);
    }

    /// A binder was created inside a store build.
    pub(crate) fn record_binder() {
        BINDERS.fetch_add(1, Ordering::Relaxed);
    }

    /// A compilation replayed a piece for the first time.
    pub(crate) fn record_piece_replay() {
        PIECES_REPLAYED.fetch_add(1, Ordering::Relaxed);
    }

    /// A replayed effect (index as in `EFFECTS_REPLAYED`).
    pub(crate) fn record_effect_replayed(kind: usize) {
        EFFECTS_REPLAYED[kind].fetch_add(1, Ordering::Relaxed);
    }

    pub(super) fn reset() {
        for counter in [
            &PIECES_BUILT,
            &PIECES_EMPTY,
            &PIECES_POISONED,
            &BINDERS,
            &PIECES_REPLAYED,
        ]
        .into_iter()
        .chain(&EFFECTS_REPLAYED)
        {
            counter.store(0, Ordering::Relaxed);
        }
    }

    pub(super) fn print_report() {
        let load = |counter: &AtomicU64| counter.load(Ordering::Relaxed);
        // Printed only when a store build ran or a piece was replayed:
        // neither happens once every persistent-rooted path is a world
        // view.
        let pieces = load(&PIECES_BUILT) + load(&PIECES_EMPTY) + load(&PIECES_POISONED);
        if pieces == 0 && load(&PIECES_REPLAYED) == 0 {
            return;
        }
        eprintln!(
            "[compiler-counter] store_pieces with_effects={} empty={} poisoned={} binders={}",
            load(&PIECES_BUILT),
            load(&PIECES_EMPTY),
            load(&PIECES_POISONED),
            load(&BINDERS),
        );
        eprintln!(
            "[compiler-counter] store_replay pieces={} prepare_pers={}",
            load(&PIECES_REPLAYED),
            load(&EFFECTS_REPLAYED[0]),
        );
    }
}

/// Reads and overlay writes of published type data. Callers gate these on
/// the context's cached counters flag and exclude nodes still being built.
pub(crate) mod frozen {
    use std::sync::atomic::{AtomicU64, Ordering};

    #[derive(Clone, Copy)]
    pub(crate) enum Kind {
        DescReadShared,
        DescReadWorker,
        LevelReadShared,
        LevelReadWorker,
        LinkShared,
        DescWriteShared,
        LinkWorker,
        LevelWriteShared,
        LevelWriteWorker,
        MemoWrite,
        RowFieldWrite,
        MutabilityWrite,
    }

    static COUNTS: [AtomicU64; 12] = [const { AtomicU64::new(0) }; 12];
    const NAMES: [&str; 12] = [
        "desc_read_shared",
        "desc_read_worker",
        "level_read_shared",
        "level_read_worker",
        "link_shared",
        "desc_write_shared",
        "link_worker",
        "level_write_shared",
        "level_write_worker",
        "memo_write",
        "row_field_write",
        "mutability_write",
    ];

    pub(crate) fn record(kind: Kind) {
        COUNTS[kind as usize].fetch_add(1, Ordering::Relaxed);
    }

    #[cfg(test)]
    pub(crate) fn count(kind: Kind) -> u64 {
        COUNTS[kind as usize].load(Ordering::Relaxed)
    }

    pub(super) fn reset() {
        for counter in &COUNTS {
            counter.store(0, Ordering::Relaxed);
        }
    }

    pub(super) fn print_report() {
        let fields: Vec<_> = NAMES
            .iter()
            .zip(&COUNTS)
            .map(|(name, counter)| format!("{name}={}", counter.load(Ordering::Relaxed)))
            .collect();
        eprintln!("[compiler-counter] frozen {}", fields.join(" "));
    }
}

/// What a build's world holds besides its units.
pub(crate) mod world {
    use std::sync::atomic::{AtomicU64, Ordering};

    static PREDEF_BUILDS: AtomicU64 = AtomicU64::new(0);
    static PREDEF_NODES: AtomicU64 = AtomicU64::new(0);

    /// The predefined declarations were built and frozen into `nodes` nodes.
    pub(crate) fn record_predef_build(nodes: usize) {
        if super::enabled() {
            PREDEF_BUILDS.fetch_add(1, Ordering::Relaxed);
            PREDEF_NODES.fetch_add(nodes as u64, Ordering::Relaxed);
        }
    }

    static VIEWS_BUILT: AtomicU64 = AtomicU64::new(0);
    static VIEWS_ADOPTED: AtomicU64 = AtomicU64::new(0);
    static VIEWS_FAILED: AtomicU64 = AtomicU64::new(0);
    static VIEW_NODES_COPIED: AtomicU64 = AtomicU64::new(0);
    static CHILDREN_FORCED: AtomicU64 = AtomicU64::new(0);
    static CHILD_NODES: AtomicU64 = AtomicU64::new(0);

    /// What the views of a build hold: signature items, values,
    /// constructors and labels of the lookup tables, then the opened
    /// values, types, constructors and labels.
    static VIEW_ITEMS: [AtomicU64; 8] = [const { AtomicU64::new(0) }; 8];

    /// A module view was built; freezing it created `nodes` nodes, and it
    /// holds `items` (see `VIEW_ITEMS`). The caller tests the flag.
    pub(crate) fn record_view_build(nodes: usize, items: [usize; 8]) {
        VIEWS_BUILT.fetch_add(1, Ordering::Relaxed);
        VIEW_NODES_COPIED.fetch_add(nodes as u64, Ordering::Relaxed);
        for (total, count) in VIEW_ITEMS.iter().zip(items) {
            total.fetch_add(count as u64, Ordering::Relaxed);
        }
    }

    /// The pool had no room for a module view.
    pub(crate) fn record_view_failure() {
        if super::enabled() {
            VIEWS_FAILED.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// A compilation adopted a module view. The caller tests the flag.
    pub(crate) fn record_view_adoption() {
        VIEWS_ADOPTED.fetch_add(1, Ordering::Relaxed);
    }

    static PAPPLY_VIEWS: AtomicU64 = AtomicU64::new(0);

    /// A compilation built the component tables of a path with a functor
    /// application on it (`F(X).t`): such a path has no world view, so each
    /// compilation that uses it builds them. The caller tests the flag.
    pub(crate) fn record_papply_view_build() {
        PAPPLY_VIEWS.fetch_add(1, Ordering::Relaxed);
    }

    /// A child module declaration of a view was forced into `nodes` nodes.
    pub(crate) fn record_forced_child(nodes: usize) {
        if super::enabled() {
            CHILDREN_FORCED.fetch_add(1, Ordering::Relaxed);
            CHILD_NODES.fetch_add(nodes as u64, Ordering::Relaxed);
        }
    }

    pub(super) fn reset() {
        PREDEF_BUILDS.store(0, Ordering::Relaxed);
        PREDEF_NODES.store(0, Ordering::Relaxed);
        VIEWS_BUILT.store(0, Ordering::Relaxed);
        VIEWS_ADOPTED.store(0, Ordering::Relaxed);
        VIEWS_FAILED.store(0, Ordering::Relaxed);
        for total in &VIEW_ITEMS {
            total.store(0, Ordering::Relaxed);
        }
        VIEW_NODES_COPIED.store(0, Ordering::Relaxed);
        CHILDREN_FORCED.store(0, Ordering::Relaxed);
        CHILD_NODES.store(0, Ordering::Relaxed);
        PAPPLY_VIEWS.store(0, Ordering::Relaxed);
    }

    pub(super) fn print_report() {
        eprintln!(
            "[compiler-counter] world predef_builds={} predef_nodes={}",
            PREDEF_BUILDS.load(Ordering::Relaxed),
            PREDEF_NODES.load(Ordering::Relaxed),
        );
        eprintln!(
            "[compiler-counter] world_views built={} adopted={} failed={} children_forced={}",
            VIEWS_BUILT.load(Ordering::Relaxed),
            VIEWS_ADOPTED.load(Ordering::Relaxed),
            VIEWS_FAILED.load(Ordering::Relaxed),
            CHILDREN_FORCED.load(Ordering::Relaxed),
        );
        eprintln!(
            "[compiler-counter] papply_views built={}",
            PAPPLY_VIEWS.load(Ordering::Relaxed),
        );
        let items = |index: usize| VIEW_ITEMS[index].load(Ordering::Relaxed);
        eprintln!(
            "[compiler-counter] world_view_items signature_items={} values={} constructors={} labels={} opened_values={} opened_types={} opened_constructors={} opened_labels={}",
            items(0),
            items(1),
            items(2),
            items(3),
            items(4),
            items(5),
            items(6),
            items(7),
        );
        eprintln!(
            "[compiler-counter] world_view_nodes copied={} shared=0 child_nodes={}",
            VIEW_NODES_COPIED.load(Ordering::Relaxed),
            CHILD_NODES.load(Ordering::Relaxed),
        );
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
    EXPLAIN_RERUNS.store(0, Ordering::Relaxed);
    SNAPSHOT_MODULE_DECODES.store(0, Ordering::Relaxed);
    if !enabled() {
        return;
    }

    store_views::reset();
    frozen::reset();
    world::reset();
    for counts in &GENTYPE_COUNTS {
        counts.modules.store(0, Ordering::Relaxed);
        counts.declarations.store(0, Ordering::Relaxed);
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
    checker::reset();
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

    eprintln!("[compiler-counter] explain_reruns={}", EXPLAIN_RERUNS.load(Ordering::Relaxed));
    eprintln!("[compiler-counter] check_attempts={}", CHECK_ATTEMPTS.load(Ordering::Relaxed));
    eprintln!("[compiler-counter] snapshot_modules_decoded={}", SNAPSHOT_MODULE_DECODES.load(Ordering::Relaxed));
    eprintln!(
        "[compiler-counter] published_signature_decodes={}",
        PUBLISHED_SIGNATURE_DECODES.load(Ordering::Relaxed)
    );
    eprintln!("signature_nonshareable={} signature_pool_full={}",
        SIGNATURE_NONSHAREABLE.load(Ordering::Relaxed), SIGNATURE_POOL_FULL.load(Ordering::Relaxed));

    if let Some(counts) = SIGNATURE_COUNTS.get() {
        let counts = counts.lock().unwrap();
        eprintln!(
            "[compiler-counter] signature_units_published={} signature_units_imported={} signature_nodes_frozen={} signature_nodes_hashed={} signature_hash_walks={}",
            counts.published.len(), counts.imported.len(),
            SIGNATURE_NODES_FROZEN.load(Ordering::Relaxed),
            SIGNATURE_NODES_HASHED.load(Ordering::Relaxed),
            SIGNATURE_HASH_WALKS.load(Ordering::Relaxed),
        );
    }

    for (index, annotated) in [false, true].into_iter().enumerate() {
        let (modules, declarations) = GENTYPE_COUNTS[index].snapshot();
        eprintln!(
            "[compiler-counter] gentype annotated={annotated} modules={modules} declarations={declarations}",
        );
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
    store_views::print_report();
    frozen::print_report();
    world::print_report();
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
    checker::print_report();
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

/// Counters for the type checker redesign
/// (`compiler-rust/docs/CHECKER_REDESIGN.md`, section F.2): where type nodes
/// come from, how much of the instantiation, generalisation and level work
/// is on variable-free types, what the two sides of a unification are, why
/// fresh variables are made, and how large a unit's exported type graph is.
///
/// A type is *ground* here when no type variable and no universal variable
/// is reachable from it (the design's `HAS_VAR` and `HAS_UNIVAR` both
/// clear). The design also keeps a constructor bound inside an expression
/// out of its ground tier (`HAS_SCOPED`); these counters do not look at
/// binding times, so they count such a type as ground.
///
/// Every function here is called only when [`enabled`] is true, from the
/// entry of an operation, never from its per-node loop. The censuses walk
/// the type on the side and write nothing: they follow links without
/// compressing them.
mod checker {
    use std::collections::HashMap;
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicU64, Ordering};

    use crate::fast_hash::AHashMap;
    use crate::types::btype;
    use crate::types::context::TypeContext;
    use crate::types::decl::SignatureItem;
    use crate::types::type_expr::{GENERIC_LEVEL, RowField, TypeDesc, TypeExprRef};

    /// What a copy of types is made for.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    pub(crate) enum CopyCause {
        /// `instance` and its variants (`copy_type_cached`).
        #[default]
        Instance,
        /// `Subst.type_expr Subst.identity` (`subst_identity_copy`).
        SubstIdentity,
        /// The copy of a looked-up or saved signature item
        /// (`copy_lookup_type_expr_with_paths`).
        Lookup,
        /// `nondep_type`.
        Nondep,
    }

    impl CopyCause {
        const ALL: [CopyCause; 4] = [
            CopyCause::Instance,
            CopyCause::SubstIdentity,
            CopyCause::Lookup,
            CopyCause::Nondep,
        ];

        fn name(self) -> &'static str {
            match self {
                CopyCause::Instance => "instance",
                CopyCause::SubstIdentity => "subst_identity",
                CopyCause::Lookup => "lookup_copy",
                CopyCause::Nondep => "nondep",
            }
        }
    }

    /// The expression a fresh variable is made the expected type of, by the
    /// case of the design's section C.9.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub(crate) struct ExpectedVar {
        /// The construct, as the parse tree names it.
        pub construct: &'static str,
        /// The C.9 case, 1 to 5.
        pub case: u8,
    }

    static COPY_SESSIONS: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];
    static COPY_NODES: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];
    static TYPE_CONTEXTS: AtomicU64 = AtomicU64::new(0);
    static LOCAL_NODES: AtomicU64 = AtomicU64::new(0);
    static STORE_BUILDS: AtomicU64 = AtomicU64::new(0);
    static STORE_BUILD_NODES: AtomicU64 = AtomicU64::new(0);

    static FRESH_VARS: AtomicU64 = AtomicU64::new(0);
    static FRESH_VAR_SITES: Mutex<Option<HashMap<(&'static str, u32), u64>>> = Mutex::new(None);
    static EXPECTED_VARS: Mutex<Option<HashMap<ExpectedVar, u64>>> = Mutex::new(None);

    /// Calls, calls whose every root is ground, visited nodes, ground
    /// visited nodes.
    struct WalkCounters {
        calls: AtomicU64,
        ground_calls: AtomicU64,
        visits: AtomicU64,
        ground_visits: AtomicU64,
    }

    impl WalkCounters {
        const fn new() -> Self {
            WalkCounters {
                calls: AtomicU64::new(0),
                ground_calls: AtomicU64::new(0),
                visits: AtomicU64::new(0),
                ground_visits: AtomicU64::new(0),
            }
        }

        fn all(&self) -> [&AtomicU64; 4] {
            [
                &self.calls,
                &self.ground_calls,
                &self.visits,
                &self.ground_visits,
            ]
        }

        fn print(&self, name: &str, visit: &str) {
            let calls = self.calls.load(Ordering::Relaxed);
            let ground_calls = self.ground_calls.load(Ordering::Relaxed);
            let visits = self.visits.load(Ordering::Relaxed);
            let ground_visits = self.ground_visits.load(Ordering::Relaxed);
            eprintln!(
                "[compiler-counter] {name} calls={calls} ground_calls={ground_calls} ({}) {visit}={visits} ground_{visit}={ground_visits} ({})",
                percent(ground_calls, calls),
                percent(ground_visits, visits),
            );
        }
    }

    static INSTANCE: WalkCounters = WalkCounters::new();
    static GENERALIZE: WalkCounters = WalkCounters::new();
    static UPDATE_LEVEL: WalkCounters = WalkCounters::new();

    const UNIFY_SHAPES: usize = 8;
    const UNIFY_SHAPE_NAMES: [&str; UNIFY_SHAPES] = [
        "same_node",
        "identical_ground",
        "different_ground",
        "var_ground",
        "var_nonground",
        "var_var",
        "structure_one_ground",
        "structure_nonground",
    ];
    static UNIFY: [AtomicU64; UNIFY_SHAPES] = [const { AtomicU64::new(0) }; UNIFY_SHAPES];
    /// Top-level unifications by the two head constructors.
    static UNIFY_HEADS: Mutex<Option<HashMap<(&'static str, &'static str), u64>>> =
        Mutex::new(None);

    static EXPORT_UNITS: AtomicU64 = AtomicU64::new(0);
    static EXPORT_NODES: AtomicU64 = AtomicU64::new(0);
    static EXPORT_NONGROUND_NODES: AtomicU64 = AtomicU64::new(0);
    static EXPORT_MAX_NONGROUND_NODES: AtomicU64 = AtomicU64::new(0);
    static EXPORT_RECURSIVE_GROUND: AtomicU64 = AtomicU64::new(0);
    /// Non-ground and all exported nodes per unit.
    static EXPORT_BY_UNIT: Mutex<Vec<(String, u64, u64)>> = Mutex::new(Vec::new());

    fn percent(part: u64, whole: u64) -> String {
        if whole == 0 {
            "-".to_string()
        } else {
            format!("{:.1}%", 100.0 * part as f64 / whole as f64)
        }
    }

    pub(super) fn derived_snapshot() -> [u64; 3] {
        [FRESH_VARS.load(Ordering::Relaxed),
         UNIFY.iter().map(|c| c.load(Ordering::Relaxed)).sum(),
         COPY_NODES[CopyCause::Instance as usize].load(Ordering::Relaxed)]
    }

    pub(super) fn reset() {
        let walks = [&INSTANCE, &GENERALIZE, &UPDATE_LEVEL];
        for counter in COPY_SESSIONS
            .iter()
            .chain(&COPY_NODES)
            .chain(&UNIFY)
            .chain(walks.iter().flat_map(|walk| walk.all()))
            .chain([
                &TYPE_CONTEXTS,
                &LOCAL_NODES,
                &STORE_BUILDS,
                &STORE_BUILD_NODES,
                &FRESH_VARS,
                &EXPORT_UNITS,
                &EXPORT_NODES,
                &EXPORT_NONGROUND_NODES,
                &EXPORT_MAX_NONGROUND_NODES,
                &EXPORT_RECURSIVE_GROUND,
            ])
        {
            counter.store(0, Ordering::Relaxed);
        }
        *FRESH_VAR_SITES.lock().unwrap() = None;
        *EXPECTED_VARS.lock().unwrap() = None;
        *UNIFY_HEADS.lock().unwrap() = None;
        EXPORT_BY_UNIT.lock().unwrap().clear();
    }

    /// A copy for `cause` allocated `nodes` type nodes, not counting the
    /// copies nested in it.
    pub(crate) fn record_copy(cause: CopyCause, nodes: usize) {
        let index = cause as usize;
        COPY_SESSIONS[index].fetch_add(1, Ordering::Relaxed);
        COPY_NODES[index].fetch_add(nodes as u64, Ordering::Relaxed);
    }

    /// A compilation's own node pool is dropped holding `nodes` nodes.
    pub(crate) fn record_local_type_nodes(nodes: usize) {
        TYPE_CONTEXTS.fetch_add(1, Ordering::Relaxed);
        LOCAL_NODES.fetch_add(nodes as u64, Ordering::Relaxed);
    }

    /// An outermost store build allocated `nodes` nodes in the worker store.
    pub(crate) fn record_store_build_nodes(nodes: usize) {
        STORE_BUILDS.fetch_add(1, Ordering::Relaxed);
        STORE_BUILD_NODES.fetch_add(nodes as u64, Ordering::Relaxed);
    }

    /// `new_var` and its variants, called from `location` outside a copy
    /// session.
    pub(crate) fn record_fresh_var(location: &'static std::panic::Location<'static>) {
        FRESH_VARS.fetch_add(1, Ordering::Relaxed);
        *FRESH_VAR_SITES
            .lock()
            .unwrap()
            .get_or_insert_with(HashMap::new)
            .entry((location.file(), location.line()))
            .or_default() += 1;
    }

    /// A fresh variable was made only to be the expected type of an
    /// expression.
    pub(crate) fn record_expected_var(var: ExpectedVar) {
        *EXPECTED_VARS
            .lock()
            .unwrap()
            .get_or_insert_with(HashMap::new)
            .entry(var)
            .or_default() += 1;
    }

    /// The representative of `ty`, without compressing the links.
    fn resolve(ctx: &TypeContext, mut ty: TypeExprRef) -> TypeExprRef {
        loop {
            match &*ctx.borrow_desc(ty) {
                TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => ty = *next,
                _ => return ty,
            }
        }
    }

    fn head_name(desc: &TypeDesc) -> &'static str {
        match desc {
            TypeDesc::Tvar(_) => "var",
            TypeDesc::Tarrow { .. } => "arrow",
            TypeDesc::Ttuple(_) => "tuple",
            TypeDesc::Tconstr { .. } => "constr",
            TypeDesc::Tobject { .. } => "object",
            TypeDesc::Tfield { .. } => "field",
            TypeDesc::Tnil => "nil",
            TypeDesc::Tlink(_) | TypeDesc::Tsubst(_) => "link",
            TypeDesc::Tvariant(_) => "variant",
            TypeDesc::Tunivar(_) => "univar",
            TypeDesc::Tpoly { .. } => "poly",
            TypeDesc::Tpackage { .. } => "package",
        }
    }

    /// The resolved children of the representative `ty`.
    fn children(ctx: &TypeContext, ty: TypeExprRef, out: &mut Vec<TypeExprRef>) {
        let start = out.len();
        match ctx.get_desc(ty).into_desc() {
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
            TypeDesc::Tarrow { args, ret } => {
                out.extend(ctx.type_args(args).iter().map(|arg| arg.typ));
                out.push(ret);
            }
            TypeDesc::Ttuple(types) => out.extend(ctx.type_list(types).iter()),
            TypeDesc::Tconstr { args, .. } | TypeDesc::Tpackage { args, .. } => {
                out.extend(ctx.type_list(args).iter());
            }
            TypeDesc::Tobject { fields } => out.push(fields),
            TypeDesc::Tfield { typ, rest, .. } => {
                out.push(typ);
                out.push(rest);
            }
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => out.push(next),
            TypeDesc::Tvariant(row) => {
                let row = ctx.row_desc(row);
                for (_, field) in row.row_fields.iter() {
                    match btype::row_field_repr(ctx, field) {
                        RowField::Rpresent(ty) => out.extend(ty),
                        RowField::Reither { types, .. } => out.extend(types),
                        RowField::Rabsent => {}
                    }
                }
                out.push(row.row_more);
                if let Some((_, args)) = &row.row_name {
                    out.extend(args.iter().copied());
                }
            }
            TypeDesc::Tpoly { body, vars } => {
                out.push(body);
                out.extend(ctx.type_list(vars).iter());
            }
        }
        for child in &mut out[start..] {
            *child = resolve(ctx, *child);
        }
    }

    /// The type graph reachable from some roots, with which of its nodes
    /// are ground.
    #[derive(Default)]
    pub(super) struct Graph {
        index: AHashMap<TypeExprRef, u32>,
        nodes: Vec<TypeExprRef>,
        /// `edges[edge_start[n]..edge_start[n + 1]]` are node `n`'s children.
        edge_start: Vec<u32>,
        edges: Vec<u32>,
        /// A variable is reachable from the node.
        nonground: Vec<bool>,
        /// The node contains itself.
        recursive: Vec<bool>,
    }

    impl Graph {
        pub(super) fn of(
            ctx: &TypeContext,
            roots: impl IntoIterator<Item = TypeExprRef>,
        ) -> (Graph, Vec<u32>) {
            let mut graph = Graph::default();
            let mut root_nodes = Vec::new();
            for root in roots {
                let root = resolve(ctx, root);
                root_nodes.push(graph.node(root));
            }
            // Nodes get their index when first seen and their edges in index
            // order, so `edge_start` is filled front to back.
            let mut scratch = Vec::new();
            let mut next = 0;
            while next < graph.nodes.len() {
                let ty = graph.nodes[next];
                scratch.clear();
                children(ctx, ty, &mut scratch);
                graph.edge_start.push(graph.edges.len() as u32);
                for child in &scratch {
                    let child = graph.node(*child);
                    graph.edges.push(child);
                }
                let is_var = matches!(
                    &*ctx.borrow_desc(ty),
                    TypeDesc::Tvar(_) | TypeDesc::Tunivar(_)
                );
                graph.nonground.push(is_var);
                next += 1;
            }
            graph.edge_start.push(graph.edges.len() as u32);
            graph.propagate_nonground();
            graph.mark_recursive();
            (graph, root_nodes)
        }

        fn node(&mut self, ty: TypeExprRef) -> u32 {
            let next = self.nodes.len() as u32;
            let index = *self.index.entry(ty).or_insert(next);
            if index == next {
                self.nodes.push(ty);
            }
            index
        }

        /// The number of distinct types reached.
        pub(super) fn len(&self) -> usize {
            self.nodes.len()
        }

        pub(super) fn is_ground(&self, node: u32) -> bool {
            !self.nonground[node as usize]
        }

        /// The ground types that contain themselves.
        pub(super) fn recursive_ground(&self) -> usize {
            self.recursive
                .iter()
                .zip(&self.nonground)
                .filter(|(recursive, nonground)| **recursive && !**nonground)
                .count()
        }

        fn children_of(&self, node: u32) -> &[u32] {
            let node = node as usize;
            &self.edges[self.edge_start[node] as usize..self.edge_start[node + 1] as usize]
        }

        /// A node is not ground when a variable is reachable from it: walk
        /// the edges backwards from the variables.
        fn propagate_nonground(&mut self) {
            let count = self.nodes.len();
            let mut parent_start = vec![0u32; count + 1];
            for &child in &self.edges {
                parent_start[child as usize + 1] += 1;
            }
            for node in 0..count {
                parent_start[node + 1] += parent_start[node];
            }
            let mut fill = parent_start.clone();
            let mut parents = vec![0u32; self.edges.len()];
            for node in 0..count as u32 {
                for &child in self.children_of(node) {
                    parents[fill[child as usize] as usize] = node;
                    fill[child as usize] += 1;
                }
            }
            let mut work: Vec<u32> = (0..count as u32)
                .filter(|node| self.nonground[*node as usize])
                .collect();
            while let Some(node) = work.pop() {
                let node = node as usize;
                for &parent in
                    &parents[parent_start[node] as usize..parent_start[node + 1] as usize]
                {
                    if !self.nonground[parent as usize] {
                        self.nonground[parent as usize] = true;
                        work.push(parent);
                    }
                }
            }
        }

        /// Mark the nodes a depth-first walk reaches again while they are
        /// still open: each is the head of a cycle.
        fn mark_recursive(&mut self) {
            let count = self.nodes.len();
            self.recursive = vec![false; count];
            // 0: not seen, 1: open, 2: done.
            let mut state = vec![0u8; count];
            let mut stack: Vec<(u32, u32)> = Vec::new();
            for start in 0..count as u32 {
                if state[start as usize] != 0 {
                    continue;
                }
                state[start as usize] = 1;
                stack.push((start, 0));
                while let Some((node, position)) = stack.last_mut() {
                    let node = *node;
                    let edges = self.children_of(node);
                    if let Some(&child) = edges.get(*position as usize) {
                        *position += 1;
                        match state[child as usize] {
                            0 => {
                                state[child as usize] = 1;
                                stack.push((child, 0));
                            }
                            1 => self.recursive[child as usize] = true,
                            _ => {}
                        }
                    } else {
                        state[node as usize] = 2;
                        stack.pop();
                    }
                }
            }
        }

        /// The nodes a walk from `roots` visits when it enters a node only
        /// if `enters` holds for it: how many, and how many of them ground.
        pub(super) fn visit(
            &self,
            roots: &[u32],
            mut enters: impl FnMut(TypeExprRef) -> bool,
        ) -> (u64, u64) {
            let mut seen = vec![false; self.nodes.len()];
            let mut work: Vec<u32> = Vec::new();
            let (mut visits, mut ground) = (0, 0);
            for &root in roots {
                work.push(root);
                while let Some(node) = work.pop() {
                    if std::mem::replace(&mut seen[node as usize], true)
                        || !enters(self.nodes[node as usize])
                    {
                        continue;
                    }
                    visits += 1;
                    if self.is_ground(node) {
                        ground += 1;
                    }
                    work.extend_from_slice(self.children_of(node));
                }
            }
            (visits, ground)
        }
    }

    fn census_walk(
        ctx: &TypeContext,
        counters: &WalkCounters,
        roots: impl IntoIterator<Item = TypeExprRef>,
        enters: impl FnMut(TypeExprRef) -> bool,
    ) {
        let (graph, roots) = Graph::of(ctx, roots);
        let (visits, ground_visits) = graph.visit(&roots, enters);
        counters.calls.fetch_add(1, Ordering::Relaxed);
        if roots.iter().all(|root| graph.is_ground(*root)) {
            counters.ground_calls.fetch_add(1, Ordering::Relaxed);
        }
        counters.visits.fetch_add(visits, Ordering::Relaxed);
        counters
            .ground_visits
            .fetch_add(ground_visits, Ordering::Relaxed);
    }

    /// An instantiation of `roots` in one copy session is about to run: it
    /// copies the nodes at the generic level it reaches through such nodes.
    pub(crate) fn census_instance(ctx: &TypeContext, roots: impl IntoIterator<Item = TypeExprRef>) {
        census_walk(ctx, &INSTANCE, roots, |ty| {
            ctx.get_level(ty) == GENERIC_LEVEL
        });
    }

    /// A generalisation of `ty` is about to run: it visits the nodes above
    /// `level` that are not generic yet.
    pub(crate) fn census_generalize(ctx: &TypeContext, level: i32, ty: TypeExprRef) {
        census_walk(ctx, &GENERALIZE, [ty], |ty| {
            let node_level = ctx.get_level(ty);
            node_level > level && node_level != GENERIC_LEVEL
        });
    }

    /// `ty` is about to be lowered to `level`: the walk visits the nodes
    /// above it.
    pub(crate) fn census_update_level(ctx: &TypeContext, level: i32, ty: TypeExprRef) {
        census_walk(ctx, &UPDATE_LEVEL, [ty], |ty| ctx.get_level(ty) > level);
    }

    /// Whether two ground types are the same type without expanding
    /// anything: the same constructors and paths all the way down.
    fn identical(ctx: &TypeContext, t1: TypeExprRef, t2: TypeExprRef, budget: &mut u32) -> bool {
        let (t1, t2) = (resolve(ctx, t1), resolve(ctx, t2));
        if t1 == t2 {
            return true;
        }
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        let (d1, d2) = (ctx.get_desc(t1).into_desc(), ctx.get_desc(t2).into_desc());
        let same_head = match (&d1, &d2) {
            (TypeDesc::Tconstr { path: p1, .. }, TypeDesc::Tconstr { path: p2, .. }) => p1.same(p2),
            (TypeDesc::Tarrow { args: a1, .. }, TypeDesc::Tarrow { args: a2, .. }) => {
                let (a1, a2) = (ctx.type_args(*a1), ctx.type_args(*a2));
                a1.len() == a2.len()
                    && a1.iter().zip(a2.iter()).all(|(x, y)| {
                        x.label().label_name() == y.label().label_name()
                            && x.label().is_optional() == y.label().is_optional()
                    })
            }
            (TypeDesc::Ttuple(_), TypeDesc::Ttuple(_)) | (TypeDesc::Tnil, TypeDesc::Tnil) => true,
            // Rows, objects and packages are compared by the unifier's own
            // rules; they are not counted as identical here.
            _ => false,
        };
        if !same_head {
            return false;
        }
        let (mut c1, mut c2) = (Vec::new(), Vec::new());
        children(ctx, t1, &mut c1);
        children(ctx, t2, &mut c2);
        c1.len() == c2.len()
            && c1
                .iter()
                .zip(&c2)
                .all(|(x, y)| identical(ctx, *x, *y, budget))
    }

    /// A top-level unification of `t1` and `t2` is about to run.
    pub(crate) fn census_unify(ctx: &TypeContext, t1: TypeExprRef, t2: TypeExprRef) {
        let (t1, t2) = (resolve(ctx, t1), resolve(ctx, t2));
        let (d1, d2) = (ctx.get_desc(t1).into_desc(), ctx.get_desc(t2).into_desc());
        *UNIFY_HEADS
            .lock()
            .unwrap()
            .get_or_insert_with(HashMap::new)
            .entry((head_name(&d1), head_name(&d2)))
            .or_default() += 1;
        let shape = if t1 == t2 {
            0
        } else {
            let (graph, roots) = Graph::of(ctx, [t1, t2]);
            let ground1 = graph.is_ground(roots[0]);
            let ground2 = graph.is_ground(roots[1]);
            let var1 = matches!(d1, TypeDesc::Tvar(_));
            let var2 = matches!(d2, TypeDesc::Tvar(_));
            match (var1, var2) {
                (true, true) => 5,
                (true, false) if ground2 => 3,
                (false, true) if ground1 => 3,
                (true, false) | (false, true) => 4,
                (false, false) if ground1 && ground2 => {
                    if identical(ctx, t1, t2, &mut 10_000) {
                        1
                    } else {
                        2
                    }
                }
                (false, false) if ground1 || ground2 => 6,
                (false, false) => 7,
            }
        };
        UNIFY[shape].fetch_add(1, Ordering::Relaxed);
    }

    fn signature_types(sig: &[SignatureItem], out: &mut Vec<TypeExprRef>) {
        use crate::types::decl::{ConstructorArguments, ModuleType, TypeInlinedType, TypeKind};
        fn module_type(mty: &ModuleType, out: &mut Vec<TypeExprRef>) {
            match mty {
                ModuleType::MtyIdent(_) | ModuleType::MtyAlias(..) => {}
                ModuleType::MtySignature(sig) => signature_types(sig, out),
                ModuleType::MtyFunctor {
                    param_type, result, ..
                } => {
                    if let Some(param_type) = param_type {
                        module_type(param_type, out);
                    }
                    module_type(result, out);
                }
            }
        }
        fn arguments(args: &ConstructorArguments, out: &mut Vec<TypeExprRef>) {
            match args {
                ConstructorArguments::CstrTuple(types) => out.extend(types.iter().copied()),
                ConstructorArguments::CstrRecord(labels) => {
                    out.extend(labels.iter().map(|label| label.ld_type));
                }
            }
        }
        for item in sig {
            match item {
                SignatureItem::SigValue(_, decl) => out.push(decl.val_type),
                SignatureItem::SigType(_, decl, _) => {
                    out.extend(decl.type_params.iter().copied());
                    out.extend(decl.type_manifest);
                    match &decl.type_kind {
                        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
                        TypeKind::TypeRecord(labels, _) => {
                            out.extend(labels.iter().map(|label| label.ld_type));
                        }
                        TypeKind::TypeVariant(constructors, _) => {
                            for constructor in constructors.iter() {
                                arguments(&constructor.cd_args, out);
                                out.extend(constructor.cd_res);
                            }
                        }
                    }
                    for inlined in &decl.type_inlined_types {
                        match inlined {
                            TypeInlinedType::Record { labels, .. } => {
                                out.extend(labels.iter().map(|label| label.ld_type));
                            }
                        }
                    }
                }
                SignatureItem::SigTypext(_, ext, _) => {
                    out.extend(ext.ext_type_params.iter().copied());
                    arguments(&ext.ext_args, out);
                    out.extend(ext.ext_ret_type);
                }
                SignatureItem::SigModule(_, decl, _) => module_type(&decl.md_type, out),
                SignatureItem::SigModtype(_, decl) => {
                    if let Some(mty) = &decl.mtd_type {
                        module_type(mty, out);
                    }
                }
                SignatureItem::SigClass | SignatureItem::SigClassType => {}
            }
        }
    }

    /// The signature `sig` of `unit` is exported: count the distinct type
    /// nodes it reaches, those that are not ground (what the design's
    /// export copy would visit), and the ground types that contain
    /// themselves (which its ground tier would not intern).
    pub(crate) fn census_exported_signature(ctx: &TypeContext, unit: &str, sig: &[SignatureItem]) {
        let mut roots = Vec::new();
        signature_types(sig, &mut roots);
        let (graph, _) = Graph::of(ctx, roots);
        let nodes = graph.len() as u64;
        let nonground = graph
            .nonground
            .iter()
            .filter(|nonground| **nonground)
            .count() as u64;
        let recursive_ground = graph.recursive_ground() as u64;
        EXPORT_UNITS.fetch_add(1, Ordering::Relaxed);
        EXPORT_NODES.fetch_add(nodes, Ordering::Relaxed);
        EXPORT_NONGROUND_NODES.fetch_add(nonground, Ordering::Relaxed);
        EXPORT_MAX_NONGROUND_NODES.fetch_max(nonground, Ordering::Relaxed);
        EXPORT_RECURSIVE_GROUND.fetch_add(recursive_ground, Ordering::Relaxed);
        EXPORT_BY_UNIT
            .lock()
            .unwrap()
            .push((unit.to_string(), nonground, nodes));
    }

    /// The `limit` largest entries, ties broken by key so that the report
    /// does not depend on hash order.
    fn largest<K: Ord + Clone>(map: &Option<HashMap<K, u64>>, limit: usize) -> Vec<(K, u64)> {
        let mut entries: Vec<(K, u64)> = map
            .iter()
            .flatten()
            .map(|(key, count)| (key.clone(), *count))
            .collect();
        entries.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        entries.truncate(limit);
        entries
    }

    pub(super) fn print_report() {
        let local = LOCAL_NODES.load(Ordering::Relaxed);
        let store = STORE_BUILD_NODES.load(Ordering::Relaxed);
        let fresh = FRESH_VARS.load(Ordering::Relaxed);
        let copied: u64 = COPY_NODES
            .iter()
            .map(|nodes| nodes.load(Ordering::Relaxed))
            .sum();
        let total = local + store;
        eprintln!(
            "[compiler-counter] type_nodes total={total} local={local} store_builds={store} type_contexts={} store_build_count={}",
            TYPE_CONTEXTS.load(Ordering::Relaxed),
            STORE_BUILDS.load(Ordering::Relaxed),
        );
        for cause in CopyCause::ALL {
            let nodes = COPY_NODES[cause as usize].load(Ordering::Relaxed);
            eprintln!(
                "[compiler-counter] type_nodes_by_cause cause={} nodes={nodes} ({}) copies={}",
                cause.name(),
                percent(nodes, total),
                COPY_SESSIONS[cause as usize].load(Ordering::Relaxed),
            );
        }
        eprintln!(
            "[compiler-counter] type_nodes_by_cause cause=fresh_variable nodes={fresh} ({})",
            percent(fresh, total),
        );
        let direct = total.saturating_sub(copied + fresh);
        eprintln!(
            "[compiler-counter] type_nodes_by_cause cause=direct nodes={direct} ({})",
            percent(direct, total),
        );

        INSTANCE.print("instance", "copied_nodes");
        GENERALIZE.print("generalize", "visits");
        UPDATE_LEVEL.print("update_level", "visits");

        let unify_total: u64 = UNIFY
            .iter()
            .map(|count| count.load(Ordering::Relaxed))
            .sum();
        let mut line = format!("[compiler-counter] unify_top_level total={unify_total}");
        for (name, count) in UNIFY_SHAPE_NAMES.iter().zip(&UNIFY) {
            let count = count.load(Ordering::Relaxed);
            line.push_str(&format!(
                " {name}={count} ({})",
                percent(count, unify_total)
            ));
        }
        eprintln!("{line}");
        for ((left, right), count) in largest(&UNIFY_HEADS.lock().unwrap(), 20) {
            eprintln!(
                "[compiler-counter] unify_top_level_heads left={left} right={right} count={count} ({})",
                percent(count, unify_total),
            );
        }

        let expected = EXPECTED_VARS.lock().unwrap();
        let expected_total: u64 = expected.iter().flatten().map(|(_, count)| *count).sum();
        let mut by_case = [0u64; 6];
        for (var, count) in expected.iter().flatten() {
            by_case[usize::from(var.case).min(5)] += count;
        }
        eprintln!(
            "[compiler-counter] fresh_variables total={fresh} as_expected_type={expected_total} ({}) case1={} case2={} case3={} case4={} case5={}",
            percent(expected_total, fresh),
            by_case[1],
            by_case[2],
            by_case[3],
            by_case[4],
            by_case[5],
        );
        let mut constructs: Vec<(ExpectedVar, u64)> = expected
            .iter()
            .flatten()
            .map(|(var, count)| (*var, *count))
            .collect();
        constructs.sort_by(|a, b| {
            b.1.cmp(&a.1)
                .then_with(|| a.0.construct.cmp(b.0.construct))
                .then_with(|| a.0.case.cmp(&b.0.case))
        });
        for (var, count) in constructs {
            eprintln!(
                "[compiler-counter] fresh_variable_as_expected_type construct={} case={} count={count} ({})",
                var.construct,
                var.case,
                percent(count, fresh),
            );
        }
        drop(expected);
        for ((file, line), count) in largest(&FRESH_VAR_SITES.lock().unwrap(), 40) {
            // The path as the compiler was built with; print it from the
            // crate's directory.
            let file = file
                .rsplit_once("compiler-rust/")
                .map_or(file, |(_, file)| file);
            eprintln!(
                "[compiler-counter] fresh_variable_site file={file} line={line} count={count} ({})",
                percent(count, fresh),
            );
        }

        let export_nodes = EXPORT_NODES.load(Ordering::Relaxed);
        let export_nonground = EXPORT_NONGROUND_NODES.load(Ordering::Relaxed);
        eprintln!(
            "[compiler-counter] exported_signatures units={} nodes={export_nodes} nonground_nodes={export_nonground} ({}) max_nonground_nodes_per_unit={} recursive_ground_types={}",
            EXPORT_UNITS.load(Ordering::Relaxed),
            percent(export_nonground, export_nodes),
            EXPORT_MAX_NONGROUND_NODES.load(Ordering::Relaxed),
            EXPORT_RECURSIVE_GROUND.load(Ordering::Relaxed),
        );
        let mut units = EXPORT_BY_UNIT.lock().unwrap().clone();
        units.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        for (unit, nonground, nodes) in units.into_iter().take(10) {
            eprintln!(
                "[compiler-counter] exported_signature unit={unit} nonground_nodes={nonground} nodes={nodes}",
            );
        }
    }
}

#[cfg(test)]
mod checker_tests {
    use std::sync::Arc;

    use crate::context::IdGenerator;
    use crate::ident::Ident;
    use crate::types::context::TypeContext;
    use crate::types::path::Path;
    use crate::types::type_expr::{AbbrevMemoRef, TypeArg, TypeDesc, TypeExprRef};

    use super::checker::Graph;

    fn constr(ctx: &TypeContext, name: &str, args: &[TypeExprRef]) -> TypeExprRef {
        ctx.new_type(TypeDesc::Tconstr {
            path: Path::pident(Ident::create_persistent(name)),
            args: ctx.new_type_list(args),
            abbrev: AbbrevMemoRef::nil(),
        })
    }

    fn arrow(ctx: &TypeContext, arg: TypeExprRef, ret: TypeExprRef) -> TypeExprRef {
        ctx.new_type(TypeDesc::Tarrow {
            args: ctx.new_type_args(&[TypeArg::unlabeled(arg)]),
            ret,
        })
    }

    /// A type is ground when no variable is reachable from it, through
    /// links and through cycles.
    #[test]
    fn ground_is_no_reachable_variable() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let int = constr(&ctx, "int", &[]);
        let var = ctx.new_var(None);
        let linked = ctx.new_var(None);
        ctx.set_desc(linked, TypeDesc::Tlink(int));
        let ground = arrow(&ctx, int, constr(&ctx, "array", &[linked]));
        let open = arrow(&ctx, ground, constr(&ctx, "array", &[var]));

        let (graph, roots) = Graph::of(&ctx, [ground, open, var]);
        assert!(graph.is_ground(roots[0]));
        assert!(!graph.is_ground(roots[1]));
        assert!(!graph.is_ground(roots[2]));
        // `int`, the two arrays and the two arrows, and the variable; the
        // linked variable is `int`.
        assert_eq!(graph.len(), 6);
        assert_eq!(graph.recursive_ground(), 0);

        // The walk from `open` that does not enter `ground` visits the
        // arrow, the open array and the variable.
        let (visits, ground_visits) = graph.visit(&roots[1..2], |ty| ty != ground);
        assert_eq!((visits, ground_visits), (3, 0));
        let (visits, ground_visits) = graph.visit(&roots[1..2], |_| true);
        assert_eq!((visits, ground_visits), (6, 3));
    }

    /// A type that contains itself and no variable is ground, and is
    /// reported as recursive; with a variable in the cycle it is not ground.
    #[test]
    fn a_cycle_without_a_variable_is_ground_and_recursive() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let int = constr(&ctx, "int", &[]);
        let knot = ctx.new_var(None);
        let list = ctx.new_type(TypeDesc::Ttuple(ctx.new_type_list(&[int, knot])));
        ctx.set_desc(knot, TypeDesc::Tlink(list));
        let (graph, roots) = Graph::of(&ctx, [list]);
        assert!(graph.is_ground(roots[0]));
        assert_eq!(graph.recursive_ground(), 1);

        let var = ctx.new_var(None);
        let knot = ctx.new_var(None);
        let open = ctx.new_type(TypeDesc::Ttuple(ctx.new_type_list(&[var, knot])));
        ctx.set_desc(knot, TypeDesc::Tlink(open));
        let (graph, roots) = Graph::of(&ctx, [open]);
        assert!(!graph.is_ground(roots[0]));
        assert_eq!(graph.recursive_ground(), 0);
    }
}

#[cfg(all(test, debug_assertions))]
mod publication_guard_tests {
    use super::SignaturePublication;
    use crate::binser::Encoded;
    use crate::cmi::portable_types::{PortableRawSignature, PortableSignature, PortableTypeGraph};

    fn signature() -> PortableSignature {
        PortableSignature {
            ps_sig: vec![],
            cmi_longident_names: vec![],
            type_graph: PortableTypeGraph {
                entries: vec![],
                variant_layouts: vec![],
                mutabilities: vec![],
            },
            locations: Default::default(),
        }
    }

    #[test]
    #[should_panic(expected = "encoding or summary before signature release")]
    fn main_signature_encoding_is_guarded() {
        let _guard = SignaturePublication::begin();
        Encoded::encode(&signature());
    }

    #[test]
    #[should_panic(expected = "encoding or summary before signature release")]
    fn raw_signature_encoding_is_guarded() {
        let sig = signature();
        let raw = PortableRawSignature {
            raw_ps_sig: sig.ps_sig,
            cmi_longident_names: sig.cmi_longident_names,
            raw_type_graph: sig.type_graph,
            raw_locations: sig.locations,
        };
        let _guard = SignaturePublication::begin();
        Encoded::encode(&raw);
    }

    #[test]
    #[should_panic(expected = "encoding or summary before signature release")]
    fn summary_construction_is_guarded() {
        let _guard = SignaturePublication::begin();
        crate::cmi::item_deps::SignatureSummary::of("Guarded", &signature());
    }
}

/// Read existing process-global counters, without locks or mutation. O(1):
/// twenty-four atomic reads. Item deltas require a single compiler worker;
/// callers must not interpret concurrent process deltas as item attribution.
pub fn derived_snapshot() -> [u64; 4] {
    let [fresh, unify, copies] = checker::derived_snapshot();
    let lookups = [&VALUE_HITS, &VALUE_MISSES, &TYPE_HITS, &TYPE_MISSES,
        &MODULE_HITS, &MODULE_MISSES, &CONSTRUCTOR_HITS, &CONSTRUCTOR_MISSES,
        &LABEL_HITS, &LABEL_MISSES, &CHILD_COMPONENT_HITS, &CHILD_COMPONENT_MISSES,
        &QUALIFIED_COMPONENT_HITS, &QUALIFIED_COMPONENT_MISSES]
        .iter().map(|c| c.load(Ordering::Relaxed)).sum();
    [fresh, unify, copies, lookups]
}
