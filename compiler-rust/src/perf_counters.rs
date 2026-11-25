//! Optional compiler performance counters.
//!
//! Counters are disabled unless `RESCRIPT_COMPILER_COUNTERS` is set. The
//! report aggregates the behavior of all worker threads.
//!
//! A probe a type context reaches counts in that context's
//! `AttemptCounters`, with plain writes, and the context adds them to the
//! process totals once: a unit attempt when the driver retains it
//! (`TypeContext::keep_attempt_counters`), never when it discards it, and
//! any other context when it is flushed or dropped. Probes no compilation
//! owns (once-per-build world and importer work, the module registry,
//! attempt counts and explain reruns) stay process-global.

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
#[cfg(feature = "native")]
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
    if context_enabled()
        && !into_publication(|p| {
            *if pool_full {
                &mut p.pool_full
            } else {
                &mut p.nonshareable
            } += 1
        })
    {
        let counter = if pool_full { &SIGNATURE_POOL_FULL } else { &SIGNATURE_NONSHAREABLE };
        counter.fetch_add(1, Ordering::Relaxed);
    }
}

/// The signature probes of one unit's publication, counted while
/// [`attribute_publication`] runs: the publication runs before the driver
/// keeps or discards the unit's checking attempt, so its counts belong to
/// that attempt.
#[derive(Clone, Default)]
struct PublicationCounts {
    nonshareable: u64,
    pool_full: u64,
    nodes_frozen: u64,
    nodes_hashed: u64,
    hash_walks: u64,
    /// The `(generation, publication id)` of each signature published.
    published: Vec<(u64, usize)>,
}

impl PublicationCounts {
    fn merge(&mut self, other: PublicationCounts) {
        self.nonshareable += other.nonshareable;
        self.pool_full += other.pool_full;
        self.nodes_frozen += other.nodes_frozen;
        self.nodes_hashed += other.nodes_hashed;
        self.hash_walks += other.hash_walks;
        self.published.extend(other.published);
    }
}

thread_local! {
    /// The publication [`attribute_publication`] is running on this thread.
    static PUBLICATION: RefCell<Option<PublicationCounts>> = const { RefCell::new(None) };
}

/// Count a signature probe in the publication running on this thread, if
/// any; `false` when none runs. One TLS access per probe call (per graph,
/// walk or fallback), not per node, and only with the counters enabled.
fn into_publication(record: impl FnOnce(&mut PublicationCounts)) -> bool {
    PUBLICATION.with(|current| match current.borrow_mut().as_mut() {
        Some(counts) => {
            record(counts);
            true
        }
        None => false,
    })
}

/// Run `publish`, a publication of the unit `ctx` checks, counting its
/// signature probes (fallbacks, frozen and hashed nodes, the published
/// signature) in `ctx`: a discarded attempt's publication publishes none of
/// them. Probes outside any publication, such as an importer's promotion,
/// stay process-global. With the counters off, one flag test.
pub(crate) fn attribute_publication<R>(
    ctx: &crate::types::TypeContext,
    publish: impl FnOnce() -> R,
) -> R {
    if !ctx.compiler_counters_enabled() {
        return publish();
    }
    struct Scope<'a> {
        ctx: &'a crate::types::TypeContext,
        previous: Option<PublicationCounts>,
    }
    impl Drop for Scope<'_> {
        fn drop(&mut self) {
            let counts = PUBLICATION.with(|current| current.replace(self.previous.take()));
            if let Some(counts) = counts {
                self.ctx
                    .record_attempt_counter(|c| c.publication.merge(counts));
            }
        }
    }
    let previous = PUBLICATION.with(|current| current.replace(Some(Default::default())));
    let _scope = Scope { ctx, previous };
    publish()
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
    if context_enabled() && (imported || !into_publication(|p| p.published.push((generation, id))))
    {
        let mut counts = SIGNATURE_COUNTS.get_or_init(Default::default).lock().unwrap();
        counts.record((generation, id), imported);
    }
}

pub(crate) fn record_signature_nodes_frozen(nodes: usize) {
    if context_enabled() && !into_publication(|p| p.nodes_frozen += nodes as u64) {
        SIGNATURE_NODES_FROZEN.fetch_add(nodes as u64, Ordering::Relaxed);
    }
}

pub(crate) fn record_signature_nodes_hashed(nodes: u64) {
    if context_enabled()
        && !into_publication(|p| {
            p.hash_walks += 1;
            p.nodes_hashed += nodes;
        })
    {
        SIGNATURE_HASH_WALKS.fetch_add(1, Ordering::Relaxed);
        SIGNATURE_NODES_HASHED.fetch_add(nodes, Ordering::Relaxed);
    }
}

/// Translated modules and their declarations, of one annotation class.
#[derive(Clone, Copy, Default)]
struct GentypeCounts {
    modules: u64,
    declarations: u64,
}

impl GentypeCounts {
    fn record(&mut self, declarations: usize) {
        self.modules += 1;
        self.declarations += declarations as u64;
    }

    fn merge(&mut self, other: GentypeCounts) {
        self.modules += other.modules;
        self.declarations += other.declarations;
    }

    fn snapshot(&self) -> (u64, u64) {
        (self.modules, self.declarations)
    }
}

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
/// It runs before the driver keeps the unit's checking attempt, so it counts
/// in the unit's context `ctx`.
pub(crate) fn record_gentype_translation(
    ctx: &crate::types::TypeContext,
    annotated: bool,
    declarations: usize,
) {
    #[cfg(test)]
    GENTYPE_TEST_COUNTS.with(|counts| {
        let mut values = counts.get();
        let offset = usize::from(annotated) * 2;
        values[offset] += 1;
        values[offset + 1] += declarations as u64;
        counts.set(values);
    });
    ctx.record_attempt_counter(|c| c.gentype[usize::from(annotated)].record(declarations));
}

#[cfg(test)]
#[test]
fn gentype_counts_include_empty_translations_and_separate_annotation_classes() {
    let mut counts = [GentypeCounts::default(); 2];
    assert_eq!(counts[0].snapshot(), (0, 0));
    counts[0].record(0);
    counts[0].record(3);
    counts[1].record(5);
    assert_eq!(counts[0].snapshot(), (2, 3));
    assert_eq!(counts[1].snapshot(), (1, 5));
}

/// A per-attempt fallback decode, as opposed to the world's once-per-build import.
pub(crate) fn record_attempt_signature_decode(ctx: &crate::types::TypeContext) {
    ctx.record_attempt_counter(|counts| counts.signature_decodes += 1);
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

#[derive(Clone, Copy)]
pub(crate) enum TypeMutationKind {
    Desc,
    Level,
    Row,
    State,
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

impl LazyLookupKind {
    const ALL: [LazyLookupKind; 6] = [
        LazyLookupKind::Value,
        LazyLookupKind::Type,
        LazyLookupKind::Module,
        LazyLookupKind::Constructor,
        LazyLookupKind::Label,
        LazyLookupKind::ChildComponent,
    ];

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
}

/// One lazy lookup kind: hits, misses, scans, scanned items, result items.
#[derive(Clone, Copy, Default)]
struct LazyCounts {
    hits: u64,
    misses: u64,
    scans: u64,
    scanned_items: u64,
    results: u64,
}

/// Qualified and stored component views.
#[derive(Clone, Copy, Default)]
struct ComponentCounts {
    qualified_hits: u64,
    qualified_misses: u64,
    qualified_registered: u64,
    stored_cached: u64,
    stored_build_find_module: u64,
}

/// Type-item signature scans.
#[derive(Clone, Copy, Default)]
struct TypeItemResolveCounts {
    scans: u64,
    scanned_items: u64,
    type_items: u64,
    found: u64,
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

    fn merge(&mut self, other: SignatureCopySite) {
        self.calls += other.calls;
        self.items += other.items;
        self.max_items = self.max_items.max(other.max_items);
    }
}

fn merge_sites<K: Eq + std::hash::Hash>(
    into: &mut HashMap<K, SignatureCopySite>,
    from: HashMap<K, SignatureCopySite>,
) {
    for (key, site) in from {
        into.entry(key).or_default().merge(site);
    }
}

/// The counts of every probe a [`crate::types::TypeContext`] reaches: plain
/// fields and dense arrays indexed by kind, with maps only for the source
/// sites, kinds and names no index exists for. No atomic or TLS operation
/// is made per probe.
///
/// A context allocates one on its first probe with the counters enabled,
/// and adds it to the process totals at most once per publication: a unit
/// attempt when it is retained, any other context when it is flushed or
/// dropped. A discarded attempt publishes nothing.
#[derive(Default)]
pub(crate) struct AttemptCounters {
    mutations: [u64; 4],
    snapshots: u64,
    backtracks: u64,
    restores: u64,
    peak_depth: u64,
    lazy: [LazyCounts; 6],
    components: ComponentCounts,
    type_item_resolve: TypeItemResolveCounts,
    signature_copies: SignatureCopySite,
    signature_copy_sites: HashMap<(&'static str, u32), SignatureCopySite>,
    qualification_kinds: HashMap<&'static str, SignatureCopySite>,
    qualification_names: HashMap<String, SignatureCopySite>,
    freshen_kinds: HashMap<&'static str, SignatureCopySite>,
    freshen_names: HashMap<String, SignatureCopySite>,
    module_copies: HashMap<String, SignatureCopySite>,
    module_freshens: HashMap<String, SignatureCopySite>,
    frozen: [u64; frozen::KINDS],
    views_adopted: u64,
    papply_views: u64,
    store_views: store_views::Counts,
    checker: checker::Counts,
    publication: PublicationCounts,
    gentype: [GentypeCounts; 2],
    signature_decodes: u64,
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

    /// Add `other` to these counts: sums, and maxima for the `max` fields.
    /// O(size of `other`'s maps).
    fn merge(&mut self, other: AttemptCounters) {
        for (total, count) in self.mutations.iter_mut().zip(other.mutations) {
            *total += count;
        }
        self.signature_decodes += other.signature_decodes;
        self.snapshots += other.snapshots;
        self.backtracks += other.backtracks;
        self.restores += other.restores;
        self.peak_depth = self.peak_depth.max(other.peak_depth);
        for (total, count) in self.lazy.iter_mut().zip(other.lazy) {
            total.hits += count.hits;
            total.misses += count.misses;
            total.scans += count.scans;
            total.scanned_items += count.scanned_items;
            total.results += count.results;
        }
        let (c, o) = (&mut self.components, other.components);
        c.qualified_hits += o.qualified_hits;
        c.qualified_misses += o.qualified_misses;
        c.qualified_registered += o.qualified_registered;
        c.stored_cached += o.stored_cached;
        c.stored_build_find_module += o.stored_build_find_module;
        let (t, o) = (&mut self.type_item_resolve, other.type_item_resolve);
        t.scans += o.scans;
        t.scanned_items += o.scanned_items;
        t.type_items += o.type_items;
        t.found += o.found;
        self.signature_copies.merge(other.signature_copies);
        merge_sites(&mut self.signature_copy_sites, other.signature_copy_sites);
        merge_sites(&mut self.qualification_kinds, other.qualification_kinds);
        merge_sites(&mut self.qualification_names, other.qualification_names);
        merge_sites(&mut self.freshen_kinds, other.freshen_kinds);
        merge_sites(&mut self.freshen_names, other.freshen_names);
        merge_sites(&mut self.module_copies, other.module_copies);
        merge_sites(&mut self.module_freshens, other.module_freshens);
        for (total, count) in self.frozen.iter_mut().zip(other.frozen) {
            *total += count;
        }
        self.views_adopted += other.views_adopted;
        self.papply_views += other.papply_views;
        self.store_views.merge(other.store_views);
        self.checker.merge(other.checker);
        self.publication.merge(other.publication);
        for (total, count) in self.gentype.iter_mut().zip(other.gentype) {
            total.merge(count);
        }
    }

    /// The four totals the derived census charges to items: fresh
    /// variables, top-level unifications, nodes copied by instantiation,
    /// and lazy and qualified-component lookups (hits plus misses).
    fn derived(&self) -> [u64; 4] {
        let [fresh, unify, copies] = self.checker.derived();
        let lookups = self
            .lazy
            .iter()
            .map(|kind| kind.hits + kind.misses)
            .sum::<u64>()
            + self.components.qualified_hits
            + self.components.qualified_misses;
        [fresh, unify, copies, lookups]
    }

    /// Add these counts to the process totals. O(size of the maps), one
    /// lock acquisition; called once per publication, never per probe.
    pub(crate) fn publish(mut self) {
        // Published keys join the process-wide set, which importers' later
        // acquisitions are matched against.
        if !self.publication.published.is_empty() {
            let mut counts = SIGNATURE_COUNTS
                .get_or_init(Default::default)
                .lock()
                .unwrap();
            for key in self.publication.published.drain(..) {
                counts.record(key, false);
            }
        }
        with_totals_mut(|totals| {
            totals.publications += 1;
            totals.counts.get_or_insert_with(Default::default).merge(self);
        });
    }
}

/// The process totals of the context-owned counts, and how many
/// publications made them.
#[derive(Default)]
struct Totals {
    publications: u64,
    counts: Option<Box<AttemptCounters>>,
}

#[cfg(not(test))]
static TOTALS: Mutex<Totals> = Mutex::new(Totals {
    publications: 0,
    counts: None,
});

// Unit tests run on parallel threads: each test thread publishes to totals
// of its own, so a test sees exactly the publications it made.
#[cfg(test)]
thread_local! {
    static TOTALS: RefCell<Totals> = RefCell::default();
}

fn with_totals_mut<R>(update: impl FnOnce(&mut Totals) -> R) -> R {
    #[cfg(not(test))]
    {
        update(&mut TOTALS.lock().unwrap_or_else(|e| e.into_inner()))
    }
    #[cfg(test)]
    {
        TOTALS.with(|totals| update(&mut totals.borrow_mut()))
    }
}

/// Read the process totals of the context-owned counts.
fn with_totals<R>(read: impl FnOnce(&AttemptCounters) -> R) -> R {
    with_totals_mut(|totals| match totals.counts.as_deref() {
        Some(counts) => read(counts),
        None => read(&AttemptCounters::default()),
    })
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

/// Print the 20 entries of `map` with the most items (then calls).
fn print_top_signature_sites<K: Clone>(
    map: &HashMap<K, SignatureCopySite>,
    mut print: impl FnMut(&K, &SignatureCopySite),
) {
    let mut entries = map
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

/// Counters of shared store data (stage P4 of `docs/CHECKER_REDESIGN.md`):
/// how often persistent-rooted component views are built against how many
/// distinct views exist, and what replaying their pieces costs.
pub(crate) mod store_views {
    use crate::types::TypeContext;

    /// Store builds with effects or guards, with none, and poisoned;
    /// binders created inside them; first replays of a piece; replayed
    /// effects (unit preparations).
    #[derive(Clone, Copy, Default)]
    pub(crate) struct Counts {
        pub(super) pieces_built: u64,
        pub(super) pieces_empty: u64,
        pub(super) pieces_poisoned: u64,
        pub(super) binders: u64,
        pub(super) pieces_replayed: u64,
        pub(super) effects_replayed: [u64; 1],
    }

    impl Counts {
        pub(super) fn merge(&mut self, other: Counts) {
            self.pieces_built += other.pieces_built;
            self.pieces_empty += other.pieces_empty;
            self.pieces_poisoned += other.pieces_poisoned;
            self.binders += other.binders;
            self.pieces_replayed += other.pieces_replayed;
            for (total, count) in self.effects_replayed.iter_mut().zip(other.effects_replayed) {
                *total += count;
            }
        }
    }

    /// A store build ended: with effects or guards, with none, or poisoned.
    pub(crate) fn record_piece(ctx: &TypeContext, poisoned: bool, empty: bool) {
        ctx.record_attempt_counter(|c| {
            let counts = &mut c.store_views;
            *if poisoned {
                &mut counts.pieces_poisoned
            } else if empty {
                &mut counts.pieces_empty
            } else {
                &mut counts.pieces_built
            } += 1;
        });
    }

    /// A binder was created inside a store build.
    pub(crate) fn record_binder(ctx: &TypeContext) {
        ctx.record_attempt_counter(|c| c.store_views.binders += 1);
    }

    /// A compilation replayed a piece for the first time.
    pub(crate) fn record_piece_replay(ctx: &TypeContext) {
        ctx.record_attempt_counter(|c| c.store_views.pieces_replayed += 1);
    }

    /// A replayed effect (index as in `Counts::effects_replayed`).
    pub(crate) fn record_effect_replayed(ctx: &TypeContext, kind: usize) {
        ctx.record_attempt_counter(|c| c.store_views.effects_replayed[kind] += 1);
    }

    pub(super) fn print_report(counts: &Counts) {
        // Printed only when a store build ran or a piece was replayed:
        // neither happens once every persistent-rooted path is a world
        // view.
        let pieces = counts.pieces_built + counts.pieces_empty + counts.pieces_poisoned;
        if pieces == 0 && counts.pieces_replayed == 0 {
            return;
        }
        eprintln!(
            "[compiler-counter] store_pieces with_effects={} empty={} poisoned={} binders={}",
            counts.pieces_built, counts.pieces_empty, counts.pieces_poisoned, counts.binders,
        );
        eprintln!(
            "[compiler-counter] store_replay pieces={} prepare_pers={}",
            counts.pieces_replayed, counts.effects_replayed[0],
        );
    }
}

/// Reads and overlay writes of published type data. Callers gate these on
/// the context's cached counters flag and exclude nodes still being built.
pub(crate) mod frozen {
    use crate::types::TypeContext;

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

    pub(super) const KINDS: usize = 12;
    const NAMES: [&str; KINDS] = [
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

    /// O(1): one plain increment in the context's counts.
    pub(crate) fn record(ctx: &TypeContext, kind: Kind) {
        ctx.record_attempt_counter(|c| c.frozen[kind as usize] += 1);
    }

    /// The count of `kind` the context holds and has not published.
    #[cfg(test)]
    pub(crate) fn count(ctx: &TypeContext, kind: Kind) -> u64 {
        ctx.attempt_counter(|c| c.frozen[kind as usize])
    }

    pub(super) fn print_report(counts: &[u64; KINDS]) {
        let fields: Vec<_> = NAMES
            .iter()
            .zip(counts)
            .map(|(name, count)| format!("{name}={count}"))
            .collect();
        eprintln!("[compiler-counter] frozen {}", fields.join(" "));
    }
}

/// What a build's world holds besides its units.
///
/// The view builds, failures and forced children are once-per-build work
/// of the shared world, made on scratch contexts no compilation owns, so
/// they stay process-global. The adoptions and functor-application tables
/// are per compilation and count in its context.
pub(crate) mod world {
    use std::sync::atomic::{AtomicU64, Ordering};

    use crate::types::TypeContext;

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
    pub(crate) fn record_view_adoption(ctx: &TypeContext) {
        ctx.record_attempt_counter(|c| c.views_adopted += 1);
    }

    /// A compilation built the component tables of a path with a functor
    /// application on it (`F(X).t`): such a path has no world view, so each
    /// compilation that uses it builds them. The caller tests the flag.
    pub(crate) fn record_papply_view_build(ctx: &TypeContext) {
        ctx.record_attempt_counter(|c| c.papply_views += 1);
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
        VIEWS_FAILED.store(0, Ordering::Relaxed);
        for total in &VIEW_ITEMS {
            total.store(0, Ordering::Relaxed);
        }
        VIEW_NODES_COPIED.store(0, Ordering::Relaxed);
        CHILDREN_FORCED.store(0, Ordering::Relaxed);
        CHILD_NODES.store(0, Ordering::Relaxed);
    }

    pub(super) fn print_report(views_adopted: u64, papply_views: u64) {
        eprintln!(
            "[compiler-counter] world predef_builds={} predef_nodes={}",
            PREDEF_BUILDS.load(Ordering::Relaxed),
            PREDEF_NODES.load(Ordering::Relaxed),
        );
        eprintln!(
            "[compiler-counter] world_views built={} adopted={} failed={} children_forced={}",
            VIEWS_BUILT.load(Ordering::Relaxed),
            views_adopted,
            VIEWS_FAILED.load(Ordering::Relaxed),
            CHILDREN_FORCED.load(Ordering::Relaxed),
        );
        eprintln!("[compiler-counter] papply_views built={papply_views}");
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

/// Whether a new type context counts its probes: [`enabled`], or in unit
/// tests, a thread that asked for it with [`force_context_counters_for_test`].
#[inline]
pub(crate) fn context_enabled() -> bool {
    #[cfg(test)]
    if FORCE_CONTEXT_COUNTERS.with(std::cell::Cell::get) {
        return true;
    }
    enabled()
}

#[cfg(test)]
thread_local! {
    static FORCE_CONTEXT_COUNTERS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Make the type contexts this thread creates from now on count probes.
#[cfg(test)]
pub(crate) fn force_context_counters_for_test() {
    FORCE_CONTEXT_COUNTERS.with(|force| force.set(true));
}

/// Forget this test thread's published totals.
#[cfg(test)]
fn reset_for_test() {
    with_totals_mut(|totals| *totals = Totals::default());
}

/// Reset all compiler performance counters. Counts a live context holds
/// and has not published yet are not reset.
pub fn reset() {
    EXPLAIN_RERUNS.store(0, Ordering::Relaxed);
    SNAPSHOT_MODULE_DECODES.store(0, Ordering::Relaxed);
    if !enabled() {
        return;
    }

    world::reset();
    for counter in [
        &SIGNATURE_NONSHAREABLE,
        &SIGNATURE_POOL_FULL,
        &SIGNATURE_NODES_FROZEN,
        &SIGNATURE_NODES_HASHED,
        &SIGNATURE_HASH_WALKS,
    ] {
        counter.store(0, Ordering::Relaxed);
    }

    for counter in [
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

    with_totals_mut(|totals| *totals = Totals::default());
    checker::reset();
}

/// Record a cached lazy-signature lookup.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_lazy_hit(ctx: &crate::types::TypeContext, kind: LazyLookupKind) {
    ctx.record_attempt_counter(|c| c.lazy[kind as usize].hits += 1);
}

/// Record a lazy-signature scan after a cache miss.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_lazy_scan(
    ctx: &crate::types::TypeContext,
    kind: LazyLookupKind,
    scanned_items: usize,
    result_items: usize,
) {
    ctx.record_attempt_counter(|c| {
        let counts = &mut c.lazy[kind as usize];
        counts.misses += 1;
        counts.scans += 1;
        counts.scanned_items += scanned_items as u64;
        counts.results += result_items as u64;
    });
}

/// Record a qualified component-view cache hit.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_component_hit(ctx: &crate::types::TypeContext) {
    ctx.record_attempt_counter(|c| c.components.qualified_hits += 1);
}

/// Record a qualified component-view cache miss.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_component_miss(ctx: &crate::types::TypeContext) {
    ctx.record_attempt_counter(|c| c.components.qualified_misses += 1);
}

/// Record a newly cached qualified component view.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_qualified_component_registered(ctx: &crate::types::TypeContext) {
    ctx.record_attempt_counter(|c| c.components.qualified_registered += 1);
}

/// Record use of an already-built stored component view.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_stored_component_cached(ctx: &crate::types::TypeContext) {
    ctx.record_attempt_counter(|c| c.components.stored_cached += 1);
}

/// Record a stored component view built for a specific lookup mode.
///
/// Caller must check [`enabled`] before calling this hot-path helper.
#[inline]
pub(crate) fn record_stored_component_build(
    ctx: &crate::types::TypeContext,
    mode: ComponentLookupApi,
) {
    match mode {
        ComponentLookupApi::FindModule => {
            ctx.record_attempt_counter(|c| c.components.stored_build_find_module += 1);
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
pub(crate) fn record_type_item_resolve_scan(
    ctx: &crate::types::TypeContext,
    scanned_items: usize,
    type_items: usize,
    found: bool,
) {
    ctx.record_attempt_counter(|c| {
        let counts = &mut c.type_item_resolve;
        counts.scans += 1;
        counts.scanned_items += scanned_items as u64;
        counts.type_items += type_items as u64;
        counts.found += u64::from(found);
    });
}

/// The module the current worker thread attributes counters to. One TLS
/// read per signature copy or freshening, not per node.
fn current_module() -> Option<String> {
    CURRENT_MODULE.with(|current| current.borrow().clone())
}

/// Record a full signature copy, grouped by call site.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_copy(
    ctx: &crate::types::TypeContext,
    location: &'static std::panic::Location<'static>,
    item_count: usize,
) {
    let module = current_module();
    ctx.record_attempt_counter(|c| {
        c.signature_copies.record(item_count);
        c.signature_copy_sites
            .entry((location.file(), location.line()))
            .or_default()
            .record(item_count);
        if let Some(module) = module {
            c.module_copies
                .entry(module)
                .or_default()
                .record(item_count);
        }
    });
}

/// Record a signature qualification before the current full-copy path.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_qualification(
    ctx: &crate::types::TypeContext,
    kind: &'static str,
    item_count: usize,
) {
    ctx.record_attempt_counter(|c| {
        c.qualification_kinds
            .entry(kind)
            .or_default()
            .record(item_count);
    });
}

/// Record a named signature qualification entry.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_qualification_name(
    ctx: &crate::types::TypeContext,
    kind: &'static str,
    name: &str,
    item_count: usize,
) {
    ctx.record_attempt_counter(|c| {
        c.qualification_names
            .entry(format!("{kind}:{name}"))
            .or_default()
            .record(item_count);
    });
}

/// Record a signature freshening entry point before it performs full-copy work.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_freshen(
    ctx: &crate::types::TypeContext,
    kind: &'static str,
    item_count: usize,
) {
    let module = current_module();
    ctx.record_attempt_counter(|c| {
        c.freshen_kinds.entry(kind).or_default().record(item_count);
        if let Some(module) = module {
            c.module_freshens
                .entry(module)
                .or_default()
                .record(item_count);
        }
    });
}

/// Record a named signature freshening entry.
///
/// Caller must check [`enabled`] before calling this helper.
pub(crate) fn record_signature_freshen_name(
    ctx: &crate::types::TypeContext,
    kind: &'static str,
    name: &str,
    item_count: usize,
) {
    ctx.record_attempt_counter(|c| {
        c.freshen_names
            .entry(format!("{kind}:{name}"))
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
            + with_totals(|counts| counts.signature_decodes)
    );
    let (publication, gentype) = with_totals(|totals| (totals.publication.clone(), totals.gentype));
    let load = |counter: &AtomicU64| counter.load(Ordering::Relaxed);
    eprintln!(
        "signature_nonshareable={} signature_pool_full={}",
        load(&SIGNATURE_NONSHAREABLE) + publication.nonshareable,
        load(&SIGNATURE_POOL_FULL) + publication.pool_full,
    );

    if let Some(counts) = SIGNATURE_COUNTS.get() {
        let counts = counts.lock().unwrap();
        eprintln!(
            "[compiler-counter] signature_units_published={} signature_units_imported={} signature_nodes_frozen={} signature_nodes_hashed={} signature_hash_walks={}",
            counts.published.len(), counts.imported.len(),
            load(&SIGNATURE_NODES_FROZEN) + publication.nodes_frozen,
            load(&SIGNATURE_NODES_HASHED) + publication.nodes_hashed,
            load(&SIGNATURE_HASH_WALKS) + publication.hash_walks,
        );
    }

    for (index, annotated) in [false, true].into_iter().enumerate() {
        let (modules, declarations) = gentype[index].snapshot();
        eprintln!(
            "[compiler-counter] gentype annotated={annotated} modules={modules} declarations={declarations}",
        );
    }
    with_totals(|totals| {
        for kind in LazyLookupKind::ALL {
            print_lazy(kind, &totals.lazy[kind as usize]);
        }
        let components = &totals.components;
        eprintln!(
            "[compiler-counter] qualified_components hits={} misses={} registered={}",
            components.qualified_hits, components.qualified_misses, components.qualified_registered,
        );
        store_views::print_report(&totals.store_views);
        frozen::print_report(&totals.frozen);
        world::print_report(totals.views_adopted, totals.papply_views);
        eprintln!(
            "[compiler-counter] stored_components cached={} build_find_module={}",
            components.stored_cached, components.stored_build_find_module,
        );
        let resolve = &totals.type_item_resolve;
        eprintln!(
            "[compiler-counter] type_item_resolve scans={} scanned_items={} type_items={} found={}",
            resolve.scans, resolve.scanned_items, resolve.type_items, resolve.found,
        );
        let copies = &totals.signature_copies;
        eprintln!(
            "[compiler-counter] signature_copies calls={} items={} max_items={}",
            copies.calls, copies.items, copies.max_items,
        );
        print_signature_sites(totals);
        eprintln!(
            "[compiler-counter] type_mutations desc={} level={} row={} abbrev={} state={} snapshots={} backtracks={} restores={} peak_depth={}",
            totals.mutations[TypeMutationKind::Desc as usize],
            totals.mutations[TypeMutationKind::Level as usize],
            totals.mutations[TypeMutationKind::Row as usize],
            // No probe records abbreviation writes; the field stays for
            // the report's shape.
            0,
            totals.mutations[TypeMutationKind::State as usize],
            totals.snapshots,
            totals.backtracks,
            totals.restores,
            totals.peak_depth,
        );
    });
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
    with_totals(|totals| checker::print_report(&totals.checker));
}

/// The signature copy and freshening sites, kinds, names and modules, in
/// the report's order.
fn print_signature_sites(totals: &AttemptCounters) {
    print_top_signature_sites(&totals.signature_copy_sites, |(file, line), counters| {
        eprintln!(
            "[compiler-counter] signature_copy_site file={} line={} calls={} items={} max_items={}",
            file, line, counters.calls, counters.items, counters.max_items,
        );
    });
    print_top_signature_sites(&totals.qualification_kinds, |kind, counters| {
        eprintln!(
            "[compiler-counter] signature_qualification kind={} calls={} items={} max_items={}",
            kind, counters.calls, counters.items, counters.max_items,
        );
    });
    print_top_signature_sites(&totals.qualification_names, |name, counters| {
        eprintln!(
            "[compiler-counter] signature_qualification_name name={} calls={} items={} max_items={}",
            name, counters.calls, counters.items, counters.max_items,
        );
    });
    print_top_signature_sites(&totals.freshen_kinds, |kind, counters| {
        eprintln!(
            "[compiler-counter] signature_freshen kind={} calls={} items={} max_items={}",
            kind, counters.calls, counters.items, counters.max_items,
        );
    });
    print_top_signature_sites(&totals.freshen_names, |name, counters| {
        eprintln!(
            "[compiler-counter] signature_freshen_name name={} calls={} items={} max_items={}",
            name, counters.calls, counters.items, counters.max_items,
        );
    });
    print_top_signature_sites(&totals.module_copies, |module, site| {
        eprintln!(
            "[compiler-counter] module_signature_copies module={} calls={} items={} max_items={}",
            module, site.calls, site.items, site.max_items
        );
    });
    print_top_signature_sites(&totals.module_freshens, |module, site| {
        eprintln!(
            "[compiler-counter] module_signature_freshens module={} calls={} items={} max_items={}",
            module, site.calls, site.items, site.max_items
        );
    });
}

fn print_lazy(kind: LazyLookupKind, counts: &LazyCounts) {
    eprintln!(
        "[compiler-counter] lazy_lookup kind={} hits={} misses={} scans={} scanned_items={} result_items={}",
        kind.name(),
        counts.hits,
        counts.misses,
        counts.scans,
        counts.scanned_items,
        counts.results,
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

    /// The type contexts dropped and the nodes their own pools held:
    /// once per context, from its drop, so process-global (a discarded
    /// attempt's pool is not counted, see `TypeContext::defer_attempt_counters`).
    static TYPE_CONTEXTS: AtomicU64 = AtomicU64::new(0);
    static LOCAL_NODES: AtomicU64 = AtomicU64::new(0);

    /// Calls, calls whose every root is ground, visited nodes, ground
    /// visited nodes.
    #[derive(Clone, Copy, Default)]
    pub(super) struct WalkCounts {
        calls: u64,
        ground_calls: u64,
        visits: u64,
        ground_visits: u64,
    }

    impl WalkCounts {
        fn merge(&mut self, other: WalkCounts) {
            self.calls += other.calls;
            self.ground_calls += other.ground_calls;
            self.visits += other.visits;
            self.ground_visits += other.ground_visits;
        }

        fn print(&self, name: &str, visit: &str) {
            let WalkCounts {
                calls,
                ground_calls,
                visits,
                ground_visits,
            } = *self;
            eprintln!(
                "[compiler-counter] {name} calls={calls} ground_calls={ground_calls} ({}) {visit}={visits} ground_{visit}={ground_visits} ({})",
                percent(ground_calls, calls),
                percent(ground_visits, visits),
            );
        }
    }

    /// The census walks, indexed by `Walk`.
    #[derive(Clone, Copy)]
    enum Walk {
        Instance,
        Generalize,
        UpdateLevel,
    }

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

    /// The head constructor names a top-level unification is counted by,
    /// indexed by [`head_index`].
    const HEADS: usize = 12;
    const HEAD_NAMES: [&str; HEADS] = [
        "var", "arrow", "tuple", "constr", "object", "field", "nil", "link", "variant", "univar",
        "poly", "package",
    ];

    /// The checker's counts in one context; see [`super::AttemptCounters`].
    #[derive(Default)]
    pub(super) struct Counts {
        copy_sessions: [u64; 4],
        copy_nodes: [u64; 4],
        store_builds: u64,
        store_build_nodes: u64,
        fresh_vars: u64,
        fresh_var_sites: HashMap<(&'static str, u32), u64>,
        expected_vars: HashMap<ExpectedVar, u64>,
        walks: [WalkCounts; 3],
        unify: [u64; UNIFY_SHAPES],
        /// Top-level unifications by the two head constructors, dense:
        /// `unify_heads[left * HEADS + right]`.
        unify_heads: Vec<u64>,
        export_units: u64,
        export_nodes: u64,
        export_nonground_nodes: u64,
        export_max_nonground_nodes: u64,
        export_recursive_ground: u64,
        /// Non-ground and all exported nodes per unit.
        export_by_unit: Vec<(String, u64, u64)>,
    }

    impl Counts {
        pub(super) fn merge(&mut self, other: Counts) {
            for (total, count) in self.copy_sessions.iter_mut().zip(other.copy_sessions) {
                *total += count;
            }
            for (total, count) in self.copy_nodes.iter_mut().zip(other.copy_nodes) {
                *total += count;
            }
            self.store_builds += other.store_builds;
            self.store_build_nodes += other.store_build_nodes;
            self.fresh_vars += other.fresh_vars;
            for (site, count) in other.fresh_var_sites {
                *self.fresh_var_sites.entry(site).or_default() += count;
            }
            for (var, count) in other.expected_vars {
                *self.expected_vars.entry(var).or_default() += count;
            }
            for (total, count) in self.walks.iter_mut().zip(other.walks) {
                total.merge(count);
            }
            for (total, count) in self.unify.iter_mut().zip(other.unify) {
                *total += count;
            }
            if !other.unify_heads.is_empty() {
                self.unify_heads.resize(HEADS * HEADS, 0);
                for (total, count) in self.unify_heads.iter_mut().zip(other.unify_heads) {
                    *total += count;
                }
            }
            self.export_units += other.export_units;
            self.export_nodes += other.export_nodes;
            self.export_nonground_nodes += other.export_nonground_nodes;
            self.export_max_nonground_nodes = self
                .export_max_nonground_nodes
                .max(other.export_max_nonground_nodes);
            self.export_recursive_ground += other.export_recursive_ground;
            self.export_by_unit.extend(other.export_by_unit);
        }

        pub(super) fn derived(&self) -> [u64; 3] {
            [
                self.fresh_vars,
                self.unify.iter().sum(),
                self.copy_nodes[CopyCause::Instance as usize],
            ]
        }

        /// The counts `attempt_tests::probe_every_family` makes `n` times
        /// with two distinct `int` nodes at level 0.
        #[cfg(test)]
        pub(super) fn assert_counts(&self, n: u64) {
            let instance = CopyCause::Instance as usize;
            assert_eq!((self.copy_sessions[instance], self.copy_nodes[instance]), (n, 3 * n));
            assert_eq!(self.copy_sessions.iter().sum::<u64>(), n);
            assert_eq!((self.store_builds, self.store_build_nodes), (n, 2 * n));
            assert_eq!(self.fresh_vars, n);
            assert_eq!(self.fresh_var_sites.values().sum::<u64>(), n);
            let expected = ExpectedVar {
                construct: "test",
                case: 2,
            };
            assert_eq!(self.expected_vars.get(&expected).copied(), Some(n));
            // Ground roots below every walk's level: no node is entered.
            for walk in self.walks {
                let WalkCounts {
                    calls,
                    ground_calls,
                    visits,
                    ground_visits,
                } = walk;
                assert_eq!([calls, ground_calls, visits, ground_visits], [n, n, 0, 0]);
            }
            // Two identical ground constructors, both headed `constr`.
            assert_eq!(self.unify, [0, n, 0, 0, 0, 0, 0, 0]);
            let constr = 3;
            assert_eq!(HEAD_NAMES[constr], "constr");
            assert_eq!(self.unify_heads.len(), HEADS * HEADS);
            assert_eq!(self.unify_heads[constr * HEADS + constr], n);
            assert_eq!(self.unify_heads.iter().sum::<u64>(), n);
            assert_eq!(
                (self.export_units, self.export_nodes, self.export_by_unit.len() as u64),
                (n, 0, n)
            );
        }
    }

    fn percent(part: u64, whole: u64) -> String {
        if whole == 0 {
            "-".to_string()
        } else {
            format!("{:.1}%", 100.0 * part as f64 / whole as f64)
        }
    }

    pub(super) fn reset() {
        TYPE_CONTEXTS.store(0, Ordering::Relaxed);
        LOCAL_NODES.store(0, Ordering::Relaxed);
    }

    /// A copy for `cause` allocated `nodes` type nodes, not counting the
    /// copies nested in it.
    pub(crate) fn record_copy(ctx: &TypeContext, cause: CopyCause, nodes: usize) {
        let index = cause as usize;
        ctx.record_attempt_counter(|c| {
            c.checker.copy_sessions[index] += 1;
            c.checker.copy_nodes[index] += nodes as u64;
        });
    }

    /// A compilation's own node pool is dropped holding `nodes` nodes.
    pub(crate) fn record_local_type_nodes(nodes: usize) {
        TYPE_CONTEXTS.fetch_add(1, Ordering::Relaxed);
        LOCAL_NODES.fetch_add(nodes as u64, Ordering::Relaxed);
    }

    /// An outermost store build allocated `nodes` nodes in the worker store.
    pub(crate) fn record_store_build_nodes(ctx: &TypeContext, nodes: usize) {
        ctx.record_attempt_counter(|c| {
            c.checker.store_builds += 1;
            c.checker.store_build_nodes += nodes as u64;
        });
    }

    /// `new_var` and its variants, called from `location` outside a copy
    /// session.
    pub(crate) fn record_fresh_var(
        ctx: &TypeContext,
        location: &'static std::panic::Location<'static>,
    ) {
        ctx.record_attempt_counter(|c| {
            c.checker.fresh_vars += 1;
            *c.checker
                .fresh_var_sites
                .entry((location.file(), location.line()))
                .or_default() += 1;
        });
    }

    /// A fresh variable was made only to be the expected type of an
    /// expression.
    pub(crate) fn record_expected_var(ctx: &TypeContext, var: ExpectedVar) {
        ctx.record_attempt_counter(|c| *c.checker.expected_vars.entry(var).or_default() += 1);
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

    /// The index in [`HEAD_NAMES`] of the head constructor of `desc`.
    fn head_index(desc: &TypeDesc) -> usize {
        match desc {
            TypeDesc::Tvar(_) => 0,
            TypeDesc::Tarrow { .. } => 1,
            TypeDesc::Ttuple(_) => 2,
            TypeDesc::Tconstr { .. } => 3,
            TypeDesc::Tobject { .. } => 4,
            TypeDesc::Tfield { .. } => 5,
            TypeDesc::Tnil => 6,
            TypeDesc::Tlink(_) | TypeDesc::Tsubst(_) => 7,
            TypeDesc::Tvariant(_) => 8,
            TypeDesc::Tunivar(_) => 9,
            TypeDesc::Tpoly { .. } => 10,
            TypeDesc::Tpackage { .. } => 11,
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
        walk: Walk,
        roots: impl IntoIterator<Item = TypeExprRef>,
        enters: impl FnMut(TypeExprRef) -> bool,
    ) {
        let (graph, roots) = Graph::of(ctx, roots);
        let (visits, ground_visits) = graph.visit(&roots, enters);
        let ground = roots.iter().all(|root| graph.is_ground(*root));
        ctx.record_attempt_counter(|c| {
            let counts = &mut c.checker.walks[walk as usize];
            counts.calls += 1;
            counts.ground_calls += u64::from(ground);
            counts.visits += visits;
            counts.ground_visits += ground_visits;
        });
    }

    /// An instantiation of `roots` in one copy session is about to run: it
    /// copies the nodes at the generic level it reaches through such nodes.
    pub(crate) fn census_instance(ctx: &TypeContext, roots: impl IntoIterator<Item = TypeExprRef>) {
        census_walk(ctx, Walk::Instance, roots, |ty| {
            ctx.get_level(ty) == GENERIC_LEVEL
        });
    }

    /// A generalisation of `ty` is about to run: it visits the nodes above
    /// `level` that are not generic yet.
    pub(crate) fn census_generalize(ctx: &TypeContext, level: i32, ty: TypeExprRef) {
        census_walk(ctx, Walk::Generalize, [ty], |ty| {
            let node_level = ctx.get_level(ty);
            node_level > level && node_level != GENERIC_LEVEL
        });
    }

    /// `ty` is about to be lowered to `level`: the walk visits the nodes
    /// above it.
    pub(crate) fn census_update_level(ctx: &TypeContext, level: i32, ty: TypeExprRef) {
        census_walk(ctx, Walk::UpdateLevel, [ty], |ty| ctx.get_level(ty) > level);
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
        let head = head_index(&d1) * HEADS + head_index(&d2);
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
        ctx.record_attempt_counter(|c| {
            let counts = &mut c.checker;
            counts.unify[shape] += 1;
            if counts.unify_heads.is_empty() {
                counts.unify_heads.resize(HEADS * HEADS, 0);
            }
            counts.unify_heads[head] += 1;
        });
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
        ctx.record_attempt_counter(|c| {
            let counts = &mut c.checker;
            counts.export_units += 1;
            counts.export_nodes += nodes;
            counts.export_nonground_nodes += nonground;
            counts.export_max_nonground_nodes = counts.export_max_nonground_nodes.max(nonground);
            counts.export_recursive_ground += recursive_ground;
            counts
                .export_by_unit
                .push((unit.to_string(), nonground, nodes));
        });
    }

    /// The `limit` largest entries, ties broken by key so that the report
    /// does not depend on hash order.
    fn largest<K: Ord + Clone>(
        entries: impl IntoIterator<Item = (K, u64)>,
        limit: usize,
    ) -> Vec<(K, u64)> {
        let mut entries: Vec<(K, u64)> = entries.into_iter().collect();
        entries.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        entries.truncate(limit);
        entries
    }

    pub(super) fn print_report(counts: &Counts) {
        let local = LOCAL_NODES.load(Ordering::Relaxed);
        let store = counts.store_build_nodes;
        let fresh = counts.fresh_vars;
        let copied: u64 = counts.copy_nodes.iter().sum();
        let total = local + store;
        eprintln!(
            "[compiler-counter] type_nodes total={total} local={local} store_builds={store} type_contexts={} store_build_count={}",
            TYPE_CONTEXTS.load(Ordering::Relaxed),
            counts.store_builds,
        );
        for cause in CopyCause::ALL {
            let nodes = counts.copy_nodes[cause as usize];
            eprintln!(
                "[compiler-counter] type_nodes_by_cause cause={} nodes={nodes} ({}) copies={}",
                cause.name(),
                percent(nodes, total),
                counts.copy_sessions[cause as usize],
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

        counts.walks[Walk::Instance as usize].print("instance", "copied_nodes");
        counts.walks[Walk::Generalize as usize].print("generalize", "visits");
        counts.walks[Walk::UpdateLevel as usize].print("update_level", "visits");

        let unify_total: u64 = counts.unify.iter().sum();
        let mut line = format!("[compiler-counter] unify_top_level total={unify_total}");
        for (name, count) in UNIFY_SHAPE_NAMES.iter().zip(counts.unify) {
            line.push_str(&format!(
                " {name}={count} ({})",
                percent(count, unify_total)
            ));
        }
        eprintln!("{line}");
        let heads = counts
            .unify_heads
            .iter()
            .enumerate()
            .filter(|(_, count)| **count != 0)
            .map(|(index, count)| {
                (
                    (HEAD_NAMES[index / HEADS], HEAD_NAMES[index % HEADS]),
                    *count,
                )
            });
        for ((left, right), count) in largest(heads, 20) {
            eprintln!(
                "[compiler-counter] unify_top_level_heads left={left} right={right} count={count} ({})",
                percent(count, unify_total),
            );
        }

        let expected = &counts.expected_vars;
        let expected_total: u64 = expected.values().sum();
        let mut by_case = [0u64; 6];
        for (var, count) in expected {
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
        let mut constructs: Vec<(ExpectedVar, u64)> =
            expected.iter().map(|(var, count)| (*var, *count)).collect();
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
        let sites = counts
            .fresh_var_sites
            .iter()
            .map(|(site, count)| (*site, *count));
        for ((file, line), count) in largest(sites, 40) {
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

        let export_nodes = counts.export_nodes;
        let export_nonground = counts.export_nonground_nodes;
        eprintln!(
            "[compiler-counter] exported_signatures units={} nodes={export_nodes} nonground_nodes={export_nonground} ({}) max_nonground_nodes_per_unit={} recursive_ground_types={}",
            counts.export_units,
            percent(export_nonground, export_nodes),
            counts.export_max_nonground_nodes,
            counts.export_recursive_ground,
        );
        let mut units = counts.export_by_unit.clone();
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

/// The current attempt's four census counts. O(1), without a global lock.
/// Item attribution happens before retention, so another unit's publication
/// (including one on the same thread) must not contribute to these deltas.
pub fn derived_snapshot(ctx: &crate::types::TypeContext) -> [u64; 4] {
    ctx.attempt_counter(AttemptCounters::derived)
}

#[cfg(test)]
mod attempt_tests {
    use std::sync::Arc;

    use super::{AttemptCounters, ExpectedVar, LazyLookupKind, TypeMutationKind, frozen};
    use crate::context::IdGenerator;
    use crate::ident::Ident;
    use crate::types::context::TypeContext;
    use crate::types::path::Path;
    use crate::types::type_expr::{AbbrevMemoRef, TypeDesc, TypeExprRef};
    use crate::types::typecore::ComponentLookupApi;

    const OPERATIONS: u64 = 10_000;

    fn context() -> TypeContext {
        let mut ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        ctx.enable_compiler_counters_for_test();
        ctx
    }

    fn int(ctx: &TypeContext) -> TypeExprRef {
        ctx.new_type(TypeDesc::Tconstr {
            path: Path::pident(Ident::create_persistent("int")),
            args: ctx.new_type_list(&[]),
            abbrev: AbbrevMemoRef::nil(),
        })
    }

    /// This thread's publications so far, and the totals they made.
    fn published<R>(read: impl FnOnce(&AttemptCounters) -> R) -> (u64, R) {
        (
            super::with_totals_mut(|totals| totals.publications),
            super::with_totals(read),
        )
    }

    /// One counted operation of every probe family a context reaches.
    fn probe_every_family(ctx: &TypeContext, left: TypeExprRef, right: TypeExprRef) {
        super::record_type_mutation(ctx, TypeMutationKind::Desc);
        super::record_type_mutation_snapshot(ctx, 3);
        super::record_type_mutation_backtrack(ctx, 2);
        frozen::record(ctx, frozen::Kind::DescReadShared);
        super::record_lazy_hit(ctx, LazyLookupKind::Label);
        super::record_lazy_scan(ctx, LazyLookupKind::Value, 4, 1);
        super::record_qualified_component_hit(ctx);
        super::record_qualified_component_miss(ctx);
        super::record_qualified_component_registered(ctx);
        super::record_stored_component_cached(ctx);
        super::record_stored_component_build(ctx, ComponentLookupApi::FindModule);
        super::record_type_item_resolve_scan(ctx, 5, 2, true);
        super::record_signature_copy(ctx, std::panic::Location::caller(), 7);
        super::record_signature_qualification(ctx, "alias", 7);
        super::record_signature_qualification_name(ctx, "alias", "M", 7);
        super::record_signature_freshen(ctx, "include", 6);
        super::record_signature_freshen_name(ctx, "include", "M", 6);
        super::world::record_view_adoption(ctx);
        super::world::record_papply_view_build(ctx);
        super::store_views::record_piece(ctx, false, true);
        super::store_views::record_binder(ctx);
        super::store_views::record_piece_replay(ctx);
        super::store_views::record_effect_replayed(ctx, 0);
        super::record_copy(ctx, super::CopyCause::Instance, 3);
        super::record_store_build_nodes(ctx, 2);
        super::record_fresh_var(ctx, std::panic::Location::caller());
        super::record_expected_var(
            ctx,
            ExpectedVar {
                construct: "test",
                case: 2,
            },
        );
        super::census_unify(ctx, left, right);
        super::census_instance(ctx, [left]);
        super::census_generalize(ctx, 0, left);
        super::census_update_level(ctx, 0, left);
        super::census_exported_signature(ctx, "Unit", &[]);
    }

    /// The counts `probe_every_family` makes `n` times, as exact values.
    fn assert_counts(c: &AttemptCounters, n: u64) {
        assert_eq!(c.mutations, [n, 0, 0, 0]);
        assert_eq!((c.snapshots, c.backtracks, c.restores, c.peak_depth), (n, n, 2 * n, 3));
        assert_eq!(c.frozen[frozen::Kind::DescReadShared as usize], n);
        assert_eq!(c.frozen.iter().sum::<u64>(), n);
        let label = c.lazy[LazyLookupKind::Label as usize];
        let value = c.lazy[LazyLookupKind::Value as usize];
        assert_eq!((label.hits, label.misses), (n, 0));
        assert_eq!(
            (value.hits, value.misses, value.scans, value.scanned_items, value.results),
            (0, n, n, 4 * n, n)
        );
        let components = c.components;
        assert_eq!(
            [
                components.qualified_hits,
                components.qualified_misses,
                components.qualified_registered,
                components.stored_cached,
                components.stored_build_find_module,
            ],
            [n; 5]
        );
        let resolve = c.type_item_resolve;
        assert_eq!(
            [resolve.scans, resolve.scanned_items, resolve.type_items, resolve.found],
            [n, 5 * n, 2 * n, n]
        );
        assert_eq!(
            (c.signature_copies.calls, c.signature_copies.items, c.signature_copies.max_items),
            (n, 7 * n, 7)
        );
        assert_eq!(c.signature_copy_sites.values().map(|s| s.calls).sum::<u64>(), n);
        assert_eq!(c.qualification_kinds["alias"].calls, n);
        assert_eq!(c.qualification_names["alias:M"].items, 7 * n);
        assert_eq!(c.freshen_kinds["include"].calls, n);
        assert_eq!(c.freshen_names["include:M"].items, 6 * n);
        // No `ModuleCounterGuard` is active on a test thread.
        assert!(c.module_copies.is_empty() && c.module_freshens.is_empty());
        assert_eq!((c.views_adopted, c.papply_views), (n, n));
        let store = c.store_views;
        assert_eq!(
            [
                store.pieces_built,
                store.pieces_empty,
                store.pieces_poisoned,
                store.binders,
                store.pieces_replayed,
                store.effects_replayed[0],
            ],
            [0, n, 0, n, n, n]
        );
        c.checker.assert_counts(n);
        // Fresh variables, unifications, instance copies, lookups.
        assert_eq!(c.derived(), [n, n, 3 * n, 4 * n]);
    }

    /// The per-context counts are plain fields allocated on first probe.
    #[test]
    fn context_counters_sizes_are_pinned() {
        assert_eq!(
            std::mem::size_of::<Option<Box<AttemptCounters>>>(),
            std::mem::size_of::<usize>()
        );
        // One heap block per counting context, never per probe or node.
        assert_eq!(std::mem::size_of::<AttemptCounters>(), 1432);
    }

    #[test]
    fn a_disabled_context_counts_nothing() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let (left, right) = (int(&ctx), int(&ctx));
        let (before, _) = published(|_| ());
        for _ in 0..OPERATIONS {
            ctx.record_attempt_counter(|c| c.views_adopted += 1);
            super::census_unify(&ctx, left, right);
        }
        assert_eq!(ctx.attempt_counter(|c| c.views_adopted), 0);
        drop(ctx);
        assert_eq!(published(|_| ()).0, before);
    }

    #[test]
    fn a_discarded_attempt_publishes_nothing() {
        let (before, totals_before) = published(AttemptCounters::derived);
        let ctx = context();
        ctx.defer_attempt_counters();
        let (left, right) = (int(&ctx), int(&ctx));
        for _ in 0..OPERATIONS {
            probe_every_family(&ctx, left, right);
        }
        ctx.attempt_counter(|c| assert_counts(c, OPERATIONS));
        // The census reader sees the attempt's unpublished counts.
        let snapshot = super::derived_snapshot(&ctx);
        let expected = [OPERATIONS, OPERATIONS, 3 * OPERATIONS, 4 * OPERATIONS];
        assert_eq!(snapshot, expected);
        drop(ctx);
        let (after, totals_after) = published(AttemptCounters::derived);
        assert_eq!(after, before);
        assert_eq!(totals_after, totals_before);
    }

    #[test]
    fn census_reads_ignore_other_retained_attempts() {
        let current = context();
        current.defer_attempt_counters();
        let sibling = context();
        sibling.defer_attempt_counters();
        let (left, right) = (int(&sibling), int(&sibling));
        let before = super::derived_snapshot(&current);
        for _ in 0..OPERATIONS {
            probe_every_family(&sibling, left, right);
        }
        sibling.keep_attempt_counters();
        assert_eq!(super::derived_snapshot(&current), before);
    }

    #[test]
    fn fallback_signature_decodes_follow_the_attempt() {
        super::reset_for_test();
        for retained in [false, true] {
            let ctx = context();
            ctx.defer_attempt_counters();
            for _ in 0..OPERATIONS {
                super::record_attempt_signature_decode(&ctx);
            }
            assert_eq!(ctx.attempt_counter(|c| c.signature_decodes), OPERATIONS);
            if retained { ctx.keep_attempt_counters(); }
            drop(ctx);
            assert_eq!(super::with_totals(|c| c.signature_decodes),
                if retained { OPERATIONS } else { 0 });
        }
    }

    #[test]
    fn a_kept_attempt_publishes_once_and_post_keep_probes_once_more() {
        super::reset_for_test();
        let ctx = context();
        ctx.defer_attempt_counters();
        let (left, right) = (int(&ctx), int(&ctx));
        // A discarded sibling attempt on the same thread contributes nothing.
        let discarded = context();
        discarded.defer_attempt_counters();
        for _ in 0..OPERATIONS {
            probe_every_family(&ctx, left, right);
            probe_every_family(&discarded, int(&discarded), int(&discarded));
        }
        drop(discarded);
        assert_eq!(published(|_| ()).0, 0);
        ctx.keep_attempt_counters();
        let (publications, ()) = published(|c| assert_counts(c, OPERATIONS));
        assert_eq!(publications, 1);
        assert_eq!(ctx.attempt_counter(AttemptCounters::derived), [0; 4]);
        // Keeping again publishes nothing more.
        ctx.keep_attempt_counters();
        assert_eq!(published(|_| ()).0, 1);
        for _ in 0..OPERATIONS {
            probe_every_family(&ctx, left, right);
        }
        assert_eq!(published(|_| ()).0, 1);
        drop(ctx);
        let (publications, ()) = published(|c| assert_counts(c, 2 * OPERATIONS));
        assert_eq!(publications, 2);
    }

    #[test]
    fn a_flushed_context_publishes_each_count_once() {
        super::reset_for_test();
        let ctx = context();
        let (left, right) = (int(&ctx), int(&ctx));
        for _ in 0..OPERATIONS {
            probe_every_family(&ctx, left, right);
        }
        assert_eq!(published(|_| ()).0, 0);
        ctx.flush_counters();
        let (publications, ()) = published(|c| assert_counts(c, OPERATIONS));
        assert_eq!(publications, 1);
        // Nothing new: neither a second flush nor the drop publishes.
        ctx.flush_counters();
        drop(ctx);
        let (publications, ()) = published(|c| assert_counts(c, OPERATIONS));
        assert_eq!(publications, 1);
    }

    /// Counts made before an attempt is deferred are not the attempt's: they
    /// are published by `defer_attempt_counters` and survive a discard.
    #[test]
    fn counts_before_deferral_survive_a_discard() {
        super::reset_for_test();
        let ctx = context();
        for _ in 0..OPERATIONS {
            super::world::record_view_adoption(&ctx);
        }
        ctx.defer_attempt_counters();
        for _ in 0..OPERATIONS {
            super::world::record_view_adoption(&ctx);
        }
        drop(ctx);
        assert_eq!(published(|c| c.views_adopted), (1, OPERATIONS));
    }

    /// The signature probes of a publication, `n` times each, as the unit
    /// `ctx` checks publishes with generation `generation`.
    fn publish_n(ctx: &TypeContext, generation: u64, n: u64) {
        super::attribute_publication(ctx, || {
            for id in 0..n as usize {
                super::record_signature_fallback(id % 2 == 0);
                super::record_signature_nodes_frozen(3);
                super::record_signature_nodes_hashed(5);
                super::record_signature_access(id, generation, false);
            }
            // A nested publication counts in the same attempt.
            super::attribute_publication(ctx, || super::record_signature_nodes_frozen(1));
        });
    }

    fn global_signature_counts(generation: u64) -> ([u64; 5], usize, usize) {
        let load = |c: &super::AtomicU64| c.load(super::Ordering::Relaxed);
        let (published, imported) = super::SIGNATURE_COUNTS
            .get()
            .map(|counts| {
                let counts = counts.lock().unwrap();
                let mine = |set: &std::collections::HashSet<(u64, usize)>| {
                    set.iter().filter(|(g, _)| *g == generation).count()
                };
                (mine(&counts.published), mine(&counts.imported))
            })
            .unwrap_or_default();
        (
            [
                load(&super::SIGNATURE_NONSHAREABLE),
                load(&super::SIGNATURE_POOL_FULL),
                load(&super::SIGNATURE_NODES_FROZEN),
                load(&super::SIGNATURE_NODES_HASHED),
                load(&super::SIGNATURE_HASH_WALKS),
            ],
            published,
            imported,
        )
    }

    /// A publication made before the attempt is kept or discarded counts in
    /// the attempt: a discarded one adds no published unit, frozen or hashed
    /// node; a kept one adds each exactly once. Probes outside a
    /// publication stay process-global.
    #[test]
    fn signature_publication_counts_follow_the_attempt() {
        super::reset_for_test();
        super::force_context_counters_for_test();
        // Generations no build uses, so other tests' keys never match.
        let (discarded_generation, kept_generation) = (u64::MAX - 1, u64::MAX - 2);
        let (globals_before, _, _) = global_signature_counts(discarded_generation);

        let discarded = context();
        discarded.defer_attempt_counters();
        publish_n(&discarded, discarded_generation, OPERATIONS);
        discarded.attempt_counter(|c| {
            let p = &c.publication;
            assert_eq!(
                [
                    p.nonshareable,
                    p.pool_full,
                    p.nodes_frozen,
                    p.nodes_hashed,
                    p.hash_walks
                ],
                [
                    OPERATIONS / 2,
                    OPERATIONS / 2,
                    3 * OPERATIONS + 1,
                    5 * OPERATIONS,
                    OPERATIONS
                ]
            );
            assert_eq!(p.published.len() as u64, OPERATIONS);
        });
        drop(discarded);
        assert_eq!(
            global_signature_counts(discarded_generation),
            (globals_before, 0, 0)
        );
        assert_eq!(published(|_| ()).0, 0);

        let kept = context();
        kept.defer_attempt_counters();
        publish_n(&kept, kept_generation, OPERATIONS);
        assert_eq!(
            global_signature_counts(kept_generation),
            (globals_before, 0, 0)
        );
        kept.keep_attempt_counters();
        let (publications, totals) = published(|c| {
            let p = &c.publication;
            [
                p.nonshareable,
                p.pool_full,
                p.nodes_frozen,
                p.nodes_hashed,
                p.hash_walks,
            ]
        });
        assert_eq!(publications, 1);
        assert_eq!(
            totals,
            [
                OPERATIONS / 2,
                OPERATIONS / 2,
                3 * OPERATIONS + 1,
                5 * OPERATIONS,
                OPERATIONS
            ]
        );
        assert_eq!(published(|c| c.publication.published.len()).1, 0);
        assert_eq!(
            global_signature_counts(kept_generation),
            (globals_before, OPERATIONS as usize, 0)
        );
        // An importer's acquisition, outside any publication, is global.
        super::record_signature_access(0, kept_generation, true);
        assert_eq!(
            global_signature_counts(kept_generation),
            (globals_before, OPERATIONS as usize, 1)
        );
        super::record_signature_nodes_frozen(7);
        let (globals_after, _, _) = global_signature_counts(kept_generation);
        assert_eq!(globals_after[2], globals_before[2] + 7);
    }

    /// GenType translations run before the attempt is kept: a discarded
    /// attempt's translations are not counted.
    #[test]
    fn gentype_translations_follow_the_attempt() {
        super::reset_for_test();
        for keep in [false, true] {
            let ctx = context();
            ctx.defer_attempt_counters();
            for i in 0..OPERATIONS {
                super::record_gentype_translation(&ctx, i % 4 == 0, 2);
            }
            if keep {
                ctx.keep_attempt_counters();
            }
        }
        let (publications, counts) = published(|c| c.gentype.map(|g| g.snapshot()));
        assert_eq!(publications, 1);
        assert_eq!(
            counts,
            [
                (OPERATIONS * 3 / 4, OPERATIONS * 3 / 2),
                (OPERATIONS / 4, OPERATIONS / 2)
            ]
        );
    }

    /// The world's scratch outlives its builds: each build's counts are
    /// published when the build ends.
    #[test]
    fn view_scratch_builds_publish_their_counts() {
        super::reset_for_test();
        super::force_context_counters_for_test();
        for round in 1..=3u64 {
            crate::types::world::ViewScratch::with(|scratch| {
                for _ in 0..OPERATIONS {
                    super::world::record_view_adoption(scratch.ctx());
                }
            });
            assert_eq!(
                published(|c| c.views_adopted),
                (round, round * OPERATIONS),
                "round {round}"
            );
        }
    }
}
