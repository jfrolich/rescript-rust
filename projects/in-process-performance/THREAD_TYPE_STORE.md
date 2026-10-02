# Per-thread persistent type store

Implementation design for proposal A of
[ARCHITECTURE_INVESTIGATION.md](ARCHITECTURE_INVESTIGATION.md), re-scoped
so it does not depend on proposal B. Clean-build target only: nothing is
persisted between builds; the store lives for the lifetime of one worker
thread inside one `rescript build` process.

## Why this first

A 12 s `sample` window of the single-worker Tella clean build on this head
(`/tmp/perf-sample-w1.txt`, worker thread, 7.2 K samples), restricted to the
call-graph section and counting each family at its outermost frame:

| family | share | what it is |
|---|---|---|
| `drop_in_place` | 23.3 % | 477 samples at the end of `compile_preprocessed_structure_in_process_until_js`; `Env` 182; `RefCell<Vec<Arc<Env>>>` 142; HAMT entries 87; `QualifiedModuleComponents` 51; component/decl `AHashMap`s 84; `TypeContext` 34; `PersistentEnv` 30 |
| `Arc` refcount traffic | 12.7 % | mostly inside those drops (`Env` 310, `TypeContext` 213) |
| `find_pers_struct` | 8.4 % | `internalize_signature` 4.0, `register_sig_types_*` 2.8, freshen/subst 1.3 |
| `open_module` (prelude) | 6.3 % | overlaps the row above for `Pervasives`/`Stdlib` |
| `hashbrown` | 8.1 % | `insert_module_stamp_subst` 64, component construction 41, subst maps 30, … |
| `TypeDesc` clone + drop | ~3 % | the class proposal B removes |

Per-module import and teardown of *dependency* state is the largest
addressable block (roughly a third of the window; `env_setup` 1.19 s +
residual 2.47 s of the 19.8 s serial build sit outside typecheck, and the
`Env`/component drops inside typecheck add to that). Type-node
representation is a distant second. A per-thread store removes the import
and the teardown for every dependency module after the first module on a
thread that needs it, without requiring `Sync` type nodes.

The earlier worker-local `TypeContext` reuse experiment
(`projects/shared-interfaces/PROGRESS.md`) is *not* what this is: that
reused the whole mutable context, including stamp-keyed declaration
registries whose keys collide when stamps reset per unit. Here only
immutable, generic-level dependency storage is shared; every mutable per-unit
table and forced substitution view stays per module.

## OCaml reference semantics

- `compiler/ml/env.ml:669-678`: `read_pers_struct` builds `ps_comps` once,
  from `Env.empty` and `Subst.identity`, and stores it in the process-wide
  `persistent_structures` table. Every unit compiled by that process shares
  those nodes and that component table.
- `compiler/ml/env.ml:1874-1877`: `open_signature` adds opened components
  from that shared table; it does not copy the signature.
- `compiler/ml/subst.ml:358-364` (`Subst.signature`) and
  `compiler/ml/env.ml:1516-1585` (`components_of_module_maker`): the
  consumer-visible substituted copies are made when a component table is
  forced. They are per `(path, mty, sub)`, not per unit.
- `compiler/ml/ctype.ml:725-765` (`copy`/`instance`) copies generic schemes
  at ordinary use sites, but this does **not** make every dependency node
  immutable during typing. Nullary constructor unification
  (`compiler/ml/ctype.ml:2118-2127`) and declaration coercion can still
  reach `Btype.link_type` (`compiler/ml/btype.ml:633-651`). Those writes
  must remain observable within the compilation; Rust isolates them in
  descriptor/level overlays rather than suppressing them. `Tsubst`
  traversal markers are already represented separately in `CopyCache`.
- `compiler/ml/subst.ml:173-177`: abbreviation memos are reset to `Mnil` when
  a signature is saved, so a fresh process starts with empty memos. Memo
  state must therefore stay per module for one-process-per-file parity.

Today's per-module internalization corresponds to one `bsc` process per
file. The **raw, unforced** dependency graph can use shared immutable storage
with compilation-local writes. This does not authorize sharing forced
components unchanged between units: `compiler/core/res_compmisc.ml:35`
resets Env caches, and `initial_env` at line 49 calls `Ident.reinit`.
Per-unit substitution identity and force effects must still match that
reference lifecycle.

## Ownership model

```
worker thread
└── ThreadTypeStore (thread_local, lives for the thread)
    ├── types:       TypeArena           append-only, generic-level nodes only
    ├── abbrevs:     Vec<AbbrevMemo>     initial (Mnil) values only
    ├── row_fields / field_kinds / variant_layouts   initial values only
    ├── id_gen:      per-thread node ids, disjoint from module-local ids
    ├── stamps:      no retained per-unit binder allocation stream
    ├── pers:        portable-struct identity -> Arc<PersStruct> (store refs)
    └── future:      context-independent component/prelude templates (not enabled)
module compile (TypeContext, dropped at the pre-JS boundary)
    ├── types:       TypeArena           local nodes, as today
    ├── store:       StoreLease (exclusive Box, returned to worker slot on drop)
    ├── overlays:    store descriptor / level / abbrev / row-field writes
    │                made by this module, indexed by store node/cell index
    └── every existing per-unit table, unchanged
```

`TypeExprRef`, `AbbrevMemoRef`, `RowFieldRef`, `FieldKindRef` and
`LayoutRef` reserve their top bit as the store tag. Accessors on
`TypeContext` branch on the tag; index arithmetic (`index()`,
`from_usize`) stays local-only and asserts the tag is clear.

Nothing in `InProcessPreJsCompileResult` references type nodes, so the
lease never crosses threads; the store is `!Send` by construction.

The worker slot transfers exclusive ownership into each `TypeContext`, not
an `Rc`/`Arc`. Overlapping contexts get independent stores; the outer context
returns its store when it finishes. A panicking compilation defensively
discards its store. Descriptor, level, row, and abbreviation writes are
compilation-local, so even a normal diagnostic return cannot leak mutations.
The lease also avoids node reference counting.

## Invariants

1. Backing store nodes remain unchanged. `set_desc`/`link_type` on a stored
   handle update this compilation's descriptor overlay while preserving the
   handle's physical identity. `repr` and `instance` see those writes.
2. `set_level` on a stored handle writes its level overlay, including both
   traversal marks and normal level lowering. An interrupted traversal cannot
   leave the next compilation with a marked dependency graph.
3. Abbrev memos and row-field cells of store nodes are read through the
   module overlay: unset means the store's initial value.
   Writes go to the overlay only. `clear_abbrev_memos`/snapshot-backtrack
   operate on the overlay plus local cells.
4. `TypeExprRefMap` selects sparse storage for mixed store/local key spans
   beyond its inline capacity. `TypeExprRefSet` keeps separate dense spans
   so the store tag cannot trigger a multi-gigabyte allocation. `snapshot_type_state` covers
   local nodes and overlays only, including descriptor writes made before
   and after the snapshot.
5. In-process unit identifier counters restart as in OCaml's
   `Res_compmisc.initial_env` / `Ident.reinit`. Forced component binders must
   not be retained as if they belonged to a later unit. Stamp-keyed per-unit
   registries (`type_decl_by_stamp` and friends) are not yet shared.
6. Store entries are keyed by portable-struct identity (`Arc::as_ptr`),
   so a module republished in watch mode never aliases a stale graph.
7. Component tables currently stay per module. Future shared templates must
   not read a unit's `Env` or retain its forced substitution results; an
   `Env.empty` construction root alone does not prove binder independence.

## Stages

Each stage lands only with `./scripts/test_js_output_parity.sh --release`
610/610 and `./scripts/test_error_output_parity.sh --release` 1431/1431,
plus the debug `./scripts/test_typedtree_parity.sh --quick` and
`./scripts/test_lambda_parity.sh --quick` so the invariant assertions run.

1. **Tagged references and store skeleton, no behaviour change.** Top-bit
   tags on the five reference types; `ThreadTypeStore` with an empty arena;
   `TypeContext` accessors branch on the tag; overlays and assertions in
   place. Paired hyperfine must show no regression from the extra branch.
2. **Store-backed `find_pers_struct`.** Portable persistent structs are
   internalized once per thread into the store; the module's
   `PersistentEnv` cache maps names to the shared `Arc<PersStruct>`.
   `register_sig_types_*` and alias-rewrite collection still run per module
   on the shared signature (they fill per-unit tables). Measure: expect
   `internalize` and the `TypeContext` node drops to fall out of the
   serial profile.
3. **Shared component templates and the prelude (design correction needed).**
   Factor context-independent tables from per-unit forced substitution views
   in `QualifiedModuleComponents`. Reuse immutable lookup/prelude layers only
   where their handles and binders are independent of the unit. Preserve
   unit-local thunk identity, force order, and stamp allocation; see the
   corrected stamp policy below. Measure `open_module`, `freshen`,
   `insert_module_stamp_subst`, and the `Env`/component drops.
4. **Per-unit registries** (`type_decl_store`, `type_decl_by_stamp`,
   `type_decl_by_path`, …) are the remaining per-module walk over shared
   signatures. Route consumers through `Env`/component lookup
   (proposal C.2) or make the registration incremental per store entry.

Proposal B (POD nodes) remains the follow-up for the remaining clone and
memmove share; with the store in place its `Sync` requirement disappears.

## Stage 1 implementation status

Tagged handles, an exclusively leased worker-store skeleton, local memo/row
write overlays, snapshot/backtrack support, and mixed-identity map/set tests
are implemented. Production imports still allocate **only local nodes**;
there is no dependency reuse or claimed speedup yet. The stored-node paths
are exercised directly by unit tests, not by the ordinary parity corpus.

Before enabling stage 2, audit every direct handle index use (including
serializer identity tables), identifier freshness, graph closure (no local
references in a retained graph), level-mark restoration on error, and build
scope/invalidation on worker pools reused by watch mode. Passing stage-1
parity does not establish these invariants for real imported signatures.
Store entries keyed by pointer identity must retain the corresponding owner;
a naked address is not a lifetime-safe cache key.

### Validation

- Release compiler and rewatch builds: pass.
- Direct unit tests (`cargo test --manifest-path compiler-rust/Cargo.toml
  --lib store`): 17/17, including 9 new store/tag/overlay tests.
- Release JS parity: 344/344 focused fixtures and 610/610 corpus files.
- Release diagnostic parity: 1431/1431.
- Debug typedtree and optimized-lambda parity: 610/610 each. Typedtree
  caches were cleared before the authoritative run.
- Formatting of touched Rust modules and `git diff --check`: pass.
- **External OCaml/Rust JS parity remains blocked**, not passed:
  `test_js_output_parity.sh --release --with-external` exits 2 during the
  OCaml reference build because `bs-css/src/Css_AtomicTypes.res` cannot
  resolve `Belt`. This also occurred before stage 1. Retried with
  `TELLA_BUILD_DIR` set to the benchmark webapp package; same failure.
- Separate candidate-versus-baseline Tella check: both clean builds parsed
  3,249 files and compiled 3,248 modules; all 4,880 `.bs.js` files present
  under the webapp (excluding `node_modules`) had identical SHA-256 hashes.
  This is **not** a substitute for the blocked OCaml comparison. The count
  is lower than the historical 5,048 inventory, but equal for both current
  arms. Tella remains at `66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa`, and the
  binary diff of its 18 pre-existing tracked modifications is unchanged.

### Clean-build overhead screen

Baseline: `7f6eceaef` (before this stage), exported with `git archive` into
an isolated build directory. Candidate: this stage's changes. Both use
release compiler/rewatch binaries and the same runtime. Hardware reported
by `sysctl`: **Apple M4, 4 performance + 6 efficiency cores**; 12 workers is
an oversubscribed setting, not a count of physical cores.

Each timed invocation is a fresh `rescript build --in-process --no-timing
true` process, preceded by `rescript clean` via hyperfine `--prepare`.
`RESCRIPT_RUNTIME` points to this worktree's runtime; `RESCRIPT_BSC_EXE`
selects the matching arm. QoS and timing/counter flags are unset. The whole
sequence holds `/tmp/rescript-tella-heavy.lock`, with no compiler builds or
parity runs in parallel. No compiler results are persisted between runs.

| Workers / samples per arm | Baseline mean ± SD | Stage 1 mean ± SD | Baseline min–max | Stage 1 min–max |
|---|---:|---:|---:|---:|
| 12 / 12 | 4.884 ± 0.425 s | 4.839 ± 0.123 s | 4.619–5.796 s | 4.694–5.006 s |
| 1 / 3 | 18.903 ± 0.102 s | 18.759 ± 0.037 s | 18.817–19.015 s | 18.731–18.801 s |

For 12 workers: A/B/A/B blocks, six runs and one warmup per block. For one
worker: A/B, three runs and one warmup per arm. Raw hyperfine results:
[`clean-w12.json`](thread-store-stage1/clean-w12.json),
[`clean-w1.json`](thread-store-stage1/clean-w1.json).

This screen does not show a material slowdown, but it is **not evidence of
an architectural speedup**: baseline parallel runs contain outliers and
pooled medians are 4.721 s baseline / 4.788 s candidate. Stage 2 is needed
to remove repeated imports. External reference parity must also be repaired
and rerun before treating the store as a validated performance improvement.

## Stage 2 implementation status

Commits `a9c5748ba`, `4e964922c`, `82b69fbd4`, `ad389b2a4`.

- `find_pers_struct` internalizes a portable persistent struct into the
  worker store the first time any compilation on the thread needs it; later
  compilations share the graph and the `Arc<PersStruct>`. Store `Tconstr`
  memo cells and `Tpackage` longident names are store-owned. The initial
  implementation suppressed stored-source links and restricted level writes;
  that was not equivalent to OCaml. The mutation-isolation correction below
  replaces those restrictions with descriptor/level overlays.
- Shareability: a graph is shared when every non-`Tlink` entry is at
  `generic_level` and no `Tsubst` remains. `Tlink` levels are dead state
  (`compiler/ml/btype.ml:107-115`, `compiler/ml/ctype.ml:488-503`). On the
  Tella build 1,101 of 1,274 first-time internalizations share; the 173
  fallbacks are polymorphic-variant rows published at non-generic levels
  (`RUST_DEBUG_STORE=1` lists them) and are internalized locally as before.
- Per-unit registries receive one shared `Arc<TypeDeclaration>` per
  declaration of a store-owned signature instead of a fresh clone.
- Rewatch bumps the store generation per build; watch mode never reuses a
  store across builds.

### Validation

Release unless noted: JS 610/610 plus 344 focused fixtures; diagnostics
1431/1431; debug typedtree 610/610; debug lambda 610/610; 18 store-filtered
unit tests. Tella clean build: 3,248 modules, 4,880 `.bs.js` files, all
byte-identical to a build with the stage-1 binaries. External OCaml/Rust
parity remains blocked on the pre-existing `bs-css`/`Belt` failure in the
OCaml reference build.

### Clean-build measurements

Same protocol as stage 1 (Apple M4, 4P+6E; A/B/A/B blocks at 12 workers,
A/B at one worker; `rescript clean` in `--prepare`; heavy lock held; no
concurrent builds). Baseline: the stage-1 head `dce149c78`.

| Workers / samples per arm | Baseline mean ± SD | Stage 2 mean ± SD | Change |
|---|---:|---:|---:|
| 12 / 12 | 4.699 ± 0.032 s | 4.421 ± 0.036 s | −5.9 % |
| 1 / 3 | 18.888 ± 0.067 s | 17.603 ± 0.058 s | −6.8 % |

Raw hyperfine results: [`clean-w12.json`](thread-store-stage2/clean-w12.json),
[`clean-w1.json`](thread-store-stage2/clean-w1.json).

Before the `Tlink` rule the same build measured 18.807 s serial (−1.7 %):
only 416 of 42,730 internalizations reached the store.

### Where the serial time sits after stage 2

`sample` of the one-worker build before the `Tlink` rule (worker thread,
7,604 samples): `find_pers_struct` 9.0 % (local `internalize_signature`
3.4 %, registry walks 4.6 %), `normalize_path_full_inner` 6.3 % (per-unit
freshening of dependency signatures, i.e. OCaml's once-per-process `ps_sig`
force), `load_pervasives` 5.3 % (opened layers of the implicit prelude rebuilt
per unit), `build_local_module_components` 2.2 %, `TypeContext`/`Env`
teardown 10 %. Stage 3 targets the component and prelude blocks; stage 4 the
registries and teardown.

### Corrected stamp policy for stages 3 and 4

The original plan incorrectly inferred a thread-continuous stamp stream
from the one-time initialization in `compiler/ml/predef.ml:450`. The actual
entry point calls `Ident.reinit` (`compiler/core/res_compmisc.ml:49`), and
`init_path` resets persistent Env caches (line 35). Absolute stamp values
also affect JS order: `compiler/core/lam_scc.ml:73-89` iterates stamp-hashed
tables, mirrored by `raw_lambda/lower.rs::binding_dependencies`.

Commit `58fa9f81d` tried continuity and passed the local gates and one Tella
comparison. A subsequent build with different worker scheduling reordered
`inputProperty_encodeJson` and `inputProperty_decode` in
`Service__McpTools.bs.js`. This is a byte-parity failure, not an acceptable
optimization. Commit `9d80fd78e` restores the reference per-unit reset.
The initial single-run validation was insufficient to detect this.

Stages 3/4 must share **unforced templates and context-independent indexes**,
not blindly retain a forced component table with another unit's binders.
Force results need unit-local substitution identity and the reference stamp
consumption/order. Replaying arbitrary global side effects or renumbering
backend identifiers after typing is not an acceptable fix. The proposed
whole-table/prelude cache remains unimplemented until this ownership and
substitution boundary is represented explicitly.

### Mutation isolation correction before stage 3b

The stage-2 `link_type` early return was not justified by the reference:
`Btype.link_type` writes `Tlink` even for a dependency declaration reached
without instancing. The stored handle now has the same `repr`, descriptor,
level, and name-propagation behavior as a local handle. Descriptor writes
allocate a compilation-owned overlay node on first write; level writes use
a separate sparse scalar overlay, so marking does not clone descriptors.
The immutable backing node is never changed. Snapshot/backtrack covers both
already-overlaid nodes and nodes first written after the snapshot. Path
compression uses the same overlay; already-direct links need no write.

This is a correctness prerequisite, not an additional claimed optimization.
In particular, shared component thunks must not retain a result built from
another unit's descriptor/row/level overlays. `Subst.typexp` deliberately
shares `Tvar`/`Tunivar` nodes (`compiler/ml/subst.ml:130-141`); serializing and
re-importing a forced signature would break that sharing, so it is not a
valid shortcut to stage 3b. Its construction context and per-unit effects
still need explicit ownership before component/prelude reuse is enabled.

#### Mutation-isolation validation and overhead screen

Implementation: `48c23780f`. Release compiler/rewatch and debug builds pass;
20 store-filtered unit tests pass, including stored-source link visibility,
name propagation, level writes, path compression, and failed-unify rollback.
Release JS: 344 focused fixtures and 610/610 corpus files. Diagnostics:
1431/1431. Debug typedtree and lambda: 610/610 each, with typedtree caches
cleared before the run. The external reference gate still exits 2 because
OCaml cannot resolve `Belt` from `bs-css`; it does not reach comparison.

After restoring per-unit stamps, all 4,880 webapp JS files match the stage-2
baseline. The final one-worker candidate outputs also match the 12-worker
baseline. Tella's 18 pre-existing `.gen.ts` modifications remain byte-for-byte
unchanged. No compiler results are persisted between clean builds.

Baseline: stage-2 release binaries saved before the stamp experiment
(`7843d130e` source state). Candidate: descriptor/level overlays with the
reference per-unit stamp reset. Same Apple M4 / 4P+6E and heavy-lock protocol
as stage 2; no concurrent compiler builds or parity runs. At 12 workers:
A/B/A/B blocks, six runs plus one warmup per block. At one worker: A/B,
three runs plus one warmup per arm. Hyperfine `--prepare` cleans before each
fresh build process; instrumentation and QoS knobs are unset.

| Workers / samples per arm | Baseline mean ± SD | Corrected store mean ± SD | Baseline min–max | Corrected min–max |
|---|---:|---:|---:|---:|
| 12 / 12 | 4.424 ± 0.025 s | 4.432 ± 0.046 s | 4.382–4.460 s | 4.356–4.524 s |
| 1 / 3 | 17.746 ± 0.076 s | 17.632 ± 0.052 s | 17.688–17.832 s | 17.600–17.692 s |

The correction has no clear material performance cost in this screen
(+0.2% parallel, −0.6% serial); it is not a claimed speedup. Hyperfine flagged
parallel candidate outliers and a slower first serial candidate sample.
Raw results: [12 workers](thread-store-mutation-isolation/clean-w12.json),
[1 worker](thread-store-mutation-isolation/clean-w1.json).

**Remaining:** stage 3's template/forced-view ownership refactor, prelude
sharing, and stage 4's registry removal/reuse. These are not implemented by
this correction; the sub-second target remains unmet.

## Process-wide shared graphs (`types/shared_store.rs`)

Worker stores still built every dependency graph once *per worker*. The
shared pool removes that duplication, after Zig's `InternPool`:

- One pool per build generation (`pool_for`), held by every worker store.
- A graph is internalized completely (descriptors, levels, variant layouts)
  and then published into a page-aligned index range. The page table is a
  `Arc<[OnceLock<Arc<SharedGraph>>]>`: any worker resolves a shared index
  with lock-free reads, and nothing is written after publication.
- `PortablePersStruct` identity -> `OnceLock<Arc<PersStruct>>` slot, so two
  workers that need the same dependency at once wait for one builder.
- References carry `STORE_REF_TAG | SHARED_REF_TAG` (types, abbreviation
  memo cells keyed by their `Tconstr` node, variant layouts). Shared
  references are also `is_store()`, so store-build poisoning treats them as
  non-local.
- Writes never touch a shared node: descriptor, level and memo writes go to
  `TypeContext::shared_*_overlay` (included in type-state snapshots), like
  writes to worker-store nodes.
- Shared descriptor borrows are `Ref::map` borrows of a never-mutably
  borrowed page-table handle, so `TypeDescRef` stays a plain `Ref`. An enum
  borrow type (`Local`/`Shared`) cost ~2.5G instructions per build because
  it stopped `repr`/`get_desc` from inlining; materializing shared nodes into
  the compilation on first read cost ~1G.

Measured on a 3248-module app, 10 workers, three interleaved pairs:
instructions 86.03G -> 85.96G, cycles 46.30G -> 46.09G, peak RSS
2.27 GB -> 1.92 GB, JS/gen.ts output byte-identical. Serial builds pay
~0.8G instructions for the extra indirection. The remaining per-worker
dependency work (component views, signature registrations, `StorePiece`
replay) is per-unit rather than duplicated.
