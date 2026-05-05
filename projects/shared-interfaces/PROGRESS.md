# Shared Interfaces — Progress Log

## Goal

Share materialized module interfaces across the modules a rayon worker
compiles, so dependency type graphs are internalized once per worker
instead of once per compile. End-state ambition: tella in-process build
under 1s wall on a 10-core machine, down from ~5s today.

## Session 1 — 2026-05-04

### What landed

The infrastructure for per-worker `TypeContext` reuse is committed but the
wire-up that actually shares state across compiles is *not yet active*.

1. **`Arc<IdGenerator>` migration.** Removed the `<'a>` lifetime parameter
   from `TypeContext` and replaced `id_gen: &'a IdGenerator` with
   `id_gen: Arc<IdGenerator>`. This was a prerequisite for putting a
   `TypeContext` in thread-local storage where no caller can express a
   borrow. ~700 mechanical references updated; no behavior change.
   Commit: `Drop lifetime parameter on TypeContext via Arc<IdGenerator>`.

2. **`TypeContext::begin_compile`.** A reset method that clears the
   compile-scoped state (generalization levels, abbreviation memos,
   env-keyed lookup caches, typed-tree env snapshots, per-compile
   parse-arena-tied caches) without touching worker-scoped state (type
   arena, declaration stores, predef singletons, persistent_env, raw and
   renamed signature caches, record-label caches). Doc-commented inline
   with what is and isn't reset and why. Currently dead code; ready for the
   wire-up.

3. **`PersistentEnv::from_registry_with_cache`.** A constructor variant
   that accepts a pre-existing `Arc<Mutex<HashMap<...>>>` cache. With this,
   per-worker compiles can share a single `PersStruct` cache so
   `internalize_pers_struct` runs once per (worker, dep) pair instead of
   once per (compile, dep) pair. Currently unused.

4. **`TypeContext::clear_persistent_env_for_park`.** Releases the
   per-compile `PersistentEnv` reference held inside `TypeContext` so the
   context can be parked back in thread-local storage between compiles.
   Currently unused.

5. **Project tracker.** This document lives in
   `projects/shared-interfaces/`. The driver.rs file has a comment block
   referencing this PROGRESS.md so future sessions find the rationale.

### What was attempted and reverted

A full wire-up that:

- parked `TypeContext` and `Arc<Mutex<PersStructCache>>` in thread-local
  storage,
- acquired them via a `WorkerSession` guard at the top of
  `compile_preprocessed_structure_in_process_with_signature_hook` and
  `typecheck_preprocessed_signature_in_process`,
- reset compile-scoped state via `begin_compile` per compile,
- reused them across the modules each rayon worker compiled.

This compiled and ran. Two real blockers showed up against the tella-fusion
in-process build and the wire-up was reverted:

#### Blocker 1: cache-hit path skips per-compile side effects

`find_pers_struct`'s portable-cache miss path runs
`collect_alias_rewrites` against `self.alias_prefix_rewrites.local` (a
`HashMap<String, Path>` owned by the current `PersistentEnv`). With the
`PersStruct` cache shared across compiles, the miss path runs only on the
first compile in a worker; later compiles hit the cache and skip the
rewrite collection. The next `PersistentEnv` is constructed fresh from the
registry's base alias rewrites, missing whatever was added during prior
compiles, and downstream lookups fail with `TypeExprRef(0)` (e.g.
`UndefinedMethod { ty: TypeExprRef(0), method: "Command.make" }` on
`TrimTranscriptEditor`).

Fix sketch: promote the `alias_prefix_rewrites.local` map into the same
thread-local storage as the cache, or have the cache hit path always run
the per-compile side effects (`collect_alias_rewrites` and any other
miss-path work that mutates `PersistentEnv` per-compile state). The
register-into-`TypeContext` side effects (`register_sig_types_recursive`,
`register_types_by_stamp_in_signature_recursive`) are already idempotent
on a shared `TypeContext`, so those don't need re-running, but a careful
audit of the miss path is required to identify all state-mutating side
effects that the cache hit path bypasses.

#### Blocker 2 (re-diagnosed): the 7.8GB was from disabled cache sharing, not arena reuse per se

I initially wrote this up as an unbounded-`TypeArena`-growth blocker
needing a between-compile sweep or generational arena. That diagnosis
was wrong. Re-thinking:

- The old model materialized a compile's full dep closure (~500K types)
  into a per-compile arena and dropped the arena at compile end. Peak
  memory at any instant was bounded by the in-flight compiles ×
  per-compile materialization, ~500MB on a 10-core run.
- The new model with cache sharing *working* would materialize each dep
  once per worker. The worker's arena holds one copy of each touched
  dep's types plus small per-compile transients. Bounded similarly to
  the old model.
- The 7.8GB run was the *worst of both worlds*: cache sharing disabled
  (after blocker 1 broke things) while `TypeContext` was still shared.
  Every compile re-materialized its dep closure into the same arena, so
  after 213 compiles each worker held ~213 copies of the same dep
  types. That's an artifact of my broken intermediate state, not of
  per-worker reuse.

The remaining concern in this category is small: per-compile transient
types (fresh tvars, intermediate Tlinks during unification) do
accumulate in an append-only arena. Order-of-magnitude estimate: a few
tens of MB per compile × 213 compiles = a few GB per worker over a long
build. That may or may not warrant a sweep, but it's an optimization
question rather than a feasibility blocker. Concrete approaches if it
matters:

- **Mark-and-sweep**: walk preserved roots, mark reachable
  `TypeExprRef`s, compact the arena, remap stored refs. Big mechanical
  pass.
- **Generational arena**: split into "permanent" (worker-scoped) and
  "scratch" (compile-scoped); promote on compile end. Composes naturally
  with the cross-worker shared-catalog Step B.

Neither is required to land per-worker reuse usefully.

### Tella build timing baseline

`/usr/bin/time -p rescript build --in-process` against tella-fusion on
a 10-core M-series:

- Pre-merge baseline (in-process-new tip before this session): 5.07s warm
- Post-Arc<IdGenerator> + infra commits, no wire-up: 5.50s warm
- Worker-session wire-up, cache shared: tella build fails on
  `TrimTranscriptEditor`
- Worker-session wire-up, cache *not* shared, TypeContext shared: 5.02s
  best, 10.21s worst, peak memory 7.8GB

Typedtree parity (`./scripts/test_typedtree_parity.sh`): 660/660. The
parity test invokes standalone `bsc`, not rewatch's in-process flow, so
it's insensitive to driver.rs / rewatch changes.

## Session 2 — 2026-05-05

### What was checked

The worker-session wire-up was re-tested against tella-fusion after adding
cache-hit preparation in `PersistentEnv::find_pers_struct`. The alias-rewrite
miss/hit mismatch from Session 1 is no longer the only issue.

### What makes sense to keep

1. **Cache-hit persistent-env preparation.** A cached `PersStruct` now still
   runs the per-`PersistentEnv` side effects that OCaml gets while
   acknowledging/loading persistent structures (`compiler/ml/env.ml:669-688,
   695-712`): alias rewrites are collected for the current env and lazy raw
   signatures are registered when needed.

2. **Stale negative shared-cache invalidation.** A shared worker cache can
   hold an old `None` miss while the `ModuleRegistry` has since published the
   module. OCaml overwrites its persistent table on save/load
   (`compiler/ml/env.ml:642-645, 687-688, 707-709, 1960-1977`), so Rust now
   discards that stale negative entry and falls through to the registry.

3. **`TypeContext::begin_compile` abbrev safety.** The abbrev memo side table
   must stay append-only because preserved arena types contain
   `AbbrevMemoRef` indices. Truncating the table between worker compiles can
   make cached type nodes observe unrelated memo cells.

### What was rejected

The active driver wire-up is still unsafe and was not retained. With a reused
worker `TypeContext`, tella-fusion clean builds either failed on
`UndefinedMethod { ty: TypeExprRef(0), method: "Command.make" }` or produced
semantic JS output drift. A direct diff in `PublicApiLogger.bs.js` changed
variant lowering shape, not just temporary variable names, so this is a real
type-representation freshness issue.

Measured during review:

- Default in-process Tella clean build: ~5.1-5.3s wall.
- Worker-session experiment: one successful 4.65s run, then unstable
  5.07s/semantic drift. Not acceptable.
- Non-Tella typedtree parity after retained changes: 660/660.
- Non-Tella JS output parity after retained changes: 660/660.

### Updated next session

The next worker-session attempt must fix type-representation freshness before
the driver wire-up can be enabled. Concretely: identify which `TypeContext`
stores/caches encode per-module representation decisions or stamp-sensitive
state, then either reset them per compile or make them key by enough
per-module identity that cached dependency declarations cannot affect the
current module's data representation/lowering.

### Superseded Session 1 next session

The next session needs *one* focused fix, not two. With the memory
re-diagnosis above, the only true blocker is cache-hit-path side
effects:

1. Walk every code path in `find_pers_struct`'s miss branch and either
   (a) move the per-compile side effects into a separate
   `prepare_per_compile_persistent_env_state(name)` method called on
   every `find_pers_struct` regardless of cache hit/miss, or (b) move
   the mutated state (`alias_prefix_rewrites.local`) onto the shared
   cache. The known-affected state is
   `PersistentEnv::alias_prefix_rewrites.local`; an audit may find more.

2. Re-enable the worker-session wire-up (`WorkerSession::acquire`,
   `from_registry_with_cache`, `begin_compile`). Validate parity still
   passes, measure tella build time, document delta.

3. Optional follow-up if transient-type accumulation in the arena
   becomes measurable: add a between-compile sweep or split the arena
   into permanent + scratch regions. Not on the critical path for the
   first measurable speedup.

This section is kept as historical context. Session 2 supersedes it: the
cache-hit side effects are partially addressed, but shared `TypeContext`
reuse still has type-representation freshness problems and must remain
inactive.
