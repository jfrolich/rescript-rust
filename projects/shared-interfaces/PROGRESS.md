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

5. **Project tracker.** This document and `PLAN.md` live in
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

#### Blocker 2: unbounded `TypeArena` growth

The `TypeArena` is append-only. Per-compile state (transient type
variables, fresh instantiations, intermediate Tlinks, etc.) accumulates
in the arena across all the modules a worker compiles. With ~213 modules
per worker on a 10-core run of tella-fusion, peak memory footprint went
from ~50MB to ~7.8GB and wall time was variable (5.0s → 10.2s on
back-to-back runs depending on allocator behavior). The per-allocation
cost rises with arena size and the system starts page-faulting under
the larger working set.

Fix sketch: between compiles, drop any types not reachable from the
worker-scoped state we actually want to preserve (the declaration stores,
the `PersStruct` cache, the predef singletons, the renamed-sig cache).
Implementation options:

- **Mark-and-sweep**: walk the preserved roots, mark every reachable
  `TypeExprRef`, compact the arena keeping only marked entries. Requires
  remapping every `TypeExprRef` in every preserved data structure to the
  compacted indices — a large but mechanical pass.

- **Generational arena**: split the arena into "permanent" (worker-scoped)
  and "scratch" (compile-scoped) regions. New allocations go into scratch
  during a compile; promotion to permanent happens at compile end for
  types reachable from preserved state. The scratch region resets to
  empty on `begin_compile`. This is closer in spirit to the published-
  interface catalog from `PLAN.md` Step B, where shared types live in a
  separate read-only catalog.

- **Per-worker session lifetime**: skip the in-arena reuse entirely and
  instead pay the full re-internalization cost; this is what the rejected
  worker session did. Doesn't move the needle.

The generational-arena approach is the right answer because it composes
with the eventual cross-worker shared catalog: the published-interface
catalog is just the global "permanent" arena.

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

### Next session

The next session should land both fixes together because they're
interdependent: cache sharing without arena pruning produces unbounded
memory growth, and arena pruning without cache sharing doesn't amortize
the materialization work. Concretely:

1. Walk every code path in `find_pers_struct`'s miss branch and either
   (a) move the per-compile side effects into a separate
   `prepare_per_compile_persistent_env_state(name)` method called on every
   `find_pers_struct` regardless of cache hit/miss, or (b) move the
   mutated state (`alias_prefix_rewrites.local`) onto the shared cache.

2. Implement either generational-arena allocation or a between-compile
   `TypeContext::sweep_unreachable_types` pass that compacts the arena
   keeping only types referenced from `type_decl_store`, `type_decl_by_stamp`,
   `type_decl_by_path`, `resolved_pdot_type_cache`, `resolved_module_sig_cache`,
   `record_label_descriptions_cache`, the persistent-env cache values, and
   the predef singletons.

3. Re-enable the worker-session wire-up. Validate parity still passes,
   measure tella build time, document delta.

Until those are in, the infrastructure committed in this session is dead
code (deliberately so) and the in-process build behaves identically to
the pre-session state.
