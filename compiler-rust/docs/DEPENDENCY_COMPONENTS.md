# Dependency component tables in in-process builds

This note covers how an in-process `rescript build` builds the component
tables of dependency units, what each module still repeats, and the plan for
building them once per build.

## OCaml reference

`Env.find_pers_struct` reads a unit's `.cmi` once per process
(`compiler/ml/env.ml:669-678`). `ps_comps` is built lazily from `Env.empty` by
`components_of_module` (`env.ml:1516-1588`), and each child's `comp_modules`
entry is a thunk that is forced on first use. `bsc` runs one process per
module, so every module rebuilds the tables of every dependency it touches,
and allocates the binder stamps of each table it forces in its own stamp
sequence.

## Current Rust design

An in-process build compiles many modules on each worker thread.

* `shared_store` (process-wide) internalizes each dependency type graph once
  per build.
* `thread_store::ThreadTypeStore` (one per worker) holds component views of
  persistent-rooted paths (`shared_components`), built inside
  `TypeContext::build_in_store`. A view is published with a `StorePiece`: the
  journal of effects the build had on the compilation that ran it (stamp
  advances, `find_pers_struct` preparation, alias-source registrations,
  nested pieces). A later compilation that uses the view replays the piece
  once (`touch_store_piece`), so it observes the same stamps and registrations
  as if it had built the view itself. A build that reads compilation-local
  state is poisoned and stays private to that compilation.

So views are already built once per worker per build, not once per consuming
module. `build_shared_persistent_root_components` passes a fresh child map,
but it runs only inside such a store build.

## Measurements (Tella, 498250d46d, 2 samply runs, busy CPU)

* Store builds: 16,976 published and 1,191 poisoned
  (`RESCRIPT_STORE_DEBUG=1`), against 4,032 distinct views, so each view is
  built about 4.2 times (once per worker that needs it). There are 112,319
  shared-view hits. `build_in_store` is 3.2% inclusive and
  `internalize_pers_struct` 1.1%.
* Replay (`touch_store_piece`) is 2.1% inclusive. 0.94% of it is
  `find_pers_struct` for `StoreEffect::PreparePers`, run on a throwaway
  `persistent_env_clone()`, where `Arc::make_mut` copies the resolution view,
  the `outside_load_path` memo restarts empty and `collect_alias_rewrites`
  runs again. Another 0.52% is `register_component_alias_source`.
* Poison reasons: `read:component_paths_for_alias_source` (646) and
  `local-stored-components` (564).
* `get_level`'s component lookups (498250d46d) cost 2.35% inclusive. Most of
  that is the first per-worker build of a view in
  `build_module_components_from_parent_path` (1.19%), plus replay (0.43%) and
  `unit_visible` (0.17%).
* `persistent_env_clone` itself is negligible (0.00%): its fields are `Arc`s.

## Per-module state reuse (Part 1): not worth it

Per-module teardown is 1.7% of busy CPU. Almost all of it is the contents of
the per-module state, not the containers that hold it:

* `TypeContext::typed_envs` (`Vec<Arc<Env>>`): 0.98%, the persistent-map
  nodes of the module's environments (`bitmaps::Iter`, `Rc::drop_slow`).
* `TypedArena`: 0.45%, the typed-tree nodes' own allocations.
* Everything else: below 0.1% each.

Clearing and reusing these containers would still drop the same entries. It
saves only the container frees and their regrowth. `reserve_rehash` (3.7%) is
spread over transient local maps: `unify` 0.25%, `Name::new` 0.17%,
`extract_type_path_from_expected_inner` 0.15%, component construction and
substitution memos. `TypeContext` maps account for well under 0.5% of it.
The rest is too small to measure against Tella's run-to-run noise
(sd about 0.08 s user), so it does not justify a reset protocol over 100
`TypeContext` fields, which could leak stamps or caches between modules.

## Plan: once per build (Part 2)

The remaining redundancy is per worker (the 4.2x above) plus per-module
replay. Building views once per build needs:

1. **Process-wide immutable view core.** Split `QualifiedModuleComponents`
   into an immutable part (the signature index, the substituted items and the
   child declaration list), built without reading compilation state, and a
   per-compilation forcing state (forced child thunks, memoized lookups) kept
   in `TypeContext`. The immutable part must be `Send + Sync` and own no
   `RefCell`.
2. **Shared allocation target for view builds.** Nodes created while a view is
   built (substitution copies) must go to a `shared_store` graph that is
   complete before it is published, as dependency graphs are today, instead of
   the worker store. Binder stamps of shared data already come from the
   process-wide `STORE_STAMP` range.
3. **Replay unchanged.** A `StorePiece` already records every effect a
   compilation must observe. Building on another thread does not change what
   is replayed, so stamps stay exactly those of a module that built the view
   itself. Hard constraint: construction must not depend on the consumer. Any
   build that reads consumer state stays poisoned and private, as today.
4. **Cheaper replay** (independent of 1–3): shrink the poison sources above
   by making their reads consumer-independent. Skipping a repeated
   `PreparePers` replay of the same unit was tried and reverted: one batch
   showed `replay_store_piece` 1.79% -> 1.57%, the next 1.80% -> 1.76%, so
   repeats are rare. Most replay cost is the first `PreparePers` of each unit
   per module (resolution-view copy on the throwaway clone,
   `collect_alias_rewrites`) and `register_component_alias_source`; a
   copy-free replay of the cached-unit case is the next candidate, at most
   ~1% of busy CPU.

Landed: a component lookup reads the compilation's own cache before it
computes the worker-shared key, so `unit_visible` runs only on a miss
(0.63% -> 0.21% of busy CPU).

Order of slices: (4), then (1) without changing ownership, then (2) and the
cross-thread publication. Each slice must keep typedtree, raw Lambda, Lambda,
JS and error-output parity, and Tella output, byte-identical.
