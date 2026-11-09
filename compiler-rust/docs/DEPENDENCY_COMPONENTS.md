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
4. **Cheaper replay and fewer private views** (landed, see below).

## Landed

* A component lookup reads the compilation's own cache before it computes
  the worker-shared key, so `unit_visible` runs only on a miss (0.63% ->
  0.21% of busy CPU).
* `StoreEffect::PreparePers` is replayed by
  `PersistentEnv::replay_cached_pers_struct` on the compilation's own
  persistent env: no `Arc::make_mut` copy of the resolution view and no
  `collect_alias_rewrites` into a throwaway copy (-0.15% to -0.18% retired
  instructions). Skipping repeated replays of the same unit was tried
  earlier and reverted (no reproducible gain).
* Guarded store builds. `flattened_alias_component_parent`'s read of the
  alias-source table (`has_component_paths_for_alias_source`) is recorded as
  a guard `(source, nonempty)` on the `StorePiece` instead of poisoning the
  build. The two caches that hand out shared views (the worker's
  persistent-root views in `with_resolved_module_components_for_path_with_cache_mode`
  and `StoredModuleComponents::with_components`) reuse a piece only when
  `store_guards_hold`; on a miss the compilation builds its own copy.
  Exact because registrations are only ever added and the build's own
  registrations are replayed before use. Other `build_in_store` callers
  still treat a guarded read as poison. Tella: poisoned builds 1210 -> 4
  (all `read:renamed_module_sig`), store builds 18024 -> 17189, no guard
  misses, -0.1% retired instructions.

## Remaining work: process-wide view core (step 1-3 above)

Expected gain: at most the per-worker repeat of `build_in_store` (about
4.2 builds per view on 10 workers; `build_in_store` is 3.2% of busy CPU
inclusive, so roughly 2-2.5%). What ties a view to one worker today, and
what each slice must change:

1. **Type nodes.** A store build allocates into the worker's
   `ThreadTypeStore` (`STORE_REF_TAG` handles, `!Send`). To share a view
   across workers, export the nodes a build created
   (`store_build_type_start..`, `store_build_row_start..`) into a
   `shared_store::SharedGraph` when the piece is published, the way
   `extract_module_update`/`portable_types` serialize a unit and
   `shared_store` publishes it, and rewrite the view's handles to
   `SHARED_REF_TAG` ones. Start by measuring how many nodes per view a
   build creates (counter at `build_in_store` exit); if export costs about
   as much as a rebuild, stop here.
2. **View object.** `QualifiedModuleComponents` holds
   `Arc<StructureComponentTables>`, whose memo tables are `RefCell`s and
   `OnceCell`s filled by later forcing (`force_entry` store pieces per name,
   `qualified_modules`, `opened_layers`). Split it into an immutable,
   `Send + Sync` core (access path, substituted signature,
   `SignatureIndex`) and the forcing tables. Keep the forcing tables per
   worker at first (they already hold store pieces), keyed by the core's
   id. Shared core plus worker-local forcing is the first slice that can
   land parity-clean.
3. **Pieces.** `StorePiece` effects hold `Arc`s of worker objects
   (`RegisterComponents(key, Arc<QualifiedModuleComponents>)`,
   `RegisterQualifiedModuleDecl`). Make them refer to shared cores or ids so
   a piece can cross threads. The effects and their order must stay exactly
   as recorded: replay is what keeps Ident stamps equal to OCaml's
   (`Stamps(n)` advances, `TriggerRename`, `PreparePers`).
4. **Publication.** Add a process-wide map next to
   `ThreadTypeStore::shared_components` (same `QualifiedModuleComponentsCacheKey`,
   `is_worker_shareable` keys only, reset by `begin_build`), consulted after
   the worker map, with `store_guards_hold` checked exactly as today.
   Visibility (`unit_visible`) stays a per-compilation check before the
   lookup.

Each slice must keep typedtree, raw Lambda, Lambda, JS and error-output
parity, and Tella output, byte-identical. Check `RESCRIPT_STORE_DEBUG=1`
counts (store-build, store-hit, store-poison, store-guard-miss) before
and after each slice.
