# Status of the design documents against the code

An audit of plan against code. Trunk `ocaml-to-rust-rewrite` at `e5ada1df9`
(2026-11-13). It answers one question with evidence: have the design
documents been followed as rewrites of the structures they name, or as
changes in front of the old structures?

How to read it.

- Every status below comes from a command run on that commit, not from a
  document's prose. Commands are run from `compiler-rust/` unless a path
  starts with another top-level directory. "0" means no match.
- A status is one of: **done as designed**; **done in part** (what is missing
  is said); **built beside** (built beside the old code and not switched on);
  **not started**; **dropped** (with the document's reason).
- Pull requests are those of this repository. They were found with
  `git log --oneline` on the files and `gh pr list --state all`.
- Savings are quoted only where a document or a merged pull request measured
  them. This audit measured no instruction count.
- "The application" is the 3,735-module application the documents measure.

## Short answer

- **The type checker has not been rewritten, and the documents decided that it
  would not be.** CHECKER_REDESIGN section 0 says "`typecore.rs` and
  `typemod.rs` (52,000 lines) are not rewritten", and I.6 dropped the new
  core (P7, P8, P9, P12) because sharing type nodes is observable in the
  output. What merged are changes on today's representation: three in-place
  slices of K.6 (C1 to C3) and five of the eleven world slices of J.4 (W1 to
  W4 whole or nearly, W5 in part). The old mechanisms J.2 lists as "gone" are
  still there in 10 of 13 rows.
- **The backend's new structures exist beside the old ones and none is on the
  default path.** The new lowering handles 1,290 of 1,438 units of the three
  in-repository corpora completely in check mode; every build still runs the
  legacy lowering, the six JS passes and the legacy printer.
- **Two front-end slices replaced what they named and deleted it** (T2, T7),
  as did the snapshot stages S1 to S5.

## 1. CHECKER_REDESIGN.md

### 1.1 Stages P0 to P12 (section F, as amended by sections I and J)

The end state of these stages is prose, not `rg` checks. The checks below
are the nearest facts the code can show.

| Stage | End state in the document | Code today | Status | Pull requests |
| --- | --- | --- | --- | --- |
| P0 | A build comparison script, counters behind `RESCRIPT_COMPILER_COUNTERS`, a canonical signature printer in `types/canonical_sig.rs` (F.2) | `src/types/canonical_sig.rs` 955 lines; `scripts/compare_checker_builds.py` exists | done as designed | #122, #131, #134 |
| P1 | As amended (F.3): only `lower_plain_levels`; the flags byte and every "skip ground types" fast path withdrawn | `rg -n 'fn lower_plain_levels\|fn level_update_is_plain' src/types/ctype.rs` gives 2; `rg -n 'HAS_VAR\|HAS_SCOPED' src` gives 3, all in comments | done as amended; the original stage is dropped (I.1: sharing ground types changes printed names and JavaScript) | #124 |
| P1b | `instance` returns a non-generic root at once (I.5) | `fn instance` in `ctype.rs` returns `ty` when `get_level(ty) != GENERIC_LEVEL`, before any copy session | done as designed | #137 |
| P2 | `Expected` in `type_expect_full`; one row of C.9 per pull request (F.4) | `rg -n 'enum Expected' src/types/typecore.rs` gives 1 | done in part: #132 converted five cases (constants, identifiers, fields, application results, the function position). Its body says `type_application` "still calls `unify_expression_types` with a fresh variable after `end_def`", and unconverted constructs materialise the variable | #132 |
| P3 | The unit's `SharedGraph` built directly; fingerprint and digests hashed from the graph; the two saving copies in `driver.rs` reduced to one (F.5) | Publication on the checking worker and the graph hash merged. `rg -n 'copy_lookup_signature_for_subst' src/driver.rs` gives 4 (J.2 expects 1) | done in part: the save copies remain; they are slice W8 | #119, #140, #143, #151, #154 |
| P4 | Process-wide views; stamp replay deleted (F.6) | `rg -n 'StoreStampOrigins\|StoreEffect::Stamps' src` gives 0 | done in part: the stamp replay is deleted; the rest became W3 to W7 | #166 |
| P5 | Absolute paths in exported graphs; no lookup copies (F.7) | `rg -n 'struct Segment\b\|UnitExports' src` gives 0 | dropped as written (J.3.7: exported graphs keep local identifiers); its saving has two owners, W4/W5 and W8 | - |
| P6 | `Env` as a binding log (F.8) | `src/types/env_log.rs` 2,384 lines and `env_log_tests.rs` 2,082 lines, declared `#[cfg(test)] mod env_log` in `env.rs`; no other use (`rg -n 'env_log' src` outside those files gives only that declaration) | built beside, and the switch is dropped (H.2.11: the real-build measurement predicts 2 to 4% more instructions) | #125, #142, #146, #168 |
| P7, P8, P9 | Term store, new core operations, switch (F.9 to F.11) | `src/types/terms.rs` does not exist; `rg -n 'CoreMode' src` gives 0 | dropped (I.6: "P8 saves nothing that is sound") | - |
| P10 | Segments, export tables, one checker per worker (F.12) | see W9, W10, W11 below | not started; re-cut as W9 to W11 | - |
| P11 | A series of profile-driven pull requests on the walk (F.13) | see C3 and C4 below | done in part: C3 only | #186 |
| P12 | Delete the old core (F.14) | - | dropped (I.6: "there is no old core") | - |

### 1.2 Section I: what the checker core should become

Section I defines no slice. Its decision (I.3.2, option 3) is that the core
stays `types/ctype.rs` on `TypeContext` storage, under the eight rules of
I.3.3. What the code shows of those rules:

| Rule of I.3.3 | Check | Result |
| --- | --- | --- |
| 1. One node per occurrence, no flags byte | `rg -n 'size_of::<TypeNode>\(\), 32' src/types/context.rs` | 1 (a 32-byte node, pinned by a test) |
| 3. Copy or share is the level | `fn instance` in `ctype.rs` | tests `GENERIC_LEVEL` only (#137) |
| 4. A fast path may skip work, not a write | `fn lower_plain_levels` and its debug check `fn level_update_is_plain` | both present (#124) |
| 5 and 6. Published nodes are frozen; a write to one goes to the compilation | `rg -n 'struct FrozenWrites' src/types/context.rs` | 1 (#180) |
| I.6: fixtures of I.2.3 and I.2.4 in the test suite first | #137's body lists fixtures 2 to 11 added to `super_errors`, `super_errors_multi` and genType | not verified here beyond the pull request body: the fixtures are named by content, not by number |

Rules 2, 7 and 8 describe behaviour of `unify`, the printer and the export;
no `rg` check exists for them and none was run.

### 1.3 Slices W1 to W11 (section J)

J.2 gives the end state as checks. All of them, run on trunk:

**"Exists" rows of J.2.**

| Fact | Check | Result on trunk |
| --- | --- | --- |
| `World` | `rg -n 'pub\(crate\) struct World\b' src/types/world.rs` | 1 (line 65) |
| Shared between threads | `rg -n 'assert_send_sync::<(World\|ModuleView)>' src/types/world.rs` | 2 lines, as expected |
| `ModuleView` has no `Rc`, `Cell`, lock | `rg -n 'Rc<\|RefCell<\|Cell<\|OnceCell<\|Mutex<' src/types/module_view.rs` | 0, as expected |
| `build_module_view(world, scratch, key)` | `rg -n 'fn build_module_view' -A3 src/types/module_view.rs` | `world: &World, scratch: &ViewScratch, key: &ViewKey<'_>`; no `TypeCheckContext`, no `Env` |
| `ViewTable::get_or_build` | `rg -n 'fn get_or_build' src/types/world.rs` | **0**: there is no view table (see 6.1) |
| `adopt_view` | `rg -n 'fn adopt_view' src/types/context.rs` | 1 |
| `FrozenWrites` | `rg -n 'struct FrozenWrites' src/types/context.rs` | 1 |
| `reset_for_module` | `rg -n 'fn reset_for_module' src/types/context.rs` | **0** |
| Two handle tiers | `rg -n 'FROZEN_REF_TAG' src/types/type_expr.rs` | **0** |

**"Gone" rows of J.2** (each expects 0 unless said).

| What | Check | Result on trunk |
| --- | --- | --- |
| Per-worker stores | `rg -n 'ThreadTypeStore\|StoreLease\|thread_store' src` | **66**; `src/types/thread_store.rs` exists, 599 lines |
| Worker-store tier of handles | `rg -n 'STORE_REF_TAG\|SHARED_REF_TAG\|SHARED_REF_BITS\|from_store_index\|fn store_index\|fn is_shared' src` | **110** |
| Store builds | `rg -n 'build_in_store\|in_store_build\|store_build_\|suspend_store_build' src` | **177** |
| Replay | `rg -n 'StorePiece\|StoreEffect\|touch_store_piece\|replay_store_piece\|record_store_effect\|EMPTY_STORE_PIECE\|touched_store_pieces' src` | **66** |
| Poisoning and guards | `rg -n 'poison_store_build\|store_guards_hold\|store_build_guards\|make_private\|forget_entry' src` | **63** |
| Per-worker views | `rg -n 'shared_components\|publish_shared_components\|fn force_entry\|store_pieces\|in_store:' src` | **25** |
| Their switches | `rg -n 'RESCRIPT_FRESH_STORE\|RESCRIPT_NO_SHARED_COMPONENTS\|RESCRIPT_STORE_DEBUG' src ../scripts ../rewatch` | **6** |
| Overlays | `rg -n 'PagedOverlay\|_overlay\b\|set_shared_desc\|store_descs' src/types` | 0 |
| Type marking in levels | `rg -n 'fn mark_type_node\|fn unmark_type\|PIVOT_LEVEL - ' src/types/btype.rs` | 0 |
| Registration tables | `rg -n 'component_alias_sources\|component_paths_by_alias_source\|qualified_module_decl_cache' src/types/context.rs` | **16** |
| Three save copies | `rg -n 'copy_lookup_signature_for_subst' src/driver.rs` expects 1; `rg -n '"save_signature"' src` expects 0 | **4** and **1** |
| Lookup copy through a view | `rg -n 'copy_lookup_' src/types/module_view.rs`; `rg -n 'copy_lookup_value_description_for_subst' src/types/env_lazy.rs` | 0 in `module_view.rs`; 2 call sites in `env_lazy.rs`, whether only for local paths was not verified (it needs reading the callers, not a pattern) |
| Fresh context per module | `rg -n 'fresh_type_context\(\)' src/driver.rs` expects tooling entry points and tests only | **6 calls**: the two tooling entry points, and `compile_until_js`, `compile_source_to_js_with_options_inner`, `typecheck_interface_source` and `typecheck_preprocessed_signature_in_process` |

Of the 13 rows, two are gone (overlays, type marking), one could only be
checked in part (the lookup copy), and ten still match.

**The slices.**

| Slice | End state in the document (J.4) | Code today | Status | Pull requests |
| --- | --- | --- | --- | --- |
| W1 | `rg -n 'RESCRIPT_WORLD_SHUFFLE' compiler-rust/src scripts` gives the read in `shared_store.rs` and the uses in the script | the read at `shared_store.rs:413`; uses in `scripts/test_worker_determinism.py` and its test | done as designed | #173, #177 (the CI job) |
| W2 | The "Overlays" and "Type marking" rows of J.2 give 0 | both 0; `struct FrozenWrites` 1 | done as designed. Measured in #180: -1.06% on `tests/tests`, -1.02% on the application (the row estimated 0.3%) | #180 |
| W3 | `rg -n 'cached_initial_env\|publish_initial_env\|owns_signature\|pool_for' src` gives 0; `rg -n 'build_in_store' src/types/env.rs` gives 0 | 0 and 0; `struct World`, `struct UnitSlot`, `trait FrozenExport`, `fn freeze`, `struct ViewScratch` present in `world.rs` | done as designed, with two differences recorded in 6.1 (the scratch context; units the pool has no room for) | #188 |
| W4 | `rg -n 'build_shared_persistent_root_components' src` gives 0; the `Rc<...` check on `module_view.rs` gives 0; keys: a unit or a chain of structure-typed children; `ViewTable::get_or_build`; items shared without a copy | 0 and 0. `enum ViewKey` exists. `fn get_or_build` 0. `perf_counters.rs` prints `world_view_nodes copied={} shared=0` as a literal | done in part: unit paths only (children moved to W5), no view table, no sharing without a copy. "W4 as built" in the document says so and the code agrees | #196 |
| W5 | The registration rows of J.2 give 0; `rg -n 'shared_components\|publish_shared_components' src` gives 0; no store build starts | 16 and 10. `ViewKey::{Unit, Child, Alias}` exist | done in part: views for structure children and aliases of a unit, transitive adoption. None of the row's deletions is made ("W5 as built": 103 distinct store-built views and 20,033 store builds left on the application with one worker) | #208, #205 |
| W6 | The "Store builds", "Replay", "Poisoning and guards" and "switches" rows of J.2 give 0 | 177, 66, 63, 6 | not started (waits for W5 to finish) | - |
| W7 | The "Per-worker stores" and "worker-store tier" rows give 0; `thread_store.rs` deleted; `MAX_SHARED_INDEX = 1 << 28` | 66 and 110; the file exists; `MAX_SHARED_INDEX` is `1 << 26` in `shared_store.rs` | not started | - |
| W8 | The "three copies" row: 1 and 0 | 4 and 1 | not started. Its stated dependency #154 has merged | - |
| W9 | `fn reset_for_module` 1; `let TypeContext {` destructuring without `..`; `fresh_type_context()` only in tooling entry points | 0; 0; 6 calls including the build path | not started | - |
| W10 | The opened initial environment built once per worker (no `rg` check in the row) | not verified by a check; no pull request found | not started | - |
| W11 | The world outlives a build in watch mode (no `rg` check in the row) | `thread_store.rs` still has `pub fn begin_build` (the discard W11 deletes) | not started | - |

### 1.4 Slices C1 to C5 (section K; "KC1 to KC5")

K.6 gives the end state as checks. Run on trunk:

| Fact | Check | Result |
| --- | --- | --- |
| A local read is one compare and one indexed load | `rg -n 'fn direct' -A8 src/types/context.rs` | `if raw < self.fast_limit.get() { Some(&self.first[raw as usize & (Self::FIRST_LEN - 1)]) }`, no call |
| `locate` | `rg -n 'fn locate' src/types/context.rs` | 1; called from `node_far` and `push` only |
| The four accessors try it first | `rg -n 'self.types.direct\(' src/types/context.rs` | 4 |
| No store-build test on the local path | `rg -n 'poison_store_build\(\)' src/types/context.rs` | 12 calls, none inside `desc` or `get_level`: the two nearest are in the out-of-line `desc_indirect` and `level_indirect` |
| Lists the same | `rg -n 'struct ListChunks' -A6 src/types/type_expr.rs`; `rg -n 'type ListChunks' src/types/type_expr.rs` | a `first` field; 0 |
| No owned clash context in the walk | `rg -n 'Option<TypeClashContext>' src/types/typecore.rs`; `rg -n 'context\.clone\(\)' src/types/typecore.rs` | 1 (the field of `TypeCoreError::ExprTypeClash`); 0 |
| Node size pinned | `rg -n 'size_of::<TypeNode>\(\), 32' src/types/context.rs` | 1 |

All seven hold.

| Slice | End state (K.6) | Code today | Status | Pull requests |
| --- | --- | --- | --- | --- |
| C1 | Leased first array, one-compare read and write | rows 1 to 4 and 7 above | done as designed. `FIRST_LEN` is `1 << 16`. Measured in #187: -5.24% on `tests/tests`, -5.63% on the application; see 6.1 for the memory gate | #187 |
| C2 | Type lists and parameter lists in the same first array | row 5 above | done as designed, with 8,192 slots. Measured in #199: -0.37% on `tests/tests`, -0.33% on the application | #199 |
| C3 | `ClashSite` (`Copy`); no `context.clone()`; no `Vec` in `type_application` | row 6 above; `ClashSite::resolve` at `typecore.rs:1043` | done as designed. Measured in #186: -0.39% on the application | #186 |
| C4 | The other walk families, one pull request per family, each from a profile | no pull request found by title for `type_record`, `let` bindings, constructors, `type_function_nary` or patterns | not started |  - |
| C5 | Snapshots without journal bookkeeping; a probe first | no pull request found | not started | - |

### 1.5 The type checker, in plain facts

```
$ wc -l src/types/{typecore,ctype,typemod,env,thread_store}.rs
  30852 src/types/typecore.rs
  15764 src/types/ctype.rs
  21667 src/types/typemod.rs
   3684 src/types/env.rs
    599 src/types/thread_store.rs
  72566 total
$ wc -l src/types/{world,module_view}.rs
   1580 src/types/world.rs
   2351 src/types/module_view.rs
   3931 total
$ git show --shortstat 5b63dc78b -- compiler-rust/src   # C1, #187
 1 file changed, 274 insertions(+), 12 deletions(-)
$ git show --shortstat 99abad390 -- compiler-rust/src   # C2, #199
 2 files changed, 309 insertions(+), 61 deletions(-)
```

- **Which structures of sections I and K exist.** Of K: the leased first
  node array with the one-compare read (C1), the same for lists (C2), the
  `Copy` clash site (C3). Of J: `World`, `UnitSlot`, the frozen predefined
  environment, `FrozenWrites`, `ModuleView` with three kinds of key, and
  `adopt_view`. Of I: nothing new was to be built; its rules hold where a
  check exists (1.2).
- **What share is still the old representation.** The five files the old
  representation lives in are 72,566 lines. The new world modules are 3,931
  lines and the leased arrays added 583 lines inside `context.rs` and
  `type_expr.rs`. By lines, 94% of that sum is the old files (72,566 of
  77,080). `typecore.rs`, `ctype.rs` and `typemod.rs` were not replaced by
  any merged pull request, and no document asks for that.
- **Which mechanisms the documents say must be deleted are still there.**
  Per-worker stores and `thread_store.rs`; the worker-store tier of handles;
  store builds; pieces and replay; poisoning and guards; per-worker views;
  their three environment switches; the registration tables of
  `TypeContext`; the three save copies; a fresh `TypeContext` per module.
  Deleted: the overlays and level-based type marking (W2), the stamp replay
  (#166), `build_shared_persistent_root_components` (W4), the inline
  `locate` and `type ListChunks` (C1, C2), `context.clone()` in the walk
  (C3).
- **What was measured for the merged parts** (each from its pull request,
  one worker): C1 -5.63% of the application's instructions (#187), W2 -1.02%
  (#180), P2 -0.83% (#132), C3 -0.39% (#186); W5 +0.36% with one worker and
  -1.86% with 8 workers (#208, and "W5 as built"). These were measured
  against different bases and are not added up here.
