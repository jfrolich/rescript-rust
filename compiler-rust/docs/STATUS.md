# Status of the design documents against the code

An audit of plan against code. Trunk `ocaml-to-rust-rewrite` at `e5ada1df9`
(2026-11-13), with the backend-lowering coverage and S3.7 row updated by
S3.7b (see [measurements](LOWERING_LOOPS_RECURSIVE_RESULTS.md)). It answers one question with evidence: have the design
documents been followed as rewrites of the structures they name, or as
changes in front of the old structures?

How to read it.

- Statuses outside the updated backend-lowering rows come from commands run
  on that commit, not from a
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
  default path.** The new lowering handles 1,453 of 1,454 units of the three
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
| `ViewTable::get_or_build` | `rg -n 'fn get_or_build' src/types/world.rs` | **0**: there is no view table (see 7.1) |
| `adopt_view` | `rg -n 'fn adopt_view' src/types/context.rs` | 1 |
| `FrozenWrites` | `rg -n 'struct FrozenWrites' src/types/context.rs` | 1 |
| `reset_for_module` | `rg -n 'fn reset_for_module' src/types/context.rs` | **0** |
| Two handle tiers | `rg -n 'FROZEN_REF_TAG' src/types/type_expr.rs` | **0** |

**"Gone" rows of J.2** (each expects 0 unless said).

| What | Check | Result on trunk |
| --- | --- | --- |
| Per-worker stores | `rg -n 'ThreadTypeStore\|StoreLease\|thread_store' src` | **66**; `src/types/thread_store.rs` exists, 599 lines |
| Worker-store tier of handles | `rg -n 'STORE_REF_TAG\|SHARED_REF_TAG\|SHARED_REF_BITS\|from_store_index\|fn store_index\|fn is_shared' src` | **110** |
| Store builds | `rg -n 'build_in_store\|in_store_build\|store_build_\|suspend_store_build' src` | **166** |
| Replay | `rg -n 'StorePiece\|StoreEffect\|touch_store_piece\|replay_store_piece\|record_store_effect\|EMPTY_STORE_PIECE\|touched_store_pieces' src` | **45** |
| Poisoning and guards | `rg -n 'poison_store_build\|store_guards_hold\|store_build_guards\|make_private\|forget_entry' src` | **60** |
| Per-worker views | `rg -n 'shared_components\|publish_shared_components\|fn force_entry\|store_pieces\|in_store:' src` | **15** (none is `shared_components` or `publish_shared_components`) |
| Their switches | `rg -n 'RESCRIPT_FRESH_STORE\|RESCRIPT_NO_SHARED_COMPONENTS\|RESCRIPT_STORE_DEBUG' src ../scripts ../rewatch` | **4** (`RESCRIPT_NO_SHARED_COMPONENTS` is gone) |
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
| W3 | `rg -n 'cached_initial_env\|publish_initial_env\|owns_signature\|pool_for' src` gives 0; `rg -n 'build_in_store' src/types/env.rs` gives 0 | 0 and 0; `struct World`, `struct UnitSlot`, `trait FrozenExport`, `fn freeze`, `struct ViewScratch` present in `world.rs` | done as designed, with two differences recorded in 7.1 (the scratch context; units the pool has no room for) | #188 |
| W4 | `rg -n 'build_shared_persistent_root_components' src` gives 0; the `Rc<...` check on `module_view.rs` gives 0; keys: a unit or a chain of structure-typed children; `ViewTable::get_or_build`; items shared without a copy | 0 and 0. `enum ViewKey` exists. `fn get_or_build` 0. `perf_counters.rs` prints `world_view_nodes copied={} shared=0` as a literal | done in part: unit paths only (children moved to W5), no view table, no sharing without a copy. "W4 as built" in the document says so and the code agrees | #196 |
| W5 | The registration rows of J.2 give 0; `rg -n 'shared_components\|publish_shared_components' src` gives 0; no store build starts | 16 and 0. `ViewKey::{Unit, Child, Alias}` exist; an alias key's target is a unit or a view (`AliasTarget`). With `RESCRIPT_COMPILER_COUNTERS=1`, `tests/tests` and a 3,735-module application report `store_build_count=0` at 1 and at 8 workers | done in part: every persistent-rooted path with components is a world view (structure children, aliases of a unit or of another view, children of alias views, children declared with a module type name the unit binds), adoption is transitive, no store build starts, and `shared_components`, the worker-shared branch, `RESCRIPT_NO_SHARED_COMPONENTS`, four `StoreEffect` kinds and `AdoptView` are deleted. Not done and dropped from the plan, because the checker rewrite replaces `TypeContext`, `env_lazy.rs` and `module_view.rs`: the three registration tables, a link's build proportional to its own declarations, view items shared without a copy ("W5b as built") | #208, #205, #226 |
| W6 | The "Store builds", "Replay", "Poisoning and guards" and "switches" rows of J.2 give 0 | 166, 45, 60, 4 | not started; nothing starts a store build since #226, so what is left is unreachable | - |
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
| C1 | Leased first array, one-compare read and write | rows 1 to 4 and 7 above | done as designed. `FIRST_LEN` is `1 << 16`. Measured in #187: -5.24% on `tests/tests`, -5.63% on the application; see 7.1 for the memory gate | #187 |
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

## 2. BACKEND_REDESIGN.md and BACKEND_LOWERING.md

### 2.1 The ratchet file

`tests/backend_coverage.txt` is what CI compares a check-mode build with
(`scripts/test_backend_coverage.py`, run by the validation workflow). Summed
over its three corpora (the parity fixtures, the runtime library,
`tests/tests`) by a ten-line script over the JSON:

| Stage | Units identical / units | Reasons left |
| --- | --- | --- |
| `lambda-bridge` (S2.2) | 1,454 / 1,454 | none |
| `lambda-norm` (S4.1) | 1,454 / 1,454 | none |
| `lambda-flatten` (S4.2) | 1,454 / 1,454 | none |
| `lambda-exits` (S4.3) | 1,454 / 1,454 | none |
| `lambda-alias` (S4.4) | 1,454 / 1,454 | none |
| `js-bridge` (S3.1a) | 1,341 / 1,341 | none |
| `lower` (S3.3 to S3.9) | 1,453 / 1,454 | `shared Lambda subtree with binder` 1 |

`lower` by corpus: fixtures 609 of 609; runtime 113 of 113;
`tests/tests` 731 of 732 (one shared Lambda subtree with a binder, catch-only).
The 3,735-module application lowers 3,848 of 3,848 units including its runtime.
Its previous baseline was 3,709 of 3,848, with `loop` 136 and `let rec` 3.

```
$ rg -U -o 'Unsupported\(\s*"[^"]*"' src/bir/lower --glob '!*tests*'
# no matches; the remaining shared-binder fallback is in the import boundary
```

### 2.2 Stages S0 to S7 (BACKEND_REDESIGN H.1)

H.1 gives a gate per row, not an `rg` check. "Code today" is the file the
row names and, where one exists, the stage of the ratchet file.

| Stage | End state in the document | Code today | Status | Pull requests |
| --- | --- | --- | --- | --- |
| S0.1 | Reformat tool as a library and binary under `scripts/js-reformat/` | the directory exists with `Cargo.toml`, `src`, `tests` | done as designed | #105, #115 |
| S0.2 | Parity scripts get a `--reformat` mode | `rg -n '\-\-reformat' scripts/*.sh` matches `test_js_output_parity_fixtures.sh`, `test_stdlib_output_parity.sh`, `test_rust_parity.sh` | done as designed | #121 |
| S1.1 | `emit/`: naming, oxc AST from `JsArena`; `RESCRIPT_JS_PRINTER=oxc`; default legacy | `src/emit/` 5,420 lines; `PrinterMode` has `#[default] Legacy` | done as designed | #127, #139, #141, #148, #149, #155, #156, #174 |
| S1.2 | Source maps through oxc tokens | `src/emit/sourcemap.rs` 308 lines | done as designed | #150 |
| S1.3 | Switch parity suites and CI to reformat-and-compare | the validation workflow has a job "oxc parity" that runs `test_<suite>_output_parity.sh --printer oxc` beside the exact suites; `tests/printer_coverage.json`: 1,105 of 1,109 outputs emitted by oxc | done in part: the suites run both ways; the exact comparison was not replaced | #160, #163 |
| S1.4 | Default printer is oxc; instruction count falls by about 2.8% | default is `Legacy` | not started, and its premise did not hold: `PRINTER_INSTRUCTIONS.md` measured the oxc printer on the JS IR at +1.51% whole-build instructions on `tests/tests` against the legacy printer. THREE_TREES T5 and T6 replace this row | #175 (the measurement) |
| S1.5 | Remove the legacy printer's layout code from release builds | `src/js_ir/printer.rs` 7,265 lines, `program_printer.rs` 897 | not started | - |
| S2.1 | `Bir`: nodes, pools, views, validator, dump | `src/bir/{mod,node,pools,vars,edit,validate,dump}.rs` exist | done as designed | #117, #123, #144 |
| S2.2 | Bridges, `BackendMode`, `Unsupported`, the report, the ratchet file, the CI job | `src/bir/bridge.rs`, `enum BackendMode { Legacy (default), New, Check }` in `bir/shadow.rs`; stage `lambda-bridge` 1,454 / 1,454 | done as designed, except what `New` does (7.2) | #129, #184 |
| S3.1 | Emit reads J-level `Bir`; naming on `VarId` | `bir/bridge_j.rs` has `import_js` and `export_js` (stage `js-bridge`); no emitter reads `Bir` on trunk | done in part (the bridge), then **dropped** as a product path by THREE_TREES section 10: the emitter over J-level `Bir` measured +10.23% whole-build instructions on `tests/tests` (`PRINTER_INSTRUCTIONS.md`) and is not on trunk | #167, #175 |
| S3.2 | J normalising rules and rounds J1 to J4 in `bir/j/{norm,inline_return,rest,subst,shake}.rs` | `ls src/bir/j`: `equal.rs facts.rs logic.rs mod.rs norm.rs plain.rs` and tests. No `inline_return`, `rest`, `subst`, `shake` | done in part: the rules (#183). The four rounds are not built and change target to T1 and T4 (THREE_TREES section 10) | #183 |
| S3.3 | Lowering, first set (BACKEND_LOWERING 8.3) | `src/bir/lower/{mod,out,expr,cond,call,args,prim,konst,unit}.rs` exist; stage `lower` | done as designed | #170, #182, #190, #191 |
| S3.4 | `Switch`, `StrSwitch`; removes `"switch"`, `"string switch"` | `switch.rs`, `variant.rs`, `untagged.rs` exist; neither reason is in the code | done as designed | #197 |
| S3.5 | `Catch`, `Exit`; removes `"static catch"` | `exit.rs`; the reason is not in the code | done as designed | #210 |
| S3.6 | `LetRec` of functions; self tail calls | `rec.rs`, `tail.rs` | done as designed | #218, #169 |
| S3.7 | Loops, `Break`, `Continue`, loop labels; `Assign`; `Try`; `LetRec` with value members; removes `"loop"`, `"try"`, `"assign"`, the rest of `"let rec"` | `assign.rs`, `try_.rs`, `loops.rs`, `label.rs`, `rec.rs`; no loop/recursive-value Unsupported arms; 512 label shapes and 10,000-element stress tests | implemented in check mode; publication/CI status is separate from the local measurements | #216, #227 |
| S3.8 | Externals; removes `"external"`, `"cross-module inline"` | `external.rs`, `ffi_args.rs`; neither reason is in the code | done as designed | #207 |
| S3.9 | `Pjsx`, `Pimport`, `Pawait`, record copy and rest | `jsx.rs`, `import.rs`, `record.rs`; none of the five reasons is in the code | done as designed | #204 |
| S3.9b | Export extraction and coercion on J-level `Bir`, in `export.rs` | `src/bir/lower/export.rs` does not exist | not started; target changed to the lowering's top-level rows, as slice T4a, which the other T4 slices wait for (THREE_TREES 11.4, finding 2) | - |
| S3.10 | Default `New` for level J; delete `lam_compile*.rs`, `js_pass_*.rs`, `js_shake.rs`, `js_exp_make.rs`, `js_ir/` | all present: `src/lambda` 46,365 lines, `src/js_ir` 16,171 | not started | - |
| S4.1 | Engine and the L normalising rules | `bir/engine.rs`, `bir/l/norm.rs`, `bir/replay.rs`; stage `lambda-norm` clean | done as designed | #153 |
| S4.2 | Deep flatten | `bir/l/flatten.rs`; stage `lambda-flatten` clean | done as designed | #161 |
| S4.3 | Exits | `bir/l/exits.rs`; stage `lambda-exits` clean | done as designed | #171 |
| S4.4 | First alias round with inlining | `bir/l/{alias,beta,arity}.rs`; stage `lambda-alias` clean | done as designed | #176 |
| S4.5 to S4.8 | One round each: `bir/l/{alpha,lets,sroa,exports}.rs` and the later rounds of C.3 | `ls src/bir/l`: `alias.rs arity.rs beta.rs exits.rs flatten.rs mod.rs norm.rs` | not started (rounds 3 to 7 of C.3) | - |
| S4.9 | Default `New` for level L; delete `lam_pass_*.rs`, `lam_beta_reduce.rs`, `lam_compile_main.rs` | all present | not started | - |
| S5.1 | A builder trait implemented by `RawArena` | `trait RawLambdaBuilder` in `raw_lambda/builder.rs` | done as designed | #118 |
| S5.2 | `Bir` builder in `bir/build.rs` | the file does not exist | not started; its input changes to the syntax tree and tables (T9) | - |
| S5.3 to S5.5 | Match compiler: hashed action keys; split-group matrix when read; context lists when read; one-row split; row pool | four of five merged; H.1 says of the row pool "not built ... ceiling 0.15% to 0.2%" | done in part: the row pool is not built, by the document's own decision. Measured (H.1): -0.75%, -0.37% and -0.15% of the application build | #152, #158, #159, #164 |
| S5.6 | Default `New` from the typed tree; delete `RawArena`, `lower.rs`, `LamArena`, the bridges | all present: `src/raw_lambda` 26,232 lines | not started | - |
| S6 | Summaries from facts, `bir/summary.rs` | the file does not exist | not started | - |
| S7 | The checker calls the `Bir` builder directly | - | not started ("own design") | - |

### 2.3 The backend, in plain facts

```
$ rg -n 'apply_.*_pass\(deps' src/lambda/lam_compile.rs      # the six JS passes
928:            apply_js_flatten_pass(deps)
932:            apply_external_shadow_pass(deps)
936:            apply_js_tailcall_inline_pass(deps)
940:            apply_js_record_rest_pass(deps)
944:            apply_js_flatten_and_mark_dead_pass(deps, self.jsx_preserve)
948:            apply_js_shake_pass(deps)
$ sed -n 22,26p src/bir/shadow.rs
    /// Application lowering is an oracle only: New retains the legacy lowering
    /// until the complete backend can replace it.
    pub(crate) fn checks_lowering(self) -> bool {
        matches!(self, Self::Check)
    }
```

- **How many units the new lowering handles completely:** 519 of 593
  fixtures, 103 of 113 runtime modules, 668 of 732 modules of `tests/tests`
  (the ratchet file), and 3,709 of 3,848 units of the application (#218).
- **What still runs the legacy code on the default path: everything.** The
  default `BackendMode` is `Legacy`. `New` runs the bridges and keeps the
  legacy lowering; only `Check` runs the new lowering, as an oracle
  comparison whose result is discarded. Raw Lambda conversion
  (`src/raw_lambda`, 26,232 lines), the Lambda passes and the legacy
  lowering (`src/lambda`, 46,365 lines), the six JS passes and the JS IR
  with its printer (`src/js_ir`, 16,171 lines) all run in every build. The
  new code beside them is `src/bir` (41,674 lines) and `src/emit` (5,420).
  No merged backend pull request claims a default-path saving except the
  match-compiler work of S5.3 to S5.5, which changed the legacy pipeline
  itself.
- **The remaining steps to the switch**, from BACKEND_LOWERING 8.3 and
  THREE_TREES section 11, in order: (1) the rest of S3.7: loops, loop labels
  and `LetRec` with value members, which removes the last two reasons; (2)
  T4: tail-call inlining, block-field substitution, dead declarations,
  record rest, the shake filter and export coercion decided by the lowering,
  so that the new side needs none of legacy passes 3 to 6; (3) T5: names
  from a log of naming events; (4) T6: the builder over oxc nodes, after
  which `RESCRIPT_BACKEND=new` prints from the new lowering; (5) S3.10: the
  default changes and `lam_compile*.rs`, the JS passes and `js_ir/` are
  deleted. For level L: S4.5 to S4.8, then S4.9. For conversion: T8 and T9
  (or S5.2), then S5.6. G.4 adds a condition to every deletion: fallback
  zero on every corpus and two clean weeks of `Check` on trunk.

### 2.4 The printer, in plain facts

- The default printer is the legacy one (`PrinterMode::Legacy`,
  `src/emit/mod.rs`): `js_ir/printer.rs` and `program_printer.rs`, 8,162
  lines.
- The oxc emitter (`src/emit`, 5,420 lines) is selected by
  `RESCRIPT_JS_PRINTER=oxc`, per file, with a whole-file fallback. It emits
  1,105 of the 1,109 outputs of the four corpora of
  `tests/printer_coverage.json`; the four fallbacks are `delete call syntax`
  (2), `JSX sequence container` (1) and `raw literal expression statement
  elision` (1). CI runs the output suites with it.
- It was not made the default. `PRINTER_INSTRUCTIONS.md` measured, on
  `tests/tests`: legacy 4,357.2 M instructions, oxc on the JS IR 4,422.8 M
  (+1.51%), oxc on J-level `Bir` 4,803.1 M (+10.23%). The naming pass alone
  is 56 M to 68 M. BACKEND_REDESIGN estimated a saving of 2.8% for S1.
- The plan for the printer is now THREE_TREES T5 and T6: no naming pass and
  no JS-level dialect. Neither is started.

## 3. THREE_TREES.md

Section 11 gives an `rg` end state per slice, run in `compiler-rust/src`.

| Slice | End state in the document | Result on trunk | Status | Pull requests |
| --- | --- | --- | --- | --- |
| T1 | `rg 'mark_tail_positions\|SELF_TAILCALL' bir` is empty | 0. `bir/lower/scope.rs` has `built` and `remaining` per variable | done as re-scoped: use counts and the deletion. Items 3 to 6 of the original prompt moved to T4 ("T1/T4 boundary finding") | #198 |
| T2 | `rg 'fn rewrite_child' binary_ast/ppx.rs` is empty; `rg 'fn expanded' parse_arena.rs` has one hit | 0; 1 (line 2886). `rg -n 'Rewritten::New' binary_ast/ppx.rs` gives 0 | done as designed for expressions. Measured in #193: -0.97% on `tests/tests`, -0.69% on the application (the row asked for at least 1%). Patterns, core types, module expressions and structure items are still rebuilt, as the row's prompt allows | #193 |
| T3 | `rg 'TastIterator' types/unit_reads.rs` is empty | **2** (`use` and `impl TastIterator for Collector`) | not started on trunk; #192 is an open draft | #192 (open) |
| T4 | `rg 'apply_js_tailcall_inline_pass\|apply_js_shake_pass' bir/shadow.rs` shows the legacy side only | 0 matches: `shadow.rs` calls neither by name, and `bir/lower/export.rs` does not exist | not started in code. Designed and re-cut into T4a to T4f in legacy pass order (THREE_TREES 11.4): the row's commit order cannot be gated, and export coercion (S3.9b) has to come first. Three tests in `bir/lower/oracle_tests.rs` pin the legacy pass order the design rests on | #229 |
| T5 | `rg 'fn replay' emit/naming.rs` has one hit | 0 | not started | - |
| T6 | `rg 'JSeq\|JBlockLit' bir/node.rs` is empty; `rg bridge_j .` is empty | 2; 35. `emit/builder.rs` does not exist | not started | - |
| T7 | `rg 'fn transform_await' binary_ast/ppx.rs` is empty | **1**: the function remains for the awaited-module rewrite, its one caller (`create_await_module_expression`) | done as designed for the four node-local rows; the end-state check does not hold, and section 13 of the document says why. Measured in #206: +0.04% on `tests/tests`, +0.05% on the application for rows A to C | #206 |
| T8 | `rg 'struct ExprRow' types/tables.rs` has one hit | `types/tables.rs` does not exist | not started | - |
| T9 | `rg 'typedtree::Expression' raw_lambda` is empty | 0, but the row is not done: `raw_lambda/convert.rs` imports `Expression` in a `use crate::types::typedtree::{...}` list, which the pattern does not match; `bir/build.rs` does not exist | not started | - |
| T10 | `rg 'push_pattern' types` is empty | 36 | not started | - |
| T11 | `rg 'tctx.typed' driver.rs` hits only the tooling functions | 23 hits | not started | - |
| T12 | `rg 'TypedArena' .` is empty | 230 | not started | - |

The document counted six materialisations of a module (seven with the oxc
printer): the parse tree, its rebuilt spine, the typed tree, raw Lambda,
Lambda and the JS IR. T2 removed the rebuilt spine for expressions. The
other five (six with the oxc printer) are built in every compilation today.

## 4. DERIVED_CODECS.md

Each slice has an "End state" list of `rg` checks, run from the repository
root.

| Slice | End state in the document | Result on trunk | Status | Pull requests |
| --- | --- | --- | --- | --- |
| (before) | The census and the derived bit (#194) | merged | done | #194 |
| 1. The plan, the obligations and the oracle, for constructor applications | `rg -n "Pstr_derived" compiler-rust/src \| wc -l` is at least 8; `rg -n "fn discharge" compiler-rust/src/types/derived.rs` matches; `rg -n "spice\|Spice" compiler-rust/src/types compiler-rust/src/raw_lambda` has no new match; `rg -n "RESCRIPT_DERIVED_PATH" compiler-rust/src` matches only `driver.rs`; `rg -l "@spice" tests/build_tests` is non-empty | 31; matches (line 223); 0; **matches four files**: `driver.rs`, `driver/derived_check.rs` (the oracle, a child module of the driver), and doc comments in `types/typecore.rs` and `parse_arena.rs`; 14 fixtures under `tests/build_tests/super_errors_derived` | done in part, by scope: a planned item still has its general form generated in the front end, plans are taken only at the top level of a unit, and the lowering is in `raw_lambda/convert/derived.rs` (7.3). #215 states "this slice saves nothing that matters": 449 of the application's 7,200 derived bindings take a plan (6.2%), -0.137% of its instructions | #215, #221 (the CI step), #222 |
| 2. Records | `rg -n "some_not_nest\|Psome_not_nest" compiler-rust/src/raw_lambda/derived.rs` has no match; `rg -n "fn compile_matching" compiler-rust/src/raw_lambda` shows one definition; every record without a general reason takes a plan | the file named does not exist (the lowering is `raw_lambda/convert/derived.rs`); `fn compile_matching` 1, with `compile_matching_unresolved` and `compile_matching_with_synced_stamps` beside it; `binary_ast/spice_ppx/plan.rs` asserts `general("@spice type t = {x: int}") == NotYetPlanned` | not started | - |
| 3. Variants | `rg -n "NotYetPlanned" compiler-rust/src/binary_ast` lists only the shapes the Q5 table keeps general | the same test asserts `general("@spice type t = A \| B(int)") == NotYetPlanned` | not started | - |
| 4. Remove the switch | `rg -n "RESCRIPT_DERIVED_PATH" .` has no match; `rg -n "DerivedPath" compiler-rust/src` has no match | 27 and 12 | not started (it follows slice 3) | - |

**Derived code, in plain facts.** The plan pools, `Pstr_derived` and
`Tstr_derived`, the discharge (`types/derived.rs`, 872 lines), the lowering
and the oracle `RESCRIPT_DERIVED_PATH=check` exist and run in CI on
`tests/ppx_spice`. One shape of four takes a plan. On `tests/ppx_spice` 78
of 413 derived bindings take one and 6 of those fall back (#215); records
(5,988 of the application's 7,200 bindings, by the document's census) and
variants do not. The document's expected saving of 5.0% to 6.6% of the
application build belongs to slice 2 and is not measured. The syntax
generator (`binary_ast/spice_ppx.rs`) stays by design: it is the general
path and the producer of every diagnostic.

## 5. RUNTIME_SNAPSHOT.md

The stages have gates, not `rg` checks. "Code today" names the function,
script or CI step that the stage adds.

| Stage | End state in the document (section F) | Code today | Status | Pull requests |
| --- | --- | --- | --- | --- |
| S1 | Belt from the snapshot; `RESCRIPT_SNAPSHOT=off\|require`; the equivalence script | `rg -n 'RESCRIPT_SNAPSHOT' rewatch/src/build/snapshot.rs` reads the variable at two sites; `scripts/test_snapshot_equivalence.sh` exists and the validation workflow has a job `snapshot-equivalence` | done as designed. Measured (F.1): a clean build of `tests/belt_tests` 1,667.8 M instructions from source, 635.3 M with the snapshot | #195, #203 |
| S2 | Runtime: published layout, path rebasing, visible fallback | `fn runtime_config` in `snapshot.rs` (the layout without a configuration file); F.3 reports zero checkout paths in the embedded container | done as designed | #202 |
| S3 | Index lookup and memoised verification; no code generation on fallback | F.3: "No runtime per-module snapshot-registration loop remains". The "stop before code generation" part was **not** made: the document's own note (D6 inspection) found the lowering computes metadata dependents read | done in part, by the document's finding | #202 |
| S4 | `rescript snapshot --write/--check`, `make lib` and CI freshness | `rewatch/cli/src/snapshot.rs` parses both flags; `Makefile:171` runs `snapshot --check`; the workflow step "Check embedded snapshot freshness" | done as designed | #213, #214 |
| S5 | Watch mode and tooling audit | `rewatch/tests/watch/30-snapshot-package-edits.sh` exists; `rg -n 'watch mode is not supported' rewatch/src` gives 0 | done as designed, with a full rebuild on a mismatch in place of dropping one package's entries (7.4). Measured (F.5): -0.05% on `tests/tests`, -0.03% on the application; "the intended one-shot saving is zero" | #220 |
| (D14) | The runtime project compiled once, not twice | the document's "D14 correction and verification" | done; found by this work, not a stage of F | #219 |
| S6 | Cache for third-party packages | no code; F.6: "needs the product decision of G.7 first" | not started | - |
| S7 | Follow the checker redesign (B.8) | waits for "P5 and P10 there", which are now W8 to W10 | not started | - |

**The runtime snapshot, in plain facts.** `rewatch/src/build/snapshot.rs`
is 1,221 lines. The runtime's and Belt's interfaces and Belt's JavaScript
are carried in the executable, found through an index, verified against a
source digest, and checked for freshness and for equivalence with a
from-source build in CI. This is the one plan of the five whose stages
replaced the old path as written: the per-module registration loop is
deleted, and no stage is "beside". What is left (S6, S7) waits on a product
decision and on the checker's world slices.

## 6. FRONTEND_REWRITES.md

The document is an inventory with measurements; it defines no slice of its
own. Its "Candidate destination" column is carried out by THREE_TREES T2 and
T7 (section 3 above).

| Part | What the document says | Code today | Status | Pull requests |
| --- | --- | --- | --- | --- |
| Safe subtree skipping | Certificate bits let the mapper and the validation skip subtrees | `ParseArena::expr_needs_no_rewrite` | done | #120, #130 |
| Expansions | The expression mapper rebuilds nothing; `ParseArena::set_expansion`, readers resolve with `expanded` | `rg -n 'set_expansion' src/binary_ast/ppx.rs` gives 4 call sites; `rg -n 'fn rewrite_child' src/binary_ast/ppx.rs` gives 0 | done for expressions (T2) | #193 |
| Rows marked "Direct (implemented)" in the inventory | `l` integers (two rows), the single record `let`, the boolean match, `async` functions, `await` | `wrap_with_unsafe_async` 0 matches; `transform_await` has one caller, the awaited-module rewrite | done (T7) | #206 |
| Every other row of the inventory | "Destinations are proposals, not claims that these moves have been implemented" | the mapper still handles them: externals, `@inline`, the pipe, `let?`, tuple bindings, `@this`, `%raw`, `%ffi`, regexp, `%todo`, `%%private`, `@deriving(accessors)`, JSX | not started; THREE_TREES section 5 assigns each a destination (expansion, direct or declaration table) but only the T2 and T7 slices exist for them |  - |
| The three validation walks | They stay (`check::Checker`, `NestedExternals`, `UnusedAttributeSweep`) | all three present | kept, as designed | - |

## 7. Where the work departed from the documents

Every entry is a merged change that did something other than the document's
row, with the check that shows it. The documents' own "as built" sections
were the starting list; each was verified against the code. "By design"
marks a departure the document allows or records; the others are open.

### 7.1 Checker

| # | The document | What merged | Verified by | Pull request |
| --- | --- | --- | --- | --- |
| 1 | W4: `ViewTable::get_or_build`, one `OnceLock` per path (J.2) | No table of paths: a unit's view cell is a field of the unit, `PersStruct::ps_view` | `rg -n 'fn get_or_build' src/types/world.rs` gives 0; `rg -n 'ps_view' src/cmi/persistent_env.rs` shows the `OnceLock<Arc<ViewCell>>` field. Recorded in "W4 as built" | #196 |
| 2 | W4: keys are a unit or a chain of structure-typed children | Units only. Children came in W5 (`ViewKey::Child`) | `enum ViewKey` has `Unit`, `Child`, `Alias`; "W4 as built" | #196, #208 |
| 3 | W3 and W4: `ViewScratch` is one context per worker thread | One fresh context per view build | `rg -n 'fn fresh' src/types/world.rs` gives `ViewScratch::fresh`; "W4 as built" | #196 |
| 4 | W4: an item that needs no substitution is taken from the unit's graph without a copy | Not built: every value of a view is copied | the counter line is the literal `world_view_nodes copied={} shared=0` in `perf_counters.rs`. "W5 as built" names this as what the one-worker cost waits for | #196 |
| 5 | W4 deletes the store build for its keys | A bridge was added to the mechanism W6 deletes: a seventh effect kind. #226 deleted it with the four kinds of the W5 row | `rg -n 'AdoptView' src` gives 0 | #196, #226 |
| 6 | W5 deletes `shared_components`, the three registration tables, four `StoreEffect` kinds and `RESCRIPT_NO_SHARED_COMPONENTS`; "after this slice no store build starts" | #208 deleted nothing. #226 moved the remaining kinds of path to views, so no store build starts, and made the deletions except the three registration tables, which the tables of local module paths register into and read too | `rg -n 'shared_components\|publish_shared_components' src` gives 0; `rg -n 'RESCRIPT_NO_SHARED_COMPONENTS' src` gives 0; the registration row of J.2 gives 16. Recorded in "W5b as built" | #208, #226 |
| 7 | J.4: a slice that costs instructions carries a trailer naming where it is repaid | W5 costs +0.49% on `tests/tests` and +0.36% on the application with one worker, and saves 1.86% on the application with 8 workers. The one-worker cost is owed by W6 and by entry 4 | the table of "W5 as built" (not re-measured here) | #208 |
| 8 | W3 deletes the worker store's unit map | A unit the pool has no room for is still internalised into the worker store by each compilation that loads it, until W7 | #188's body, item 4; `thread_store.rs` exists. The branch itself was not traced here | #188 |
| 9 | C1: `FIRST_LEN` "try 8,192 and 16,384 and take the smallest that keeps the instruction count within 0.2% of 65,536" | 65,536, because neither smaller size met the criterion (they cost 4.3% and 2.5% more on the application). The peak-memory gate of the task was not met: +2.74% at the maximum of two 8-worker runs, +1.55% at the mean | `const FIRST_LEN: usize = 1 << 16` in `context.rs`; #187's body, "Gate concern" | #187 |
| 10 | C1 and C2 (by design): the old addressing stays for nodes above the first array and while a store build is active | `direct` beside `node_far`; `set_direct` sets `fast_limit` to 0 during store builds. K.6 says both go with W6 and W7 | `rg -n 'fn set_direct\|fn node_far' src/types/context.rs` gives 2 | #187, #199 |
| 11 | P2: one row of C.9 per pull request until every construct handles `Infer` | Five cases converted; the variable of `type_application` after `end_def` stays because it can lower the function type and report an escape | #132's body; `rg -n 'Expected::Infer' src/types/typecore.rs` gives 6 | #132 |
| 12 | P6 (by design, H.2.11): the log replaces the tables | 4,466 lines of log and tests stay in the tree, compiled only under `cfg(test)`; the production `Env` is unchanged | `#[cfg(test)] #[path = "env_log.rs"] mod env_log;` in `env.rs` | #146, #168 |
| 13 | P1: a flags byte and fast paths for ground types | Withdrawn after it was built and measured (+3.4% for the flags byte; the fast paths change output) | section I; `rg -n 'HAS_VAR' src` matches comments only | #124, #133 |

### 7.2 Backend

| # | The document | What merged | Verified by | Pull request |
| --- | --- | --- | --- | --- |
| 1 | BACKEND_REDESIGN G.1: `New` is "the new path; if it reports `Unsupported(reason)` for a module, the legacy path compiles that module" | `New` keeps the legacy lowering; only `Check` runs the new lowering, and its output is discarded | `BackendMode::checks_lowering` in `bir/shadow.rs` matches `Check` only. BACKEND_LOWERING 8.1 states it | #170, #182 |
| 2 | S1.3 and S1.4: the suites switch to reformat-and-compare, then the default printer is oxc | The oxc printer is a second printer, opt-in, with a whole-file fallback to the first; the suites run both ways. It was measured slower than the legacy printer (+1.51% of the build on `tests/tests`) | `PrinterMode` default `Legacy`; `PRINTER_INSTRUCTIONS.md` | #127 to #174, #175 |
| 3 | S3.1: emit reads J-level `Bir` | Built on a branch, measured at +10.23% of the build, not merged. What merged is its bridge (`bir/bridge_j.rs`, 35 references) which T6 deletes | `PRINTER_INSTRUCTIONS.md`, "Historical experiment"; `rg bridge_j src` gives 35 | #167, #175 |
| 4 | S3.2: rounds J1 to J4 as passes in `bir/j/` | Not built. THREE_TREES changed the target to decisions of the lowering (T1, T4); the legacy passes run on both sides of the gate meanwhile | `ls src/bir/j` | #189 (the decision) |
| 5 | T1 (original prompt): dead declarations, block-field substitution and record rest decided in the lowering; the new side skips legacy passes 4 and 5 | Reduced to use counts and the deletion of the tail-position analysis. A test shows that substitution and dead removal do not commute with the legacy tail-call pass, so items 3 to 6 moved to T4 | `rg -n 'block_substitution_and_dead_removal_do_not_commute_with_tailcall_inlining' src/bir/lower/oracle_tests.rs` gives 1; "T1/T4 boundary finding" | #198 |
| 6 | T4b: move flatten rules to statement-list copies | Done as RESULT B, not a pass removal. R5 changes the copied-branch `simplify_if_head` reader; both final texts are pinned. No dormant implementation; pass 1 stays until T6 | `flattening_a_copied_return_branch_changes_the_simplify_if_head_reader` in `src/bir/lower/oracle_tests.rs`; THREE_TREES §11.4 | #233 |
| 6 | S3.7: loops, labels, `Assign`, `Try`, `LetRec` with value members in one slice | `Assign`, `Try` and `TryFinally` only | reasons `"loop"` (3 sites) and `"let rec"` (1) remain; no `loops.rs` or `label.rs` | #216 |
| 7 | BACKEND_LOWERING 7.1, as first written: `lambda_contains_statement_value_form` needs no fact | It needs one: `HAS_STATEMENT`, recorded where `HAS_EXIT` is. The document was amended in the same pull request | `rg -n 'HAS_STATEMENT' src/bir` gives 13; #210's body, finding 3 | #210 |
| 8 | A stub left beside its replacement | `bir/bridge.rs` still has `import_js` returning `Unsupported("JS arena import not implemented")`; the real one is `bir/bridge_j.rs::import_js` | `rg -n 'fn import_js' src/bir` gives both | #129, #167 |
| 9 | Every stage "deletes the code it replaces" (0.2 item 7) | No backend stage has reached its deletion: S1.5, S3.10, S4.9 and S5.6 are not started, so 47,094 lines of new code sit beside 88,768 lines of legacy backend | the `wc -l` counts of 2.3 | - |

### 7.3 Derived code

All from #215, whose body lists them under "Where this differs from the
design note"; each verified.

| # | The document | What merged | Verified by |
| --- | --- | --- | --- |
| 1 | A planned item "is no longer expanded to syntax" | The general form is still generated in the front end and stored beside the plan, because the checker holds the parse arena by shared reference. A plan saves checking and conversion, not generation or the front-end rewrite | `pub fn general_form(arena: &ParseArena, idx: DerivedIdx)` in `binary_ast/derive.rs` takes a shared reference |
| 2 | The Q5 table of general reasons | One more reason: `Nested` (a declaration not at the top level of its unit); 23% of the application's derived bindings by #215's count | `GeneralReason::Nested` in `binary_ast/derive.rs` |
| 3 | New file `raw_lambda/derived.rs` | `raw_lambda/convert/derived.rs` | `ls src/raw_lambda` |
| 4 | `RESCRIPT_DERIVED_PATH` matches only `driver.rs` | Also `driver/derived_check.rs` and two doc comments | the `rg` of section 4 |
| 5 | `check` compares the stored interface | It compares the canonical signature; stored bytes differ in which nodes two values share | #215's body (not re-run here) |
| 6 | Commit 1 of the prompt updates `tests/ERROR_VARIANTS.md` | Not done: the file does not exist on trunk (AGENTS.md still names it) | `ls tests/ERROR_VARIANTS.md` fails |

### 7.4 Runtime snapshot

| # | The document | What merged | Verified by | Pull request |
| --- | --- | --- | --- | --- |
| 1 | S3: "on a from-source runtime compile, stop before code generation (D6)" | Not made: the lowering computes purity, constants, arities and inlinable bodies that dependents read; only rendering is skipped, as before | the document's "D6 inspection at SN2" | #202 |
| 2 | S5: "drop that package's snapshot entries and compile it from source" | A mismatch revokes the package for the session and requests the existing full rebuild, which recompiles all project dependents | `rg -n 'revoke\|revoked' rewatch/src` gives 13; F.5 says "rather than adding a second invalidation planner" | #220 |
| 3 | B.7: the fallback message is verbose-only | It is at info level, which the CLI shows by default | the document's S1 implementation notes (not re-run here) | #195 |
| 4 | B.4: one filename table to rebase | Three: original and imported tables of exported Lambda locations and an imported index; signatures have two more | the document's S1 implementation notes (not re-run here) | #195 |

### 7.5 Three trees and the front end

| # | The document | What merged | Verified by | Pull request |
| --- | --- | --- | --- | --- |
| 1 | T2: the instruction count falls by at least 1% | -0.97% on `tests/tests`, -0.69% on the application | #193's body; THREE_TREES section 13 | #193 |
| 2 | T2 prompt, step 6: the unused-attribute sweep gets a predicate computed from the tree as written | No predicate: the sweep walks the expansions | `walk_expr(self, arena, arena.expanded(idx))` in `binary_ast/ast_iter.rs`; section 13 | #193 |
| 3 | T2: the mapper's rebuild goes | For expressions. Patterns, core types, module expressions and structure items are still rebuilt by their mappers, and an expression whose such child changed gets a copy as its expansion | FRONTEND_REWRITES, "Expansions" | #193 |
| 4 | T7: `rg 'fn transform_await' binary_ast/ppx.rs` is empty | One hit: the awaited-module rewrite still uses it | the `rg` of section 3 | #206 |
| 5 | T7: direct rows need matching arms in the core IR builder | None was needed: the checker builds the same typed nodes as before | THREE_TREES section 13 (not re-verified beyond the diff being confined to the front end and checker) | #206 |
| 6 | T3 can start at once | Open as a draft since 2026-11-12; trunk still walks the typed tree for unit reads | `gh pr view 192` : `"isDraft":true,"state":"OPEN"` | #192 |

## 8. What is left, in dependency order

Taken from the documents' dependency columns, corrected by sections 1 to 7.
A slice is listed once, under the first thing it waits for.

**Checker (CHECKER_REDESIGN J.4 and K.6).**

1. **W5, the rest**: views for a structure child of an alias view, an alias
   whose target is not a unit, a child that is a module type name; then the
   row's deletions. Waits for nothing.
2. **W4's sharing without a copy**: owed since W4; it is what repays the
   one-worker cost of whole views. Waits for nothing.
3. **W6** (delete store builds, pieces, replay, guards, poisoning): waits
   for 1. K.6 says `fast_limit` becomes a constant and `set_direct` goes in
   the same slice.
4. **W7** (delete the worker-store tier and `thread_store.rs`): waits for
   W6.
5. **W9** (one checker context per worker): waits for W7. **W10** waits for
   W9. **W11** (watch mode) waits for W7.
6. **W8** (publication is one export walk): waits for #154 and W3, both
   merged. It can start now.
7. **C4** (walk families) waits for C3, merged; **C5** (snapshots) waits
   for C1 and W2, merged. Both start with a probe, by K.6.
8. **P2, the remaining rows of C.9**: waits for nothing.

**Backend (BACKEND_LOWERING 8.3, BACKEND_REDESIGN H.1, THREE_TREES 11).**

1. **S3.7, the rest** (loops, labels, `LetRec` with value members): waits
   for nothing; S3.4 and S3.6 are merged.
2. **T4** (scope-close decisions, top-level rows, export coercion; it
   absorbs S3.2's rounds and S3.9b): waits for T1, merged.
3. **T5** (naming events): waits for T1, merged.
4. **T6** (the builder over oxc nodes): waits for T4, T5 and S3.9 (merged,
   but 1 above has to finish for full coverage).
5. **S3.10** (default `New` for level J; delete the legacy lowering, the JS
   passes and the JS IR): waits for T6 and for G.4's conditions.
6. **S4.5 to S4.8** (rounds 3 to 7 of C.3): wait for S4.1, merged. **S4.9**
   (delete the Lambda passes) waits for S4.8 and S3.10.
7. **S6** (summaries) waits for S4.9.

**Trees (THREE_TREES 11).**

1. **T3** (unit reads without a walk): open as #192.
2. **T8** (result tables beside the typed tree): waits for nothing.
3. **T9** (the core IR builder reads the syntax tree and tables) waits for
   T8 and S4.9. **S5.6** follows it.
4. **T10, T11, T12** in sequence after T9. The document allows stopping
   after T9.
5. The inventory rows of FRONTEND_REWRITES that are neither expansions nor
   direct yet have no slice. THREE_TREES names their destinations only.

**Derived code.** Slice 2 (records), then 3 (variants), then 4 (remove the
switch), in sequence. Slice 2's first commit is the document's one decision
point: whether `compile_matching` can be called without typed expression
nodes.

**Snapshot.** S6 waits for the product decision of G.7. S7 waits for the
checker's W8 to W10.

## 9. Open questions

Places where the audit suggests a decision in a document may no longer hold.
No document was changed for these.

1. **CHECKER_REDESIGN J.4, W5.** The slice was to be one pull request that
   deletes what it replaces. As merged it adds a third way to build a
   component view (world view, store build, private build) and deletes
   none. The remaining keys ("W5 as built": 103 views on the application)
   decide whether W6 can ever start. Is finishing W5 the next checker task,
   ahead of W8 and C4?
2. **CHECKER_REDESIGN J.6 against "W5 as built".** Whole views cost
   instructions with one worker on both projects. If sharing without a copy
   (W4) does not repay it, is a whole view still the right unit, or should
   a view describe names on first use as B.6 had it?
3. **BACKEND_REDESIGN G.4.** "`Check` mode has been clean on trunk for two
   weeks" gates every deletion. With four deletions in sequence that is two
   months of calendar time in which both backends are built and tested. Is
   the rule still wanted as written?
4. **BACKEND_REDESIGN S1.** The oxc printer over the JS IR is slower than
   the legacy printer and is a product path only until T6. Should it stay
   selectable (`RESCRIPT_JS_PRINTER=oxc`, with its CI jobs) for that time,
   or be kept as a test oracle only?
5. **THREE_TREES T2.** The saving came in under the row's 1%. Patterns,
   core types and module expressions are still rebuilt. Is extending
   expansions to them worth a slice, or does T9 make it moot?
6. **DERIVED_CODECS slice 1.** The general form is still generated for
   every planned item, so the generation and rewrite rows of the savings
   table (0.2% to 0.4% and 0.3% to 0.4% of the application build) are not
   reachable by the
   design as built. Should the savings table be re-derived before slice 2?
7. **CHECKER_REDESIGN H.2.11.** The environment log (4,466 lines with its
   tests) is kept test-only after the switch was dropped. Is it still
   wanted in the tree?
8. **AGENTS.md** names `tests/ERROR_VARIANTS.md`, which does not exist on
   trunk, and says builds write `.cmt` files, which THREE_TREES section 13
   found they do not. Outside this audit's files.

## 10. Corrections made to the design documents with this audit

Statements that no longer held on trunk, each changed by a minimal edit. No
design decision was changed.

| Document | Correction |
| --- | --- |
| CHECKER_REDESIGN.md | The status line points here. J's introduction: #154 is merged, not open. F.1: P1b, P2 and P3 marked as landed with their pull requests. J.4: a line under the slice table naming the merged slices. "W4 as built": the substitution-map seeds were fixed in #205. K.6: C1, C2 and C3 marked as merged |
| BACKEND_REDESIGN.md | The status line: implemented in part, not on the default path |
| BACKEND_LOWERING.md | The status line: which slices are implemented. Section 9, item 9: the tail flags were removed in #198. Item 18: `import_js` exists in `bir/bridge_j.rs` since #167 |
| THREE_TREES.md | The status line: T1, T2 and T7 are implemented. `PRINTER_INSTRUCTIONS.md` is on trunk. Section 3: `RUNS_NO_CODE` is not a flag; the fourth J flag is `J_SUBEXPR`. Section 5: the description of the mapper is of the code before T2. Section 10: S3.4 to S3.9 are merged except loops; #175 merged as a measurement record. Row T7: its end-state check gives one hit, as section 13 explains |
| DERIVED_CODECS.md | The status line: slice 1 is implemented. The fixtures and the buildable `tests/ppx_spice` exist. #194 is merged. The lowering's path is `raw_lambda/convert/derived.rs` (seven mentions), so that slice 2's end-state check names a file that exists |
| RUNTIME_SNAPSHOT.md | S7's dependency names the slices that replaced P5 and P10. The S1 note on watch mode says S5 changed it |
| FRONTEND_REWRITES.md | `ppx::rewrite_jsx_element` and `rewrite_value_binding_without_flattening` no longer exist; the text names the code that does that work now. "Expansions": the four rows T7 made direct no longer get an expansion |

## 11. What could not be verified

- No instruction count, memory figure or timing was measured for this
  audit. Every such number is quoted from a document or a pull request body
  and attributed there.
- Counts on the application (store-built views, lowered units, derived
  bindings) are quoted, not re-run: they need a release build and a check
  build of the application.
- J.2's row "a lookup copy when a value is read through a view" for
  `env_lazy.rs`: whether the two call sites are reached only for local
  module paths needs reading their callers.
- Rules 2, 7 and 8 of I.3.3 have no pattern to search for.
- Whether the fixtures of I.2.3 and I.2.4 are all in the suites was taken
  from #137's body.
- W10 and W11 have no `rg` check in the document; "not started" rests on
  the absence of a pull request and, for W11, on `begin_build` still
  discarding the world.
- Departure 7.1 entry 8, 7.3 entry 5 and 7.4 entries 3 and 4 rest on the
  pull request body or the document's own implementation note.
- `cargo build`, `cargo test` and `cargo doc` were not run: no manifest's
  sources and no doc comment changed.
