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

## 2. BACKEND_REDESIGN.md and BACKEND_LOWERING.md

### 2.1 The ratchet file

`tests/backend_coverage.txt` is what CI compares a check-mode build with
(`scripts/test_backend_coverage.py`, run by the validation workflow). Summed
over its three corpora (the parity fixtures, the runtime library,
`tests/tests`) by a ten-line script over the JSON:

| Stage | Units identical / units | Reasons left |
| --- | --- | --- |
| `lambda-bridge` (S2.2) | 1,438 / 1,438 | none |
| `lambda-norm` (S4.1) | 1,438 / 1,438 | none |
| `lambda-flatten` (S4.2) | 1,438 / 1,438 | none |
| `lambda-exits` (S4.3) | 1,438 / 1,438 | none |
| `lambda-alias` (S4.4) | 1,438 / 1,438 | none |
| `js-bridge` (S3.1a) | 1,325 / 1,325 | none |
| `lower` (S3.3 to S3.9) | 1,290 / 1,438 | `loop` 134, `let rec` 13, `shared Lambda subtree with binder` 1 |

`lower` by corpus: fixtures 519 of 593 (`loop` 74); runtime 103 of 113
(`loop` 10); `tests/tests` 668 of 732 (`loop` 50, `let rec` 13, shared
binder 1). The application is not in the file; #218 reports 3,709 of 3,848
units lowered completely, with `loop` 136 and `let rec` 3 left.

```
$ rg -U -o 'Unsupported\(\s*"[^"]*"' src/bir/lower --glob '!*tests*'   # distinct reasons
"let rec"   (1 site, rec.rs)
"loop"      (3 sites)
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
| S2.2 | Bridges, `BackendMode`, `Unsupported`, the report, the ratchet file, the CI job | `src/bir/bridge.rs`, `enum BackendMode { Legacy (default), New, Check }` in `bir/shadow.rs`; stage `lambda-bridge` 1,438 / 1,438 | done as designed, except what `New` does (6.2) | #129, #184 |
| S3.1 | Emit reads J-level `Bir`; naming on `VarId` | `bir/bridge_j.rs` has `import_js` and `export_js` (stage `js-bridge`); no emitter reads `Bir` on trunk | done in part (the bridge), then **dropped** as a product path by THREE_TREES section 10: the emitter over J-level `Bir` measured +10.23% whole-build instructions on `tests/tests` (`PRINTER_INSTRUCTIONS.md`) and is not on trunk | #167, #175 |
| S3.2 | J normalising rules and rounds J1 to J4 in `bir/j/{norm,inline_return,rest,subst,shake}.rs` | `ls src/bir/j`: `equal.rs facts.rs logic.rs mod.rs norm.rs plain.rs` and tests. No `inline_return`, `rest`, `subst`, `shake` | done in part: the rules (#183). The four rounds are not built and change target to T1 and T4 (THREE_TREES section 10) | #183 |
| S3.3 | Lowering, first set (BACKEND_LOWERING 8.3) | `src/bir/lower/{mod,out,expr,cond,call,args,prim,konst,unit}.rs` exist; stage `lower` | done as designed | #170, #182, #190, #191 |
| S3.4 | `Switch`, `StrSwitch`; removes `"switch"`, `"string switch"` | `switch.rs`, `variant.rs`, `untagged.rs` exist; neither reason is in the code | done as designed | #197 |
| S3.5 | `Catch`, `Exit`; removes `"static catch"` | `exit.rs`; the reason is not in the code | done as designed | #210 |
| S3.6 | `LetRec` of functions; self tail calls | `rec.rs`, `tail.rs` | done as designed | #218, #169 |
| S3.7 | Loops, `Break`, `Continue`, loop labels; `Assign`; `Try`; `LetRec` with value members; removes `"loop"`, `"try"`, `"assign"`, the rest of `"let rec"` | `assign.rs`, `try_.rs` exist; `loops.rs` and `label.rs` do not; `"loop"` at 3 sites, `"let rec"` at 1 | done in part: `Assign`, `Try`, `TryFinally` (#216). Missing: loops and their labels, `LetRec` with value members | #216 |
| S3.8 | Externals; removes `"external"`, `"cross-module inline"` | `external.rs`, `ffi_args.rs`; neither reason is in the code | done as designed | #207 |
| S3.9 | `Pjsx`, `Pimport`, `Pawait`, record copy and rest | `jsx.rs`, `import.rs`, `record.rs`; none of the five reasons is in the code | done as designed | #204 |
| S3.9b | Export extraction and coercion on J-level `Bir`, in `export.rs` | `src/bir/lower/export.rs` does not exist | not started; target changed to the lowering's top-level rows (T4) | - |
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
| T4 | `rg 'apply_js_tailcall_inline_pass\|apply_js_shake_pass' bir/shadow.rs` shows the legacy side only | 0 matches: `shadow.rs` calls neither by name, and `bir/lower/export.rs` does not exist | not started | - |
| T5 | `rg 'fn replay' emit/naming.rs` has one hit | 0 | not started | - |
| T6 | `rg 'JSeq\|JBlockLit' bir/node.rs` is empty; `rg bridge_j .` is empty | 2; 35. `emit/builder.rs` does not exist | not started | - |
| T7 | `rg 'fn transform_await' binary_ast/ppx.rs` is empty | **1**: the function remains for the awaited-module rewrite, its one caller (`create_await_module_expression`) | done as designed for the four node-local rows; the end-state check does not hold, and section 13 of the document says why. Measured in #206: +0.04% on `tests/tests`, +0.05% on the application for rows A to C | #206 |
| T8 | `rg 'struct ExprRow' types/tables.rs` has one hit | `types/tables.rs` does not exist | not started | - |
| T9 | `rg 'typedtree::Expression' raw_lambda` is empty | 0, but the row is not done: `raw_lambda/convert.rs` imports `Expression` in a `use crate::types::typedtree::{...}` list, which the pattern does not match; `bir/build.rs` does not exist | not started | - |
| T10 | `rg 'push_pattern' types` is empty | 36 | not started | - |
| T11 | `rg 'tctx.typed' driver.rs` hits only the tooling functions | 23 hits | not started | - |
| T12 | `rg 'TypedArena' .` is empty | 230 | not started | - |

The tree count today is the six of the document's summary (seven with the
oxc printer): the parse tree, the typed tree, raw Lambda, Lambda, the JS IR,
and the oxc tree when selected. T2 removed the rebuilt parse spine for
expressions; nothing else of the count has changed.
