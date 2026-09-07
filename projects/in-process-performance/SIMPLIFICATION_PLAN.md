# Compiler simplification and performance plan

## Starting point

Keep main untouched and work on the existing feature branch and jfrolich/rescript-rust#20. Commit `1c02247de` undoes the rejected rollback on this branch. At that restoration checkpoint, compiler and Rewatch source matched main `d98b8b943`; the selected implementation and its later validation are recorded below. The identifier-freshness fix stays intact.

The latest fixed comparison measured main at 4.7759s parallel and 20.2464s serial. Rolling back the three storage/ownership changes was slower in every pair. Historical A is a separate branch, not evidence that main regressed. Existing reports and failed attempts remain intact.

## 1. Read-only structural audit

Review the active compiler and full-clean build pipeline in bounded waves, covering scheduling and driver lifetimes, parsing/arenas, binary AST and PPX, CMI/portable signatures, lazy Env queries, type graphs, context ownership, expression/module typing, Raw matching/conversion, Lambda optimization, JavaScript emission, GenType and diagnostics. The canonical coverage report stays outside the checkout under the organization-controlled `simplify-and-speed/audit-report.md` artifact.

For each subsystem, retain at most two findings that remove work or state concepts, not merely relocate branches or reduce line count. Require exact source and native-reference evidence, an explicit current/proposed ownership model, migration scope, risks, tests, and the runtime measurements needed to establish materiality. Record skips and rejected ideas. Independently check coverage, duplication, abstraction cost and priority ranking before selecting the implementation.

## 2. Fresh tracing of the measured main implementation

Use the already-preserved coherent main release pair, not newly rebuilt ordinary target files. First preregister separate diagnostic runs: phase/module/runtime/scheduler timings at w1 and w12; existing compiler counters at w1 only; process sampling at w1 and w12. Existing global/TLS instrumentation may be used as-is; do not introduce new mutable global/TLS probes. Counters and sampling are separate so their perturbation is visible.

Every diagnostic gets exact commands, binary/source hashes, owned-process bounds, compiler PID and sampler coverage where applicable, fresh input inventories, output hashes, and protected-file restoration. Preserve all failures. Reuse the fixed Tella source pin, 3,248 project modules, 107 freshly compiled runtime modules, and required 5,048-file JavaScript digest. Keep a single heavy owner under the shared lock. Do not upload private code, logs or traces.

Treat aggregate thread time, inclusive stack samples and logical copied bytes as different quantities. Never add overlapping timings, call waiting samples CPU work, or turn allocation-size estimates into a speedup forecast. Trace unmeasured setup/drop/I/O when phase totals leave a material gap. The old profiling reports provide leads, not current-main attribution.

## 3. Evidence-backed implementation design

Publish the ranked findings and a concrete implementation plan before changing compiler behavior or representation. Select one coherent high-impact root cause whose fix both simplifies the organizing model and removes measured work. State which structures, caches, scans, copies, states or passes disappear. Prefer an ownership/traversal refactor over another layer of conditional caches. Larger refactors are allowed; inactive M6 work is not resumed automatically.

Map every semantic obligation to the OCaml reference: physical type identity, captured Env and forcing order, substitution/journal scopes, identifier allocation, raw conversion effects, diagnostics and output. No new unsafe code, per-node reference counting, path/name heuristics, serializer normalization or mode-dependent semantics.

## 4. Implement and validate

Implement the selected design on this branch in coherent signed commits, with tests at each changed layer. Keep one source/heavy owner and independent exact-head review. Rebuild and validate release artifacts, typedtree/raw/optimized Lambda, JavaScript and error parity; use targeted syntax, GenType or source-map checks as required by the change. Preserve existing red-gate history rather than retrying benchmarks into green.

Preregister a fresh before/after release comparison with matched inputs and output verification, parallel performance primary and serial reported separately. Require fewer architectural concepts or less duplicated state/work as well as a credible runtime benefit. Reject a slower or inconclusive performance candidate rather than pushing it to main. A verified native correctness fix is evaluated separately and never hidden by a performance rollback.

Update the existing PR with the design, implementation, correctness evidence and measured outcome. Do not merge without explicit user authorization. The one-second target remains a goal, not a promise from an unmeasured refactor.


## Evidence checkpoint and final selection gate

The source audit now covers 17 bounded review/reconciliation areas, including active bootstrap and Lambda helpers found by fresh coverage review. Three independent checking passes validated coverage/schema, ownership/native semantics and materiality/ranking. Full reports, 27 conditional/deferred/correctness entries and the acceptance matrix remain in organization-controlled `simplify-and-speed` artifacts.

All five current-main diagnostics completed once with the required output. Serial observations are typecheck 8.402s, Raw/Lambda 2.535s, optimization 1.451s, parse 1.983s and 4.237s outside the phase timers. Parallel values are thread sums and sampling is late-biased. The prominent signature-copy family was checked against real ownership: portable, raw, freshened, GenType and publication views have simultaneous native users. Their logical copy counts do not authorize fusion/elision.

The first implementation shortlist is S02-1 unused position-content index removal; S10-1 producer-owned exports replacing Raw rediscovery; S07-2 single identifier owner replacing reconciliation-only state/scans. Before choosing, run exactly one targeted non-sampling serial release diagnostic in an instrumented archive. Count position-map operations and deterministic sampled map self-time without extrapolating it into a budget. Exactly time whole export/identifier reconciliation scans and visited nodes by module. Preserve allocation, force, output and input contracts; no new mutable global/TLS probe state.

Choose one directly removable cost after migration risk. If export/identity scans are material, introduce the producer artifact first and migrate identity ownership only under its own proof. If those scans are negligible, remove the proven unused parser index first and judge its release effect by a fixed before/after comparison. No further broad profiling round, cache layering, or speculative unsafe representation rewrite is planned.

Larger Env, copy-window, Parmatch and artifact-lifecycle designs remain a documented roadmap with strict prerequisites. They are not folded into this first implementation. Inclusion's depth-success cutoff and discarded arbitrary PPX output remain separate correctness investigations. No performance result closes those limitations. Main is untouched; implementation stays on this branch and PR.


## Selected implementation: remove the unused position index

The single targeted release diagnostic completed with the required 3,248 project modules, 107 runtime modules and exact 5,048-file output. Its sealed preregistration is `7b8cbf6e2da918d7e5f2fe318b0e536f1453e668c52fdf01eaaa4d8749cf77ae`. The parent independently checked source and binary hashes, input preservation, output manifests and the 18 protected originals. Evidence is in the organization-controlled `simplify-and-speed/removable-work` artifacts.

Across project and runtime compilation, the probe observed:

| Mechanism | Work observed | Instrumented time |
|---|---:|---:|
| Position-content index | 7,287,211 writes, 4,330,455 insertions, 2,956,756 existing-key writes | 7.188 ms across 121,967 sampled operations only |
| Raw export rediscovery | 2,025,747 visited nodes | 24.371 ms |
| Five identifier-reconciliation scans | 11,318,345 visited nodes | 66.675 ms |

The sampled position time is not extrapolated. Tree timings include counters, and none of these values predicts the eventual clean-build improvement. The index maintained 6,255,731 capacity slots cumulatively across arenas, not simultaneously live memory. Export and identifier scans do not justify the larger ownership migrations as the first performance change.

S02-1 is selected because every position-content index write maintains state with no repository consumer. The implementation deletes `PosKey`, `ParseArena.position_dedup`, its initialization and writes, and the unused `get_position_idx` / `push_position_dedup` methods. The experimental Rust library exposes these methods publicly, so their removal is an explicit Rust API change. Repository search does not establish that no external client exists. ReScript syntax and CLI behavior are unchanged.

`push_position` will still record the filename and append exactly one fresh arena entry. `push_pos`, `PosIdx` reuse, position/location ordering, string identity and serialization remain unchanged. This follows the reference propagation in `compiler/syntax/src/res_parser.ml:65-95` and its lookahead restoration at `165-198`; content equality does not replace physical sharing.

Add a regression test for equal-content `push_position` calls, mixed insertion APIs, stable sequential indices, shared position handles in locations, and filename preservation. Then build normal release compiler/Rewatch artifacts with no probe fields, run affected parser and full compiler parity gates, and preserve the exact candidate binaries. Finally preregister a fresh fixed main/candidate comparison with parallel and serial results separate. Existing failed gates remain disclosed. The change is a candidate until correctness and performance validation finish; the one-second target remains unmet.


The selected map removal and identity regression test are implemented. The focused release test passed, with 1 test run and 1,454 filtered out. The first test launch failed before Cargo started because the non-login PATH omitted Cargo; the corrected launch and both logs are retained in `position-index-validation`. Exact-head release validation at `eba0277be` is complete: core gates passed, while syntax and legacy AST0 remain red and external native validation is blocked. The fresh comparison stopped at its initial clean/input-preservation gate, before any qualification or timed build. See [POSITION_INDEX_VALIDATION.md](POSITION_INDEX_VALIDATION.md) for the results, control provenance loss, and failed-freeze evidence. No performance acceptance is claimed.


## Completed fixed comparison

The user-authorized second comparison completed all 32 timed builds with exact JavaScript output. Independent audit found a 1.08% parallel improvement, 4.829113s to 4.777105s, and a 1.84% serial improvement, 19.680941s to 19.318480s. Paired 95% intervals exclude zero in both modes. See [POSITION_INDEX_PERFORMANCE.md](POSITION_INDEX_PERFORMANCE.md) for the full statistics, original stopped cohort, qualification timestamp-repair amendment and retained correctness limitations. Main remains untouched; the one-second target is unmet. The next task is a trace-backed type-checker performance investigation, not another broad audit or automatic signature-copy fusion.
