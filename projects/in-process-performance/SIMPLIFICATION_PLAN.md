# Compiler simplification and performance plan

## Starting point

Keep main untouched and work on the existing feature branch and jfrolich/rescript-rust#20. Commit `1c02247de` undoes the rejected rollback on this branch. Compiler and Rewatch source again match main `d98b8b943`; no new optimization is implemented yet. The identifier-freshness fix stays intact.

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
