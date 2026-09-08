# Module lifecycle and artifact handoff investigation

## Scope

This investigation covers one boundary in the full-clean in-process build: the lifetime of one module from Rewatch dispatch through compiler return, signature publication, pre-JS handoff, JavaScript metadata publication, output writing, and completion. It will attribute work outside the named compiler phase timers and determine which part, if any, extends the observed parallel dependency tail.

It does not change compiler semantics or scheduling policy. It does not assume the 4.237-second serial phase gap is destruction, I/O, locking, allocation, or removable work. It also does not treat idle slots as proof of a scheduler bug.

## Current ownership and release order

For a `.res` module without an interface, `compile_preprocessed_structure_in_process_until_js` saves and finalizes the inferred signature, serializes its portable graph, and calls the signature-ready hook before GenType, Raw Lambda conversion, Lambda lowering, required-module collection, and function-return cleanup. Rewatch receives that artifact, applies its registry update, and inserts newly unblocked dependents into the ready heap. This matches the save-before-translation order in `compiler/ml/typemod.ml:1768-1788` and `compiler/ml/translmod.ml:267`.

Signature send makes the artifact available, but later work can still delay dependent execution by occupying workers or by reaching the coordinator ahead of the signature message. The diagnostic must therefore distinguish worker send, coordinator receive, registry apply, dependent ready insertion, dispatch, and dependent worker start.

At the JavaScript boundary, the driver constructs the backend program and checks module paths before calling the metadata-ready hook. The worker sends that metadata before rendering, explicit JS-program disposal, file writes, and completion. The coordinator may receive and apply the message while rendering is underway or after it finishes. Backend dependents become ready at metadata apply, so separate send, receive, apply, render, and dispatch timestamps are required. The persistent raw/component split remains unchanged and follows `compiler/ml/env.ml:669-678`, `compiler/ml/env.ml:1513-1530`, and `compiler/ml/env.ml:1949-1977`. Required-module semantics remain those of `compiler/core/lam_convert.ml:358-479` and `compiler/core/lam_compile_main.ml:278,409-418`.

Interfaces, runtime bootstrap modules, namespace artifacts, no-hook calls, and fallback publication paths need explicit records. The dependency analysis must not infer a missing release edge.

## Diagnostic

Prepare one archive-only instrumented compiler and Rewatch pair. Run exactly two fresh Tella slots in order: w1, then w12. A failure or partial artifact in either slot stops the cohort. There are no retries, replacements, extensions, or old-root replays.

Instrumentation uses one build-owned monotonic epoch passed into worker hooks and messages. It adds coarse per-module timestamps and durations only. It adds no global or thread-local state, no per-node timers, and no extra whole-tree traversal.

Pre-JS records will cover:

- coordinator dispatch and worker start;
- Rewatch setup before the driver call;
- driver setup, typecheck wall interval, signature preparation, raw-signature copy, current-signature finalization, portable extraction, hook send, post-signature work, Raw conversion, Raw-to-Lambda lowering, and the existing lowered-Lambda required-module traversal;
- signature send, coordinator receive, registry apply, dependent ready insertion, dependent dispatch, and worker start;
- the returned driver's in-body elapsed time and the enclosing Rewatch call elapsed time;
- Rewatch required-module derivation, pre-JS message send, coordinator receive, and JS dispatch/start.

The difference between enclosing driver-call elapsed and returned in-body elapsed will be named `unclassified_call_residual`. It is not an exact destruction timer. It includes call entry/return, result construction, instrumentation, and implicit local drops. Instrumentation will not move drops or result-field construction to isolate this value.

JavaScript records will cover Rewatch setup, driver persistent-environment setup, JS compile, path checks, metadata-hook send, rendering plus explicit nonrecursive JS disposal, driver body/call elapsed, fallback publication if used, write, post-build, completion send, coordinator receive, and registry apply. The existing Lambda-optimization phase delta is nested inside JS compile and will never be added to it.

Only O(1) sizes already available from owners may be recorded, such as type arena length, signature length, portable graph length, output count, and required-module set length. A count naturally produced by an existing traversal is acceptable. The probe will not walk Lambda or another graph solely to count nodes.

## Reconciliation and dependency analysis

For every module, sequential child intervals must fit within their enclosing call interval. Nested named phase times remain annotations, not additive siblings. The analyzer will reject negative residuals, impossible timestamp order, missing release classification, duplicate terminal events, and child sums larger than their registered parent apart from a stated clock-resolution tolerance.

The serial report will reconcile module lifecycle intervals with the global timing window without adding overlapping pre-JS, JS, and named phase totals. The parallel report will keep summed worker intervals separate from elapsed build time.

Critical-path analysis will use actual signature dependency edges and the recorded `needed_modules` metadata edges. It will replay the observed release and dispatch rules. For each dependent it will separate artifact wait, coordinator handling, ready-queue delay, and worker-start delay. Removing a measured owner is worth considering only if the replay shows that owner lies on the w12 tail and its serial or parallel budget is large enough to justify a coherent refactor.

## Implementation gate

No production change follows from raw counts or inclusive samples. A candidate needs evidence for hundreds of milliseconds of parallel elapsed time or seconds of serial work, and it must remove actual work or state rather than shift it across a timer.

Any proposed compiler change must preserve physical `TypeExprRef` sharing and cycles, identifier allocation and traversal order, captured Env/substitution/force boundaries, signature and metadata publication order, diagnostics, CMI/CMJ/GenType artifacts, source maps, and JavaScript bytes. Full portable/raw/renamed/GenType signature fusion remains vetoed. No unsafe code, per-node reference counting, structural interning, path-spelling equivalence, serializer normalization, sorting, force suppression, or swallowed errors is allowed.

If the lifecycle diagnostic disproves a high-impact removable owner, the investigation stops without a micro-optimization fallback.
