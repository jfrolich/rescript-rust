# Module lifecycle and artifact handoff investigation

## Scope

This investigation covers one boundary in the full-clean in-process build: module work from Rewatch dispatch through compiler return, signature publication, pre-JS handoff, JavaScript metadata publication, output writing, and completion. It measures work outside named compiler phase timers and determines which observed artifact boundary, if any, extends the parallel dependency tail. It is not a whole-AST lifetime or last-owner study.

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

The difference between enclosing driver-call elapsed and returned in-body elapsed will be named `unclassified_call_residual`. It is not an exact destruction timer. It includes call entry/return, result construction, instrumentation, and implicit drops of call-local owners. Instrumentation will not move drops or result-field construction to isolate this value. Rewatch's stored-AST snapshot clones a map of `Arc` values; dropping that snapshot does not drop the `ParseArena` values still retained by `BuildCommandState`. Registry snapshots likewise are not established last owners. Those retained lifetimes and later build teardown are outside this window and remain unattributed. The moved lifecycle event/DAG buffers are explicitly dropped and timed after their post-compile flush. Concretely, `rewatch/src/build/build_types.rs:153-156` stores each parsed payload behind `Arc`, `BuildCommandState.stored_asts` owns the persistent table at `build_types.rs:233`, and `snapshot_stored_asts` clones that table at `build_types.rs:538-540`; the compile-local clone is created at `rewatch/src/build/compile.rs:1130`. The build API returns `BuildCommandState` from `rewatch/src/build.rs`, so the probe does not observe its last-owner teardown.

JavaScript records will cover Rewatch setup, driver persistent-environment setup, JS compile, path checks, metadata-hook send, rendering plus explicit nonrecursive JS disposal, driver body/call elapsed, fallback publication if used, write, post-build, completion send, coordinator receive, and registry apply. The existing Lambda-optimization phase delta is nested inside JS compile and will never be added to it.

Only O(1) sizes already available from owners may be recorded, such as type arena length, signature length, portable graph length, output count, and required-module set length. A count naturally produced by an existing traversal is acceptable. The probe will not walk Lambda or another graph solely to count nodes.

## Reconciliation and dependency analysis

For every module, non-overlapping child intervals must fit within their enclosing body interval with no tolerance. Nested named phase times remain annotations, not additive siblings. The analyzer rejects every negative numeric duration, impossible timestamp order, malformed/unknown/duplicate/missing fields or records, incomplete module sets, missing release/readiness classification, and child sums larger than their registered parent.

The serial report will reconcile module lifecycle intervals with the global timing window without adding overlapping pre-JS, JS, and named phase totals. The parallel report will keep summed worker intervals separate from elapsed build time.

Artifact-chain analysis uses actual signature dependency edges, recorded `needed_modules` metadata edges, and explicit scheduler-visible readiness batch endpoints. For each work item it separates ready-to-dispatch delay from dispatch-to-worker-start delay and reconstructs only the observed artifact-release blocker chain. It does not replay owner removal, model CPU/resource capacity, or claim a speedup. Source follow-up is warranted only for an observed budget of hundreds of milliseconds on the parallel artifact tail or seconds in serial aggregate; any production candidate still requires separate C/N benchmarking.

## Implementation gate

No production change follows from raw counts or inclusive samples. A candidate needs evidence for hundreds of milliseconds of parallel elapsed time or seconds of serial work, and it must remove actual work or state rather than shift it across a timer.

Any proposed compiler change must preserve physical `TypeExprRef` sharing and cycles, identifier allocation and traversal order, captured Env/substitution/force boundaries, signature and metadata publication order, diagnostics, CMI/CMJ/GenType artifacts, source maps, and JavaScript bytes. Full portable/raw/renamed/GenType signature fusion remains vetoed. No unsafe code, per-node reference counting, structural interning, path-spelling equivalence, serializer normalization, sorting, force suppression, or swallowed errors is allowed.

If the lifecycle diagnostic disproves a high-impact removable owner, the investigation stops without a micro-optimization fallback.

## Completed diagnostic disposition

The single admitted w1→w12 cohort completed successfully and is permanently closed. Both resulting 5,048-file JavaScript manifests were byte-identical, and the independent process/input/output/restoration audit passed. The complete measured and source-only disposition is archived at `lifecycle-handoff-diagnostic/LIFECYCLE_SOURCE_DISPOSITION.md`; raw audit and metric records are `provenance/parent-postrun-audit.json` and `provenance/parent-lifecycle-metrics.json`.

The result rejects outer compile-return teardown and coordinator registry apply as large targets: compile-return residual was 0.129/0.267 ms, while signature receive-to-apply totaled 2.984/16.887 ms. It finds substantial but non-causal post-publication occupancy: signature-send→pre-JS-send totaled 4.144/12.342 worker-s. The unclassified per-module call residual totaled 1.012/3.614 worker-s and was associated with type volume, but mixes entry, result construction, return mechanics, and several local owners; it is not a contiguous post-body or destruction interval. `write_ns=0` was unmeasured because `RESCRIPT_MODULE_TIMINGS` was unset, not evidence of no I/O.

Source inspection identifies one plausible material representation mismatch but no safe local change. Rust creates a per-module `TypeContext` (`compiler-rust/src/driver.rs:15052`) whose `TypeArena` owns `TypeExpr` values and whose descriptors own variable-length payloads (`compiler-rust/src/types/context.rs:44-76,244-330`; `compiler-rust/src/types/type_expr.rs:53-59,160-239`). Normal return drops unmoved `typed_structure`, `final_env`, `Env`, `TypeCheckContext`, and finally `TypeContext`; the body timestamp is taken before later metric reads, return-field construction, and `source_file_names()` cloning (archived `source/probe/compiler-rust/src/driver.rs:15407-15445`; production return construction is at `compiler-rust/src/driver.rs:15337-15353`). Native type records are GC-managed (`compiler/ml/types.ml:22-58`; `compiler/ml/btype.ml:46-49`) and have no equivalent deterministic per-module destructor boundary. The residual cannot isolate `TypeContext` from the other owners.

No production change is retained. A future investigation may evaluate safe context-owned indexed/range storage for common `TypeDesc` payloads, preserving physical identity, mutation, sharing, traversal and force order. It must not leak or suppress drops, defer cleanup, share mutable schemes, introduce `unsafe`, or substitute a scheduler workaround. Inline-container alternatives need measured enum sizes rather than assumptions about layout. Any proposed representation change requires separate parity gates and preregistered C/N benchmarks.
