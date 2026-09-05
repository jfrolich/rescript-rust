# Correct one-second Tella clean builds

## Objective and acceptance

Continue implementation and measurement toward a reproducible <=1s clean parallel build of the full pinned Tella webapp. This is a target, not a demonstrated feasible bound. Measure single-worker builds separately. Do not replace clean builds with incremental or precompiled application-output benchmarks.

- Tella: `66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa`.
- Target: `/Users/jake/dev/tella-fusion/packages/core/webapp`.
- Historical complete output scope: 3,248 compiled modules and 5,048 generated `.js` files under webapp, excluding `node_modules`. Verify counts and content, not counts alone.
- Fix the compiler revision, binary hashes, source runtime, machine, build flags and worker counts for each comparison.
- Keep release typedtree, raw/optimized Lambda, JavaScript, diagnostics, compiler and rewatch tests correct. Compare complete base/candidate Tella output manifests. Report unavailable external-reference gates explicitly.
- Preserve type identity, mutation isolation, identifier allocation, declaration cleanup, component force order, diagnostics and output. Storage changes must not introduce another typechecker algorithm.

## Current branch and historical baseline

This campaign runs on shared branch `can-you-do-a-torough-look`, initially `a023e8adc`. Do not switch branches, reset, rebase, stash, cherry-pick, or replace sibling work. Use the existing branch PR and never merge a PR without specific user permission.

The previously profiled optimized stack is `fb4497659`, 70 commits ahead of `a023e8adc`. It is NOT the current implementation baseline. A read-only comparison found optimized `compiler-rust/src/lambda` and `rewatch/src/build/compile.rs` unchanged across that range; `raw_lambda/matching.rs` differs substantially. New optimized-Lambda work can start here without reproducing the match-action DAG optimization. Benchmark the actual current branch before each candidate. Do not claim its result is cumulative with an unintegrated sibling stack.

Historical profile: `/tmp/tella-profile-fb4497659/REPORT.md`. Temporary artifacts can disappear; the figures below preserve the useful conclusions.

| Historical mode | Wall mean | SD | User CPU | Peak RSS, single separate run |
| --- | ---: | ---: | ---: | ---: |
| 1 worker | 18.688s | 0.212s | 17.799s | 2.083GB |
| 12 workers | 4.615s | 0.033s | 39.068s | 2.913GB |

The later eight alternating worker-count pairs superseded earlier noisy batches. Retired instructions were about 240B in both modes; measured IPC was 3.134 at one worker and 1.787 at twelve. This supports investigating memory traffic and contention, but is not proof of bandwidth saturation. Heterogeneous cores, frequency, scheduling and preemption also require consideration.

A one-worker instrumented run attributed 6.066s to Lambda/lowering, Lambda optimization and codegen combined. Typecheck was 8.746s. Portable internalization cost 715.9ms and later signature/component copies cost 650.8ms, totaling 1.367s serial. Their 12-worker aggregate thread time was 3.268s, NOT serial CPU or reclaimable wall time. Those operations allocated 26.35M local type nodes; required identities cannot simply be deleted.

The observed parse/dependency barrier was 0.33s at twelve workers; post-barrier idle-slot wait was only 13.5ms. Runtime precompile was about 52ms parallel wall. Only 225 of the 3,248 modules were dependency-package modules. A package cache alone is not a plausible path to one second.

## Analysis and sequence

Reaching one second from the historical 4.615s requires about 78% less elapsed time. The prior proposed backend, signature-storage and pipeline savings do not establish that outcome, and their ceilings overlap. Do not add projected gains or equate aggregate thread time divided by worker count with a hard wall-time bound.

1. Measure full-tree optimized-Lambda passes and implement an indexed-arena ownership refactor where reconstruction is expensive. Preserve OCaml pass/traversal order. Avoid converting back to recursive trees between every pass.
2. Reprofile after the first retained slice. Consider compact type-node/payload storage and flat portable graph images before speculative lazy materialization. Any lazy approach must reproduce the actual OCaml Env/Ctype boundary, not defer required allocations or force effects opportunistically.
3. Evaluate per-module frontend/dependency/signature pipelining if its measured overlap ceiling still justifies the complexity. It principally targets parallel time, not serial work.
4. Reassess the critical path and scaling after every retained change. Large refactors are authorized; unrelated micro-optimizations and repeatedly rejected scheduler policies are not the plan.

External design references provide mechanisms, not transferable speedups:

- Roc typed indices and split storage: https://github.com/roc-lang/roc/blob/main/src/collections/safe_list.zig
- OXC compilation-unit arena ownership: https://github.com/oxc-project/oxc/blob/main/ARCHITECTURE.md
- rustc worker-local state and parallel queries: https://rustc-dev-guide.rust-lang.org/parallel-rustc.html
- rustc external metadata queries: https://rustc-dev-guide.rust-lang.org/query.html

## Execution discipline

Serialize all heavy builds, profiling, tests and benchmarks with:

```sh
/usr/bin/lockf -k /tmp/rescript-tella-heavy.lock /bin/bash -lc '<command>'
```

Never remove the lock or delete directories with `rm -rf`. Inspect and preserve pre-existing generated Tella modifications individually.

Save instrumentation-free exact binaries. Profile separately from timing. Use hyperfine and high-resolution alternating paired comparisons at one and twelve workers; fix sample counts before inspecting significance. Report mean, standard deviation, range, paired uncertainty, user/system time, RSS and corpus verification. Do not extend runs until a confidence interval excludes zero. If further testing is justified, define a separate confirmation experiment and report its results independently.

Each implementation task gets a fresh session. Only one task owns heavy testing or compiler edits at a time. Commit meaningful changes atomically with DCO sign-off. Require fresh exact-head correctness review and full validation before retaining/pushing performance claims. Verified OCaml-aligned correctness work must not be silently undone to improve a local score.

## Active work

- Implementation session: `bks-a6a8bd41-ce05-7988-af5b-765ebd313f05`.
- Task: M2, an owning arena/metadata context with safe split borrows, followed by indexed exit counting, substitution and exit simplification.
- Status: started after M1's owner explicitly released compiler/heavy-test ownership. Production remains unchanged. No performance change has been retained in this campaign yet.
- Previous session `bks-4aaf1530-49fa-702d-9ee3-eb34b0afc450` completed and released compiler/heavy-test ownership after rejecting deep-flatten Box/Vec reuse. An intermediate `GroupArena` was also removed because the existing reverse Vec iterator already avoids copying; the wrapper added links and optional entries without removing work.
- Parent owns this campaign file. The implementation session owns its code, tests and focused measurement documentation.

### Completed inactive indexed foundation, M1

Accepted and pushed at `56ad852fc494922b0287c7cb36910ce1c40f81da`. The implementation adds compact indexed storage, lossless compatibility conversion and a real indexed collect/arity pass. The production optimizer and JS consumer do not use it yet. [INDEXED_LAMBDA.md](INDEXED_LAMBDA.md) records the remaining migration.

Parent review caught incorrect nested-module arity fallthrough; the port and regression tests were fixed. Independent reviewer `bks-0f56b06f-4673-7701-9f08-97ac1dab5c5a` accepted the exact final head with no remaining findings after additional cache-miss, control-flow and function-retention tests. Order checks against a separate traversal model are documented separately from actual metadata/arity/resolver differential tests.

Validation:

- Focused debug tests: 13 passed.
- Full debug compiler tests: 1,209 passed, 108 ignored. Comptime: 16 passed, 23 ignored. Doctests: 9 passed, 7 ignored.
- Release compiler build passed at implementation head `24eb1273b`; the later delta contains only tests and documentation. This is not a release test run or an exact-final-head binary claim.
- Release bsc SHA-256: `03d16966a528a15db169ab37b950ae40a801385093256b789f11afe88ba8a436`.
- Logs: `/tmp/indexed-m1-final-head-validation.log`, `/tmp/indexed-m1-low-findings-focused.log`, `/tmp/indexed-m1-low-findings-full.log`. The parent checked logs and the binary hash; the read-only reviewer inspected source but could not access these external logs.

No full parity, Tella or timing result is claimed for this inactive milestone. M2 must resolve the immutable arena borrow in metadata, keep handles paired with their owning store, and quantify live versus superseded nodes and payloads. Production integration still requires the contiguous passes and consumer, full correctness gates and measured performance.

### Rejected deep-flatten trial

Artifacts: `/tmp/tella-lambda-arena-a023e8adc/`. The release base is `636fe1965`, whose compiler/rewatch source matches `a023e8adc`. The saved base binary SHA-256 values are `4b68d9fbbc0f40d052399bc1a10903701235d3cb431bb270ef9c4120142e479d` for bsc and `95c919fc8745ac69dd920b5e1e04eb5336fc5c3c7da98abee8d0ac1e41eb5a55` for rewatch. The fixed runtime is this campaign worktree's `packages/@rescript/runtime`.

Instrumented serial pass totals were deep flatten 358ms, alias simplification 338ms, metadata collection 238ms, exit simplification 196ms, alpha conversion 188ms and let simplification 146ms. These are aggregate pass timings across the build, not independent wall-time savings. They also do not cover the entire backend. The original logs' `output_nodes` fields used an inlining-size heuristic and are invalid as node counts; exclude them. Temporary instrumentation has been removed from the candidate source.

Five-run hyperfine screening with cleanup outside timing gave:

| Mode | Base mean / SD | Candidate mean / SD |
| --- | ---: | ---: |
| 1 worker | 19.989s / 0.185s | 20.092s / 0.096s |
| 12 workers | 5.078s / 0.160s | 5.047s / 0.108s |

These separate screening batches did not establish a gain. The earlier 23.172s / 5.294s screening timed cleanup plus compilation and is not comparable with build-only results. The completed authoritative experiment instead used eight alternating pairs per worker count, `perf_counter_ns` wall time, and cleanup/hashing outside the interval.

| Mode | Base mean / SD | Candidate mean / SD | Paired delta, 95% t interval |
| --- | ---: | ---: | ---: |
| 1 worker | 20.1791s / 0.0186s | 20.2691s / 0.0511s | +90.0ms, +42.4 to +137.7ms |
| 12 workers | 5.0029s / 0.0320s | 5.0245s / 0.0338s | +21.6ms, -19.4 to +62.6ms |

All 32 builds reported 3,248 compiled modules and matching 5,048-file JavaScript manifests. Full CPU/RSS/range data is in [SCRATCHPAD.md](SCRATCHPAD.md#rejected-deep-flatten-ownership-reuse-a023e8adc-compiler-source), committed in `526f2ef0f` with follow-up wording in `12bb54e07`. Independent artifact review confirmed the rejection, and the parent separately reproduced the CSV statistics and binary hashes. Compiler source and release target binaries were restored to the exact base. Full compiler/parity/diagnostic gates were not run for this rejected candidate; output hashes alone are not full correctness acceptance.

The result rejects this specific candidate. It does not establish that all within-pass allocation reuse fails, or that cross-pass indices will improve performance. The next indexed representation is still a hypothesis requiring full integration, correctness validation and measurement.

Continue after each completed task with the next evidence-supported task. Stop claiming progress when only proposals exist. If one second remains beyond measured headroom, say so while reporting actual retained improvements.
