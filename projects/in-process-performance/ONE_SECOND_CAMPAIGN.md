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

- Implementation session: `bks-4aaf1530-49fa-702d-9ee3-eb34b0afc450`.
- Task: establish current-branch release baselines and per-pass evidence; implement and validate one substantial optimized-Lambda arena slice.
- Status: started; no new measured gain yet.
- Parent owns this campaign file. The implementation session owns its code, tests and focused measurement documentation.

Continue after each completed task with the next evidence-supported task. Stop claiming progress when only proposals exist. If one second remains beyond measured headroom, say so while reporting actual retained improvements.
