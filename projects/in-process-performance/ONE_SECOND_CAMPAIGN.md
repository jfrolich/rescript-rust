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

- M3 implementation session `bks-f4716114-50d4-71a7-9e32-5e376b22b74b` completed and explicitly released compiler/shared-worktree/heavy-test ownership.
- M4 implementation session `bks-bb9d19d9-0007-715b-a420-03bce7fe0492` completed and explicitly released compiler/shared-worktree/heavy-test ownership.
- M5 implementation session `bks-aaf59a2b-a59b-739a-a6ae-af214f2678fb` completed and explicitly released compiler/shared-worktree/heavy-test ownership.
- M6 remains unfinished. Initial owner `bks-72bab2fa-4087-7d0b-9976-74b1ae764ea5` reached its context limit and explicitly released compiler/shared-worktree/heavy-test ownership at `14e0dfa00bd7aee8d3d5ea9c64742cf566b71246`. Continuation owner `bks-8ee24d6d-81b3-7c53-88ea-052bd521c7d3` also reached its context limit and released all ownership at `a70f35b4fff8e2363dcee1a7c2acbca69d67dddc`. Third continuation `bks-d578783b-9948-7bce-979a-eefb8ce0d81a` released ownership without retaining code changes. Re-examining the rejected scratch patch produced no progress. The user has paused further M6 implementation in favor of fresh, thorough measurement. Owner `bks-bfdc9bdf-f2be-7060-8939-c7f191d8f90e` committed a safe pause at `542b505076e73552325566d45116f5d2d9b60024` and explicitly released all compiler/shared-worktree/heavy-test ownership. The parent verified the clean head. Existing release binaries do not represent this pause head; the measurement session must pin and rebuild its selected revisions.
- The indexed pipeline remains inactive. M3's shared primitive-purity helper and M5's identifier flags and legacy generator representation affect active code; their output parity passed. No measured performance gain has been retained in this campaign yet.
- Previous session `bks-4aaf1530-49fa-702d-9ee3-eb34b0afc450` completed and released compiler/heavy-test ownership after rejecting deep-flatten Box/Vec reuse. An intermediate `GroupArena` was also removed because the existing reverse Vec iterator already avoids copying; the wrapper added links and optional entries without removing work.
- Parent owns this campaign file. The implementation session owns its code, tests and focused measurement documentation.

### Fresh measurement priority

The user requested another measurement session to find the largest-impact opportunities using data-driven design. Fresh session `bks-15ec12cd-4569-737e-a07a-c200a134f9b7` completed measurement at `39c5d0077` and explicitly released all ownership with a clean worktree and no running processes. M6's compiler owner remains paused. The report and reproducibility artifacts are in `MEASUREMENT_REBASELINE.md` and `measurement-542/`. The historical 4.5-4.6s result remains the result to beat. No new performance gain has been demonstrated, and inactive M6 checkpoints do not change that.

Reproduce the optimized `fb4497659` baseline and current production source under the same pinned corpus, toolchain, runtime, clean policy and timing boundaries. Measure serial and parallel builds separately. Use immutable saved binaries, preset alternating comparisons, output manifests and explicit uncertainty. Then profile the best reproducible baseline, including phase time, critical path, CPU scaling and allocation/data-layout costs. Rank opportunities by measured headroom and correctness risk, not by ease of implementation or the amount of work already invested in M6. Historical profiles are hypotheses to verify, not new evidence.

M6 remains paused, incomplete and inactive. Its general dispatcher, all-family coverage, grouped integration and final validation are still missing.

Fresh paired results: optimized source A = **19.0288s serial / 4.65115s at 12 workers**; current source B = **20.2044s / 5.00862s**. Eight pairs per mode give B-minus-A **+1.17556s [1.11811, 1.23301] / +0.35748s [0.33007, 0.38489]**. Parent independently recomputed these statistics, verified all 32 paired runs had 3,248 compiled modules and one identical 5,048-file manifest, matched committed raw rows to local originals, verified all four immutable executable hashes/read-only permissions, and checked exact restoration of the 18 pre-existing generated files. This is a same-toolchain source comparison, not a new optimization gain or full compiler acceptance.

Typechecking is the largest measured family (8.095s serial on A). Fresh diagnostics point to map/copy/storage work: 36.9M type-node allocations, 33.2M descriptor clone calls and 80B type arguments, 84.4% unlabeled. Those are allocation/call/layout measurements, not peak live heap or physical memory traffic. Worker tuning produced only a separately confirmed 28ms improvement with more memory. The signature-DAG trace is not a hardware floor.

The next bounded implementation experiment is the existing identity-exact hybrid `TypeExprRefMap` representation on current B, with map length/span/capacity evidence and an isolated comparison. Fresh owner `bks-5f227324-a8e2-75b0-bbb0-f33135ca210e` is the sole compiler/shared-worktree/heavy-test owner for this experiment; measurement owner `bks-15ec12cd-4569-737e-a07a-c200a134f9b7` and M6 owner `bks-bfdc9bdf-f2be-7060-8939-c7f191d8f90e` have released and remain inactive. The whole A/B gap does not establish this map's gain. Recovery toward the old fast stack must not be presented as beating it. Compact hot/cold `TypeArg` storage is the next measured new-speed hypothesis beyond A; its timing benefit is unproven. Do not resume M6 by inertia or silently integrate the historical 70-commit stack.

Hybrid-map candidate `8311daed8a67141e834c92db97d5bff7bea6e166` changes only map storage/tests plus the experiment notes. The preceding B probe (`730dcbf30`) found 214,998 maps with at most eight entries accounting for 8.582GB of summed final dense-vector capacity; this is cumulative capacity across lifetimes, not concurrent heap or memory traffic. Seven focused tests and cargo check passed according to the owner. Independent read-only reviewer `bks-07f65088-608b-7554-adb9-897e55dd0c9a` returned **NO FINDINGS** at exact `8311daed8`, auditing physical-identity keys, bounds/transitions/ownership, current callers and the tests. It was a source-only review, not a test run or performance acceptance. Owner `bks-5f227324-a8e2-75b0-bbb0-f33135ca210e` completed the experiment at clean `414598900488cef127ab96f107622e51e7b8ba12` and explicitly released all ownership. Compiler source remains exactly the reviewed `8311daed8`.

Parent independently verified the fixed 32-run order, original/committed raw rows, all exits and 3,248-module/5,048-JS scope, paired statistics, B/C executable hashes/read-only permissions, Tella pin and exact restoration of the 18 generated-file backups. Matched B/C means were **20.23018 → 20.14258s** at one project worker and **5.03591 → 4.96683s** at twelve. Paired changes were **−87.60ms [−130.56, −44.64] / −69.09ms [−136.86, −1.31]**. One parallel pair regressed; its interval barely excludes zero. No samples were removed or added. This small recovery does not beat or freshly compare against A's 4.65s result.

Parent read the full gate logs: default compiler 1,334 library tests plus both binaries, 16 comptime and 9 doctests passed; release compiler library still failed `benchmark_index` (1.31x versus 1.20x), with the remaining release binary/comptime/doc targets passing when run once separately. Rewatch release 150 passed. Release typed/raw/optimized parity each passed 610, JS passed 344 focused plus 610 snapshots, diagnostics passed 1,431. External OCaml parity remained blocked on `bs-css`'s missing `Belt`. No failure was suppressed or retried into green. The source-only review and small measured gain therefore leave this as an **experimental branch candidate, not a production-accepted optimization**.

The next bounded research step is compact hot/cold `TypeArg` storage, with all label names/locations and physical type references preserved, measured against an immutable current control. Fresh owner `bks-fb2a0e85-f454-79be-9857-52c9cb1ece14` has sole compiler/shared-worktree/heavy-test ownership for that experiment; map owner `bks-5f227324-a8e2-75b0-bbb0-f33135ca210e` has released. It must not claim recovery as a new best result or clear the existing blockers by implication. M6 stays paused.

Initial TypeArg source candidate `c6278e79535d2b672d455b02559a5c0a7249353b` uses a private optional owned label box, borrowed access and the original Debug shape across ten scoped Rust files. Owner reports cargo check and four focused tests passing. Fresh independent read-only reviewer `bks-52275976-2a5c-7d56-abd7-171b46031403` found no semantic/parity defect but raised a P2 performance issue: `subst_type` and `substitute_type_params` allocate and discard cold-label replacements when substitution leaves the type unchanged. Owner fixed both sites in `5dc38ba2154e158d43436ada2142a13eef9f2c8c`, delaying label copies until mapped type handles actually change. The same reviewer confirmed the P2 resolved with no new source-level findings. The changed path temporarily needs an extra small type-handle vector; its net cost remains for measurement, not another speculative change. Existing Rust traversal stays unchanged. The `btype.ml` constructor expression does not by itself prove argument-before-result native evaluation order.

Parent read the preserved initial `c6278e795` default and release logs: both report 1,337 library tests, both binary targets, 16 comptime tests and 9 doctests passing; rewatch release reports 150 passing. The release harness reports `benchmark_index` as passing, but captured passing-test output hides its ratio and potential early-skip message. Parent requested output/provenance evidence from the already-planned final-head run, not an extra retry. These initial results do not validate the review-fix head or prove the old benchmark instability resolved. The final `5dc38ba21` default/release compiler and rewatch runs also passed with those counts. Parent read those logs plus final release typed/raw/optimized parity at 610 each, JS at 344 focused plus 610 snapshots, and diagnostics at 1,431.

### TypeArg result and disposition

Owner completed and released all ownership at clean `b49d3a8ea85c0ced418038bb951d157461557394`. Parent verified compiler/rewatch source unchanged from reviewed `5dc38ba21`, all 32 prescribed rows/order/counts/manifests, original/committed/durable raw-data equality, paired statistics, immutable control/candidate/probe binary hashes, 95 log hashes, all 684 preserved files, 414 restored archived source files and Tella's exact pin/18 original modified-file bytes. Saved inventories differ only by the 12 approved generated outputs during timing; the separate 92 pre-gate differences are classified individually.

| Project workers | Matched control C | Candidate D | Paired D minus C, 95% CI |
|---|---:|---:|---:|
| 1 | 20.040806s | 19.961624s | −79.18ms [−129.53, −28.84] |
| 12 | 4.956757s | 4.907486s | −49.27ms [−93.86, −4.68] |

This is about 0.4% serial and 1.0% parallel in this fixed cohort. Two parallel pairs regressed, and the separate serial screening favored the control. No samples were added or excluded. Mean peak RSS rose by 1.18MB serial and 13.90MB parallel. Smaller retained argument payload did not translate into lower whole-process memory. The parallel interval narrowly excludes zero, so generalization confidence remains limited. There was no fresh A comparison, and this does not beat the historical 4.5–4.6s result or establish a path to one second.

The standalone fixture's original seven-pass claim was invalid: its JS mode compared empty stderr instead of generated JavaScript. Parent identified the output-preservation problem. Correcting it exposed a real OCaml/Rust declaration-order difference. One untimed immutable-control check produced byte-identical C and D JavaScript, so the difference predates TypeArg. Parent independently checked the three outputs and their exact diff. Runtime assertions pass, but exact JS parity remains red. Original false-pass evidence and both failed harness corrections remain preserved; no output normalization, compiler change or timing repetition hid the failure.

**Disposition: keep TypeArg only as a reviewed, measured experimental branch candidate.** Full acceptance remains blocked by that preexisting standalone JS mismatch and external OCaml Tella compilation's missing `Belt`. The passing release harness does not prove the historical parser benchmark instability fixed. No merge or production-release acceptance follows.

See [TYPE_ARG_STORAGE_EXPERIMENT.md](TYPE_ARG_STORAGE_EXPERIMENT.md) and `type-arg-5dc38/` for the complete evidence. Private raw copies are under `/Users/jake/.opensession/artifacts/rescript-performance-20260905/type-arg/`. No TypeArg owner remains active. Further measurement should target the much larger descriptor-copy work before another representation is chosen; no further optimization is authorized by this result alone.

Descriptor attribution owner `bks-6cfd619b-e1ae-704f-9bc7-adf03b873edf` completed at clean `818cab324a5737e0161220d941053ad754cfeeff` and released all ownership. No production source changed. Parent verified the four fixed diagnostic builds and two separately registered full-duration profile builds, full output scope, raw counter totals, original/committed/durable diagnostic rows, all 489 preserved artifact hashes, all 414 restored archived files, exact input differences and Tella's original 18 modified-file bytes. D binaries remain read-only and hash-identical; separate probe binaries match recorded hashes but are writable, not immutable controls. Parent corrected an overly broad read-only assertion during verification without changing any artifacts or rerunning measurements.

The serial census counted **36,304,460 `get_desc` requests**, 3,485,228,160 logical inline bytes and 489,020,525 nested requested bytes. Parallel counted 36,289,530 requests and 488,480,578 nested bytes; the small scheduling/cache-dependent difference remains unattributed and the modes are not pooled. The probe added about 23% wall time in each single diagnostic comparison, not a performance gain or statistical estimate. Sample wrapper durations include symbol processing, and worker samples include blocking. Neither those times nor inclusive sample families establish snapshot CPU cost or bandwidth saturation.

The largest audited short-borrow-safe group is five sites: `typecore.rs:9868/9898/9918`, `ctype.rs:8533/9925` in D. Together they request 2,371,770 snapshots with 89,310,173 nested requested bytes, 18.26% of this census's nested volume. Parent inspected the source: these are tag checks or snapshots immediately copied into the actual owned result. The owned argument/handle vectors must remain, and every descriptor guard must end before allocation, instancing, expansion, unification or other Env/Ctype operations. Mutation-heavy unification, prefix rewriting and rollback still require saved payload and are outside this first experiment. A descriptor arena is not justified by these counts alone.

See [DESCRIPTOR_SNAPSHOT_ATTRIBUTION.md](DESCRIPTOR_SNAPSHOT_ATTRIBUTION.md) and `descriptor-snapshots-5dc38/`. The attribution goal is complete, not a new performance result. Fresh owner `bks-a6d8d8ba-711d-7981-b177-2be13b15413d` has sole compiler/shared-worktree/heavy ownership for the next bounded candidate. It will test only those five short projections against immutable D, with a separate preregistered parallel A comparison to distinguish an isolated gain from a new best. The plan is eight D/E pairs per project-worker mode plus eight separate A/E parallel pairs, without selecting sample counts from results. No speedup is assumed.

Projection candidate `08c884be8412d44d4ca32ef76a8792febeae35e8` received a fresh **NO FINDINGS** source-only review from `bks-ef2a1650-88bc-7b3b-b6aa-21d761dea55a`. Parent verified the clean head and scoped diff. All five guards end before mutation or recursive calls; necessary owned vectors, short-circuiting and the later substitution snapshot remain. Owner reports cargo check and five focused tests passing. The reviewer checked the final test expectations against the existing contracts; the modeled typecore projection test still needs the standalone fixture and full gates for actual production coverage. Test-development failures remain recorded. Source is frozen while final validation and the two fixed timing comparisons proceed; no new parity or speed claim follows from review. M6 stays paused and all existing exact-output acceptance blockers remain.

Raw binaries, logs, manifests and backups from both measurements were preserved locally under `/Users/jake/.opensession/artifacts/rescript-performance-20260905/{measurement-542,hybrid-map-8311}` (202 and 138 files respectively), with per-file SHA-256 inventories. Disposable source/build directories were not copied. These organization-controlled copies avoid depending solely on `/tmp`; nothing was uploaded to a public host.

### Completed inactive indexed foundation, M1

Accepted and pushed at `56ad852fc494922b0287c7cb36910ce1c40f81da`. The implementation adds compact indexed storage, lossless compatibility conversion and a real indexed collect/arity pass. The production optimizer and JS consumer do not use it yet. [INDEXED_LAMBDA.md](INDEXED_LAMBDA.md) records the remaining migration.

Parent review caught incorrect nested-module arity fallthrough; the port and regression tests were fixed. Independent reviewer `bks-0f56b06f-4673-7701-9f08-97ac1dab5c5a` accepted the exact final head with no remaining findings after additional cache-miss, control-flow and function-retention tests. Order checks against a separate traversal model are documented separately from actual metadata/arity/resolver differential tests.

Validation:

- Focused debug tests: 13 passed.
- Full debug compiler tests: 1,209 passed, 108 ignored. Comptime: 16 passed, 23 ignored. Doctests: 9 passed, 7 ignored.
- Release compiler build passed at implementation head `24eb1273b`; the later delta contains only tests and documentation. This is not a release test run or an exact-final-head binary claim.
- Release bsc SHA-256: `03d16966a528a15db169ab37b950ae40a801385093256b789f11afe88ba8a436`.
- Logs: `/tmp/indexed-m1-final-head-validation.log`, `/tmp/indexed-m1-low-findings-focused.log`, `/tmp/indexed-m1-low-findings-full.log`. The parent checked logs and the binary hash; the read-only reviewer inspected source but could not access these external logs.

No full parity, Tella or timing result is claimed for this inactive milestone. Its immutable metadata borrow and incomplete reference behavior were addressed during M2 below. Production integration still requires the contiguous passes and consumer, full correctness gates and measured performance.

### Completed inactive indexed exits, M2

Accepted at `981542736860551bbab78c1ed69e6f43112e9c1f`. An owning context now keeps the arena, canonical root and metadata together. Indexed exit counting, substitution and simplification operate on that store without recursive Lambda conversion. The context exposes no public pass taking a caller-supplied raw node ID.

Independent reviews rejected the intermediate implementations. Fixes cover unsupported switch constants, wrapper eta reduction, no-catch traversal, constructor truthiness/comparison, integer-tag switches and payload accounting. The final review also removed the old Rust function-retention compensation: indexed collection retains every bound function as OCaml does. Substitution always traverses, including an empty map, and resets transformed-JSX metadata; direct exit simplification preserves it. Tests distinguish these reference behaviors from known debt in the unchanged recursive Rust helpers rather than normalizing away differences.

Reviewer `bks-b2aa52a4-ccb0-7f38-bd42-3206710a2648` accepted the exact final head with no remaining findings. Parent verification confirmed:

- Full default debug tests: 1,222 compiler tests passed, 108 ignored; comptime 16 passed, 23 ignored; doctests 9 passed, 7 ignored.
- Focused indexed exits: 12 passed. Indexed collect: 9 passed.
- Release compiler build passed. bsc SHA-256: `f050628eac5108c83c34948fcc3da56ad473941a50de91912b213cd28d4eba9f`. The executable hash stayed unchanged across these inactive-code fixes; the build logs record recompilation.
- Logs: `/tmp/indexed-m2-review2-full-tests.log`, `/tmp/indexed-m2-review2-release-build.log`, `/tmp/indexed-m2-review2-exits.log`, `/tmp/indexed-m2-review2-collect.log`.

Retention measurements partition shallow payload storage into current-root live, metadata-retained-only and unreachable storage, counting shared payloads once. A test-only observer measures temporary substitution-table root reachability. Neither is a total deep-heap or total peak-memory measurement. Repeated rewrites can retain superseded generations; lower wall time has not been established.

This acceptance is limited to inactive M2. It does not establish release-test, full parity, Tella or performance acceptance. The production optimizer, driver and JS consumer remain unchanged.

### Completed inactive indexed alias/beta/deep-flatten, M3

Accepted at `d7af23efdf7a40f53220882f3c7fa1b80afa8a68`. Shared indexed constructors and substitution support real deep flatten, beta reduction, alias simplification and their analysis queries in one owning context. Every pass uses the caller's pipeline-wide identifier generator. External CMJ Lambda import remains an explicit compatibility boundary.

Reviewer `bks-dbfe3094-1852-7075-89fa-956776c91056` rejected the intermediate boxed-nullable identity compensation, incomplete tests and wrong inlining predicate order. All three findings were closed at the final head. Earlier parent review also corrected randomized unused-argument ordering and a duplicate size analysis that omitted logical sparse fields. The implementation now reproduces native `Hash_ident` hashing, bucket traversal, resizing and retained capacity, including failed beta attempts. Native OCaml reference vectors cover initial, resized and repeated calls.

Parent verification at the accepted clean head confirmed:

- Full default debug compiler tests: 1,245 passed, 108 ignored. Comptime: 16 passed, 23 ignored. Doctests: 9 passed, 7 ignored. Focused indexed tests: 49 passed.
- Release compiler and rewatch builds passed. These were builds, not release test runs.
- Release non-external output parity: optimized Lambda 610/610; JavaScript fixtures 344/344 and snapshots 610/610; diagnostics 1,431/1,431.
- Release bsc SHA-256: `8cb1673e5ab0d0f2ef95085e025cec57d54cb3756d88018285c557dc3ae51968`.
- Release rewatch SHA-256: `592e4e5fe1e9b02f5f09173c01b646dd40e3470fff15944cf993b0efe2c252cd`.
- Logs: `/tmp/indexed-m3-rereview-full-tests.log`, `/tmp/indexed-m3-rereview-release-compiler-build.log`, `/tmp/indexed-m3-rereview-release-rewatch-build.log`, `/tmp/indexed-m3-review-fixes-focused.log`, `/tmp/indexed-m3-final-optimized-lambda-parity.log`, `/tmp/indexed-m3-final-js-parity.log`, `/tmp/indexed-m3-final-diagnostic-parity.log`.

The reviewer audited source without running builds or tests. Parent verification checked logs, hashes and Git state. This accepts inactive M3 and the behavior-preserving active purity-helper extraction, not production integration or a performance gain. No external Tella parity or timing was run. The historical external OCaml `bs-css`/`Belt` blocker remains unresolved.

Coverage is not exhaustive. Debug-tree comparisons cover the exercised fields, but custom `Ident::Debug` omits some identifier flags. Remaining test gaps include in-range `Na`, allocating-constant and unknown-record field fallbacks, external-specific async/directive/arity rejection, and separate null/undefined `NormalOptional` cases. These did not expose source mismatches in review. Substitution-table peak assertions remain partial reachability checks, not total peak-heap measurements.

### Completed inactive indexed alpha/lets, M4

Accepted at `79453b29b355784ace2b50b6a86c018c51704ba8`. Indexed alpha conversion, eta expansion, occurrence counting, reference elimination and let simplification now operate in the owning store. Count and lets share the context-retained native beta hash capacity. The one-store test covers the contiguous indexed passes with the same caller-provided identifier generator and includes metadata-retained storage.

Parent review found incorrect eta identifier allocation and a broader traversal-order mismatch. The final implementation follows each OCaml boundary separately. Eta's fold-right callback allocates right-to-left, while its binding list remains in source order. Native constructor arguments can evaluate right-to-left; explicit `let` and list-map boundaries retain their reference order. A linked OCaml alpha oracle confirmed sibling freshening: from frontier 1002, the second under-application received identifiers 1003/1004, then the first received 1005/1006. Tests also cover application, letrec, list-map and switch-record boundaries. Count preserves its explicit source-order traversal and the invalid both-full switch assertion.

Reviewer `bks-39ccf69c-9858-7134-bdc9-b38b87d0a4e0` audited every branch in the four new passes and accepted the exact clean head with no remaining findings. Parent verification confirmed:

- Full default debug compiler tests: 1,277 passed, 108 ignored. Comptime: 16 passed, 23 ignored. Doctests: 9 passed, 7 ignored.
- The all-indexed checkpoint passed 75 tests before the final alpha boundary additions. The later focused alpha suite passed 12 tests; the final full default suite includes those additions.
- Exact-head release compiler build passed. This was not a release test run.
- Release bsc SHA-256: `beeeaf11f8a67eba11b222a09ceb053c7740f645062bd0e1e27194cf16ff92ae`.
- Logs: `/tmp/indexed-m4-full-default-tests.log`, `/tmp/indexed-m4-release-compiler-build.log`, `/tmp/indexed-m4-order-focused.log`, `/tmp/indexed-m4-alpha-boundaries.log`.
- Executed native oracle source and output: `/tmp/indexed-m4-ocaml-alpha-oracle.ml` and `/tmp/indexed-m4-ocaml-alpha-oracle.log`. The initial `utop` attempt failed because its library was unavailable; the linked executable supplied the evidence. Temporary repository source and Dune changes were removed.

The reviewer inspected source and the oracle without running builds or tests. The tests are not exhaustive over every leaf combination or identifier flag. This accepts inactive M4 only. No new release-test, output-parity, Tella-manifest or timing result is claimed. The production optimizer and JS consumer still use recursive Lambda; M5 and M6 remain necessary before activation and performance validation.

### Completed inactive indexed exports and ownership, M5

Accepted at `2ace324d1c229fedfc4e7907d07745bab61ba132`. The candidate runs the contiguous optimizer sequence in one store, then retains grouped/export/CMJ roots in an owning pre-JS result. A sealed Raw-Lambda producer carries the same compilation-wide identifier generator through conversion, lowering, optimization, coercion and the later-consumer boundary. Grouping consumes the optional optimizer root, including for empty output. No group RHS stands in for the whole program.

Reviewer `bks-e555ec17-d5fe-7670-82fa-b7b1e57eb530` rejected intermediate revisions and found no remaining source issues at the accepted head. Fixes distinguish full-flag `Set_ident` free variables from identity-based `Hash_set_ident` visited membership, preserve JS/object flags, and retain exact hoisted collision locations. A lightweight warning sink delivers warnings in source order, including before a later error, without enabling debug-only per-pass materialization. The sealed producer path honors caller warning configuration. Fatal warnings remain pending until an explicit post-JS/dependency, pre-effect/CMJ gate that M6 must invoke. Optional debug captures use established Lambda/group representations and the reference pass labels; direct indexed sexp printing remains available.

Parent verification confirmed the clean head, final logs and binary hashes:

- Full default debug compiler tests: 1,307 passed, 108 ignored. Both binary test targets passed with zero tests. Comptime: 16 passed, 23 ignored. Doctests: 9 passed, 7 ignored.
- An earlier full run failed `small_untagged_object_value_switches_keep_ocaml_runtime_guards` with a temporary-identifier mismatch. The owner reported an isolated pass; the parent verified the final full default rerun passed. No unrelated fix was made. This does not establish that the intermittent failure is resolved.
- Exact-head release compiler and rewatch builds passed. These were not release test suites.
- Release non-external parity: typedtree 610/610, raw Lambda 610/610, optimized Lambda 610/610, focused JS 344/344, JS snapshots 610/610, diagnostics 1,431/1,431.
- Release bsc SHA-256: `d1c1d47ddc12587c27cee54ec960a9a84954cc1eafe5e8b6ab8d7eeab9265069`.
- Release rewatch SHA-256: `63725c768a9365f30808cb0d57b48b774467306aae09672f76087f33779ef96f`.
- Logs: `/tmp/indexed-m5-final-clean-full-default-tests.log`, `/tmp/indexed-m5-final-head-release-compiler-build.log`, `/tmp/indexed-m5-final-head-release-rewatch-build.log`, and `/tmp/indexed-m5-final-release-{typedtree-parity,raw-lambda-parity,optimized-lambda-parity,js-parity,diagnostic-parity}.log`.

The reviewer inspected source only. These parity runs validate the still-recursive production path and active helper changes, not the inactive indexed pipeline end to end. M5 acceptance does not establish release-test, external Tella, manifest or timing results. The owner released all compiler/shared-worktree/heavy-test ownership. M6 must port the JS consumer without a final recursive-tree conversion before activation can be considered.

### Unfinished M6 checkpoint and continuation

Checkpoint `14e0dfa00bd7aee8d3d5ea9c64742cf566b71246` adds borrowed recursive/indexed cursors and child/binding/case adapters. It also corrects the JS compiler's generator storage to `Owned(IdGenerator) | Shared(Arc<IdGenerator>)`. Legacy constructors remain stack-owned; the indexed constructor accepts the real shared stream without creating a dummy generator first. Parent verification found a passing cargo check and two filtered allocator tests in `/tmp/indexed-m6-cursor-check.log` and `/tmp/indexed-m6-allocator-tests.log`. These are not full M6 validation or acceptance. The remote branch already contains this checkpoint; that does not imply acceptance. The owner reports no push invocation, and the parent has not established which external actor advanced the remote.

The full common consumer refactor is not implemented. The initial owner released a clean worktree after unsuccessful partial attempts. `/tmp/indexed-m6-common-consumer-wave2.patch` is reference material only, not a patch to apply wholesale: it includes prohibited indexed-argument materialization during CMJ beta and incomplete control-flow APIs.

The continuation must solve consumer-side CMJ beta with mutable access to the owning indexed context. Inspect an application through a short-lived view, release the borrow, resolve and import the CMJ body at the actual query boundary into the same store, then run indexed beta/substitution with argument IDs and the same generator. Do not preload CMJs, skip inlining or materialize indexed call arguments. Immutable cursors remain useful for read-only helpers but cannot by themselves support this mutation boundary.

The second continuation committed the narrow mutable CMJ mechanism in `1aafdbd3a` and query preparation in `1dc615ca5`, with limitations documented in `a70f35b4f`. `prepare_indexed_external_field_apply` is not yet called by an indexed consumer, and its `Reduced(NodeId)` is not yet compiled directly. One mechanism test still materializes the reduced root before old-consumer compilation. This test-only check does not meet the requested direct indexed-consumption criterion. No full or release validation was reported for these checkpoints.

Remaining work covers the actual expression, return/effect/assignment, recursive-binding, catch/raise, loop, switch, primitive/external and metadata traversal APIs. Then compile grouped roots directly, run JS passes and dependency resolution, invoke the delayed fatal-warning gate before effect/CMJ work, and test the sealed producer-to-JS path. No unsupported-family fallback or final conversion to the recursive consumer is acceptable.

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
