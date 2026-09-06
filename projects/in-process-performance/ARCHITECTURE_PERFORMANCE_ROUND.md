# Architecture performance round

The user requested a new round of benchmarks, study of the OCaml compiler, web research and willingness to make larger changes. This round starts after the rejected snapshot experiment at `1571f2e4992d22f5666d22e92121f6b0ee042e4d`. Normal compiler/rewatch source and release executables remain D, `5dc38ba2154e158d43436ada2142a13eef9f2c8c`.

## Question

Which larger change removes enough measured work to matter for full-clean parallel builds, while preserving the checked-in OCaml semantics?

The previous five-site change removed logically redundant copying but did not establish a parallel gain. Its serial gain remains recorded. We will not choose another change from clone counts or struct sizes alone. The historical optimized control still beats this branch; recovering that gap and establishing a new best are separate outcomes. The one-second target remains unmet and unproven.

## Work streams

1. **Fresh measurement.** One owner preregisters matched A/D serial and parallel benchmarks, whole-build profiles and any diagnostic instrumentation. It distinguishes actual runtime evidence from logical payload estimates, blocking samples and overlapping costs. Existing verified evidence should be reused where it answers the question already. Normal production source stays unchanged during this phase.
2. **OCaml study.** A read-only reviewer traces the dominant type-checking and Raw lowering work through native allocation, sharing, copying, forcing and mutation contracts. It evaluates larger ownership/storage or traversal changes and identifies the semantic obligations, rather than implementing another local parity compensation.
3. **Public research.** A read-only researcher reads primary compiler-engineering sources and papers on data layout, allocation, repeated work, intermediate representations and parallel scalability. It records URLs, conditions, limits and relevance to this compiler. Published speedups are not forecasts for Tella.

Only the measurement owner may run builds, benchmarks or profilers. Reviewers do not edit the shared worktree or launch heavy processes. Public research must not send private corpus source, paths, artifacts or other organization data to public services. Parent documentation edits stop during frozen benchmark inventories.

## Selection and implementation

Reconcile the three reports before choosing one implementation. Rank opportunities by measured work affected, confidence in causality, semantic risk and required infrastructure. A large refactor is allowed when the evidence supports it. M6 is not resumed automatically, and previously rejected approaches are not reinstated without addressing their recorded failure mechanisms.

The selected implementation gets a fresh bounded owner, exact-head independent review, full default/release tests and parity gates, and preregistered before/after release measurements. Preserve physical identity, captured environments, force/query order, diagnostics, CMJ, source maps and byte-for-byte JavaScript. Do not add unsafe code, global mutable instrumentation, per-node reference counting, serializer normalization or Rust-only force/path heuristics.

Keep the fixed Tella pin and all 18 original modifications. Every measured full build must compile 3248 modules and reproduce the same 5048-file JS digest. Preserve failed attempts and narrowly classify generated outputs. Do not extend samples to resolve an inconvenient interval. Keep raw evidence in organization-controlled durable storage, not public uploads.

The inherited external missing-Belt and standalone JS declaration-order blockers remain explicit. Research eligibility, source equivalence, passing internal gates and production acceptance remain separate decisions.

## Completed research and measurement

See [COMPILER_PERFORMANCE_RESEARCH.md](COMPILER_PERFORMANCE_RESEARCH.md) for the eleven public sources, reading limits and corrected native contracts. Parent checked the actual Lambda-to-Lam stage, the different journal rules for type nodes and mutable cells, Sampson's toy benchmark conditions and Roofline's DRAM definition. Native and public-source reviewers completed their read-only tasks.

Measurement owner `bks-86001e17-97c6-78b7-b1c7-6d0030a78065` completed and released ownership at clean `4ab1a7c29be9ac758d7e673dd252a2d3b81bba60`. [ARCHITECTURE_BENCHMARKS.md](ARCHITECTURE_BENCHMARKS.md) contains the full protocol, data and limitations. Fixed A/D means were 18.265164/19.200754s at project w1 and 4.600557/4.856618s at w12. D lost every pair; the paired parallel gap was 256.06ms with CI [244.54, 267.58]. This is a source-stack comparison, not an optimization result.

The actual copy-function probe counted 9.591M entries, 575403 cache hits and 5.944M outer scopes. Its 416.53ms serial scope time includes instrumentation but excludes cache creation/destruction. It is not a complete instantiation cost or upper bound. Together with the modest instancing sample family, it does not support choosing a map-only rewrite as the principal speed effort. The earlier descriptor census omitted the direct CopyAction payload clones, which this probe measured separately.

Parent independently verified all 178 durable evidence hashes, compact committed summaries, the 52 full-build output checks, raw per-context graph accounting, all 414 restored archive/current source files, immutable controls and ordinary D executables, four exact 12-addition input inventories, 472 runtime hashes and Tella's pin/status/18 original modified-file bytes. Paired row order and statistics were independently recomputed. Parallel sampling severely perturbed execution; header offsets are not exact first-sample coverage measurements. No new benchmark or full-gate run was performed during this verification.

## Selected next hypothesis

Proceed with a bounded **Env/component ownership refactor**, starting with complete lookup/construction lifetime attribution and a native-contract design checkpoint. The Env family has substantial sampled breadth across typechecking and Raw, unlike the narrow copy-function hypothesis. This supports investigating a larger boundary, not a predicted speedup. See [ENV_COMPONENT_OWNERSHIP.md](ENV_COMPONENT_OWNERSHIP.md).

The implementation must remove demonstrated repeated transport/construction work through one compilation-owned component representation, not merely add another cache or rename a signature wrapper. Preserve the mandatory native first-force pass and distinct child/module-declaration/modtype thunks. If the initial accounting shows no material removable work, stop this hypothesis with the evidence rather than force a large patch or switch silently to another task. Otherwise carry it through implementation, independent review, full gates and fixed release timing. M6 remains paused; no backend redesign is selected.

Fresh owner `bks-9b72b0de-396c-7d5f-a662-e90f9799f817` now holds sole compiler/shared-worktree/heavy ownership for this Env hypothesis. The first checkpoint is complete-boundary attribution and the native ownership design. Production activation requires parent acceptance of that checkpoint. The prior measurement and read-only research owners have finished and released their scopes.

## Env checkpoint accepted; implementation scope narrowed

The fixed four-build Env diagnostic completed at `adbca0cc670e07b4817b201df98958c12d0973c6`. Parent independently verified all four process records and identical 5048-file manifests, raw per-context counter and exclusive-time arithmetic, the exact 12 input additions, frozen tracked-source and symlink inventories, Tella's 18 originals/pin/status, unchanged D source and executable hashes. All 8893 final durable evidence hashes and the original 122-file snapshot also verified. These are diagnostic results, not optimization timings.

The probe establishes repeated cached-query transport: 2.228M type queries, 1.871M cache hits, 3.708M wrapper clones and 1.541M counted declaration-container clones. Three disjoint serial scopes measured 754.522ms of wrapper cloning, selected declaration cloning and resolver-local wrapper destruction. This excludes other ownership lifetimes and includes instrumentation. It is neither a removable budget nor a total-cost bound. The broad 5.790s Env union and 2.253s root census cannot predict a gain; the probe added 4.614s to the serial process. Layout's measured Env union was only 39.249ms across its typecheck/Raw work, so this does not explain its earlier full typecheck gap.

Parent approves **candidate implementation of resolution-view and declaration-result ownership**, retaining owner `bks-9b72b0de-396c-7d5f-a662-e90f9799f817`. First settle the two concrete contracts in source and direct tests: which callers inspect versus mutate returned containers, and which loader-view override/hidden/alias-preparation state is independent at each query. Then integrate the tested ownership APIs into actual Ctype, typecore, Env and Raw callers. A helper that still invokes the old clone path is not completion. Preserve required owned copies at mutation/strengthening boundaries and the same captured loader state; avoiding allocation must not publish previously private mutations.

This approval does **not** cover a wholesale component-image or forcing rewrite. Keep the existing component construction/query boundaries and their known debt unchanged in this transport-only candidate. Do not add per-member laziness, deduplicate separate native thunks, combine substitution cleanup scopes, or claim the existing implementation is fully native-aligned. Any need to change those semantics must return to parent review rather than be bundled into an ownership optimization. Required signature views and sparse record storage remain intact.

Proceed with tested code, not another diagnostic cohort or proposal-only pause. Independent review of the complete exact-head candidate, full correctness gates and preregistered fixed release comparisons remain mandatory before retaining it as an optimization. The external missing-Belt and standalone exact-JS-order blockers remain unwaived. There is no speedup forecast or one-second claim.


## Integrated query ownership: reviewed, validation blocked by disk capacity

The candidate is integrated. Independent reviewer `bks-801b182e-f548-7ef9-902c-47a60ae82d2b` found no blocking runtime findings at `57ff05309100737bd034b113668811844f10d8bb` against `8658dbdd67a5129703f80db64e68a2fd0bf359f2`. The additional fallback test needed proof that the original cache contained only `Cycle -> None` before a third TypeContext used it. The reviewer accepted that assertion fix at `9d6a4a0b72f6f69724bb49816853fe77e3089399` and released review ownership. Production code is unchanged by those test additions. Read-only tool restrictions required review of immutable Git objects; parent separately verified the main checkout. Neither review certifies performance or production acceptance.

Release compiler and rewatch builds passed. The first full release library run reported 1295 passed, 50 failed and 108 ignored. After missing native runtime and test/dependency artifacts were built, one registered recovery invocation per unique exact name passed all 48 functional instances across 45 names. Parent matched the original failure multiset, registration, every process record and raw output. No parser benchmark ran during recovery. The original full-suite failure remains recorded. Its parser CSS and index ratios were 1.26 and 1.25 against the unchanged 1.20 limit. Remaining binaries, comptime, documentation and rewatch targets ran once and passed.

Parent checked successful release parity logs: 610 typed trees, 610 raw lambdas, 610 optimized lambdas, 344 focused JavaScript fixtures, 610 JavaScript snapshots and 1431 diagnostic fixtures. The external comparison still fails in OCaml on missing `Belt`, before Rust comparison. The existing standalone TypeArg JavaScript ordering mismatch also remains: D equals the candidate, not OCaml.

The fresh EnvOwnership fixture has exact native/D/candidate JavaScript stdout at 671 bytes and exact typed/raw/optimized stderr at 25728/821/4839 bytes. The first fixture script incorrectly compared both output channels in debug modes; its failure is preserved, and parent verified the intended IR channel directly without normalization or recompilation. Actual native/candidate parser sexp-locs stdout matches at 16454 bytes. Parent executed the saved JavaScript for all three compilers and checked alias identity, captured and shadowed values, and recursive-variant values. These checks do not erase the broader failed gates.

Parent reviewed and authorized deletion of exactly 4474 disposable release-cache files listed in `candidate/disposable-release-cache-inventory.json`, SHA256 `24eef40bca5b6d0c8cec141895c5e2cc3c29d9a397b3a7a69a66fa22c0d74fe9`, under the Env experiment's own cache. Directories, retained executables, source archives, historical evidence and immutable controls were excluded. The owner reports that exact cleanup completed and preserved the retained hashes. The subsequent default compiler build passed, but default rewatch failed with ENOSPC. Default tests have not started. About 131 MiB remained free; compiler profiles and flags were not changed. Build/test launches are stopped.

Read-only capacity inspection found only an additional 810 MiB historical experiment cache, insufficient evidence of enough space to finish the remaining default build and tests. The preserved old worktree's compiler and rewatch target directories occupy about 24 GiB and 3.5 GiB respectively. They remain untouched and outside the cleanup authorization. Further cleanup there requires explicit permission, or the user can provide additional free disk space. The exact remaining build-space requirement is unknown.

The candidate remains experimental and unaccepted. Fixed timing is registered but has not been authorized or run. The implementation owner retains the task while capacity is resolved; M6 remains paused. No one-second or speedup claim is justified.


## User-approved cache cleanup and resumed validation

The user approved removing disposable files from the old worktree's Cargo targets while preserving executables, source and evidence. Under the shared heavy-work lock, parent checked that no compiler/build process was active, inventoried regular non-executable intermediates under the two targets' debug/release `deps` and `incremental` directories, and removed exactly 53302 files. No directories, source files, executable files, dSYM bundles or benchmark evidence were removed. All six top-level executable hashes remained unchanged. Both worktrees' tracked files remained unchanged.

The audit is preserved at `env-ownership/candidate/user-approved-old-cargo-cleanup.json`. Free space after cleanup was 26175324 KiB, about 25 GiB. Logical unlinked sizes include filesystem sharing and are not the reclaimed-space measurement.

The previous worker remained parked and quarantined with a stored disk-full error even after cleanup. Steering it failed twice. Parent assigned continuation of this same task to `bks-a8d0beb6-b792-7038-a6a5-163fb72dcdf0`, now the sole compiler/shared/heavy owner. The old worker must not run concurrently. The replacement starts with a separately recorded default rewatch build recovery, then the unstarted default test targets. It must preserve the original ENOSPC attempt, all failed release/parser/external/TypeArg gates, and unchanged compiler profiles. No completed parser benchmark or full release suite is to be repeated. Timing remains unauthorized pending validation and parent eligibility review.

## Query-ownership default validation complete; eligibility pending

Replacement owner `bks-a8d0beb6-b792-7038-a6a5-163fb72dcdf0` completed only the remaining validation. The separately named default rewatch recovery passed after the approved capacity cleanup, preserving the original ENOSPC attempt. Default compiler library, bins, comptime, docs and rewatch tests then each ran once and passed: 1345/0/108 library, two zero-test bins, 16/0/23 comptime, 9/0/7 docs and 150/0/0 rewatch library. All attempts used unchanged default flags, the existing Env target, the global lock and 600-second per-process bounds.

Fresh preservation checks found 156/156 runtime mirrors equal, 18/18 Tella originals restored at the fixed pin, the old worktree unchanged and the target links still scoped to Env ownership. Durable summary SHA256 is `7cf62e9efae1ff72842e0457f80b6855183be565da46e64ccae80bdf9c681375`. No timing started. Default validation is green, while the original release-library/parser, external and TypeArg gates remain red. The candidate therefore remains experimental pending an explicit parent eligibility decision; no production or one-second claim follows.


## Experimental timing decision after default validation

Parent independently verified the six successful default/recovery process records, raw output hashes, test counts and preserved ENOSPC attempt in the summary committed at `8258bf90bc7e75b6ccd468da37982fbf94f06aeb`. Live checks also verified the 156 source/runtime mirrors, Tella's eighteen originals/pin/status, unchanged old-worktree status, target paths and recorded executable hashes. Compiler and rewatch source still match the reviewed test head.

The preregistered 56-build comparison may proceed as an **experimental measurement**, after executable provenance and the frozen-input runner pass parent preflight. This is not a waiver of the failed release/parser, external-reference or standalone TypeArg gates, and cannot authorize production retention. Default validation, recovered release functional tests, internal parity and independent source review provide enough evidence to measure this candidate against its existing controls without claiming complete compiler correctness. Keep every failed gate visible in the timing report.

One preflight discrepancy remains explicit: the ordinary release bsc hashes to `7f3e605c37473be2d1b172930a21eb95a9b7a2f007ae24cecaca7d52fbd6f1ce`, while the preserved candidate bsc hashes to `88c8a9338abefba9681cc4f4d7d39228a28b47039ee7928ac2f81f9b26b0f4fe`. Parent verified both files; they are not interchangeable without provenance. The owner must establish which build and validation used each artifact and freeze the justified executable pair. Do not overwrite either or rerun parser benchmarks to resolve this.

No full timing attempt is authorized until that preflight is complete and parent explicitly acknowledges the input freeze. The fixed counts, separate historical A comparison, output digest checks and no-extra-run rules remain unchanged. No new diagnostic cohort, compiler redesign or performance forecast is requested.
