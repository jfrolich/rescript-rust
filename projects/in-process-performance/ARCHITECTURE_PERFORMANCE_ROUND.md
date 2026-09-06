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
