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
