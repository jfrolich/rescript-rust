# Ralph Loop: Typechecker Performance

You are improving **Rust typechecker performance** while preserving compiler
behavior. The primary repro is `tests/tests/src/Import.res`.

## First Read

Before doing anything else, read:

- [PLAN.md](./PLAN.md)
- [RALPH_TODO.md](./RALPH_TODO.md)
- [RALPH_SETUP.md](./RALPH_SETUP.md)
- [CORPUS_BASELINE.md](./CORPUS_BASELINE.md)
- [IMPORT_RES_PERFORMANCE_HANDOFF.md](./IMPORT_RES_PERFORMANCE_HANDOFF.md)

## Main Objective

Make Rust behave more like OCaml in module-signature-heavy typing paths:

- make the lazy qualified module-components path the architectural backbone
- reuse cached qualified module views
- stop rebuilding fresh whole-signature copies for repeated lookups
- preserve sharing during substitution work
- implement the proper lazy/module-components shape rather than a bandaid cache

Then use the canonical 657-file benchmark to confirm the change improves the
broader corpus instead of only the single-file `Import.res` repro.

## First Task

Before doing more profiling passes or local optimizations, implement
`env_lazy` properly across the hot typechecker/module-resolution paths. Treat
that infrastructure change as the first required task for this project.

Specifically:

- route the real hot lookup paths through `env_lazy` instead of bypassing it
- make `env_lazy` the default/source-of-truth path in `ctype.rs`,
  `typecore.rs`, and the shared module-resolution helpers they depend on
- only profile to confirm the impact of that work or to debug what still
  bypasses it

Do not spend cycles on random small fixes before this lands. The expected
largest impact is making the OCaml-shaped lazy environment machinery real
everywhere it matters.

## Implementation Principle

Do not start by trying to invent a Rust-specific performance improvement. For
this effort, look closely at what OCaml actually does and implement the same
algorithm, forcing behavior, sharing model, and lookup structure in Rust.

Working assumption:

- if Rust stops doing extra work and follows the OCaml algorithm closely, the
  large performance gap should collapse without needing random clever fixes
- when in doubt, spend more time reading the OCaml path instead of guessing at
  a new optimization
- the target is algorithmic equivalence first, speedup second

## Rules

1. Do not add `Import.res`-specific hacks.
2. Do not weaken typing semantics to get speed.
3. Do not optimize the small unpack-retyping path first; fix the main
   signature-copy problem first.
4. Before changing Rust behavior, read the relevant OCaml code and align with it.
5. Do not treat profiling as the first task. Use it to validate or focus the
   `env_lazy` rollout, not to justify unrelated tweaks.
6. Measure before and after every change.
7. Always measure canonical typedtree parity for this project. Do not rely only
   on a focused `Import` parity slice before keeping a change.
8. Do not begin by searching for a novel performance trick. First match the
   OCaml algorithm and lazy forcing behavior as directly as possible.
9. Do not accept a speedup that regresses typedtree parity.
10. Do not accept an endpoint that is still slower than OCaml.
11. Prefer the OCaml lazy-components design over local memoization bandaids.

## Workflow

1. Check `git status --short` first.
2. If there is unfinished local work on this project, finish it first.
3. Reproduce the exact `Import.res` timing baseline.
4. Reproduce the canonical corpus baseline if it is missing or stale.
5. Read the OCaml and Rust files named in the handoff documents, with special
   focus on the `EnvLazy`/`components_of_module_maker` path.
6. Derive the implementation plan from the OCaml code path first; do not invent
   a different algorithm unless the OCaml shape has already been matched.
7. Implement the `env_lazy` infrastructure change first across the real hot
   paths before attempting smaller optimizations.
8. Re-run the exact timing repro.
9. Re-run the canonical corpus benchmark or a justified focused slice.
10. Run the canonical typedtree parity suite and any focused correctness checks
   needed for diagnosis.
11. Update `RALPH_TODO.md` with concrete new timing data.
12. Commit the result.

## Priority Order

1. implement `env_lazy` properly everywhere it matters and make the lazy
   qualified module-components path the source of truth
2. match the OCaml algorithm/forcing order/data sharing for that path as
   directly as possible
3. make `ctype` and `typecore` both use that path end-to-end
4. cache fully qualified access-path views, not just raw signatures
5. preserve sharing inside substituted type graphs
6. only then clean up secondary costs or revisit profiler-guided residuals

## Success Condition

The project is complete when:

- all planned optimization work for this project is complete
- `Import.res` is at least `2x` faster than OCaml on the same machine
- the canonical 657-file benchmark shows aggregate Rust time at or below
  `0.50x` aggregate OCaml time
- Rust no longer uses multi-GB memory for the file
- the profiler is no longer dominated by repeated
  `copy_lookup_signature_for_subst` / `copy_lookup_type_expr`

If all tasks are complete, output exactly:

```text
RALPH_COMPLETE
```
