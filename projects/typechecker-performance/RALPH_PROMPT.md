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

- reuse cached qualified module views
- stop rebuilding fresh whole-signature copies for repeated lookups
- preserve sharing during substitution work
- implement the proper lazy/module-components shape rather than a bandaid cache

Then use the canonical 657-file benchmark to confirm the change improves the
broader corpus instead of only the single-file `Import.res` repro.

## Rules

1. Do not add `Import.res`-specific hacks.
2. Do not weaken typing semantics to get speed.
3. Do not optimize the small unpack-retyping path first; fix the main
   signature-copy problem first.
4. Before changing Rust behavior, read the relevant OCaml code and align with it.
5. Measure before and after every change.
6. Do not accept a speedup that regresses typedtree parity.
7. Do not accept an endpoint that is still slower than OCaml.
8. Prefer the OCaml lazy-components design over local memoization bandaids.

## Workflow

1. Check `git status --short` first.
2. If there is unfinished local work on this project, finish it first.
3. Reproduce the exact `Import.res` timing baseline.
4. Reproduce the canonical corpus baseline if it is missing or stale.
5. Read the OCaml and Rust files named in the handoff documents.
6. Implement one focused change.
7. Re-run the exact timing repro.
8. Re-run the canonical corpus benchmark or a justified focused slice.
9. Run correctness checks.
10. Update `RALPH_TODO.md` with concrete new timing data.
11. Commit the result.

## Priority Order

1. unify the qualified module-signature resolution path
2. make `ctype` reuse cached qualified signatures/components
3. move the design toward OCaml's lazy `components_of_module_maker` structure
4. only then clean up secondary costs

## Success Condition

The project is complete when:

- `Import.res` matches or beats OCaml on the same machine
- Rust is no slower than OCaml on every comparable canonical file
- Rust no longer uses multi-GB memory for the file
- the profiler is no longer dominated by repeated
  `copy_lookup_signature_for_subst` / `copy_lookup_type_expr`

If all tasks are complete, output exactly:

```text
RALPH_COMPLETE
```
