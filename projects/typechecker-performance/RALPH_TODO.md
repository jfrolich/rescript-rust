# Ralph TODO: Typechecker Performance

**Last Updated:** 2026-04-14
**Status:** env_lazy dotted module/module-type lookup checkpoint landed; broader perf gap still open

## Goal

Make Rust at least as fast as OCaml on the canonical recursive
`tests/tests/src/**/*.res` corpus (`657` files), starting with the
module-signature-heavy `tests/tests/src/Import.res` cliff and moving the design
closer to OCaml's lazy module-components model.

## Baseline

Authoritative `Import.res` timing repro from this worktree on `2026-04-13`:

- OCaml: `0.04s` (`/usr/bin/time -lp`)
- Rust: `8.93s` (`/usr/bin/time -lp`)
- Rust max RSS: about `3.30GB`
- Rust peak footprint: about `9.40GB`

Authoritative canonical-corpus benchmark from this worktree on `2026-04-13`:

- Files tested: `657`
- Comparable files: `657`
- Rust faster or equal: `2`
- Rust slower: `655`
- Materially slower: `253`
- OCaml failures: `0`
- Rust failures: `0`
- Aggregate OCaml total: `5491.7ms`
- Aggregate Rust total: `25029.1ms`
- Aggregate Rust / OCaml ratio: `4.56x`

Detailed corpus baseline:

- [CORPUS_BASELINE.md](./CORPUS_BASELINE.md)

## Current Understanding

- The main cost is not JS emission.
- The dominant root cause is repeated deep-copy and path-rewrite of module
  signatures and nested type graphs.
- The main architectural fix is OCaml's lazy `EnvLazy` /
  `components_of_module_maker` path. Rust already has partial pieces of this,
  but the hot `ctype` path still bypasses them and falls back to eager whole-
  signature copying.
- The previous `31` "OCaml failures" were a benchmark bug, not real OCaml
  failures: the harness flattened temp output basenames in a way that broke
  interface `.cmi` lookup for every `.resi`-backed module.
- The hottest Rust functions are:
  - `copy_lookup_signature_for_subst`
  - `copy_lookup_type_expr`
  - `resolve_type_item_through_env`
  - `resolve_module_signature_for_path`
- This module-signature cliff is not limited to `Import.res`; it also appears in
  `global_module_alias_test.res`, `module_alias_test.res`, `test_include.res`,
  Belt collection tests, JSX-heavy files, and `mario_game.res`.
- There is at least one additional nontrivial cluster in deep pattern matching
  (`gpr_1150.res`), but it should be investigated after the main module-view
  cliff is fixed so the residual signal is cleaner.
- The next agent should not spend time on profiling detours or random local
  fixes before completing the `env_lazy` infrastructure rollout through the hot
  lookup paths. That rollout is the highest-impact task.
- The next agent should not begin from "find a performance improvement." It
  should begin from "match the OCaml algorithm and lazy forcing behavior more
  exactly." The expectation is that removing Rust-only extra work is the real
  win.

## Rejected Prototype

- Attempted change: cache the path-qualified module signature produced for
  `ctype::resolve_type_item_through_env` instead of rebuilding it on every
  lookup.
- Best observed `Import.res` timing during the prototype: Rust `1.56s`
  (`/usr/bin/time -lp`) with about `575MB` max RSS and about `548MB` peak
  footprint. A slightly earlier version measured Rust `2.38s` to `4.07s`
  depending on the cache variant.
- Why it was rejected: typedtree parity regressed on exactly these files:
  `Import.res`, `ImportAttributes.res`, `DynamicImportModuleWithAlias.res`,
  `stdlib/Stdlib_ImportTests.res`.
- Parity symptom: the diffs were dominated by identifier/stamp drift in the
  import-heavy path, which means the cache shape still does not match OCaml's
  lazy forcing behavior closely enough.
- Outcome: prototype reverted. Keep the measurements, but do not keep the code.

Detailed investigation:

- [IMPORT_RES_PERFORMANCE_HANDOFF.md](./IMPORT_RES_PERFORMANCE_HANDOFF.md)
- [CORPUS_BASELINE.md](./CORPUS_BASELINE.md)

## Current Checkpoint

Checkpoint measurements from this worktree after routing dotted
module/module-type/type lookups through cached qualified module components on
`2026-04-14`:

- Full typedtree parity: Rust `657 passed`, OCaml `657 passed`, parity
  `232/657`, `43117` hunk mismatches
- Focused import parity: `1/4` files match, `283` hunk mismatches
- Authoritative `Import.res` repro:
  - OCaml: `0.05s` (`/usr/bin/time -lp`)
  - Rust: `0.34s` (`/usr/bin/time -lp`)
  - Rust max RSS: about `73MB`
  - Rust peak footprint: about `58MB`
- Authoritative canonical corpus benchmark:
  - Files tested: `657`
  - Comparable files: `656`
  - Rust faster or equal: `1`
  - Rust slower: `655`
  - Materially slower: `231`
  - Rust failures: `1` (`src/ticker.res`: stack overflow)
  - Aggregate OCaml total: `4761.9ms`
  - Aggregate Rust total: `11277.8ms`
  - Aggregate Rust / OCaml ratio: `2.37x`

What landed in this checkpoint:

- `build_module_signature_for_path` no longer clones and scans a fresh parent
  signature just to resolve `Pdot` child modules; it now reads the child module
  directly from cached `QualifiedModuleComponents`
- `ctype::resolve_module_type_through_env_path` now uses the cached qualified
  parent components as the source of truth for dotted module/module-type lookup,
  while preserving the required parent-child substitution step for functor and
  other non-signature child module types
- `ctype::resolve_type_item_through_env` now reads the target `SigType`
  directly from cached qualified components instead of resolving and scanning a
  copied whole signature
- `typemod::lookup_module_path_by_lid`, `lookup_modtype_path_by_lid`, and
  `lookup_module_type_by_lid` now route dotted lookups through the same cached
  qualified components path instead of rebuilding parent signatures for each
  child lookup
- the intermediate functor regression in `defunctor_make_test.res` was fixed by
  keeping child module-type substitution against the cached parent qualified
  signature slice rather than dropping that step entirely

What this means:

- the qualified module-components path is now carrying dotted module,
  module-type, and type lookup work in both `ctype` and `typemod`, not only
  dotted value lookup
- `Import.res` improved from the prior `0.65s` / `536MB` checkpoint to `0.34s`
  / `73MB`, which is the strongest sign so far that moving child lookups onto
  the OCaml-shaped lazy path is the right direction
- the broader corpus also improved from `11795.0ms` (`2.60x`) to `11277.8ms`
  (`2.37x`), and the `Import.res` entry in the benchmark dropped from `30.40x`
  slower than OCaml earlier in this worktree to `7.74x`
- parity stayed effectively flat at the checkpoint level, which means the new
  speedup did not require a new serializer workaround or an import-specific
  hack
- the next session should keep pushing allocation-sharing improvements through
  the same cached qualified view and then re-profile the residual clusters
  (`mario_game`, JSX-heavy files, `gpr_1150`, and the `ticker.res` stack
  overflow)

## Task List

- [ ] Keep `scripts/benchmark_typechecker_performance.py` authoritative for the
  canonical recursive 657-file corpus
- [ ] Implement `env_lazy` properly everywhere it matters before doing more
  profiling or secondary optimizations
- [ ] Read the OCaml path closely enough to copy the same algorithm, forcing
  order, and sharing model before attempting alternative optimizations
- [ ] Make the lazy qualified module-components path the real source of truth,
  not a side path that `ctype` bypasses
- [x] Add a shared path-qualified module-signature/components helper that both
  `typecore.rs` and `ctype.rs` use
- [x] Move `ctype::resolve_type_item_through_env` onto that lazy qualified path
  instead of building throwaway copied signatures
- [x] Move the matching `typecore.rs` and shared module-resolution lookups onto
  the same lazy qualified path so `env_lazy` is not partial
- [ ] When retrying the `ctype` cache, preserve typedtree stamp parity for
  `Import*` files and `DynamicImportModuleWithAlias` before keeping any speedup
- [ ] Ensure the qualified view is cached by access path, not only module name
- [ ] Cache the fully rewritten/qualified signature or components view, not just
  the raw signature
- [ ] Preserve sharing while substituting/rebasing nested type expressions so
  the lazy path is also allocation-efficient
- [ ] Replace bandaid-style eager copies with a design that is structurally
  closer to OCaml's lazy `components_of_module_maker` path
- [x] Re-measure `Import.res` and capture new timing/memory numbers
- [ ] Re-sample the compiler and confirm the hot path moved away from
  `copy_lookup_signature_for_subst` / `copy_lookup_type_expr`
- [ ] Land an OCaml-shaped cached module-components layer if the intermediate
  shared-helper step is still slower than OCaml
- [x] Re-run the full canonical corpus after the lazy-components work and record
  which slower-than-OCaml files disappear
- [ ] Re-investigate residual slower files after the module-view fix, starting
  with `gpr_1150.res`, JSX-heavy files, and polyvariant/Intl files
- [ ] Clean up secondary costs such as repeated unpack semantic-module-type
  recovery only after the main signature-copy issue is fixed

## Priority Order

1. Implement `env_lazy` properly everywhere it matters and make the lazy
   components path the architectural backbone.
2. Match the OCaml algorithm/forcing order/sharing model for that path as
   directly as possible.
3. Route `ctype` / `typecore` lookup through it.
4. Cache fully qualified access-path views.
5. Preserve sharing inside substituted type graphs.
6. Only then optimize secondary paths like unpack recovery or revisit profiler
   outliers.

## Validation Gates

- exact `Import.res` timing and memory repro before/after every optimization
- full canonical-corpus benchmark before claiming broad progress
- full canonical typedtree parity before accepting the change
- focused correctness checks on `Import.res` only as a diagnostic supplement

## Exit Condition

The project is done when:

- every planned optimization task in this project is complete
- `Import.res` is at least `2x` faster than OCaml on the same machine
- the canonical 657-file benchmark shows aggregate Rust time at or below
  `0.50x` aggregate OCaml time
- Rust peak memory usage for the authoritative `Import.res` repro is at or
  below OCaml on the same machine
- Rust is not using larger equivalent data structures than OCaml through this
  path
- the dominant hotspot is no longer repeated whole-signature deep-copy
