# Ralph TODO: Typechecker Performance

**Last Updated:** 2026-04-13
**Status:** Baseline complete, implementation not started

## Goal

Make Rust at least as fast as OCaml on the canonical recursive
`tests/tests/src/**/*.res` corpus (`657` files), starting with the
module-signature-heavy `tests/tests/src/Import.res` cliff and moving the design
closer to OCaml's lazy module-components model.

## Baseline

Authoritative `Import.res` timing repro:

- OCaml: about `0.07s`
- Rust: about `8.69s`
- Rust peak memory: about `5.7GB`

Authoritative canonical-corpus benchmark:

- Files tested: `657`
- Comparable files: `657`
- Rust faster or equal: `2`
- Rust slower: `655`
- Materially slower: `252`
- OCaml failures: `0`
- Rust failures: `0`
- Aggregate Rust / OCaml ratio: `4.29x`

Detailed corpus baseline:

- [CORPUS_BASELINE.md](./CORPUS_BASELINE.md)

## Current Understanding

- The main cost is not JS emission.
- The dominant root cause is repeated deep-copy and path-rewrite of module
  signatures and nested type graphs.
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

Detailed investigation:

- [IMPORT_RES_PERFORMANCE_HANDOFF.md](./IMPORT_RES_PERFORMANCE_HANDOFF.md)
- [CORPUS_BASELINE.md](./CORPUS_BASELINE.md)

## Task List

- [ ] Keep `scripts/benchmark_typechecker_performance.py` authoritative for the
  canonical recursive 657-file corpus
- [ ] Add a shared path-qualified module-signature resolution helper that both
  `typecore.rs` and `ctype.rs` can use
- [ ] Move `ctype::resolve_type_item_through_env` onto the shared qualified
  signature path instead of building throwaway copies
- [ ] Ensure the qualified view is cached by access path, not only module name
- [ ] Cache the fully rewritten/qualified signature or components view, not just
  the raw signature
- [ ] Replace bandaid-style eager copies with a design that is structurally
  closer to OCaml's lazy `components_of_module_maker` path
- [ ] Re-measure `Import.res` and capture new timing/memory numbers
- [ ] Re-sample the compiler and confirm the hot path moved away from
  `copy_lookup_signature_for_subst` / `copy_lookup_type_expr`
- [ ] Land an OCaml-shaped cached module-components layer if the intermediate
  shared-helper step is still slower than OCaml
- [ ] Re-run the full canonical corpus after the lazy-components work and record
  which slower-than-OCaml files disappear
- [ ] Re-investigate residual slower files after the module-view fix, starting
  with `gpr_1150.res`, JSX-heavy files, and polyvariant/Intl files
- [ ] Clean up secondary costs such as repeated unpack semantic-module-type
  recovery only after the main signature-copy issue is fixed

## Validation Gates

- exact `Import.res` timing repro before/after every optimization
- full canonical-corpus benchmark before claiming broad progress
- focused correctness checks on `Import.res`
- broader parity guard before accepting the change

## Exit Condition

The project is done when:

- `Import.res` matches or beats OCaml on the same machine
- Rust is no slower than OCaml on every comparable file in the canonical corpus
- Rust no longer allocates multi-GB on this file
- the dominant hotspot is no longer repeated whole-signature deep-copy
