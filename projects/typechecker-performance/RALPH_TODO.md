# Ralph TODO: Typechecker Performance

**Last Updated:** 2026-04-13
**Status:** Investigation complete, implementation not started

## Goal

Make the Rust typechecker at least as fast as OCaml on module-signature-heavy
files, starting with `tests/tests/src/Import.res`, by moving the design closer
to OCaml's lazy module-components model.

## Baseline

Authoritative `Import.res` timing repro:

- OCaml: about `0.07s`
- Rust: about `8.69s`
- Rust peak memory: about `5.7GB`

## Current Understanding

- The main cost is not JS emission.
- The dominant cost is repeated deep-copy and path-rewrite of module signatures
  and nested type graphs.
- The hottest Rust functions are:
  - `copy_lookup_signature_for_subst`
  - `copy_lookup_type_expr`
  - `resolve_type_item_through_env`
  - `resolve_module_signature_for_path`

Detailed investigation:

- [IMPORT_RES_PERFORMANCE_HANDOFF.md](./IMPORT_RES_PERFORMANCE_HANDOFF.md)

## Task List

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
- [ ] Clean up secondary costs such as repeated unpack semantic-module-type
  recovery only after the main signature-copy issue is fixed

## Validation Gates

- exact `Import.res` timing repro before/after every optimization
- focused correctness checks on `Import.res`
- broader parity guard before accepting the change

## Exit Condition

The project is done when:

- `Import.res` matches or beats OCaml on the same machine
- Rust no longer allocates multi-GB on this file
- the dominant hotspot is no longer repeated whole-signature deep-copy
