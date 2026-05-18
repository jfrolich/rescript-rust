# OCaml Alignment Progress

## 2026-05-18 Initial Project Baseline

Created this project to track OCaml-alignment work separate from intentional
in-process and performance differences.

Recent branch work already moved several areas in the right direction:

- shared cached module component views
- `OnceCell`-backed stored module components
- lazy functor result substitution caching
- grouped/precomputed module component lookup indices
- reduced Env path lookup churn
- removal of the legacy Rust direct lambda converter

Those changes are useful, but they do not close the project. The remaining risk
is still algorithmic: Rust has several explicit reconstruction paths around
lazy module components, alias identity, force modes, and type graph sharing that
need to be proven against OCaml or replaced with a more direct port.

## Current Open Questions

- Does every `ComponentLookupCacheMode` call site correspond exactly to an
  OCaml Env API boundary?
- Can `flattened_alias_component_paths` be removed by carrying component thunk
  identity through alias scraping and substitution instead?
- Are signature-content inference helpers still affecting force order?
- Do `ctype.rs` abbreviation caches have the same lifetime and env dependency
  behavior as OCaml?
- Are copy/instance row and non-generic sharing rules exact enough for strict
  typedtree sexp identity parity?

## Next Recommended Session

Start with task 1 in [RALPH_TODO.md](./RALPH_TODO.md):

1. Read OCaml `compiler/ml/env.ml:1513-1598`.
2. Read Rust `StoredModuleComponents::with_components` and
   `build_local_module_components`.
3. Produce a small mapping table from each Rust branch to the OCaml branch it
   claims to implement.
4. Remove or rewrite the first branch that cannot be justified by OCaml source.

