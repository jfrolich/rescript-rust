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

Continue task 1 in [RALPH_TODO.md](./RALPH_TODO.md):

1. Read OCaml `compiler/ml/env.ml:1533-1579`.
2. Read Rust `build_local_module_components`, especially child module handling.
3. Prove or fix whether Rust child `comp_modules` and `comp_components` share
   the same forced thunk state as OCaml's `EnvLazy.create (sub, md)` and
   `components_of_module ~deprecated ~loc:md.md_loc !env sub path md.md_type`.
4. Verify that module declarations are forced at the OCaml
   `EnvLazy.force subst_modtype_maker` boundary, not earlier.

## 2026-05-18 Stored Component Thunk Audit

Task 1 progress:

- Checked off `StoredModuleComponents::with_components` audit and replacement
  of Rust-specific parent/sibling/alias reconstruction.
- Commit: `b67270ba6 Align child component thunks with OCaml EnvLazy`.
- OCaml references:
  - `compiler/ml/env.ml:1516-1530`: `components_of_module_maker` scrapes the
    raw module type and then applies `prefix_idents path sub sg`.
  - `compiler/ml/env.ml:1567-1578`: child module declarations and child
    component thunks both capture the same substitution/environment boundary.
- Rust change:
  - `compiler-rust/src/types/env_lazy.rs:1745-1773` now passes the stored
    `module_decl` unchanged to `build_local_module_components`.
  - Parent component substitution is carried uniformly from `parent_context`
    into `build_local_module_components`.
  - Removed the branchy parent/sibling/persistent-alias pre-rewrite helpers
    `parent_matches_component_context` and `raw_component_module_type`.

Validation evidence for `b67270ba6`:

- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --manifest-path compiler-rust/Cargo.toml`: passed.
- `rustfmt --edition 2024 --check compiler-rust/src/types/env_lazy.rs`: passed.
- `git diff --check -- compiler-rust/src/types/env_lazy.rs`: passed.
- `./scripts/test_typedtree_parity.sh ModuleWithAlias`: `2/2`.
- `./scripts/test_typedtree_parity.sh --quick`: `660/660`.
- `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.

Performance note:

- Same-session release Tella clean in-process `hyperfine` comparison did not
  show a material speedup: previous `af8b2ede7` measured `2.640s +/- 0.028s`,
  current `b67270ba6` measured `2.629s +/- 0.022s`.

Post-tracker validation on `473cab890`:

- `./scripts/test_typedtree_parity.sh --quick`: `660/660`.
- `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- `./scripts/test_lambda_parity.sh --quick`: `660/660`.
