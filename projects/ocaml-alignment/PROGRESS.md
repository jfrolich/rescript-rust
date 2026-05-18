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

1. Read OCaml `compiler/ml/env.ml:475-477`, `781-793`, `865-882`,
   `1516-1588`, and `1841-1877`.
2. Audit remaining Rust module declaration force sites against those Env API
   boundaries.
3. Verify that module declarations are forced at the OCaml
   `EnvLazy.force subst_modtype_maker` boundary, not earlier.
4. Verify that signature freshening and stamp consumption happen at that same
   force point.

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

## 2026-05-18 Open Module Component Sharing

Task 1 progress:

- Checked off child `comp_modules` / `comp_components` sharing for opened
  modules.
- OCaml references:
  - `compiler/ml/env.ml:1516-1588`: `components_of_module_maker` stores both
    child module declarations and child component thunks for each `Sig_module`.
  - `compiler/ml/env.ml:1841-1860`: `add_components` installs both
    `comp_modules` and `comp_components` when a signature is opened.
  - `compiler/ml/env.ml:1874-1877`: `open_signature` opens the component table
    from `get_components (find_module_descr root)`.
- Rust change:
  - Added an opened-module path that reuses the resolved
    `QualifiedModuleComponents` view instead of reopening a detached signature.
  - Routed expression opens, structure opens, and signature opens through that
    shared component view first, falling back to detached signature opening only
    when no component view can be resolved.
  - This keeps opened `comp_modules` and `comp_components` on the same lazy
    component state rather than rebuilding only the module declarations.

Validation evidence:

- `cargo build --release --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --release --manifest-path rewatch/Cargo.toml`: passed.
- `./scripts/test_typedtree_parity.sh ModuleWithAlias`: `2/2`.
- `./scripts/test_typedtree_parity.sh test_include`: `1/1`.
- `./scripts/test_typedtree_parity.sh nested_module_alias`: `1/1`.
- `./scripts/test_typedtree_parity.sh`: `660/660`.
- `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- `./scripts/test_lambda_parity.sh --quick`: `660/660`.
- `./scripts/test_js_output_parity.sh --with-external --quick`:
  focused fixtures `344/344`, local JS output `660/660`, Tella JS output
  `2127/2127`.

## 2026-05-18 Dotted Module Path Lookup

Task 1 progress:

- Fixed one descriptor-only module path lookup to stop observing a child module
  declaration's `md_path`.
- OCaml reference:
  - `compiler/ml/env.ml:1064-1073`: `lookup_module` for `Ldot` reads
    `comp_modules` only for the runtime position and returns `Pdot(p, s, pos)`;
    it does not force the child module declaration with `subst_modtype_maker`.
- Rust change:
  - `typemod` `lookup_module_path_by_lid` now returns the selected component
    path from the parent component table for dotted longidents instead of using
    the child declaration's alias path.
  - This keeps path construction on the same descriptor/component boundary as
    OCaml and reserves module declaration observation for real
    `find_module`-style force sites.

Validation evidence:

- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- `./scripts/test_typedtree_parity.sh ModuleWithAlias`: `2/2`.
- `./scripts/test_typedtree_parity.sh nested_module_alias`: `1/1`.
- `./scripts/test_typedtree_parity.sh DynamicImportModuleWithAlias`: `1/1`.
- `./scripts/test_typedtree_parity.sh global_module_alias_test`: `1/1`.
- `./scripts/test_typedtree_parity.sh`: `660/660`.
- `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- `./scripts/test_lambda_parity.sh --quick`: `660/660`.
- `./scripts/test_js_output_parity.sh --with-external --quick`:
  focused fixtures `344/344`, local JS output `660/660`, Tella JS output
  `2127/2127`.
