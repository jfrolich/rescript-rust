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

## 2026-05-18 Forced Child Module Owner Paths

Task 1 progress:

- Removed the same `md_path` owner-path shortcut from the force-through-module
  path used while resolving constrained module components.
- OCaml reference:
  - `compiler/ml/env.ml:1064-1073`: the selected module path for dotted lookup
    is `Pdot(p, s, pos)`.
  - `compiler/ml/env.ml:865-882`: forcing `comp_modules` returns the module
    declaration; it does not replace the caller's selected path with the
    declaration's alias target path.
- Rust change:
  - The forced child module branch now anchors non-alias module types at the
    selected component path and follows aliases through `md_type`, matching the
    OCaml separation between path selection and module-declaration forcing.

Validation evidence:

- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- `./scripts/test_typedtree_parity.sh ModuleWithAlias`: `2/2`.
- `./scripts/test_typedtree_parity.sh global_module_alias_test`: `1/1`.
- `./scripts/test_typedtree_parity.sh`: `660/660`.
- `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- `./scripts/test_lambda_parity.sh --quick`: `660/660`.
- `./scripts/test_js_output_parity.sh --with-external --quick`:
  focused fixtures `344/344`, local JS output `660/660`, Tella JS output
  `2127/2127`.

## 2026-05-18 Component Lookup API Boundaries

Task 2 progress:

- Replaced the generic `ComponentLookupCacheMode` name with
  `ComponentLookupApi` and split the normal publishing paths by the OCaml Env
  API they model.
- Direct Rust API boundaries now have one-line OCaml citations in the enum:
  - `FindModule`: `compiler/ml/env.ml:865-882`.
  - `LookupModule`: `compiler/ml/env.ml:1036-1074`.
  - `FindModuleDescr`: `compiler/ml/env.ml:781-793`.
  - `FindType`: `compiler/ml/env.ml:800-813` and `1091-1143`.
  - `FindModtype`: `compiler/ml/env.ml:800-815` and `1091-1145`.
  - `OpenSignature`: `compiler/ml/env.ml:1841-1860` and `1874-1877`.
- `forces_alias_sig` now follows OCaml `components_of_module_maker`: every real
  component-table lookup can run `scrape_alias` at `env.ml:1516-1518`, which
  may reach `find_module` through `env.ml:1435-1446`. Only
  `ProbeModuleDescr` suppresses publish/alias forcing, because those call sites
  are Rust-only existence probes that do not correspond to an OCaml lookup step.
- Call-site mapping:
  - Let-module alias-root resolution stays on `FindModule`.
  - Source module longident signature resolution uses `LookupModule`.
  - Generic component descent uses `FindModuleDescr`.
  - Type and module-type component lookup use `FindType` and `FindModtype`.
  - Opened modules use `OpenSignature`.
  - The remaining probe callers are limited to unresolved-local-path and
    qualification existence checks.

Validation evidence:

- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --manifest-path rewatch/Cargo.toml`: passed.
- `./scripts/test_typedtree_parity.sh ModuleWithAlias`: `2/2`.
- `./scripts/test_typedtree_parity.sh nested_module_alias`: `1/1`.
- `./scripts/test_typedtree_parity.sh test_include`: `1/1`.
- `./scripts/test_typedtree_parity.sh`: `660/660`.
- `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- `./scripts/test_lambda_parity.sh --quick`: `660/660`.
- `./scripts/test_js_output_parity.sh --with-external --quick`: focused
  fixtures `344/344`, local JS output `660/660`, Tella JS output `2127/2127`.

Formatting note:

- `cargo fmt --manifest-path compiler-rust/Cargo.toml --check` still reports
  pre-existing repo-wide formatting diffs in files outside this slice, plus
  unrelated older formatting opportunities in `typecore.rs`. This patch avoided
  applying whole-file formatting churn.

## 2026-05-18 Component Module Declaration Force Point

Task 1 completion:

- Centralized component module-declaration forcing in
  `env_lazy::force_component_module_declaration_thunk`.
- Removed the unused open-coded `raw_qualified_child_module_decl` helper in
  `typecore.rs`.
- Routed the remaining raw self-alias recovery paths through the same helper
  used by `QualifiedModuleComponents::lookup_qualified_module_shared`.
- OCaml references:
  - `compiler/ml/env.ml:475-477`: `subst_modtype_maker` applies
    `Subst.modtype sub md.md_type` when a lazy module declaration is forced.
  - `compiler/ml/env.ml:865-882`: `find_module` is the API boundary that forces
    `comp_modules`.
  - `compiler/ml/env.ml:1516-1530`: `components_of_module_maker` scrapes aliases
    and builds the component substitution before table construction.
  - `compiler/ml/env.ml:1567-1578`: `Sig_module` stores separate lazy
    `comp_modules` and `comp_components` entries.
  - `compiler/ml/subst.ml:345-356` and `358-389`: `Subst.modtype` and
    `Subst.signature` freshen module-type/signature binders.
- Task 1 checklist is now complete: module signature freshening and stamp
  consumption for component module declarations goes through the OCaml-cited
  force helper instead of scattered Rust call-site freshening.

Validation evidence:

- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --manifest-path rewatch/Cargo.toml`: passed.
- `cargo build --release --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --release --manifest-path rewatch/Cargo.toml`: passed.
- `git diff --check -- compiler-rust/src/types/env_lazy.rs compiler-rust/src/types/typecore.rs`:
  passed.
- Focused typedtree parity:
  - `./scripts/test_typedtree_parity.sh ModuleWithAlias`: `2/2`.
  - `./scripts/test_typedtree_parity.sh nested_module_alias`: `1/1`.
  - `./scripts/test_typedtree_parity.sh global_module_alias_test`: `1/1`.
- Full debug typedtree parity: `./scripts/test_typedtree_parity.sh`: `660/660`.
- Tella debug typedtree quick: `./scripts/test_typedtree_parity.sh --tella --quick`:
  `1697/1697`.
- Debug lambda quick: `./scripts/test_lambda_parity.sh --quick`: `660/660`.
- Debug JS output quick with external/Tella:
  `./scripts/test_js_output_parity.sh --with-external --quick`: focused fixtures
  `344/344`, local JS output `660/660`, Tella JS output `2127/2127`.
- Release typedtree parity: `./scripts/test_typedtree_parity.sh --release`:
  `660/660`.
- Release lambda parity: `./scripts/test_lambda_parity.sh --release`: `660/660`.

Formatting note:

- `rustfmt --edition 2024 --check compiler-rust/src/types/env_lazy.rs compiler-rust/src/types/typecore.rs`
  still reports pre-existing formatting diffs in unrelated `typecore.rs`
  regions. This patch did not apply broad formatting churn.
