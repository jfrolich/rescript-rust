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
- Are signature-content inference helpers still affecting force order?
- Do `ctype.rs` abbreviation caches have the same lifetime and env dependency
  behavior as OCaml?
- Are copy/instance row and non-generic sharing rules exact enough for strict
  typedtree sexp identity parity?

## Next Recommended Session

Continue task 6 in [RALPH_TODO.md](./RALPH_TODO.md):

1. Read OCaml `compiler/ml/ctype.ml` and `compiler/ml/btype.ml` around
   `copy`, `instance`, `copy_type_desc`, `Tsubst`, row copying, and
   `cleanup_types`.
2. Audit Rust `copy_type_cached`, `instance`, and row-copy code against the
   exact temporary-mutation and cleanup sequence.
3. Replace remaining Rust-only stale-copy compensations with the OCaml-shaped
   temporary `Tsubst`/copy-cache behavior where possible.
4. Keep internal and Tella typedtree/lambda/JS parity green.

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

## 2026-05-18 Declaration-Derived Component Aliases

Task 3 completion:

- Removed the old `flattened_alias_component_paths` side-channel from
  `TypeContext`.
- Replaced it with a declaration-derived relation between selected component
  paths and alias source paths:
  - Producer: `QualifiedModuleComponents` records `SigModule` declarations whose
    module type is `MtyAlias` or `MtyIdent`.
  - Consumers: component module lookup, raw backing signature lookup,
    include-alias heads, selected value substitution, and the remaining
    typecore alias helpers now ask for alias sources/component paths instead of
    matching flattened string heads.
- The relation uses `Path::same` for lookup and insertion, so OCaml-style path
  identity ignores runtime position hints. This fixed the Tella repro where
  `TellaStd.Request.json` still carried `Webapi__Fetch.Request.t`.
- Persistent flattened-module metadata is still used only to derive backing
  source paths from an already registered alias declaration prefix. It no longer
  creates semantic alias identity by spelling alone.
- Added `component_alias_sources_are_path_based` to cover declaration-backed,
  position-insensitive path lookup and to reject unrelated spelling-only names.

OCaml references:

- `compiler/ml/env.ml:1435-1449`: `scrape_alias` resolves `Mty_alias` through
  `find_module` and strengthens non-alias module types.
- `compiler/ml/env.ml:1454-1505`: `prefix_idents` constructs selected
  component paths and substitution entries.
- `compiler/ml/env.ml:1513-1530`: `components_of_module_maker` scrapes aliases
  before building component tables.
- `compiler/ml/env.ml:1530-1588`: component table construction stores selected
  values, types, modules, and child components under the prefixed path.
- `compiler/ml/env.ml:865-882`: `find_module` forces module declarations through
  the lazy component boundary.
- `compiler/ml/subst.ml:345-389`: `Subst.modtype` and related substitution
  functions rewrite module declarations/signatures at that boundary.

Validation evidence:

- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --release --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --release --manifest-path rewatch/Cargo.toml`: passed.
- `git diff --check -- compiler-rust/src/types/context.rs compiler-rust/src/types/env_lazy.rs compiler-rust/src/types/typecore.rs compiler-rust/src/types/typemod.rs compiler-rust/src/cmi/persistent_env.rs`:
  passed.
- Focused typedtree parity:
  - `./scripts/test_typedtree_parity.sh --tella API__AnalyticsEvents`: `1/1`.
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
- Release Tella clean in-process `hyperfine`: `2.664s +/- 0.032s` over 10 runs,
  range `2.606s..2.706s`, with load averages `2.93 4.89 5.47`.

Unit-test caveat:

- `cargo test --manifest-path compiler-rust/Cargo.toml component_alias_sources_are_path_based`
  still fails before running the focused test because the crate's lib/test
  target has pre-existing unrelated compile errors, including duplicate
  `persistent_env.rs` test modules and stale Lambda/comptime test APIs.

## 2026-05-18 Signature-Content Inference Removed

Task 4 completion:

- Removed `Env::signature_has_package_self_manifests`, which recursively scanned
  signatures for direct self-manifest type declarations and used that shape
  guess to skip component substitution.
- Removed the direct type-family inference path
  (`infer_direct_sig_type_family_path` plus its whole-signature type-expression
  walk). Rebinding now uses only declaration `type_path` fields and direct
  manifest paths already produced by lookup/substitution.
- Removed the let-module cleanup fallback that searched a resolved signature for
  the unique path that looked like a matching type family. The remaining cleanup
  follows the OCaml-shaped path: one-step abbreviation expansion first, then
  explicit alias-root replacement.
- Kept the component qualification flow unconditional: copied signatures always
  run through the selected access-path substitution boundary instead of
  branching on "only values", self-manifest signatures, or inferred unique
  contents.

OCaml references:

- `compiler/ml/env.ml:1513-1588`: `components_of_module_maker` always builds
  component tables through `prefix_idents` and `Subst.value_description`,
  `Subst.type_declaration`, `Subst.extension_constructor`, and lazy module
  component thunks. It does not scan the signature first to decide whether
  substitution should run.
- `compiler/ml/mtype.ml:56-102`: strengthening rewrites type declarations and
  child module declarations while walking declarations directly, not by
  inferring paths from all value/type payloads in the signature.
- `compiler/ml/typecore.ml:3399-3424`: `Pexp_letmodule` enforces scoping through
  the normal body typing and final `Ctype.unify_var` step.
- `compiler/ml/ctype.ml:4307-4378`: `nondep_type_rec` handles escaping
  let-module paths by trying abbreviation expansion and package-path
  normalization; it does not inspect sibling signature contents to guess a
  replacement type-family root.

Validation evidence:

- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --manifest-path rewatch/Cargo.toml`: passed.
- Focused typedtree parity:
  - `./scripts/test_typedtree_parity.sh --tella API__AnalyticsEvents`: `1/1`.
  - `./scripts/test_typedtree_parity.sh module_parameter_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh defunctor_make_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh bs_poly_map_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh bs_poly_set_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh global_module_alias_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh module_alias_test`: `3/3`.
- Full debug typedtree parity after clearing cached typedtree artifacts:
  `./scripts/test_typedtree_parity.sh`: `660/660`.
- Tella debug typedtree quick after clearing cached typedtree artifacts:
  `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- Debug lambda quick: `./scripts/test_lambda_parity.sh --quick`: `660/660`.
- Debug JS output quick with external/Tella:
  `./scripts/test_js_output_parity.sh --with-external --quick`: focused fixtures
  `344/344`, local JS output `660/660`, Tella JS output `2127/2127`.

## 2026-05-18 Abbreviation Expansion Cache Alignment

Task 5 completion:

- Audited live Rust abbreviation caches against OCaml's `simple_abbrevs`,
  `proper_abbrevs`, `check_abbrev_env`, `memorize_abbrev`, and `find_expans`.
- Removed the dead `generic_dotted_constr_copies` cache from `TypeContext`.
  It had no producers or consumers and did not correspond to an OCaml
  abbreviation cache.
- Replaced remaining shared-nil `Tconstr` construction in `nondep_type_rec` and
  `unroll_abbrev` with fresh mutable `Mnil` cells, matching OCaml `ref Mnil`
  constructor allocation.
- Changed the direct `nondep_type_rec` abbreviation-substitution path to pass
  `proper_abbrevs path args abbrev` into `subst_with_memo` instead of a detached
  nil memo. This keeps `subst` on the same memo target that OCaml gets from
  `expand_abbrev env (newty2 ty.level ty.desc)`.
- Added two focused tests:
  - `simple_abbrev_cache_clears_when_module_env_changes` covers the exact
    same-path cache lifetime case by rebinding a module declaration in an Env
    and requiring `check_abbrev_env` to clear `simple_abbrevs`.
  - `tests/tests/src/abbrev_env_cache_test.res` covers repeated nullary type
    abbreviation expansion through changed opened module environments in the
    normal typedtree parity suite.

OCaml references:

- `compiler/ml/ctype.ml:236-241`: `simple_abbrevs` and `proper_abbrevs`.
- `compiler/ml/btype.ml:531-536`: `find_expans`.
- `compiler/ml/btype.ml:555-564`: `cleanup_abbrev` and `memorize_abbrev`.
- `compiler/ml/ctype.ml:1270-1292`: `subst` memorizes the original
  abbreviation before `instance_parameterized_type`, sets `abbreviations`, then
  clears it before unification.
- `compiler/ml/ctype.ml:1322-1325`: `check_abbrev_env` clears all memorized
  abbreviation refs when the physical environment object changes.
- `compiler/ml/ctype.ml:1346-1372`: `expand_abbrev_gen` checks memoized
  expansions before `Env.find_type_expansion` and normalizes only after that
  lookup fails.
- `compiler/ml/ctype.ml:4307-4330`: `nondep_type_rec` expands escaping
  constructors with `expand_abbrev env (newty2 ty.level ty.desc)`, preserving
  the constructor's abbreviation memo ref.
- `compiler/ml/ctype.ml:4380-4388`: `unroll_abbrev` relinks through a fresh
  `Tconstr (Path.Pident id, params, ref Mnil)`.

Validation evidence:

- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --manifest-path compiler-rust/Cargo.toml`: passed.
- `cargo build --manifest-path rewatch/Cargo.toml`: passed.
- `git diff --check -- compiler-rust/src/types/context.rs compiler-rust/src/types/ctype.rs`:
  passed.
- `rustfmt --edition 2024 --check compiler-rust/src/types/ctype.rs`: passed.
- Focused typedtree parity:
  - `./scripts/test_typedtree_parity.sh abbrev_env_cache_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh module_alias_test`: `3/3` after
    rerunning without overlapping build-artifact writers.
  - `./scripts/test_typedtree_parity.sh global_module_alias_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh defunctor_make_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh module_parameter_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh bs_poly_map_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh --tella API__AnalyticsEvents`: `1/1`.
- Full debug typedtree parity after clearing cached typedtree artifacts:
  `./scripts/test_typedtree_parity.sh`: `661/661`.
- Tella debug typedtree quick after clearing cached typedtree artifacts:
  `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- Debug lambda quick: `./scripts/test_lambda_parity.sh --quick`: `661/661`.
- Debug JS output quick with external/Tella:
  `./scripts/test_js_output_parity.sh --with-external --quick`: focused fixtures
  `344/344`, local JS output `661/661`, Tella JS output `2127/2127`.

Unit-test caveat:

- `cargo test --manifest-path compiler-rust/Cargo.toml simple_abbrev_cache_clears_when_module_env_changes --lib`
  still fails before running the focused test because the crate's lib/test
  target has pre-existing unrelated compile errors, including duplicate
  `persistent_env.rs` test modules and stale Lambda/typecore test APIs.

## 2026-05-18 Copy / Instantiation Sharing Alignment

Task 6 completion:

- Audited Rust `instance`, `instance_list`, `instance_parameterized_type`,
  `copy_type_cached`, `copy_sep_inner`, `subst_identity_copy_rec`,
  `copy_type_deep`, and `copy_row_cached` against OCaml's instantiation and
  copy helpers.
- Verified the normal `partial = None` rule: generic nodes are copied through
  one scoped copy window, while non-generic nodes are returned by identity.
- Verified Rust's scoped node and row marker tables model OCaml's temporary
  `Tsubst` mutation window without serializer normalization.
- Verified row-copy behavior for polymorphic variants and object rows against
  `copy_row`: payload types are copied, `Reither` links are kept only when the
  source row is kept, fixed rows force matched cases, and row names copy their
  type arguments.
- Fixed the one concrete audit mismatch: copied arrows now preserve OCaml
  commutability-copy semantics. Rust previously rebuilt copied arrows as
  `Cok`; it now uses `copy_commutable`, which returns `Cok` only for a
  representative `Cok` source and otherwise allocates a fresh
  `Clink(Cunknown)`, matching OCaml `copy_commu`.

OCaml references:

- `compiler/ml/ctype.ml:872-1044`: `copy` handles generic/non-generic
  sharing, installs temporary `Tsubst` stubs, handles constructor abbreviation
  representatives, and registers row-more recursion markers.
- `compiler/ml/ctype.ml:1052-1138`: `instance`, `instance_list`,
  `instance_constructor`, and `instance_parameterized_type` share one copy
  window until `cleanup_types`.
- `compiler/ml/ctype.ml:1191-1255`: `copy_sep` / `instance_poly` copy with
  free-univar-sensitive sharing and delayed generic copies.
- `compiler/ml/btype.ml:384-410`: `copy_row` preserves row field order and
  controls `Reither` link and fixed-row behavior.
- `compiler/ml/btype.ml:418-432`: `copy_commu` and `copy_type_desc` preserve
  arrow commutability as `Cok` or fresh `Clink(Cunknown)`.
- `compiler/ml/btype.ml:456-475`: `save_desc`, `dup_kind`, and
  `cleanup_types` define the temporary mutation window Rust models with scoped
  copy caches.
- `compiler/ml/subst.ml:130-239`: `Subst.typexp` uses the same
  `copy_type_desc` and row-more `Tsubst(Ttuple [...])` shape for full
  structural substitution copies.

Validation evidence:

- `rustfmt --edition 2024 --check compiler-rust/src/types/ctype.rs`: passed.
- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- Debug builds:
  - `cargo build --manifest-path compiler-rust/Cargo.toml`: passed.
  - `cargo build --manifest-path rewatch/Cargo.toml`: passed.
- Focused typedtree parity:
  - `./scripts/test_typedtree_parity.sh label_uncurry`: `1/1`.
  - `./scripts/test_typedtree_parity.sh test_type_based_arity`: `1/1`.
  - `./scripts/test_typedtree_parity.sh poly_variant_test`: `2/2`.
  - `./scripts/test_typedtree_parity.sh object_type_spreads`: `1/1`.
  - `./scripts/test_typedtree_parity.sh abbrev_env_cache_test`: `1/1`.
- Full debug typedtree parity after clearing cached typedtree artifacts:
  `./scripts/test_typedtree_parity.sh`: `661/661`.
- Tella debug typedtree quick after clearing cached typedtree artifacts:
  `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- Debug lambda quick: `./scripts/test_lambda_parity.sh --quick`: `661/661`.
- Debug JS output quick with external/Tella:
  `./scripts/test_js_output_parity.sh --with-external --quick`: focused fixtures
  `344/344`, local JS output `661/661`, Tella JS output `2127/2127`.
- Release builds:
  - `cargo build --release --manifest-path compiler-rust/Cargo.toml`: passed.
  - `cargo build --release --manifest-path rewatch/Cargo.toml`: passed.
- Release parity gates after clearing cached typedtree artifacts:
  - `./scripts/test_typedtree_parity.sh --release`: `661/661`.
  - `./scripts/test_lambda_parity.sh --release`: `661/661`.

## 2026-05-18 Type Declaration Group Staging Alignment

Task 9 completion:

- Audited OCaml `Typedecl.transl_type_decl` as the shared implementation for
  structure and signature type declarations. The important group shape is:
  prepend synthetic fixed-row declarations, allocate row identifiers before the
  user-written type identifiers, enter abstract placeholders at the OCaml
  `enter_type` boundary, translate declarations under one definition level,
  then run duplicate, recursion, constraint, variance, immediacy, and
  abbreviation checks over the finalized declaration group.
- Fixed Rust fixed private row declarations to emit the OCaml synthetic
  `t#row` declaration before the main private type declaration. The row
  variable in the manifest now links to the synthetic row path, not to the main
  type path.
- Applied the same synthetic-row staging to `Psig_type` translation. Signature
  fixed rows now allocate, enter, translate, generalize, and participate in the
  variance fixpoint like structure fixed rows.
- Kept ordinary recursive and nonrecursive declaration visibility semantics
  unchanged: recursive groups still translate through main-type placeholders;
  nonrecursive groups only enter the synthetic row placeholders, matching
  OCaml's `enter_type` exception for row names.
- Audited variance and immediacy ordering. Rust still computes immediacy after
  kind/manifest translation, and variance is now computed across the combined
  row-plus-main declaration entry list while skipping source-variance checks for
  synthetic rows.
- Audited constraints and extension constructors against the OCaml phase order.
  Constraint unification remains before `end_def`/generalization, constraint
  touching remains after untagged checks, and extension constructor translation
  stays outside the fixed-row declaration change.
- Did not split out a new `compiler-rust/src/types/typedecl.rs` in this pass:
  the OCaml-aligned helpers are now factored at the top of `typemod.rs`, and a
  file split would be mechanical rather than improving the current phase match.

OCaml references:

- `compiler/ml/typedecl.ml:80-115`: `enter_type` enters all recursive
  placeholders and, for nonrecursive groups, still enters row-name placeholders.
- `compiler/ml/typedecl.ml:159-194`: fixed type detection and `set_fixed_row`
  link the manifest row variable to the synthetic row type.
- `compiler/ml/typedecl.ml:370-397`: `transl_declaration` resets type
  variables and begins per-declaration type translation inside the group.
- `compiler/ml/typedecl.ml:692-733`: kind/manifest translation, constraint
  handling, `end_def`, and fixed-row setup.
- `compiler/ml/typedecl.ml:767-845`: declaration constraint checking.
- `compiler/ml/typedecl.ml:1030-1388`: variance and immediacy fixpoint
  computation.
- `compiler/ml/typedecl.ml:1399-1443`: duplicate checks and name recursion.
- `compiler/ml/typedecl.ml:1446-1620`: full `transl_type_decl` phase order,
  including synthetic fixed-row prepending and final checks.
- `compiler/ml/typedecl.ml:1624-1845`: type extension constructor
  translation.
- `compiler/ml/typedecl.ml:2059-2065`: recursive module type declaration
  checks.
- `compiler/ml/typemod.ml:300-370`: with-constraint fixed rows create a
  synthetic row signature item.
- `compiler/ml/mtype.ml:51-54`: strengthening skips synthetic row types before
  private types.

Validation evidence:

- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- Debug builds:
  - `cargo build --manifest-path compiler-rust/Cargo.toml`: passed.
  - `cargo build --manifest-path rewatch/Cargo.toml`: passed.
- Focused typedtree parity:
  - `./scripts/test_typedtree_parity.sh fixed_private_row_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh 'fixed_private_row_test|type_coercion_free_vars|record_name_test|bs_abstract_test|Import'`:
    `8/8`.
- Full debug typedtree parity after clearing cached typedtree artifacts:
  `./scripts/test_typedtree_parity.sh`: `662/662`.
- Tella debug typedtree quick:
  `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- Debug lambda quick: `./scripts/test_lambda_parity.sh --quick`: `662/662`.
- Debug JS output quick with external/Tella:
  `./scripts/test_js_output_parity.sh --with-external --quick`: focused
  fixtures `344/344`, local JS output `662/662`, Tella JS output `2127/2127`.
- Release builds:
  - `cargo build --release --manifest-path compiler-rust/Cargo.toml`: passed.
  - `cargo build --release --manifest-path rewatch/Cargo.toml`: passed.
- Release parity gates after clearing cached typedtree artifacts:
  - `./scripts/test_typedtree_parity.sh --release`: `662/662`.
  - `./scripts/test_lambda_parity.sh --release`: `662/662`.
## 2026-05-18 Pattern / GADT Backtracking Alignment

Task 7 completion:

- Audited OCaml's pattern backtracking state model. `save_state` captures the
  `Btype` mutation snapshot, saved `Ctype` levels, and the mutable Env ref;
  `set_state` restores all three before retrying a split or-pattern branch.
- Added an internal Rust `NeedBacktrack` sentinel and `PatternMode::SplitOr`
  so the mode lattice matches OCaml's `Normal`, `Splitting_or`, `Inside_or`,
  and `Split_or`.
- Added Rust pattern backtracking checkpoints for pattern variables, module
  variables, and delayed label-argument forces, plus a full speculative state
  snapshot covering mutable type nodes, levels, abbreviation memos, unifier
  state, pending force paths, and `newtype_level`.
- Reworked parsed `Ppat_or` typing to match OCaml's non-split branch order:
  type branch 1 in `Inside_or`, keep its pattern/module binders, restore only
  binder lists before branch 2, then alpha-rename branch 2 onto branch 1 and
  keep branch 1's binders live.
- Added the OCaml split retry shape for the Rust `NeedBacktrack` path: restore
  the saved state, retry branch 1 in split mode, and on a typed error restore
  again before retrying branch 2.
- Fixed constructor-pattern GADT unification to follow the PR#7214 rule:
  generalized constructors use GADT unification only outside `Inside_or` and
  only when existentials are allowed; `Inside_or` and no-existential contexts
  use plain pattern unification.
- Audited the Parmatch callback difference. OCaml's `partial_pred` retypes
  generated witness patterns and always restores `Btype`, levels, and Env
  afterward. Rust's current exhaustiveness/unused logic works from typed
  patterns and does not expose the same untyped `constrs`/`labels` callback, so
  the new full restore machinery is wired to the internal split/backtrack path
  that exists in Rust rather than adding a second Rust-only Parmatch algorithm.

OCaml references:

- `compiler/ml/typecore.ml:1251-1259`: `unify_head_only` instantiates a GADT
  constructor head, replaces result arguments with fresh vars, enforces
  constraints, and unifies with the expected pattern type.
- `compiler/ml/typecore.ml:1262-1271`: `state`, `save_state`, and `set_state`
  define the backtracking snapshot over `Btype`, `Ctype` levels, and Env.
- `compiler/ml/typecore.ml:1273-1299`: pattern mode definitions and the
  `Splitting_or -> Normal` recursive default.
- `compiler/ml/typecore.ml:1489-1527`: constructor pattern flow, `Inside_or`
  `Need_backtrack` for Parmatch GADT witnesses, and the PR#7214
  `unify_pat_types` / `unify_pat_types_gadt` choice.
- `compiler/ml/typecore.ml:1688-1733`: `Ppat_or` branch typing, binder reset,
  alpha-renaming, state restore, and split fallback retry order.
- `compiler/ml/typecore.ml:1813-1832`: `partial_pred` saves state, retypes a
  witness pattern for Parmatch, then restores state on success and typed error.
- `compiler/ml/typecore.ml:4366-4536`: `type_cases` GADT scope lifetime and
  post-pattern/body/exhaustiveness escape check ordering.
- `compiler/ml/ctype.ml:1492-1505`: `enforce_constraints` checks constructor
  type parameter constraints through declaration substitution.

Validation evidence:

- `git diff --check -- compiler-rust/src/types/ctype.rs compiler-rust/src/types/typecore.rs`:
  passed.
- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- Debug builds:
  - `cargo build --manifest-path compiler-rust/Cargo.toml`: passed.
  - `cargo build --manifest-path rewatch/Cargo.toml`: passed.
- Focused typedtree parity:
  - `./scripts/test_typedtree_parity.sh typeof_test`: `1/1`.
  - `./scripts/test_typedtree_parity.sh poly_variant_test`: `2/2`.
  - `./scripts/test_typedtree_parity.sh variantsMatching`: `1/1`.
  - `./scripts/test_typedtree_parity.sh 'complete_parmatch_test|test_simple_pattern_match|nested_pattern_match_test|ffi_js_test'`:
    `4/4`.
- Full debug typedtree parity after clearing cached typedtree artifacts:
  `./scripts/test_typedtree_parity.sh`: `661/661`.
- Tella debug typedtree quick:
  `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- Debug lambda quick: `./scripts/test_lambda_parity.sh --quick`: `661/661`.
- Debug JS output quick with external/Tella:
  `./scripts/test_js_output_parity.sh --with-external --quick`: focused
  fixtures `344/344`, local JS output `661/661`, Tella JS output `2127/2127`.
- Release builds:
  - `cargo build --release --manifest-path compiler-rust/Cargo.toml`: passed.
  - `cargo build --release --manifest-path rewatch/Cargo.toml`: passed.
- Release parity gates after clearing cached typedtree artifacts:
  - `./scripts/test_typedtree_parity.sh --release`: `661/661`.
  - `./scripts/test_lambda_parity.sh --release`: `661/661`.

## 2026-05-18 Let / Match Definition-Level Boundary Alignment

Task 8 completion:

- Audited OCaml let-binding staging from pattern typing through
  generalization. OCaml opens one definition level for the whole binding group,
  types all patterns through one `type_pattern_list` call, runs delayed pattern
  forces before RHS expression typing, closes the definition level, applies the
  value restriction, then generalizes all subpatterns.
- Fixed Rust `type_let_bindings` to reset `PatternState` once per let group
  instead of once per binding. This matches OCaml's single `reset_pattern`
  window for `type_pattern_list`, so duplicate binders across `and` bindings are
  detected during pattern typing and group binder order is preserved for
  environment extension.
- Added a compiler-diagnostic parity fixture for a recursive `and` group with a
  duplicate value binder. Before the fix, Rust accepted the file and emitted
  unused warnings; now Rust errors at the same point as OCaml with byte-for-byte
  diagnostic output.
- Audited match/case definition-level staging. The Rust batch non-GADT and
  GADT/sequential paths already model the OCaml shape for this task: establish
  the case definition level and GADT scope, type patterns before bodies, run
  delayed pattern unification/forces before body typing, then perform
  partiality/exhaustiveness and escape checks after typed cases are available.
  No match/case code change was needed in this pass.
- Audited local abstract type and existential handling around patterns against
  the task-7 backtracking work. The existing Rust paths keep `newtype_level`,
  constructor existential allowance, and GADT instance level lifetime aligned
  with the OCaml pattern/type-cases boundaries; the let-group bug was isolated
  to pattern-variable table lifetime.

OCaml references:

- `compiler/ml/ctype.ml:181-194`: `begin_def` and `end_def` save and restore
  `current_level` and `nongen_level`.
- `compiler/ml/ctype.ml:628-648`: `generalize_structure`.
- `compiler/ml/ctype.ml:753-778`: `generalize_expansive`.
- `compiler/ml/typecore.ml:1848-1888`: `add_pattern_variables`,
  `type_pattern`, and `type_pattern_list`; `type_pattern_list` calls
  `reset_pattern` once and types the whole pattern group through one
  `pattern_variables` table.
- `compiler/ml/typecore.ml:4366-4536`: `type_cases` order for case definition
  levels, GADT scope, pattern typing, delayed pattern unification/forces, body
  typing, partiality/exhaustiveness, and escape checks.
- `compiler/ml/typecore.ml:4540-4784`: `type_let` order for `begin_def`,
  `type_pattern_list`, recursive approximation, delayed forces, RHS typing,
  partiality, `end_def`, value restriction, generalization, and illegal letrec
  pattern checks.

Validation evidence:

- `cargo check --manifest-path compiler-rust/Cargo.toml`: passed.
- Debug builds:
  - `cargo build --manifest-path compiler-rust/Cargo.toml`: passed.
  - `cargo build --manifest-path rewatch/Cargo.toml`: passed.
- Diagnostic parity:
  - `./scripts/test_error_output_parity.sh --compiler-only let_group_duplicate_binder`:
    `1/1`.
  - `./scripts/test_error_output_parity.sh --release --compiler-only let_group_duplicate_binder`:
    `1/1`.
- Focused valid typedtree parity:
  - `./scripts/test_typedtree_parity.sh 'minimal_test|fun_pattern_match|bdd|inline_map_test|Import'`:
    `8/8`.
- Full debug typedtree parity after clearing cached typedtree artifacts:
  `./scripts/test_typedtree_parity.sh`: `661/661`.
- Tella debug typedtree quick:
  `./scripts/test_typedtree_parity.sh --tella --quick`: `1697/1697`.
- Debug lambda quick: `./scripts/test_lambda_parity.sh --quick`: `661/661`.
- Debug JS output quick with external/Tella:
  `./scripts/test_js_output_parity.sh --with-external --quick`: focused
  fixtures `344/344`, local JS output `661/661`, Tella JS output `2127/2127`.
- Release builds:
  - `cargo build --release --manifest-path compiler-rust/Cargo.toml`: passed.
  - `cargo build --release --manifest-path rewatch/Cargo.toml`: passed.
- Release parity gates after clearing cached typedtree artifacts:
  - `./scripts/test_typedtree_parity.sh --release`: `661/661`.
  - `./scripts/test_lambda_parity.sh --release`: `661/661`.
