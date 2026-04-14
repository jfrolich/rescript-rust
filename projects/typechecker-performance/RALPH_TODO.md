# Ralph TODO: Typechecker Performance

**Last Updated:** 2026-04-14
**Status:** shared env_lazy-backed detached-signature copy path landed in `typecore` / `typemod`, dotted shared module-signature scraping now consults env_lazy-backed qualified views first, lazy child module/modtype qualification now comes from cached parent qualified views, dotted alias/modtype expansion inside `typecore`'s shared `Env::resolve_module_type` helper now consults those cached child views before raw recursive signature scans, the env_lazy cache-key path now uses env-owned cached local-alias metadata instead of rebuilding it on every lookup, a broader `typemod`/`typecore` env_lazy rollout was attempted and reverted because it regressed import-family parity, and the broader env_lazy rollout is still incomplete

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

Checkpoint measurements from this worktree after making detached whole-signature
copies come from cached qualified module components in `typecore` /
`typemod` on `2026-04-14`:

- Full typedtree parity: Rust `657 passed`, OCaml `657 passed`, parity
  `232/657`, `43117` hunk mismatches
- Focused import parity: `1/4` files match, `283` hunk mismatches
- Authoritative `Import.res` repro:
  - OCaml: `0.04s` (`/usr/bin/time -lp`)
  - Rust: `0.32s` (`/usr/bin/time -lp`)
  - Rust max RSS: about `71MB`
  - Rust peak footprint: about `57MB`
- Authoritative canonical corpus benchmark:
  - Files tested: `657`
  - Comparable files: `656`
  - Rust faster or equal: `8`
  - Rust slower: `648`
  - Materially slower: `222`
  - Rust failures: `1` (`src/ticker.res`: stack overflow)
  - Aggregate OCaml total: `5866.2ms`
  - Aggregate Rust total: `12340.7ms`
  - Aggregate Rust / OCaml ratio: `2.10x`
  - `Import.res` benchmark entry: OCaml `49.5ms`, Rust `339.0ms`, `6.85x`

What landed in this checkpoint:

- added `typecore::copy_resolved_module_signature_for_path` and
  `typecore::copy_module_signature_in_resolved_path` so callers that still need
  a detached mutable signature can copy from cached
  `QualifiedModuleComponents` instead of rebuilding the qualified signature
  pipeline from raw module types
- `typemod::localize_exported_structure_module_type` now uses that
  env_lazy-backed detached-signature copy path instead of re-resolving the raw
  module path and rebuilding its signature view first

What this means:

- env_lazy is now backing both the cheap lookup path and a shared
  detached-signature copy path for callers that still need a full signature
- the import-family parity guard stayed at the prior checkpoint level, so this
  speedup did not introduce new `Import*` / `DynamicImportModuleWithAlias`
  stamp drift
- the broader corpus aggregate ratio improved from `2.37x` to `2.10x`, and the
  Rust-faster-or-equal count moved from `1` to `8`
- the next session should push the same source-of-truth approach into the
  remaining whole-signature copy hotspots, then re-profile `mario_game`,
  JSX-heavy files, `gpr_1150`, and the `ticker.res` stack overflow

## Session Update: Dotted Shared Resolution Through `env_lazy` In `typecore`

Additional checkpoint from this worktree on `2026-04-14` after routing the
remaining dotted module/modtype expansion inside `typecore`'s shared
`Env::resolve_module_type` helper through `lookup_module_in_resolved_path` /
`lookup_modtype_in_resolved_path`, and removing two lingering parent-signature
clones in `typecore`:

- exact `Import.res` repro after rebuild:
  - OCaml: `0.08s` (`/usr/bin/time -lp`)
  - Rust: `0.32s` (`/usr/bin/time -lp`)
  - Rust max RSS: about `56.9MB`
  - Rust peak footprint: about `41.3MB`
- focused import parity: unchanged at `1/4`, `283` hunk mismatches
- full typedtree parity: unchanged at `232/657`, `43117` hunk mismatches
- canonical corpus benchmark, confirming rerun:
  - Files tested: `657`
  - Comparable files: `657`
  - Rust faster or equal: `0`
  - Rust slower: `657`
  - Materially slower: `220`
  - OCaml failures: `0`
  - Rust failures: `0`
  - Aggregate OCaml total: `4483.6ms`
  - Aggregate Rust total: `9900.6ms`
  - Aggregate Rust / OCaml ratio: `2.21x`
  - `Import.res` benchmark entry: OCaml `41.2ms`, Rust `156.6ms`, `3.80x`

Before/after against the same-session pre-change benchmark command:

- before: aggregate Rust total `11472.3ms`, materially slower `225`,
  `Import.res` `168.5ms`
- after: aggregate Rust total `9900.6ms`, materially slower `220`,
  `Import.res` `156.6ms`

What landed in this step:

- `typecore::Env::resolve_module_type` now treats dotted child module/modtype
  expansion the same way OCaml `Env.find_module` / `find_modtype` do: it asks
  the cached env_lazy-qualified parent view for the child declaration first
  instead of recursively rebuilding and scanning the parent signature
- `typecore::resolve_type_item_identity` now reads dotted child types through
  `lookup_type_in_resolved_path` instead of cloning the whole parent signature
- `typecore::build_module_signature_for_path` now borrows the parent signature
  from `with_resolved_module_components_for_path` for flattened-alias child
  prefix rewriting instead of cloning it via `resolve_module_signature_for_path`

What this means:

- the shared typecore module-resolution helper now matches the OCaml-shaped
  env_lazy/components path more closely for dotted child lookups, instead of
  leaving that helper on a raw recursive signature-scan path
- the import-family parity checkpoint stayed flat, so this dotted env_lazy
  rollout did not reintroduce the rejected `Pident` forcing-order regression
- the broader corpus still needs more work, but Rust's aggregate total and the
  materially-slower count both improved on the canonical benchmark even though
  the OCaml side sped up enough on the rerun that the ratio remained noisy

## Session Update: `ctype` Dotted Module-Type Path

Additional checkpoint from this worktree on `2026-04-14` after routing
`ctype::resolve_module_type_through_env_path` through the shared env_lazy-backed
detached-signature copy helpers for dotted child modules:

- exact `Import.res` repro:
  - OCaml: `0.07s` (`/usr/bin/time -lp`)
  - Rust: `0.47s` (`/usr/bin/time -lp`)
  - Rust max RSS: about `70.7MB`
  - Rust peak footprint: about `56.8MB`
- focused import parity: unchanged at `1/4`, `283` hunk mismatches
- full typedtree parity: unchanged at `232/657`, `43117` hunk mismatches
- canonical corpus benchmark:
  - Files tested: `657`
  - Comparable files: `656`
  - Rust faster or equal: `4`
  - Rust slower: `652`
  - Materially slower: `227`
  - Rust failures: `1` (`src/ticker.res`: stack overflow)
  - Aggregate OCaml total: `4581.5ms`
  - Aggregate Rust total: `10729.0ms`
  - Aggregate Rust / OCaml ratio: `2.34x`
  - `Import.res` benchmark entry: OCaml `41.5ms`, Rust `323.1ms`, `7.78x`

Before/after for this specific change on the same benchmark command:

- before: aggregate ratio `2.39x`, aggregate Rust total `10991.0ms`,
  `Import.res` `328.6ms`
- after: aggregate ratio `2.34x`, aggregate Rust total `10729.0ms`,
  `Import.res` `323.1ms`

What landed in this step:

- `ctype::resolve_module_type_through_env_path` no longer resolves the parent
  module type recursively just to recover alias information for `Pdot`
  lookups
- the dotted child-module `MtySignature` path now copies from
  `typecore::copy_resolved_module_signature_for_path` /
  `copy_module_signature_in_resolved_path`-style qualified views instead of
  rebuilding a fresh child signature from the parent signature on every lookup
- dotted modtype and non-signature child-module cases now reuse the already
  resolved parent qualified signature from `typecore::resolve_module_signature_for_path`
  for child substitution

Next focus after this step:

- push the same env_lazy-backed detached-signature source-of-truth into the
  remaining manual child-substitution sites in `typemod` / shared module-type
  resolution
- keep prioritizing the module-signature-heavy cluster (`Import`, module alias
  tests, Belt set/map tests, JSX-heavy files) before secondary cleanups

## Session Update: Remove Duplicate CMI Signature Rewrite

Additional checkpoint from this worktree on `2026-04-14` after removing the
second whole-signature qualification pass from
`ctype::resolve_type_through_modules`:

- `sample` on repeated `Import.res` compiles now shows the dominant stack under
  `lookup_module_type_from_unpack_expr -> type_pack -> includemod::modtypes_inner`,
  with repeated `resolve_type_through_modules ->
  persistent_env::substitute_type_paths_in_sig`; it is no longer primarily
  spending time in `copy_lookup_signature_for_subst`
- focused import-family benchmark (`defunctor_make_test|Import`):
  - Files tested: `5`
  - Comparable files: `5`
  - Aggregate OCaml total: `67.5ms`
  - Aggregate Rust total: `324.2ms`
  - Aggregate Rust / OCaml ratio: `4.80x`
  - `Import.res` benchmark entry: OCaml `40.7ms`, Rust `274.4ms`, `6.74x`
- exact `Import.res` repro:
  - OCaml: `0.04s` (`/usr/bin/time -lp`)
  - Rust: `0.40s` (`/usr/bin/time -lp`)
  - Rust max RSS: about `70MB`
  - Rust peak footprint: about `55MB`
- focused import parity: unchanged at `1/4`, `283` hunk mismatches
- full typedtree parity: unchanged at `232/657`, `43117` hunk mismatches
- canonical corpus benchmark:
  - Files tested: `657`
  - Comparable files: `656`
  - Rust faster or equal: `4`
  - Rust slower: `652`
  - Materially slower: `224`
  - Rust failures: `1` (`src/ticker.res`: stack overflow)
  - Aggregate OCaml total: `5855.5ms`
  - Aggregate Rust total: `12137.5ms`
  - Aggregate Rust / OCaml ratio: `2.07x`
  - `Import.res` benchmark entry: OCaml `47.9ms`, Rust `282.6ms`, `5.90x`

What landed in this step:

- `ctype::resolve_type_through_modules` no longer reruns
  `substitute_type_paths_in_sig` /
  `substitute_sig_decl_paths_in_place` after
  `resolve_module_signature_through_cmi` has already returned the qualified
  signature view
- this keeps the existing parity checkpoint while removing one redundant
  whole-signature substitution pass from repeated type expansion through CMI
  lookups

What this means:

- one more eager whole-signature rewrite was removed from the import-heavy hot
  path without reopening the `Import*` / `DynamicImportModuleWithAlias` parity
  drift
- the corpus aggregate ratio improved modestly from `2.10x` to `2.07x`, which
  is directionally correct but still far from the OCaml-shaped target
- the remaining hot path is now clearer: repeated unpack/module-type comparison
  work in `includemod::modtypes_inner` plus the remaining qualification work
  reached through `resolve_type_through_modules`

## Session Update: Rejected `typemod` / `typecore` EnvLazy Pident Rollout

Attempted on `2026-04-14`:

- make `typemod::resolve_path_to_sig_impl` consult
  `typecore::resolve_module_signature_for_path` for additional `Pident`
  module-path cases so shared module-type resolution would use the cached
  qualified view as the source of truth
- make `typecore::resolve_letmodule_direct_type_family_root` read direct type
  families from `with_resolved_module_components_for_path` instead of copying a
  raw signature first
- also tried forcing `includemod::expand_module_type_in_env` through
  `ctype::resolve_module_type_through_env` for all non-`Papply` paths

What happened:

- the `includemod` variant was pure overhead and regressed the exact
  `Import.res` repro to about `0.40s` to `0.44s`; it should not be retried in
  that shape
- the narrower `typemod` + `typecore` variant improved the exact `Import.res`
  repro to about `0.25s` and improved the canonical corpus benchmark to:
  - Files tested: `657`
  - Comparable files: `656`
  - Rust faster or equal: `2`
  - Rust slower: `654`
  - Materially slower: `215`
  - Rust failures: `1` (`src/ticker.res`: stack overflow)
  - Aggregate OCaml total: `5070.8ms`
  - Aggregate Rust total: `10809.9ms`
  - Aggregate Rust / OCaml ratio: `2.13x`
  - `Import.res` benchmark entry: OCaml `46.4ms`, Rust `252.0ms`, `5.44x`
- but that same variant regressed typedtree parity in exactly the import-heavy
  family we are using as a guard:
  - focused import parity moved from `1/4`, `283` hunk mismatches to `1/4`,
    `313` hunk mismatches
  - full parity moved from `232/657`, `43117` hunk mismatches to `232/657`,
    `43147` hunk mismatches

Outcome:

- all code for that broader rollout was reverted
- current clean worktree measurements after the revert:
  - exact `Import.res` repro: Rust back to about `0.28s`
  - focused import parity: back to `1/4`, `283` hunk mismatches
- likely root cause: routing `typemod`'s `Pident`-based module-signature
  resolution through `resolve_module_signature_for_path` changes lazy forcing
  and stamp allocation order in the import path, even though it helps runtime
  performance

What the next agent should do:

- do not reintroduce the `typemod::resolve_path_to_sig_impl` `Pident`
  pre-check in its current form
- do not force `includemod::expand_module_type_in_env` through the env_lazy
  path for every local identifier; that was all cost and no benefit
- if revisiting shared module-type resolution, compare the OCaml
  `EnvLazy.components_of_module_maker` forcing order more directly before
  asking for cached qualified signatures from `typemod`

## Session Update: Route Dotted Shared Module-Type Scraping Through `env_lazy`

Additional checkpoint from this worktree on `2026-04-14` after routing dotted
shared module/modtype signature scraping through the env_lazy-backed qualified
view before falling back to raw recursive scans:

- exact `Import.res` repro:
  - OCaml: `0.07s` (`/usr/bin/time -lp`)
  - Rust: `0.27s` (`/usr/bin/time -lp`)
  - Rust max RSS: about `79MB`
  - Rust peak footprint: about `65MB`
- focused import parity: unchanged at `1/4`, `283` hunk mismatches
- full typedtree parity: unchanged at `232/657`, `43117` hunk mismatches
- canonical corpus benchmark:
  - Files tested: `657`
  - Comparable files: `656`
  - Rust faster or equal: `2`
  - Rust slower: `654`
  - Materially slower: `225`
  - Rust failures: `1` (`src/ticker.res`: stack overflow)
  - Aggregate OCaml total: `4652.8ms`
  - Aggregate Rust total: `10606.7ms`
  - Aggregate Rust / OCaml ratio: `2.28x`
  - `Import.res` benchmark entry: OCaml `43.6ms`, Rust `253.0ms`, `5.80x`

What landed in this step:

- `typemod::resolve_path_to_sig_impl` now tries
  `typecore::resolve_module_signature_for_path` /
  `lookup_modtype_in_resolved_path` for dotted paths before falling back to raw
  recursive signature scans
- `includemod::modtypes_inner` now tries
  `ctype::resolve_module_type_through_env` for dotted and persistent paths
  before the older local recursive module-type expansion
- `ctype::resolve_module_type_through_env_path` now prefers the shared
  env_lazy-backed qualified signature copy path for persistent `Pident`
  fallback before going back to direct CMI resolution

What this means:

- dotted shared module-type scraping no longer bypasses the env_lazy-backed
  qualified module view first
- the typedtree parity checkpoint stayed flat, so this routing change did not
  introduce a new parity regression
- the broader corpus benchmark did not yet show a clear speedup over the best
  earlier checkpoint, so the next session should keep pushing the OCaml-shaped
  source-of-truth path deeper into inclusion/pack resolution while reducing
  detached copies rather than broadening them

## Session Update: Cache Lazy Child Module/Modtype Qualification From Parent Views

Additional checkpoint from this worktree on `2026-04-14` after making
env_lazy-backed qualified parent components lazily cache dotted child
module/modtype qualification and route the hot dotted lookup helpers through
that cached child view:

- exact `Import.res` repro:
  - OCaml: `0.07s` (`/usr/bin/time -lp`)
  - Rust: `0.24s` to `0.26s` across three immediate `/usr/bin/time -lp`
    reruns after build
  - Rust max RSS: about `78MB` to `81MB`
  - Rust peak footprint: about `63MB` to `66MB`
- focused import/module-alias benchmark
  (`Import|global_module_alias_test|module_alias_test|test_include|bs_poly_set_test|bs_poly_map_test|bs_poly_mutable_set_test|bs_mutable_set_test`):
  - Files tested: `12`
  - Comparable files: `12`
  - Aggregate OCaml total: `154.2ms`
  - Aggregate Rust total: `699.6ms`
  - Aggregate Rust / OCaml ratio: `4.54x`
  - `Import.res`: OCaml `42.9ms`, Rust `239.0ms`, `5.58x`
  - `global_module_alias_test.res`: OCaml `16.7ms`, Rust `92.7ms`, `5.56x`
  - `bs_poly_set_test.res`: OCaml `13.9ms`, Rust `74.3ms`, `5.34x`
- full typedtree parity: unchanged at `232/657`, `43117` hunk mismatches
- canonical corpus benchmark:
  - Files tested: `657`
  - Comparable files: `656`
  - Rust faster or equal: `3`
  - Rust slower: `653`
  - Materially slower: `226`
  - Rust failures: `1` (`src/ticker.res`: stack overflow)
  - Aggregate OCaml total: `5430.0ms`
  - Aggregate Rust total: `11317.4ms`
  - Aggregate Rust / OCaml ratio: `2.08x`
  - `Import.res` benchmark entry: OCaml `44.1ms`, Rust `241.4ms`, `5.47x`

What landed in this step:

- `env_lazy::QualifiedModuleComponents` now lazily caches qualified dotted
  child `ModuleDeclaration` and `ModtypeDeclaration` values instead of
  re-running `substitute_type_paths_in_child_module_type` on every lookup
- `typecore::with_resolved_module_components_for_path` can now build a dotted
  child module's qualified components directly from the already-cached parent
  qualified view when the child resolves to a signature, instead of rebuilding
  the child signature pipeline from the raw module type first
- `typecore::lookup_module_in_resolved_path` /
  `lookup_modtype_in_resolved_path`, `ctype::resolve_module_type_through_env`,
  `typemod::lookup_module_type_by_lid`, and the shared typed-module extraction
  helpers now consume that cached child qualification path instead of doing
  fresh child substitution work per query
- access-path-only dotted lookup (`resolve_module_access_path_for_lid`) was left
  on the cheap raw slot/path path so the new lazy child qualification only
  forces when callers actually need the child module type/components, matching
  OCaml's split between `comp_modules` and `comp_components`

What this means:

- env_lazy is now carrying one more OCaml-shaped responsibility: qualified
  dotted child module/modtype forcing comes from cached parent views rather than
  ad hoc child-substitution helpers in each caller
- the canonical corpus moved from `2.20x` slower to `2.08x` slower without any
  new typedtree parity regression
- the import-heavy module-alias cluster improved again, but the project is
  still materially slower than OCaml and the remaining work is now mostly the
  residual inclusion/unpack/secondary-module-resolution costs above this child
  view cache

## Session Update: Preserve EnvLazy Sharing In `ctype`

Additional checkpoint from this worktree on `2026-04-14` after stopping
`ctype` from deep-copying env_lazy-qualified signatures and type declarations
after the qualified view has already been built:

- exact `Import.res` repro after rebuild:
  - OCaml: `0.07s` (`/usr/bin/time -lp`)
  - Rust: first rerun `0.40s`, then warmed reruns `0.24s`, `0.22s`, `0.22s`
  - Rust max RSS on warmed reruns: about `55.5MB`
  - Rust peak footprint on warmed reruns: about `42.2MB`
- canonical corpus benchmark:
  - Files tested: `657`
  - Comparable files: `657`
  - Rust faster or equal: `1`
  - Rust slower: `656`
  - Materially slower: `217`
  - OCaml failures: `0`
  - Rust failures: `0`
  - Aggregate OCaml total: `4655.8ms`
  - Aggregate Rust total: `10144.0ms`
  - Aggregate Rust / OCaml ratio: `2.18x`
  - `Import.res` benchmark entry: OCaml `41.5ms`, Rust `225.2ms`, `5.43x`
- full typedtree parity: unchanged at `232/657`, `43117` hunk mismatches

What landed in this step:

- `ctype::resolve_module_type_through_env_path` now reuses
  `typecore::resolve_module_signature_for_path` for env_lazy-backed signature
  cases instead of asking for a detached deep-copied signature first
- `ctype::resolve_signature_through_env_module_type` now preserves the sharing
  already present in env_lazy-qualified `MtySignature` values instead of
  re-running `copy_lookup_signature_for_subst`
- `ctype::resolve_type_item_through_env` now returns the env_lazy-qualified
  declaration graph directly, only cloning the outer declaration record, rather
  than re-running `copy_lookup_type_decl_for_subst` before self-manifest and
  strengthening checks

What this means:

- the env_lazy-qualified module view now remains the source of truth one step
  further into the hot `ctype` path instead of being immediately wrapped in a
  second fresh copy layer
- the exact `Import.res` repro keeps improving on warm runs while cutting peak
  memory again, which is consistent with preserving OCaml-shaped sharing rather
  than rebuilding equivalent type graphs
- full parity stayed flat, so this sharing-preserving rollout did not reopen
  the import-family stamp drift that killed the earlier broader env_lazy
  reroute attempt

## Session Update: Avoid Local Modtype Clone In `includemod`

Additional checkpoint from this worktree on `2026-04-14` after teaching
`includemod::modtypes_inner` to recurse through non-persistent local `Pident`
module/modtype paths by reference instead of cloning the expanded local module
type on every comparison:

- direct `-dtyped-sexp` inspection of `Import.res` shows the unpack/package
  path in the hot repro is the local modtype `BeltList`, not a dotted module
  path
- exact `Import.res` repro after rebuild:
  - OCaml: `0.07s` (`/usr/bin/time -lp`)
  - Rust: `0.26s`, then `0.26s` on the immediate warmed rerun
  - Rust max RSS: about `56.6MB` to `56.8MB`
  - Rust peak footprint: about `42.4MB` to `43.5MB`
- focused `Import.res` benchmark:
  - before this change: OCaml `48.0ms`, Rust `254.4ms`, `5.30x`
  - after this change: OCaml `47.8ms`, Rust `245.0ms`, `5.13x`
- full typedtree parity: unchanged at `232/657`, `43117` hunk mismatches
- canonical corpus benchmark:
  - Files tested: `657`
  - Comparable files: `657`
  - Rust faster or equal: `0`
  - Rust slower: `657`
  - Materially slower: `233`
  - OCaml failures: `0`
  - Rust failures: `0`
  - Aggregate OCaml total: `4946.8ms`
  - Aggregate Rust total: `11235.8ms`
  - Aggregate Rust / OCaml ratio: `2.27x`
  - `Import.res` benchmark entry: OCaml `59.0ms`, Rust `263.8ms`, `4.47x`

What landed in this step:

- `includemod::modtypes_inner` now has a narrow fast path for local
  non-persistent `Pident` module/modtype expansion: when the environment
  already holds the expanded `MtySignature`/`mtd_type`, it reuses that module
  type by reference and only falls back to the older owned expansion path for
  dotted/persistent/alias cases
- added `types::includemod::tests::test_local_modtype_ident_matches_signature`
  to lock the local module-type identifier inclusion case

## Session Update: Cache EnvLazy Alias-Scope Metadata In `Env`

Additional checkpoint from this worktree on `2026-04-14` after moving the
env_lazy cache-scope alias metadata into `Env` and memoizing the
`module-components` env-scope decision per environment:

- exact `Import.res` repro after release rebuild:
  - OCaml: `0.09s` cold (`/usr/bin/time -lp`)
  - Rust: cold rerun `0.32s`, then warmed reruns `0.17s`, `0.16s`, `0.16s`
  - Rust max RSS on warmed reruns: about `54MB` to `58MB`
  - Rust peak footprint on warmed reruns: about `41.7MB` to `43.3MB`
- canonical corpus benchmark:
  - Files tested: `657`
  - Comparable files: `657`
  - Rust faster or equal: `2`
  - Rust slower: `655`
  - Materially slower: `220`
  - OCaml failures: `0`
  - Rust failures: `0`
  - Aggregate OCaml total: `5747.7ms`
  - Aggregate Rust total: `11427.2ms`
  - Aggregate Rust / OCaml ratio: `1.99x`
  - `Import.res` benchmark entry: OCaml `48.4ms`, Rust `154.7ms`, `3.18x`
- full typedtree parity after clearing `.parity-cache/tests/*` files: unchanged
  at `232/657`, `43117` hunk mismatches

What landed in this step:

- `Env` now memoizes the active local module-alias list instead of rebuilding
  and sorting it from the modules table on every env_lazy cache-key lookup
- `Env` now memoizes whether a given module path needs env-scoped
  `module-components` caching, and invalidates that cache only when module
  bindings change
- `typecore::module_path_requires_env_scoped_cache` now uses that env-owned
  metadata instead of rescanning the environment every time
- added `types::env::tests::test_module_path_requires_env_scoped_cache_tracks_active_aliases`
  to lock the alias-cache invalidation behavior

What this means:

- the lazy qualified module-components path stayed behaviorally identical, but
  its own cache-key bookkeeping got substantially cheaper on import-heavy local
  alias stacks
- the exact `Import.res` warmed repro improved from the pre-change `0.23s` to
  about `0.16s` to `0.17s`, and the canonical corpus aggregate ratio moved
  below `2.0x` for the first time in this worktree
- the profile still shows the remaining cost clustered under
  `includemod::modtypes_inner`, `lookup_module_type_from_unpack_expr`, and the
  residual local module-type resolution/inclusion path rather than the old
  repeated whole-signature copy cliff

Next focus after this step:

- keep pushing the env_lazy/source-of-truth architecture into the remaining
  inclusion/unpack/local-module-type helpers without reintroducing the rejected
  `typemod::resolve_path_to_sig_impl` `Pident` reroute
- compare the remaining local `Pident` module-type forcing order against OCaml's
  env/components split, especially around `lookup_module_type_from_unpack_expr`
  and `includemod::modtypes_inner`

What this means:

- the hot `Import.res` unpack comparison path is still paying for repeated
  local modtype signature cloning, and this narrow sharing-preserving shortcut
  trims that cost without changing typedtree parity
- this is not the main env_lazy breakthrough: the broader 657-file corpus is
  still far slower than OCaml, so the next session still needs to push the
  OCaml-shaped lazy/shared module-type path deeper into inclusion/unpack work
  rather than stop at this local cleanup

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
- [x] Remove the duplicate CMI-signature qualification pass from
  `ctype::resolve_type_through_modules`
- [x] Re-measure `Import.res` and capture new timing/memory numbers
- [x] Re-sample the compiler and confirm the hot path moved away from
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
