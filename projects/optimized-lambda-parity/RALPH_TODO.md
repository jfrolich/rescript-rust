# Ralph TODO: Optimized Lambda Parity

**Last Updated:** 2026-04-12
**Status:** 514/657 (78.2%), 143 parity failures, 610 hunks

## Goal

Achieve **100% optimized lambda parity** between the Rust compiler and the OCaml reference implementation using:

```bash
./scripts/test_lambda_parity.sh -j1
```

Execution order and phase gates live in `PLAN.md`.

## Current Baseline

Authoritative run:

```bash
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **514/657**
- Exact hunks: **610**
- Stamp-canonicalized parity: not re-baselined in this rerun
- Stamp-canonicalized hunks: not re-baselined in this rerun
- Largest current exact diffs:
  - `js_json_test.res`: **45** hunks
  - `coercion_module_alias_test.res`: **40** hunks
  - `mario_game.res`: **36** hunks
  - `bs_unwrap_test.res`: **21** hunks
  - `uncurried_default.args.res`: **16** hunks
  - `ticker.res`: **13** hunks

## Working Rules

1. **Read the OCaml source first.** Do not invent optimized-lambda behavior from the diff output.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Use hunk count as a navigation signal.** File count alone hides structural progress.
5. **Fix lowering, not the sexp printer.** `sexp_lambda.rs` should reflect produced lambda, not normalize it.
6. **Optimized work is still mostly post-raw.** Keep `-drawlambda` as a guardrail when changing raw-lambda construction; the end-of-session raw rerun below surfaced one residual exact raw failure outside this slice.
7. **Do not confuse `-dlambda-sexp` with later backend passes.** The parity target is the output printed immediately after `Lam_convert.convert`.

## Remaining Parity Failures

There are **143** remaining optimized-lambda failures after this slice. The dominant frontier is still post-raw lowering, not dump-path routing.

Current frontier characteristics:
- `-dlambda-sexp` and `-dlambda-sexp-locs` now route through raw lambda plus `raw_lambda::lower`.
- `raw_lambda/lower.rs` is no longer an identity shim.
- Small structural sanity checks now pass exactly:
  - `AsInUncurriedExternals.res`
  - `DerivingAccessorsCurried.res`
  - `DerivingAccessorsUncurried.res`
  - `DictInternalRepresentation.res`
  - `DictInference.res`
  - `DictPatternMatchingOptimization.res`
  - `DynamicImportModuleWithAlias.res`
  - `ExternalExtension.res`
  - `Import.res`
  - `VariantCoercion.res`
  - `minimal_test.res`
- `conditional/cond_a.res` now also passes exactly as a minimal assert-failure guard.
- `js_array_test.res` now also passes exactly as a large-file guard.
- `big_polyvar_test.res` now also passes exactly on the current authoritative baseline.
- `LetUnwrap.res` now also passes exactly after preserving named polyvariant hash metadata in raw match tests.
- `polyvar_test.res` now also passes exactly on the current authoritative baseline.
- export-aware alias retention now keeps OCaml's module-export alias lets, which removed both accessor-file failures.
- the focused `Lam.if_` assert-failure rewrite is now landed:
  - `stringmatch_test.res`: **exact parity** (down from **1 hunk** on the prior baseline)
  - `js_json_test.res`: **45 hunks** on a focused rerun, so its remaining diffs are no longer dominated by that one rewrite
- the next visible optimized frontier is the current exact-diff leaders (`js_json_test.res`, `coercion_module_alias_test.res`, `mario_game.res`, `bs_unwrap_test.res`, `uncurried_default.args.res`, `ticker.res`) plus the exception static-exit numbering cluster (`test_trywith.res`, `exception_raise_test.res`).
- a fresh full raw `-drawlambda` rerun reported **656/657** with one exact failure in `coercion_module_alias_test.res`; that looks separate from the assert-failure lowering slice and should be handled in a dedicated raw-parity session.
- Stamp canonicalization needs a fresh dedicated rerun; this slice was verified against exact parity output.

## Key Findings from Session 2026-04-12

### `Pextension_slot_eq` lowering moved the exception frontier
`compiler/core/lam_convert.ml` lowers `Pextension_slot_eq` by comparing the
exception id field (`RE_EXN_ID`) with `Pstringcomp Ceq`; Rust was still leaking
the raw primitive into optimized lambda dumps.

`compiler-rust/src/raw_lambda/lower.rs` now mirrors that `lam_prim` rule and has
a unit test covering the lowered `Pfield(0, Fld_record "RE_EXN_ID")` shape.

Verified focused checks:

- `test_trywith.res`: still failing, but now only **10 hunks**, all from static-exit numbering
- `exception_raise_test.res`: still failing, but now only **12 hunks**, again from static-exit numbering

Authoritative repo-wide baseline moved from:

- **501/657**, **680** hunks

to:

- **514/657**, **610** hunks

That is a gain of **13 files** and **70 hunks**. The next exception-oriented
lowering frontier is no longer slot comparison shape; it is static-catch /
static-raise numbering and aliasing.

### polyvariant constant-match metadata moved the frontier again
`compiler-rust/src/raw_lambda/convert.rs` and `compiler-rust/src/raw_lambda/matching.rs`
now keep `PointerInfo::PolyVariant` on hashed constant polyvariant equality tests
instead of degrading them to raw `"123a"` pointer strings too early.

That keeps `-drawlambda` parity intact while allowing `raw_lambda/lower.rs` to recover
OCaml's symbolic `Const_pointer "Tag"` form during optimized-lambda lowering.

Verified focused checks:

- `LetUnwrap.res`: **exact parity** (down from **1 hunk**)
- `more_poly_variant_test.res`: **3 hunks** (down from **9**)

Authoritative repo-wide baseline moved from:

- **496/657**, **724** hunks

to:

- **501/657**, **679** hunks

This confirms the remaining polyvariant frontier is no longer the simple constant-hash
comparison path. The next visible cluster is the broader `more_poly_variant_test.res` /
`poly_variant_test.res` family plus the existing large-file leaders.

### `Lam.if_` smart-constructor parity moved again
`compiler-rust/src/lambda/mod.rs` now mirrors the OCaml `Lam.seq` / `Lam.if_`
smart-constructor branches that were still missing for:

- `Pt_assertfalse` branches lowering to `seq`
- boolean `if a then true else false` / `if a then false else true`
- raise-then / non-constant-else lowering to `seq (if ... raise ... ()) else_`
- `Pisout` switch-failaction folding
- `Pisint` rewrites that reuse or invert nested integer predicates

That slice is covered by new unit tests in `lambda::tests` for:

- assert-false sequencing
- boolean-condition reuse and negation
- raise-then sequencing
- `Pisint` branch reuse

Verified focused checks:

- `stringmatch_test.res`: **exact parity**
- `js_json_test.res`: **45 hunks** unchanged

Authoritative repo-wide baseline moved from:

- **493/657**, **733** hunks

to:

- **496/657**, **724** hunks

This confirms the OCaml-aligned `Lam.if_` slice was real and useful, but also
confirms the remaining `js_json_test.res` / exception-control-flow cluster is no
longer explained by this single smart-constructor gap.

### dump routing is now correct
`compiler-rust/src/driver.rs` no longer prints `-dlambda-sexp` from the legacy typedtree-to-lambda shortcut.
The dump path now does:

```text
typedtree -> raw_lambda::convert -> raw_lambda::lower -> sexp_lambda
```

The JS backend path remains unchanged for now.

### the first real `Lam_convert.convert` slice is landed
`compiler-rust/src/raw_lambda/lower.rs` now performs real lowering work instead of
`raw.into_lowered()`.

Implemented slices include:
- alias-following through a lowering context
- application status lowering to `App_uncurry`
- constructor/pointer normalization needed by optimized lambda
- let/letrec rebuilding, including splitting non-recursive bindings out of `letrec`
- switch lowering, including offset-switch folding
- try/with lowering with `PwrapExn`
- initial primitive/module-lowering cases used by the small parity files

### constructor metadata had to survive the raw stage
To keep raw parity intact while enabling optimized lowering:
- `raw_lambda/convert.rs` now preserves constructor information on integer constants
- `raw_lambda/print.rs` prints constructor-tagged ints back as raw `0a`-style pointers
- lambda string-delimiter handling was extended for `*j` / `js` / `json` / backtick forms

### switch names and JS FFI lowering moved the frontier again
`compiler-rust/src/raw_lambda/matching.rs` now preserves constructor names for optimized
switch printing, and `compiler-rust/src/raw_lambda/convert.rs` now threads enough FFI
metadata into lowering to distinguish:

- blank JS calls that should become `Pjs_object_create`
- unit-returning JS calls that must lower as `seq(Pjs_call ..., ())`

That same slice is consumed in `compiler-rust/src/raw_lambda/lower.rs`, so the lambda
printer can stay dumb while the lowerer makes the OCaml-aligned constructor choice.

### the repo-wide baseline moved materially again
Verified focused checks:

- `AsInUncurriedExternals.res`: **exact parity**
- `DictInference.res`: **exact parity**
- `DictPatternMatchingOptimization.res`: **exact parity**
- `js_array_test.res`: **exact parity**

Authoritative repo-wide baseline moved from:

- **208/657**, **7862** hunks

to:

- **377/657**, **3723** hunks

This drop confirms the next `Lam_convert.convert` slice is landing in the right place:
constructor-name preservation plus JS-call result-kind lowering removed both small-file
structural mismatches and one of the major large-file guards.

### constructor runtime metadata now survives lowering
The next slice had to preserve more raw-stage detail without breaking `-drawlambda` parity:

- typed string constants now keep OCaml's plain-string delimiter as `DNone`
- constructor `@as(...)` payloads now survive typing and raw conversion for int/string/float/bigint/bool/null/undefined cases
- constant polymorphic variants now keep their source tag names alongside the hashed raw representation
- optimized lowering now uses that metadata to recover OCaml-aligned pointer, constructor, and switch shapes

This is what made `DictInternalRepresentation.res` and `VariantCoercion.res` drop out while
cutting `big_polyvar_test.res` roughly in half.

### primitive folding needs to match OCaml, but must stay crash-free
`raw_lambda/lower.rs` now folds the small set of binary integer primitives that OCaml's
`Lam_convert.convert` folds after constructor runtime tags have been resolved.

That slice initially introduced a divide-by-zero crash because `then_some(...)` eagerly
evaluated `wrapping_div` / `wrapping_rem`. The authoritative rerun is only valid after
switching those guards to lazy `then(|| ...)`, which restored Rust compile coverage to
**657/657**.

### the repo-wide baseline moved materially again
Verified focused checks:

- `DictInternalRepresentation.res`: **exact parity**
- `VariantCoercion.res`: **exact parity**
- `big_polyvar_test.res`: **602 hunks** (down from **1202**)

Authoritative repo-wide baseline moved from:

- **377/657**, **3723** hunks

to:

- **426/657**, **2006** hunks

This slice confirms the next broad lowering frontier is no longer constructor runtime tags.
The biggest remaining cluster is now the `big_polyvar_test.res` family around `Praw_js_code_exp`
argument shape and `Lglobal_module`/exception payload construction.

### imported-module and raw-js-code lowering moved the frontier again
`compiler-rust/src/raw_lambda/lower.rs` now mirrors the `Lam_convert.convert`
branches that were still missing for:

- `Pimport` argument lowering with OCaml's `~dynamic_import` scoping rules
- collapsing imported `let global-module = ... in ...` bundles back to a single
  `Lglobal_module ... true`
- `Praw_js_code_exp` / `Praw_js_code_stmt` payload recovery from raw string
  arguments into the primitive payload itself

That slice is covered by new lowerer unit tests for:

- imported field access becoming `Lglobal_module ... true`
- alias-wrapped module imports staying `false`
- imported let-bound global-module bundles collapsing correctly
- raw JS code primitives lowering to zero-arg payload forms

Verified focused checks:

- `DynamicImportModuleWithAlias.res`: **exact parity**
- `ExternalExtension.res`: **exact parity**
- `Import.res`: **1 hunk** remaining
- `big_polyvar_test.res`: **601 hunks** (down from **602**)

Authoritative repo-wide baseline moved from:

- **426/657**, **2006** hunks

to:

- **460/657**, **1859** hunks

This confirms the import/raw-JS slice is now mostly complete. The next visible
frontier in this area is the missing `Lam.if_` smart-constructor behavior that
still leaves `Import.res` with a constant-condition branch.

### constant-condition folding in `Lam.if_` moved the baseline again
`compiler-rust/src/lambda/mod.rs` now matches the first OCaml `Lam.if_` branch:
when the condition is a constant, the smart constructor returns the selected
branch instead of preserving `Lifthenelse`.

That is deliberately limited to the constant-condition case. The remaining
`Lam.if_` parity work is still in the smarter non-constant rewrites from
`compiler/core/lam.ml`.

Verified focused checks:

- `Import.res`: **exact parity**
- `LetUnwrap.res`: **19 hunks**
- `DerivingAccessorsCurried.res`: **1 hunk**
- `DerivingAccessorsUncurried.res`: **1 hunk**
- `big_polyvar_test.res`: **601 hunks**

Authoritative repo-wide baseline moved from:

- **460/657**, **1859** hunks

to:

- **461/657**, **1855** hunks

This confirms the constant-condition branch was the last blocker for
`Import.res`. The next structural frontier is the remaining `Lam.if_`
smart-constructor rewrites plus the alias/module-export shape still showing up
in the accessor files.

### direct-ident constructor switch names now honor `pat_env`
`compiler-rust/src/raw_lambda/matching.rs` now mirrors the OCaml
`matching_polyfill.ml` rule for direct constructor-type identifiers: recover
switch names from the typed pattern environment instead of resolving against an
empty environment.

That slice is intentionally narrow:

- direct `Path::Pident` constructor types now use `pat.pat_env`
- qualified paths still fall back to the old resolver for now because a broad
  `env.lookup_type` path introduced a `string_set.res` stack overflow
- a new unit test covers `result` constructor-name recovery through `pat_env`

Verified focused checks:

- `LetUnwrap.res`: **1 hunk** remaining (down from **19**)
- `string_set.res`: direct repro no longer crashes after narrowing lookup back
  away from `Pdot` resolution

Authoritative repo-wide baseline moved from:

- **461/657**, **1855** hunks

to:

- **461/657**, **1858** hunks

This is a correctness-aligned change, not a local parity win yet. The direct
`pat_env` recovery is still worth keeping because it matches OCaml for the
`Pident` case and removes the wrong switch-metadata shape from `LetUnwrap.res`;
the remaining work is to port the qualified-path lookup safely enough to avoid
reintroducing the `string_set.res` recursion and then clean up the constructor
literal / exception-tail regressions it exposes.

## Root-Cause Frontiers

1. **Continue porting `Lam_convert.convert`**
   - module export tail shape
   - let-kind selection (`Strict`, `Alias`, `StrictOpt`, `Variable`)
   - remaining non-constant `Lam.if_` smart-constructor behavior
   - remaining JS-call primitive lowering
   - remaining exception/module lowering forms outside the import/raw-JS slice
   - module/coercion lowering forms
2. **Use smallest failures for quick structural validation**
   - `LetUnwrap.res`
   - `coercion_module_alias_test.res`
   - `UncurriedExternals.res`
3. **Use large files to validate that a rule generalizes**
   - `big_polyvar_test.res`
   - `js_json_test.res`
   - `caml_compare_test.res`
   - `js_string_test.res`
   - `stringmatch_test.res`
4. **Treat later `lam_pass_*` work as out of direct parity scope**
   - only touch those passes if a shared infrastructure change requires it
   - do not spend cycles there while `raw_lambda/lower.rs` is still incomplete

## Immediate Next Milestone

1. Finish the next focused optimized-lambda gaps revealed by the small-file frontier:
   - constructor-literal recovery for `LetUnwrap.res`
   - quoted-identifier output parity in `coercion_module_alias_test.res`
2. Keep the larger-file watchlist on the remaining broad lowering frontier:
   - `big_polyvar_test.res`
   - `js_json_test.res`
   - `caml_compare_test.res`
   - `stringmatch_test.res`
3. Re-test:
   - `LetUnwrap.res`
   - `coercion_module_alias_test.res`
   - `UncurriedExternals.res`
4. Validate the same rule on:
   - `big_polyvar_test.res`
   - `js_json_test.res`
   - `caml_compare_test.res`
   - `stringmatch_test.res`
5. Re-run:

```bash
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

6. Commit immediately after the next verified OCaml-aligned improvement.

## Session Log

### 2026-04-12 (predef-exception lowering and plain loc strings)

Ran:

```bash
cargo build --release --manifest-path compiler-rust/Cargo.toml
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::lowers_predef_exception_global_module_to_string_constant -- --exact
timeout 300 ./scripts/test_lambda_parity.sh -j1 tests/tests/src/conditional/cond_a.res
timeout 300 ./scripts/test_lambda_parity.sh -j1 stringmatch_test
timeout 300 ./scripts/test_lambda_parity.sh -j1 --raw tests/tests/src/conditional/cond_a.res
timeout 1800 ./scripts/test_lambda_parity.sh -j1
timeout 1800 ./scripts/test_lambda_parity.sh -j1 --raw
```

Result:

- Optimized lambda:
  - OCaml compile coverage: **657/657**
  - Rust compile coverage: **657/657**
  - Optimized lambda parity: **493/657**
  - Stamp-canonicalized parity: **493/657**
  - Exact hunks: **733**
  - Stamp-canonicalized hunks: **733**
- Raw lambda guardrail:
  - OCaml compile coverage: **657/657**
  - Rust compile coverage: **657/657**
  - Raw lambda parity: **656/657**
  - Raw parity hunks: **2**

Key checkpoints:

- `conditional/cond_a.res`: passes
- `stringmatch_test.res`: **1 hunk** remaining
- focused `--raw tests/tests/src/conditional/cond_a.res`: passes
- `js_json_test.res`: **8 hunks**
- `big_polyvar_test.res`: **2 hunks**

This slice ports the `Lam_convert.convert` rule that treats predefined exceptions
like `Assert_failure` as string constants at the optimized-lambda boundary instead
of leaving them as `Lglobal_module`. The same pass also now preserves OCaml's plain
`DNone` delimiter on file-name strings threaded through assert-failure, match-failure,
and recursive-module location payloads. That combination removed the broad
`Assert_failure` / location-string shape mismatch across the suite and collapsed
`stringmatch_test.res` to a single remaining `Lam.if_` hunk.

The end-of-session full raw rerun reported one exact raw failure in
`coercion_module_alias_test.res`. The saved diff does not touch the new
predef-exception or location-string branches, so this commit keeps the session
scoped to the verified optimized-lambda improvement and leaves that raw exact-diff
drift for a separate follow-up.

### 2026-04-12 (export-aware alias retention for module exports)

Ran:

```bash
cargo test --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests -- --nocapture
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 600 ./scripts/test_lambda_parity.sh -j1 'DerivingAccessorsCurried|DerivingAccessorsUncurried|coercion_module_alias_test|LetUnwrap'
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **463/657**
- Stamp-canonicalized parity: **463/657**
- Exact hunks: **1853**
- Stamp-canonicalized hunks: **1853**

Key checkpoints:

- `DerivingAccessorsCurried.res`: passes
- `DerivingAccessorsUncurried.res`: passes
- `LetUnwrap.res`: **1 hunk**
- `coercion_module_alias_test.res`: **40** hunks
- next visible frontier: `LetUnwrap` constructor-literal recovery plus the quoted-identifier output mismatch in `coercion_module_alias_test.res`

This slice ports the `Lam_convert.convert` rule that keeps `Alias = Lvar`
bindings when the alias identifier is exported. Rust now discovers exported
idents from `Blk_module_export` metadata before lowering, keeps those alias lets,
and still rewrites downstream uses through the alias table the same way OCaml does.
That is what removed the accessor-file module-export tail mismatch.

### 2026-04-12 (constant-condition folding in `Lam.if_`)

Ran:

```bash
cargo test --manifest-path compiler-rust/Cargo.toml test_if_then_else_constant_fold
cargo test --manifest-path compiler-rust/Cargo.toml test_print_if
cargo build --release --manifest-path compiler-rust/Cargo.toml
timeout 600 ./scripts/test_lambda_parity.sh -j1 'Import.res|LetUnwrap.res|DerivingAccessorsCurried.res|DerivingAccessorsUncurried.res|big_polyvar_test.res'
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **461/657**
- Stamp-canonicalized parity: **461/657**
- Exact hunks: **1855**
- Stamp-canonicalized hunks: **1855**

Key checkpoints:

- `Import.res`: passes
- `LetUnwrap.res`: **19 hunks**
- `DerivingAccessorsCurried.res`: **1 hunk**
- `DerivingAccessorsUncurried.res`: **1 hunk**
- `big_polyvar_test.res`: **601 hunks**
- next visible frontier: non-constant `Lam.if_` rewrites and the accessor alias/module-export shape

### 2026-04-12 (dynamic import scoping and raw JS code payload lowering)

Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests -- --nocapture
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 180 ./scripts/test_lambda_parity.sh -j1 DynamicImportModuleWithAlias
timeout 180 ./scripts/test_lambda_parity.sh -j1 ExternalExtension
timeout 180 ./scripts/test_lambda_parity.sh -j1 Import
timeout 300 ./scripts/test_lambda_parity.sh -j1 big_polyvar_test
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **460/657**
- Stamp-canonicalized parity: **460/657**
- Exact hunks: **1859**
- Stamp-canonicalized hunks: **1859**

Key checkpoints:

- `DynamicImportModuleWithAlias.res`: passes
- `ExternalExtension.res`: passes
- `Import.res`: **1 hunk**
- `big_polyvar_test.res`: **601 hunks**
- next visible frontier: `Lam.if_` smart-constructor behavior

### 2026-04-12 (constructor runtime tags, DNone strings, polyvariant names, integer folding)

Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml lambda::sexp_lambda::tests -- --nocapture
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests -- --nocapture
timeout 180 ./scripts/test_lambda_parity.sh -j1 DictInternalRepresentation
timeout 180 ./scripts/test_lambda_parity.sh -j1 VariantCoercion
timeout 180 ./scripts/test_lambda_parity.sh -j1 big_polyvar_test
timeout 180 ./scripts/test_lambda_parity.sh -j1 div_by_zero_test
timeout 180 ./scripts/test_lambda_parity.sh -j1 gpr_1760_test
timeout 180 ./scripts/test_lambda_parity.sh -j1 jsoo_400_test
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **426/657**
- Stamp-canonicalized parity: **426/657**
- Exact hunks: **2006**
- Stamp-canonicalized hunks: **2006**

Key checkpoints:

- `DictInternalRepresentation.res`: passes
- `VariantCoercion.res`: passes
- `big_polyvar_test.res`: **602 hunks** (down from **1202**)
- `div_by_zero_test.res`: passes after the lazy divide/mod guard fix
- `gpr_1760_test.res`: passes after the lazy divide/mod guard fix
- `jsoo_400_test.res`: passes after the lazy divide/mod guard fix

### 2026-04-12 (switch names and JS FFI result kinds)

Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::lowers_blank_js_call_to_object_create -- --exact
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::keeps_unlabeled_blank_js_call_as_call -- --exact
cargo test --release --manifest-path compiler-rust/Cargo.toml lambda::sexp_lambda::tests::prints_switch_names_consts_and_blocks -- --exact
timeout 180 ./scripts/test_lambda_parity.sh -j1 DictInference
timeout 180 ./scripts/test_lambda_parity.sh -j1 js_array_test
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **377/657**
- Stamp-canonicalized parity: **377/657**
- Exact hunks: **3723**
- Stamp-canonicalized hunks: **3723**

Key checkpoints:

- `AsInUncurriedExternals.res`: passes
- `DictInference.res`: passes
- `DictPatternMatchingOptimization.res`: passes
- `js_array_test.res`: passes

### 2026-04-12 (routing fixed, first lowerer slice landed)

Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests
timeout 180 ./scripts/test_lambda_parity.sh -j1 AsInUncurriedExternals
timeout 180 ./scripts/test_lambda_parity.sh -j1 minimal_test
timeout 180 ./scripts/test_lambda_parity.sh -j1 js_array_test
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **208/657**
- Stamp-canonicalized parity: **208/657**
- Exact hunks: **7862**
- Stamp-canonicalized hunks: **7862**

Key checkpoints:

- `AsInUncurriedExternals.res`: passes
- `minimal_test.res`: passes
- `js_array_test.res`: 207 hunks

### 2026-04-11 (project created from first optimized baseline)

Ran:

```bash
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **0/657**
- Parity hunks: **1631**

The script-generated normalized diffs matched the exact baseline exactly, so stamp
canonicalization did not reduce a single failure. This was the starting point for the
optimized-lambda project.
