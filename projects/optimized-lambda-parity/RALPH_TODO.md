# Ralph TODO: Optimized Lambda Parity

**Last Updated:** 2026-04-12
**Status:** 461/657 (70.2%), 196 parity failures, 1855 hunks

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
- Optimized lambda parity: **461/657**
- Stamp-canonicalized parity: **461/657**
- Exact hunks: **1855**
- Stamp-canonicalized hunks: **1855**
- Largest current exact diffs:
  - `big_polyvar_test.res`: **601** hunks
  - `stringmatch_test.res`: **284** hunks
  - `bs_queue_test.res`: **81** hunks
  - `coercion_module_alias_test.res`: **40** hunks
  - `mario_game.res`: **37** hunks

## Working Rules

1. **Read the OCaml source first.** Do not invent optimized-lambda behavior from the diff output.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Use hunk count as a navigation signal.** File count alone hides structural progress.
5. **Fix lowering, not the sexp printer.** `sexp_lambda.rs` should reflect produced lambda, not normalize it.
6. **Raw lambda parity is already complete.** All remaining differences are after the raw stage.
7. **Do not confuse `-dlambda-sexp` with later backend passes.** The parity target is the output printed immediately after `Lam_convert.convert`.

## Remaining Parity Failures

All **196** remaining failures are now real optimized-lambda lowering gaps, not a dump-path mismatch.

Current frontier characteristics:
- `-dlambda-sexp` and `-dlambda-sexp-locs` now route through raw lambda plus `raw_lambda::lower`.
- `raw_lambda/lower.rs` is no longer an identity shim.
- Small structural sanity checks now pass exactly:
  - `AsInUncurriedExternals.res`
  - `DictInternalRepresentation.res`
  - `DictInference.res`
  - `DictPatternMatchingOptimization.res`
  - `DynamicImportModuleWithAlias.res`
  - `ExternalExtension.res`
  - `Import.res`
  - `VariantCoercion.res`
  - `minimal_test.res`
- `js_array_test.res` now also passes exactly as a large-file guard.
- constant-condition folding in `Lam.if_` is now landed; the remaining `Lam.if_` frontier is the non-constant smart-constructor behavior still visible in `LetUnwrap.res`.
- `big_polyvar_test.res` dropped from **1202** hunks to **601** hunks.
- Stamp canonicalization still does not reduce the baseline at all.

## Key Findings from Session 2026-04-12

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
   - `DerivingAccessorsCurried.res`
   - `DerivingAccessorsUncurried.res`
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

1. Port the next `Lam.if_` smart-constructor slices that OCaml applies during lowering after constant-condition folding.
2. Re-test:
   - `LetUnwrap.res`
   - `DerivingAccessorsCurried.res`
   - `DerivingAccessorsUncurried.res`
3. Validate the same rule on:
   - `big_polyvar_test.res`
   - `js_json_test.res`
   - `caml_compare_test.res`
   - `stringmatch_test.res`
4. Re-run:

```bash
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

5. Commit immediately after the next verified OCaml-aligned improvement.

## Session Log

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
