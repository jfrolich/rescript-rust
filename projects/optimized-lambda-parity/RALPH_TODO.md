# Ralph TODO: Optimized Lambda Parity

**Last Updated:** 2026-04-12
**Status:** 208/657 (31.7%), 449 parity failures, 7862 hunks

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
- Optimized lambda parity: **208/657**
- Stamp-canonicalized parity: **208/657**
- Exact hunks: **7862**
- Stamp-canonicalized hunks: **7862**
- Largest current exact diffs:
  - `big_polyvar_test.res`: **1203** hunks
  - `belt_list_test.res`: **347** hunks
  - `stringmatch_test.res`: **284** hunks
  - `js_date_test.res`: **252** hunks
  - `bs_array_test.res`: **238** hunks

## Working Rules

1. **Read the OCaml source first.** Do not invent optimized-lambda behavior from the diff output.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Use hunk count as a navigation signal.** File count alone hides structural progress.
5. **Fix lowering, not the sexp printer.** `sexp_lambda.rs` should reflect produced lambda, not normalize it.
6. **Raw lambda parity is already complete.** All remaining differences are after the raw stage.
7. **Do not confuse `-dlambda-sexp` with later backend passes.** The parity target is the output printed immediately after `Lam_convert.convert`.

## Remaining Parity Failures

All **449** remaining failures are now real optimized-lambda lowering gaps, not a dump-path mismatch.

Current frontier characteristics:
- `-dlambda-sexp` and `-dlambda-sexp-locs` now route through raw lambda plus `raw_lambda::lower`.
- `raw_lambda/lower.rs` is no longer an identity shim.
- Small structural sanity checks now pass exactly:
  - `AsInUncurriedExternals.res`
  - `minimal_test.res`
- `js_array_test.res` is still a useful large-file guard at **207** hunks.
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

### the first milestone produced repo-wide movement
Verified focused checks:

- `AsInUncurriedExternals.res`: **exact parity**
- `minimal_test.res`: **exact parity**
- `js_array_test.res`: **207 hunks**

Authoritative repo-wide baseline moved from:

- **0/657**, **1631** hunks

to:

- **208/657**, **7862** hunks

The file-count improvement confirms the routing/lowering boundary is now real. The hunk increase is expected: parity is finally measuring the correct optimized stage instead of the old shortcut path.

## Root-Cause Frontiers

1. **Continue porting `Lam_convert.convert`**
   - module export tail shape
   - let-kind selection (`Strict`, `Alias`, `StrictOpt`, `Variable`)
   - JS-call primitive lowering
   - constant/block/pointer representation
   - module/coercion lowering forms
2. **Use smallest failures for quick structural validation**
   - `Coercion.res`
   - `DictInference.res`
   - `DictInternalRepresentation.res`
   - `DictPatternMatchingOptimization.res`
   - `DisambiguateOptionalFields.res`
3. **Use large files to validate that a rule generalizes**
   - `js_array_test.res`
   - `caml_compare_test.res`
   - `js_math_test.res`
   - `js_string_test.res`
   - `js_float_test.res`
4. **Treat later `lam_pass_*` work as out of direct parity scope**
   - only touch those passes if a shared infrastructure change requires it
   - do not spend cycles there while `raw_lambda/lower.rs` is still incomplete

## Immediate Next Milestone

1. Port the next `Lam_convert.convert` rules around module export tails and let-kind selection.
2. Re-test:
   - `Coercion.res`
   - `DictInference.res`
   - `DictInternalRepresentation.res`
   - `DictPatternMatchingOptimization.res`
3. Validate the same rule on:
   - `js_array_test.res`
   - `caml_compare_test.res`
4. Re-run:

```bash
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

5. Commit immediately after the next verified OCaml-aligned improvement.

## Session Log

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
