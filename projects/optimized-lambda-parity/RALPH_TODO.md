# Ralph TODO: Optimized Lambda Parity

**Last Updated:** 2026-04-11
**Status:** 0/657 (0%), 657 parity failures, 1631 hunks

## Goal

Achieve **100% optimized lambda parity** between the Rust compiler and the OCaml reference implementation using:

```bash
./scripts/test_lambda_parity.sh -j1
```

## Current Baseline

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657** on the 1-way authoritative run
- Optimized lambda parity: **0/657**
- Stamp-canonicalized parity: **0/657**
- Parity hunks: **1631**
- Stamp-canonicalized hunks: **1631**
- Largest current exact diffs:
  - `js_array_test.res`: **69** hunks
  - `caml_compare_test.res`: **54** hunks
  - `js_math_test.res`: **50** hunks
  - `js_string_test.res`: **42** hunks
  - `js_float_test.res`: **38** hunks

## Working Rules

1. **Read the OCaml source first.** Do not invent optimized-lambda behavior from the diff output.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Use hunk count as a navigation signal.** File count alone hides structural progress.
5. **Fix lowering and passes, not the sexp printer.** `sexp_lambda.rs` should reflect produced lambda, not normalize it.
6. **Raw lambda parity is already complete.** All remaining differences are after the raw stage.

## Remaining Parity Failures

All **657** files still fail optimized-lambda parity.

Current frontier characteristics:
- The smallest failures are already structural 1-hunk diffs, not just stamp noise.
- Stamp canonicalization does not improve the baseline at all.
- The current Rust `-dlambda-sexp` path is still using the legacy typedtree-to-lambda shortcut.

## Key Findings from Session 2026-04-11

### raw lambda parity is complete, but optimized parity still bypasses that work
The current Rust `-dlambda-sexp` path in `compiler-rust/src/driver.rs` still constructs
lambda with `lambda::convert::LambdaConverter::convert_structure(&typed_structure)` and
prints that directly. OCaml prints optimized lambda after `Lam_convert.convert` and the
pass pipeline inside `lam_compile_main.ml`.

This means optimized parity is currently measuring the old shortcut path, not the real
OCaml-aligned raw-lambda-plus-passes pipeline.

### the raw-to-lowered boundary is still an identity conversion
`compiler-rust/src/raw_lambda/lower.rs` currently does:

```rust
pub fn lower_to_lambda(raw: RawLambda) -> Lambda {
    raw.into_lowered()
}
```

That is not an OCaml `Lam_convert.convert` port. It confirms the optimized stage still
needs a real conversion boundary and pass pipeline.

### stamp canonicalization does not help the current baseline
The parity script already writes exact diffs and stamp-canonicalized normalized diffs.
The normalized baseline is identical to the exact one:

- exact parity: **0/657**, **1631** hunks
- normalized parity: **0/657**, **1631** hunks

This means stamp numbering is not the primary problem. The current gap is stage shape and
pass behavior.

### small diffs already show stage-structure mismatches
`AsInUncurriedExternals.res` is only a 1-hunk diff, but it already shows major pipeline
differences:

- OCaml emits nested `Llet Strict` structure with module-export assembly
- Rust emits `Lsequence` plus `Llet Alias`
- OCaml uses the expected call/application shapes
- Rust emits a different `Pjs_call` / `App_na` / constant structure

These are not printer formatting issues.

### simple files still miss the optimized tail shape
`minimal_test.res` shows the raw data-structure shape is still off in optimized output:

- OCaml ends with the expected module-export block
- Rust ends with `Const_js_undefined true`
- list/block construction shape also differs

This is another signal that the optimized pipeline itself has not been ported yet.

## Root-Cause Frontiers

1. **Route `-dlambda-sexp` through the real optimized path**
   - Stop using the legacy `lambda::convert` shortcut as the parity target
   - Start from the now-correct raw lambda stage
2. **Port `Lam_convert.convert`**
   - Replace the identity `raw.into_lowered()` boundary
   - Match OCaml's lowering decisions and data sharing
3. **Port the pass pipeline in OCaml order**
   - `Lam_pass_deep_flatten`
   - `Lam_pass_exits`
   - `Lam_pass_remove_alias`
   - `Lam_pass_alpha_conversion`
   - Any downstream passes required before parity converges
4. **Use smallest failures for quick structural validation**
   - `AsInUncurriedExternals.res`
   - `Coercion.res`
   - `DictInference.res`
   - `DictInternalRepresentation.res`
   - `DictPatternMatchingOptimization.res`
5. **Use largest failures for pass-order validation**
   - `js_array_test.res`
   - `caml_compare_test.res`
   - `js_math_test.res`
   - `js_string_test.res`
   - `js_float_test.res`

## Session Log

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
canonicalization did not reduce a single failure. This is the starting point for the
optimized-lambda project.
