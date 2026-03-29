# Ralph TODO: Raw Lambda Parity

**Last Updated:** 2026-03-29
**Status:** 3 completed, 5 open

## Goal

Achieve **100% unoptimized lambda parity** between the Rust compiler and the OCaml reference implementation using:

```bash
./scripts/test_lambda_parity.sh --unoptimized -j1
```

This is parity for the **pre-optimization raw lambda stage** (`-drawlambda`), not the later optimized lambda sexp dump.

## Current Baseline

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Unoptimized lambda parity: **171/657**
- Parity hunks: **1028**

## Working Rules

1. **Read the OCaml source first.** Do not invent raw-lambda behavior from the diff output.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Use hunk count as a navigation signal.** File count alone hides structural progress.
5. **Do not fix raw parity in the printer.** Fix the raw IR construction first.
6. **Do not touch unrelated dirty files.** This worktree already has unrelated edits.

## Accepted Progress So Far

- [x] Added a dedicated raw-lambda project baseline and loop discipline.
- [x] Ported raw constructor binding fixes:
  - `34672b27c` `raw-lambda: preserve constructor payload bind order`
  - `8e5f8e7e9` `raw-lambda: bind constructor fields from scrutinee`
  - `8e2e77d4c` `raw-lambda: preserve irrefutable var aliases`
- [x] Ported raw array translation:
  - `9daa6db0b` `raw-lambda: port raw array translation`

## Highest-Impact Open Tasks

- [ ] **Port OCaml grouped constructor/or/alias matching from `matching.ml`**
  - Focus on grouped `switch` + `catch` compilation, not local heuristics.
  - Primary targets:
    - `combine_constructor`
    - `share_actions_sw`
    - `reintroduce_fail`
    - positive/default fail construction used for overlapping rows
  - Main Rust file:
    - `compiler-rust/src/raw_lambda/convert.rs`

- [ ] **Eliminate raw fallbacks in `VariantPatternMatchingSpreads.res`**
  - Known fallback sites from `RUST_RAW_FALLBACK_TRACE=1`:
    - `match:scrut=Texp_ident:pat=Tpat_alias:cases=2:loc=55:3-58:4`
    - `match:scrut=Texp_ident:pat=Tpat_construct:cases=4:loc=36:3-41:4`
    - `match:scrut=Texp_ident:pat=Tpat_alias:cases=3:loc=29:3-33:4`
    - `match:scrut=Texp_ident:pat=Tpat_alias:cases=3:loc=22:3-26:4`
  - Required outcome:
    - OCaml-like grouped `switch`/`catch` raw shape instead of lowered-style `if` ladders

- [ ] **Port raw module alias/coercion handling from `translmod.ml`**
  - The remaining `Import.res` mismatch is not just path normalization.
  - Investigate OCaml raw handling for:
    - `Mty_alias (Mta_absent, _)`
    - `lambda_module_alias`
    - `apply_coercion`
  - Ensure Rust raw module translation mirrors OCaml before lowering.

- [ ] **Separate true raw-stage construction from later lowered-lambda behavior**
  - Audit `raw_lambda/mod.rs`, `convert.rs`, and `driver.rs`.
  - Remove places where raw translation still inherits lowered JS-oriented behavior.
  - The raw stage must stand on its own functionally, even if later lowering still consumes it.

- [ ] **Track hunk-leading clusters, not only file totals**
  - After each authoritative run, record the biggest remaining hunk clusters.
  - Use the cache under `.parity-cache/lambda/` and prefer structural clusters over smallest diffs.

## Current Evidence / Findings

- The raw stage already has separate scaffolding:
  - `compiler-rust/src/raw_lambda/mod.rs`
  - `compiler-rust/src/raw_lambda/convert.rs`
  - `compiler-rust/src/raw_lambda/print.rs`
- But the stage is not yet fully independent from lowered lambda behavior.
- `VariantPatternMatchingSpreads.res` and `VariantPatternMatchingSpreadsWithPayloads.res` are good canaries for grouped constructor matching.
- `Import.res` is the best canary for raw module alias/coercion mismatch.
- Local canary improvements often reduce structural distance without moving the global file count. Keep tracking hunk movement.

## Loop Checklist

For each iteration:

- [ ] Run `./scripts/test_lambda_parity.sh --unoptimized -j1`
- [ ] Pick one root-cause cluster
- [ ] Read the matching OCaml source
- [ ] Implement the Rust port
- [ ] Re-run focused checks
- [ ] Re-run the authoritative baseline
- [ ] Update this file with before/after counts and findings
- [ ] Commit immediately if the change is verified OCaml-aligned

## Session Log

### 2026-03-29

- Baseline recorded at **171/657** parity with **1028** hunks.
- Confirmed that raw parity work must target the real OCaml raw stage, not printer normalization.
- Confirmed current highest-value next task is the grouped constructor/or/alias path from `compiler/ml/matching.ml`.
