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
- Unoptimized lambda parity: **174/657**
- Parity hunks: **1038**

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

### 2026-03-30

Starting parity: **171/657** with **1028** hunks.
Current parity: **172/657** with **1032** hunks.

**Analysis**: 485 failing files split into:
- 211 **ident-only** files (333 hunks): Structurally identical, but different ident stamp numbers from type checker
- 274 **structural** files (694 hunks): Real differences in raw lambda output

**Ident-only files**: Stamp offsets range from -117 to +117, most common -1 (34 files). Stamps come from type checker, not raw lambda. No single fix addresses all.

**Structural patterns** across 274 files:
- 74 files: missing `match/N =a` bindings for unused constructor fields → **FIXED** (d02e9c688)
- 56 files: missing catch/exit wrapping for default cases
- 51 files: `field:tag` access instead of switch dispatch
- 23 files: different module field indices (e.g. `epsilon_float/10` vs `/92`)
- 22 files: missing switch construct

**Commits this session**:
1. `c091b0e53` raw-lambda: port or-pattern support in constructor matching
   - Flatten Tpat_or into individual cases with shared body via catch/exit
   - Reduce raw-match fallbacks (fib.res: 1→0, variantsMatching: 8→5)
2. `83c1720ad` raw-lambda: skip identity functor coercion wrapping (171→172)
   - Tcoerce_functor(none, none) = identity, don't eta-expand
3. `7a1477735` raw-lambda: port @inline attribute on functor module bindings
   - Extract @inline(always/never) from mb_attributes
4. `d02e9c688` raw-lambda: bind constructor fields for wildcard patterns
   - Create (let (match/N =a (field:var/K scrut)) body) for Tpat_any args

**Key findings**:
- Lowered Lambda fallback always produces JS-oriented if-chains, never switch/catch
- All switch/catch in raw lambda must come from the raw lambda matchers, not fallback
- Functor wrapper (eta-expansion) was caused by Rust's module typing producing Tcoerce_functor(none,none) instead of OCaml's Tcoerce_none
- Field index differences (e.g. Pervasives field positions) are module system issues, not raw lambda

### 2026-03-29

- Baseline recorded at **171/657** parity with **1028** hunks.
- Confirmed that raw parity work must target the real OCaml raw stage, not printer normalization.
- Confirmed current highest-value next task is the grouped constructor/or/alias path from `compiler/ml/matching.ml`.
