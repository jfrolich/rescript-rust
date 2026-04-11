# Ralph TODO: Raw Lambda Parity

**Last Updated:** 2026-04-11
**Status:** 626/657 (95.3%), 31 failures, 89 hunks

## Goal

Achieve **100% unoptimized lambda parity** between the Rust compiler and the OCaml reference implementation using:

```bash
CANONICAL_STAMPS=1 ./scripts/test_lambda_parity.sh --raw
```

## Current Baseline

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Unoptimized lambda parity: **626/657**
- Parity hunks: **89**
- Canonicalization: per-function stamp/exit reset (`scripts/canonicalize_lambda_stamps.py`)

## Working Rules

1. **Read the OCaml source first.** Do not invent raw-lambda behavior from the diff output.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Use hunk count as a navigation signal.** File count alone hides structural progress.
5. **Log in BOTH compilers to compare behavior.** Add eprintln in Rust, Printf.eprintf in OCaml.
6. **The typed trees are identical.** ALL remaining differences are in the lambda conversion stage.

## Remaining 31 Failures by Category

### Matching compiler: split_precompile case partitioning (~15 files, ~50 hunks)
test_set(13), inline_map2_test(9), set_gen(6), mario_game(5), gpr_1698_test(5),
exception_raise_test(5), bigint_test(6), more_poly_variant_test(3), gpr_1150(3),
inline_record_test(1), inline_condition_with_pattern_matching(1), int_poly_var(1),
UntaggedVariants(1), exception_rebound_err_test(1)

**Root cause confirmed:** `do_split_or` partitioning is IDENTICAL between OCaml and Rust.
The switch case differences come from the INNER compilation after flattening. Specifically,
`compile_flattened` → `compile_match` → `comp_match_handlers` produces different exit ID
structures. All unseen constructors map to the SAME exit (defs has 1 entry) because
`reintroduce_fail` removes explicit cases when 3+ share the same exit.

**Key finding:** OCaml's `scan_def` produces different exits per unseen constructor because
it has MULTIPLE default entries. Rust has only 1. But `do_split_or` partitioning (which
creates defaults via `cons_next_or`) is identical — both produce `no=EMPTY`.

**Next investigation:** The difference must be in `compile_flattened` → `compile_match`
→ `split_precompile` for the FLATTENED sub-problems. Each flattened arg produces its own
`split_precompile` call which may create different `nexts` (catch handlers with exit IDs).
Compare the INNER `split_precompile` calls between OCaml and Rust.

### Module coercion (~5 files, ~11 hunks)
coercion_module_alias_test(7), Import(1), offset(1), DynamicImportModuleWithAlias(1),
derive_projector_test(1)

**Issues:**
- `strengthen_module_type_for_inclusion_path` creates mismatches for modules with value shadowing
- Module alias paths not normalized (pr6726 uses `field:All/0 ExtUnix/1` instead of `ExtUnixAll/1`)
- Include signatures have extra entries from @deriving PPX
- Recursive module init shapes wrong (components_of_module_maker not implemented)

### JSX PPX field positions (~3 files, ~7 hunks)
jsx_preserve_test(5), jsx_optional_props_test(1), async_jsx(1)

**Root cause:** `@react.component` generates TWO `let make` bindings (original + wrapper).
`signature_runtime_value` returns position of LAST occurrence (1), but module block
deduplication keeps LAST value at position 0. OCaml's env stores simplified signatures.

### Dict pattern compilation (~5 files, ~7 hunks)
DictInternalRepresentation(1), DictPatternMatchingOptimization(1), stdlib_Stdlib_DictTests(1),
pattern_match_json(1), json_decorders(2)

**Issue:** OCaml uses typed field accesses for Dict patterns. Rust uses option checks.

### Other (~6 files, ~7 hunks)
bs_poly_map_test(2), stdlib_Stdlib_JsonTests(1), recmodule(1), pr6726(1)

**Issues:** some_not_nested type expansion, stamp differences, module aliases, recursive module shapes

## Key Findings from Session 2026-04-10/11

### do_split_or is identical
Added logging to BOTH OCaml (`Printf.eprintf`) and Rust (`eprintln!`) for `do_split_or`.
The case partitioning into `before`/`ors`/`no` is IDENTICAL. Both produce `no=EMPTY` for
`gpr_1698_test`, meaning `cons_next_or` never creates new default entries.

### The difference is in inner compilation
The outer `split_precompile` produces 8 nexts in both compilers. But the INNER compilation
of flattened sub-problems produces different switch structures. The inner `compile_match`
calls `split_precompile` again for each arg, and THESE inner splits may differ.

### make_key / up_ok_action comparison
OCaml uses structural equality (`=`) on normalized lambdas. Rust uses string comparison
via `lambda_to_string`. Both `make_key` implementations are identical. The `up_ok_action`
results should be equivalent for normalized lambdas.

### reintroduce_fail is the proximate cause
When all unseen constructors share the same exit ID, `reintroduce_fail` (threshold >= 3)
removes explicit cases and replaces with `default:`. OCaml has different exits per
constructor (from multiple default entries), so `reintroduce_fail` doesn't trigger.

### scan_def fail-case order now matches OCaml
Rust `scan_def` was building the positive-fail constructor list in the reverse group order.
OCaml folds `env` in list order and prepends each group ahead of the accumulator, which
restores oldest-first constructor groups. The Rust port now matches that constructor-list
ordering while keeping the current jump-context workaround in place.

**Result:** full raw baseline stays **626/657** with **89** hunks. This is a verified
OCaml-aligned cleanup, but it does NOT fix the remaining inner-handler mismatch by itself.

**Next investigation:** switching the jump side of `scan_def` from the current outer-context
workaround back to OCaml's `ctx_lub (list_as_pat pats) ctx` still exposes `ctx_lshift`
panics in `gpr_1698_test`, `inline_map2_test`, and `test_set`. The remaining bug is in the
downstream context remapping, not in `do_split_or`.

### get_mins order now matches OCaml
Rust `get_mins` was preserving survivors in forward order, while OCaml prepends survivors on
each pass. The helper now matches OCaml's selection order exactly.

**Result:** full raw baseline still stays **626/657** with **89** hunks. This confirms the
remaining raw-lambda mismatch is not just a context-order artifact inside `get_mins`.

## Session Log

### 2026-04-10/11 (major session)

Starting parity: **610/657** (from previous typed tree parity work)
Final parity: **626/657** with **89** hunks

**18 commits:**
1. `770ae1801` Fix double #fn_mk wrapping for uncurried Record_unboxed encoding
2. `5b48507d3` Fix function flattening to match OCaml's transl_function conditions
3. `8ee2c9ac4` Add type-specialized primitives to raw lambda converter
4. `3eb48bfe5` Fix @as(undefined) attribute parsing for type_cannot_contain_undefined
5. `ddbfd86b3` Fix unboxed constructor inline record field extraction
6. `cebb6b6ee` Fix record spread setfield ordering to match OCaml's fold_left
7. `4351acc65` Fix comparison specialization using expression env instead of initial env
8. `9fdfd523b` Refactor is_base_type to accept env parameter
9. `8d8ef77bd` Improve stamp canonicalization with per-function scope reset
10. `480de0ea8` Enable functor constraint coercion computation + recursion guard
11. `3a4379cb6` Fix function param pattern binding order to match OCaml
12. `786369886` Skip module strengthening for same-stamp modules in signature_item
13. `fc7b581e4` Route function param patterns through matching compiler for lower_bind
14. `b5fe704ad` Don't skip Tpat_alias patterns in function param processing

**Key techniques used:**
- Per-function stamp/exit canonicalization in Python script
- Route function params through `full_matching::for_function` for `lower_bind` behavior
- Use expression's stored env for comparison specialization
- Same-stamp module skip in includemod to avoid false Tcoerce_structure
- Recursion depth guard in modtypes_inner for Pmty_functor

### 2026-04-11 (scan_def ordering)

Verified against OCaml that `scan_def` builds its positive-fail constructor list by
folding `env` in list order and prepending each group's constructors ahead of the
accumulator. Updated Rust to match that constructor-list ordering.

**Baseline after change:** still **626/657** with **89** hunks.

**Important follow-up:** changing the jump side of `scan_def` to full OCaml semantics
(`ctx_lub (list_as_pat pats) ctx`) still crashes several focused matching files, so the
remaining divergence is in later context remapping / handler compilation, not in the
constructor-list ordering itself.

### 2026-04-11 (get_mins ordering)

Aligned Rust `get_mins` with OCaml's survivor ordering by prepending retained elements on
each selection pass instead of appending them.

**Baseline after change:** still **626/657** with **89** hunks.

**Takeaway:** the remaining inner-handler mismatch is not explained by `get_mins` ordering
alone. The next likely root cause is still later context remapping during handler
compilation (`compile_list`, `compile_orhandlers`, or the downstream `ctx_*` transforms).
