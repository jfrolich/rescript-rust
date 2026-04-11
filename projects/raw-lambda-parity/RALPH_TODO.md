# Ralph TODO: Raw Lambda Parity

**Last Updated:** 2026-04-11
**Status:** 628/657 (95.6%), 29 failures, 79 hunks

## Goal

Achieve **100% unoptimized lambda parity** between the Rust compiler and the OCaml reference implementation using:

```bash
CANONICAL_STAMPS=1 ./scripts/test_lambda_parity.sh --raw
```

## Current Baseline

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Unoptimized lambda parity: **628/657**
- Parity hunks: **79**
- Canonicalization: per-function stamp/exit reset (`scripts/canonicalize_lambda_stamps.py`)

## Working Rules

1. **Read the OCaml source first.** Do not invent raw-lambda behavior from the diff output.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Use hunk count as a navigation signal.** File count alone hides structural progress.
5. **Log in BOTH compilers to compare behavior.** Add eprintln in Rust, Printf.eprintf in OCaml.
6. **The typed trees are identical.** ALL remaining differences are in the lambda conversion stage.

## Remaining 31 Failures by Category

### Matching compiler: recursive default chaining in split_precompile (~13 files, ~44 hunks)
test_set(13), inline_map2_test(9), set_gen(6), mario_game(5), exception_raise_test(5),
bigint_test(6), more_poly_variant_test(3), gpr_1150(3), inline_record_test(1),
inline_condition_with_pattern_matching(1), int_poly_var(1), UntaggedVariants(1)

**Root cause confirmed:** `do_split_or` partitioning is IDENTICAL between OCaml and Rust,
but the recursive split helpers were rebuilding defaults from the OUTER `def` instead of
the recursive branch's `top_default`. That collapsed OCaml's cumulative default suffixes
like `[10,9,8,7,6,5,4,3]` down to `[10]` in Rust.

**Result of fix:** Rust now threads `top_default` through `cons_next_or`, `split_exc`,
`split_noexc`, `split_ex`, and `split_noex`, matching OCaml's recursive default chaining.
That fixes `gpr_1698_test`, removes `exception_rebound_err_test`, and drops raw hunks
from **85** to **79**.

**Next investigation:** The remaining matching failures are no longer caused by collapsed
default suffixes. Focus next on the specific inner handler/default combinations that still
diverge in `test_set`, `set_gen`, and `inline_map2_test`.

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

### scan_def jump contexts now match OCaml
Rust `scan_def` now uses OCaml's real jump context again:
`ctx_lub (list_as_pat pats) ctx`. The crash on `gpr_1698_test`, `inline_map2_test`,
`test_set`, and `string_set` was not in `scan_def` itself. The real bug was in
`get_variant_constructors`: qualified `Pdot` result types like `Set_gen.t` were hitting
`Env.lookup_type` leaf fallback and resolving to the local alias `type t = Set_gen.t<elt>`
instead of the parent module's actual variant declaration. That forced `complete_pats_constrs`
to synthesize a fake one-arg unseen constructor and poisoned the downstream contexts.

The Rust port now:
- requires exact-path matches for `env.lookup_type` / `lookup_type_decl_for_path_pub`
- resolves `Pdot(parent, name)` through the parent module signature when the direct type
  lookup is abstract or alias-backed

**Result:** full raw baseline stays **626/657** with **85** hunks. This is a verified
OCaml-aligned fix that restores full compile coverage under the precise `scan_def` port and
removes four raw diff hunks, but it does NOT fix the remaining inner-handler mismatch by
itself.

### recursive split default chaining now matches OCaml
OCaml's recursive split helpers rebuild each new default entry on top of the recursive
branch's `top_default`, not on top of the caller's incoming `def`. Rust had the right
`cons_default` helper, but several recursive sites fed it the wrong environment, which
collapsed cumulative default suffixes during inner `split_precompile`.

The Rust port now threads recursive `top_default` through:
- `cons_next_or`
- `split_exc`
- `split_noexc`
- `split_ex`
- `split_noex`

**Result:** full raw baseline improves to **628/657** with **79** hunks. `gpr_1698_test`
now reaches full raw parity, and `exception_rebound_err_test` drops out of the failure set.

### do_for_multiple_match flattening no longer threads TypeContext
OCaml's flattened multi-match path explicitly calls `split_precompile None pm1`.
Rust had been threading `Some(ctx_ref)` into that single call site, which let
`simplify_cases` see extra type information during flatten precompilation that
OCaml never supplies there.

Rust now matches the OCaml entry point exactly:
- `do_for_multiple_match` calls `split_precompile(None, &None, &pm1, ...)`

**Result:** full raw baseline still stays **626/657** with **85** hunks, and the focused
matching cluster (`gpr_1698_test`, `test_set`, `set_gen`, `inline_map2_test`) is unchanged.
This keeps the control flow aligned with OCaml and confirms the remaining mismatch is
deeper than this top-level flattened-entry context.

### get_mins order now matches OCaml
Rust `get_mins` was preserving survivors in forward order, while OCaml prepends survivors on
each pass. The helper now matches OCaml's selection order exactly.

**Result:** full raw baseline still stays **626/657** with **89** hunks. This confirms the
remaining raw-lambda mismatch is not just a context-order artifact inside `get_mins`.

### compile_list recursion now matches OCaml
Rust `compile_list` used an iterative accumulator, while OCaml prepends the current
`jumps_map ctx_combine total1` result and only then recurses into the remaining division
cells. The Rust helper now follows the OCaml recursion directly.

**Result:** full raw baseline still stays **626/657** with **89** hunks. This does not move
the remaining inner-matching failures, but it removes another ordering difference from the
matching runtime.

### compile_orhandlers recursion now matches OCaml
Rust `compile_orhandlers` used an imperative loop, while OCaml recursively threads `r` and
`total_r` through the handler list. The Rust helper now follows the OCaml recursion
directly.

**Result:** full raw baseline still stays **626/657** with **89** hunks. The remaining
inner-matching failures survive this port too, so the root cause is narrower than the
high-level handler traversal shape.

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

### 2026-04-11 (scan_def jump contexts + qualified variant lookup)

Restored OCaml's real `scan_def` jump context:
`ctx_lub (list_as_pat pats) ctx`.

The follow-up crash came from qualified variant lookup, not from `scan_def`. For
`Set_gen.t` and similar `Pdot` result types, Rust `get_variant_constructors` was accepting
`Env.lookup_type` leaf fallback and retrieving the local alias declaration instead of the
parent module's real variant declaration. That made `complete_pats_constrs` synthesize a
fake unseen non-constant constructor with arity 1, which later broke `ctx_lshift`.

Updated Rust raw matching to:
- require exact-path matches before trusting `env.lookup_type`
- fall back to exact qualified-type resolution via `lookup_type_decl_for_path_pub`
- resolve `Pdot(parent, name)` through `resolve_module_type_through_env` and scan the
  parent signature for the real `SigType`

**Baseline after change:** still **626/657**, but parity hunks improve **89 -> 85** with
compile coverage held at **657/657**.

**Takeaway:** the remaining matching failures are still in inner handler/default
compilation, but the `scan_def` context path is now back on the OCaml control flow and the
qualified-constructor alias bug is removed.

### 2026-04-11 (get_mins ordering)

Aligned Rust `get_mins` with OCaml's survivor ordering by prepending retained elements on
each selection pass instead of appending them.

**Baseline after change:** still **626/657** with **89** hunks.

**Takeaway:** the remaining inner-handler mismatch is not explained by `get_mins` ordering
alone. The next likely root cause is still later context remapping during handler
compilation (`compile_list`, `compile_orhandlers`, or the downstream `ctx_*` transforms).

### 2026-04-11 (flattened multi-match split_precompile context)

Aligned the flattened multi-match entry point with OCaml: `do_for_multiple_match` now calls
`split_precompile None pm1` instead of threading the current `TypeContext` into the
flattened precompile step.

**Baseline after change:** still **626/657** with **85** hunks.

**Takeaway:** the remaining matching mismatch is not caused by the top-level flattened
entry context. The next root cause is deeper in the inner split/handler compilation that
follows flattening.

### 2026-04-11 (recursive default chaining in split_precompile)

Compared env-gated `split_precompile` traces in both compilers on `gpr_1698_test` and
found the first decisive divergence: OCaml carried cumulative default suffixes such as
`[10,9,8,7,6,5,4,3]`, while Rust collapsed the same branch to `[10]`.

The bug was not in `cons_default` itself. Several recursive split helpers were calling it
with the caller's incoming `def` instead of the recursive branch's `top_default`. Updating
those sites to thread `top_default` exactly like OCaml fixes the default chain.

**Baseline after change:** **626/657 -> 628/657**, **85 -> 79 hunks**.

**Takeaway:** this confirms the remaining matching failures are in later inner compilation
details, not in the recursive default-env chaining anymore.

### 2026-04-11 (compile_list recursion)

Aligned Rust `compile_list` with OCaml's recursive control flow instead of the previous
iterative accumulation.

**Baseline after change:** still **626/657** with **89** hunks.

**Takeaway:** the remaining mismatch survives even after aligning `compile_list`, so the
next likely root cause is narrower inside the later handler/context remapping path
(`compile_orhandlers` or a downstream `ctx_*` transform).

### 2026-04-11 (compile_orhandlers recursion)

Aligned Rust `compile_orhandlers` with OCaml's recursive control flow instead of the prior
imperative loop.

**Baseline after change:** still **626/657** with **89** hunks.

**Takeaway:** the remaining mismatch survives even after aligning both `compile_list` and
`compile_orhandlers`, so the next root cause is likely inside the downstream context
transforms or the specific handler payloads rather than the outer traversal order.
