# Ralph Guidance: 607 → 657 (100% Parity)

**Last Updated:** 2026-02-23
**Current:** 607/657 (50 failures) on `typed-tree-parity-2`
**Previous Best:** 654/657 on `typed-ast-parity` (lost in repo reconstruction)

This document lists the **exact fixes** from the `typed-ast-parity` branch (612→654 range), verified against Claude session logs. Each fix has its original parity delta and description. We've verified which are present vs missing on the current branch.

---

## CRITICAL: Stack-Based Cycle Detection

On the old `typed-ast-parity` branch, stack-based cycle detection was applied early (at parity 613) and gained +16 tests. **On the current branch it causes 607→220 regression.**

**Why:** The current branch has typecore.rs/ctype.rs from the FINAL state (654), which has non-generic identity returns, deep copies, etc. creating MORE arena node sharing than the old branch had at 613. Stack-based detection + more sharing = massive false expansions.

**When to try:** Only AFTER all other missing type checker fixes are applied. Even then, test carefully.

Five serializer approaches failed on this branch:
- Stack-based: 607→220
- Leaf-node skip: 607→239
- Ancestor-path tracking: massive regression
- One-level look-ahead: no improvement
- Hybrid marking: no improvement

---

## Fix Inventory: What's Present vs Missing

### Already Present (7 fixes)
| # | Original Parity | Fix |
|---|----------------|-----|
| 1 | 612→613 | Restrict linking heuristics to Pdot paths |
| 6 | 634→636 | Deep copy in type_newtype (subst_identity_copy) |
| 10 | 639→640 | pressure_variants for let binding patterns |
| 11 | 640→641 | unify_pats re-unification for polyvariant cases |
| 12 | 641→642 | Unify-based poly variant row closure |
| 22 | 651→652 | Label disambiguation lookup_from_type fallback |
| 23 | 652→653 | Non-generic Tarrow/Tobject/Tfield/Tnil identity |

### Partially Present (2 fixes)
| # | Original Parity | Fix | What's Missing |
|---|----------------|-----|----------------|
| 4 | 630→631 | Qualified label lookup returns last-defined | No explicit last-match for ambiguous labels in lookup_label_in_module |
| 20 | 649→650 | Skip expansion for local Pdot in update_level_expand | Only handles specific `.t`/`.cmp` paths, needs all nullary Pdot with local roots |

### Missing — 15 Fixes to Apply

These are ordered by recommended application order (safest/most-independent first):

---

## Fix 18: Predef Type Variances (647→648, +1)

**File:** `compiler-rust/src/types/env.rs`
**Test:** `ext_array_test.res`

Standard predef types (`option`, `list`, `result`) have empty `type_variance: vec![]`. Add correct variance annotations: `option` covariant, `list` covariant, `result` covariant in both params.

**OCaml ref:** `compiler/ml/predef.ml`

---

## Fix 19: Depth-Restricted Prefix Rewriting (648→649, +1)

**File:** `compiler-rust/src/cmi/persistent_env.rs`
**Test:** `Stdlib_TempTests.res`

In `substitute_submodule_paths`, add a `min_depth` parameter (default 2) so paths are only rewritten when the old module name appears as a module prefix (e.g., `Stdlib_JSON.Classify → Stdlib.JSON.Classify`) but preserved when it directly prefixes a type name (e.g., `Stdlib_Date.msSinceEpoch` stays as identity).

---

## Fix 3: Coercion Subtype Approximation (629→630, +1)

**File:** `compiler-rust/src/types/typecore.rs` — `type_coerce` / `Pexp_coerce`
**Test:** `type_coercion_free_vars.res`

In `type_coerce`, when there's no explicit `from_type` and `from_ty` is a fresh `new_var(None)`, unify the coercion result type with `from_ty` when `from_ty` is still an unresolved Tvar. Guard: only unify when still Tvar to avoid incorrectly replacing `type t = private int`.

**OCaml ref:** `compiler/ml/typecore.ml` `Pexp_coerce` handler

---

## Fix 13: Deep-Copy Tvariant/Tobject/Tfield in copy_type_deep (642→643, +1)

**File:** `compiler-rust/src/types/ctype.rs` — `copy_type_deep_inner`
**Test:** `jsxv4_newtype.res`

The `copy_type_deep_inner` currently returns Tvariant, Tobject, Tfield via `_ => ty` catch-all (no copy). Add proper deep copying:
- **Tvariant**: Copy `row_fields`, `row_more`, `row_name`
- **Tobject**: Copy fields and row variable
- **Tfield**: Copy field components

Without this, `replace_newtype_path` corrupts both copy and original.

**OCaml ref:** `compiler/ml/subst.ml` `Subst.type_expr`

---

## Fix 9: Expand Abbreviations Before Structural Match (638→639, +1)

**File:** `compiler-rust/src/types/ctype.rs` — unification
**Tests:** `unboxed_use_case.res`, `ExternalArity.res`

When both Tconstr types have the same path and `n_args > 0`, expand both and if they expand away from Tconstr (e.g., to Tvariant for polymorphic variant aliases), unify the expanded forms directly instead of unifying args. This prevents phantom type parameters from being incorrectly concretized. Do NOT link `t1→t2` in the expansion path.

**OCaml ref:** `compiler/ml/ctype.ml` `unify2` → `unify3`

---

## Fix 14: build_as_type for Tpat_variant and Tpat_or (643→644, +1)

**File:** `compiler-rust/src/types/typecore.rs` — `build_as_type`
**Test:** `more_poly_variant_test.res`

Currently Tpat_variant and Tpat_or fall through to `_ => pat.pat_type`. Add:
- **Tpat_variant**: Create single-field open row with Rpresent
- **Tpat_or**: Open the row (`row_closed=false`, fresh `row_more`)

**OCaml ref:** `compiler/ml/typecore.ml` `build_as_type`

---

## Fix 17: Label Type Param Sharing (646→647, +1)

**File:** `compiler-rust/src/types/typecore.rs`
**Test:** `gpr_4274_test.res`

When building `LabelDescription` from type declarations, `lbl_arg` and `lbl_res` can reference different Tvar nodes despite being the same type parameter. Add `remap_label_type_to_params` that walks label type and replaces Tvar nodes with corresponding `type_params` entries by name matching. Without this, `instance_label`'s cache breaks, leaving closure params as `Tvar(None)`.

---

## Fix 5: Shallow-Copy Pattern Variable Types (631→634, +3)

**File:** `compiler-rust/src/types/typecore.rs` — `type_function`, `type_case_impl`
**Tests:** 3 Belt-related files

When adding pattern variables to the body environment, create shallow Tconstr copies for pattern variable types that have non-empty args. Apply in `type_function` (only for non-simple-variable patterns) and `type_case_impl` (always). This gives the body its own type node to unify against while preserving pattern type identity.

**Note:** Fix 15 (per-case generalization) later replaces this with proper begin_def/end_def/generalize, but this simpler version is a useful stepping stone.

---

## Fix 7: Protect Scrutinee Type from Pattern Unification (636→637, +1)

**File:** `compiler-rust/src/types/typecore.rs`
**Test:** `option_repr_test.res`

When `instance()` returns the scrutinee's `exp_type` by identity (non-generic predef Tconstr like `option`), pattern unification can corrupt the scrutinee's path (e.g., `option` becoming `u`). Create a shallow copy when `instance()` returns the same node.

---

## Fix 16: Shallow Copy Nullary Pattern Var Types (645→646, +1)

**File:** `compiler-rust/src/types/typecore.rs`
**Test:** `reasonReactRouter.res`

Body typing unifying pattern variable (e.g., `raw`) with `Js.String.t` contaminates shared scrutinee type, causing other patterns to show wrong path. Create shallow copy of nullary Tconstr pattern variable types for the body env.

---

## Fix 8: Force-Generalize Module Sig Value Types (637→638, +1 net)

**Files:** `compiler-rust/src/types/ctype.rs`, `compiler-rust/src/types/typemod.rs`
**Tests:** `inline_map2_test.res`, `set_gen.res` (+2), `LetUnwrap.res` (-1 regression)

Add `force_generalize()` that walks all reachable types in a module signature and promotes to `GENERIC_LEVEL`. **Guard:** exclude nullary Tconstr from generalization to avoid `find_simple_abbrev` remap.

---

## Fix 21: GADT Equation Support (650→651, +1)

**Files:** `compiler-rust/src/types/ctype.rs`, `compiler-rust/src/types/typecore.rs`
**Test:** `js_json_test.res`

Add GADT-aware unification preserving existential type variables. Key additions:
- `UnifyState` with `gadt_equations` storage
- `with_gadt_mode` context
- `add_gadt_equation` for type constraints
- `is_newtype_path` in ctype
- `copy_case_type` keeps locally abstract types as Tconstr (not Tvar)

**OCaml ref:** `compiler/ml/ctype.ml` `unify_gadt`

---

## Fix 15: Per-Case Pattern Generalization (644→645, +1)

**Files:** `compiler-rust/src/types/typecore.rs`, `compiler-rust/src/types/ctype.rs`

Add `begin_def()/end_def()/generalize()` around pattern typing in `type_case_impl`. This replaces/improves fix 5's shallow copy approach. Also add guard in `update_level_expand` to preserve nullary local type alias identity.

---

## Fix 24: begin_def/generalize/instance in type_function (653→654, +1)

**Files:** `compiler-rust/src/types/typecore.rs`, `compiler-rust/src/types/ctype.rs`
**Test:** `ticker.res`

Same pattern as fix 15 but for `type_function` specifically. **REQUIRES** extending `update_level_expand` to skip expansion for ALL local Pident types (the guard committed as `1ef01d46c` on this branch). Without the guard: 20+ regressions.

---

## Fix 2: Stack-Based Cycle Detection — TRY LAST (613→629, +16)

**File:** `compiler-rust/src/types/sexp_typedtree.rs`

Switch permanent-marking cycle detection to stack-based (add on entry, remove on exit). On the old branch this gained +16 tests at parity 613. **On current branch: 607→220 regression.** Only try after ALL above fixes are applied — the sharing context must be correct first.

---

## Partial Fix 4: Qualified Label Lookup Last-Defined (630→631, +1)

**File:** `compiler-rust/src/types/typecore.rs`
**Test:** `Stdlib_Intl_DateTimeFormatTest.res`

In `lookup_label_in_module`, when multiple record types define the same field name, return the LAST match (most recently defined). Current code has leaf-name fallback but not explicit last-match for ambiguous labels.

---

## Partial Fix 20: General Local Pdot Expansion Guard (649→650, +1)

**File:** `compiler-rust/src/types/ctype.rs`
**Test:** `topsort_test.res`

Generalize the `update_level_expand` Pdot guard from specific `.t`/`.cmp` patterns to ALL nullary Pdot paths with local roots. This prevents expansion of type aliases like `String_set.value → string`.

---

## Known Anti-Patterns (DO NOT RETRY)

| Approach | Result | Why |
|----------|--------|-----|
| Stack-based cycle detection (on current branch) | 607→220 | Current sharing causes massive false expansions |
| Leaf-node cycle exemption | 607→239 | Same issue |
| ALL non-generic types → identity | 650/656 | defunctor compile failure + 3 regressions |
| Non-generic Tvariant → identity | 1 regression | |
| Blanket unify_var on pattern nodes | 619/657 | Modifies shared nodes |
| init_def before structure items (no guards) | 11 compile failures | Level system differences |
| begin_def + raising param_ty level (no guard) | 20+ regressions | Cascading expansion |
| Copy ALL Tconstr in type_function body | 7 regressions | Contamination |
| Stdlib flattened-path probes | 612→606 | Over-broad normalization |
| UnifyMode::Pattern routing | 609→602 | Over-broad |
| Skipping SigValue path substitution | Parity 431/622 | Load-bearing |

---

## Diagnostic Recipes

```bash
# Quick single-file parity check (regenerates sexp via rewatch --filter, ~1s)
./scripts/test_typedtree_parity.sh FILE_MODULE
# e.g.: ./scripts/test_typedtree_parity.sh async_inline

# Glob pattern (e.g. all belt tests)
./scripts/test_typedtree_parity.sh "belt_*"

# Full parity run (all modules, ~30s)
./scripts/test_typedtree_parity.sh

# When filter matches a failing file, the diff is shown inline.
```

### Inspecting cached results

All parity results persist in `.parity-cache/` between runs:
- `.parity-cache/$label/ocaml/*.sexp` — raw OCaml sexp output
- `.parity-cache/$label/rust/*.sexp` — raw Rust sexp output
- `.parity-cache/$label/diffs/*.diff` — per-module diffs (failing files only)
- `.parity-cache/$label/summary.txt` — pass/fail counts
- `.parity-cache/$label/failures.txt` — list of failing module names

Where `$label` is `tests` for the main test project or `tella_*` for external corpora.
