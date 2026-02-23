# Fixes from typed-ast-parity branch: 612 → 654

Extracted from Claude session logs (`~/.claude/projects/-Users-jake-dev-rescript-rust/*.jsonl`).
Each fix verified against current `typed-tree-parity-2` branch for PRESENT/MISSING status.

---

## Fix 1: 612→613 (+1) — PRESENT

**Commit:** `6f22424fa`
**Message:** `typecore: remove force_fresh_local_float and restrict linking heuristics to Pdot paths`
**File:** `typecore.rs`
**What:** Removed `force_fresh_local_float`. Restricted three linking heuristics (adjacent args, tail return, arg-ret) to only apply for `Pdot` paths, not `Pident` paths. The arg-ret linking for `Pident("t")` in `t -> t` functions was causing false cycles in `update_record_test.res`.
**Test:** `update_record_test.res` (net +1, swapped b.res for earger_curry_test.res)

---

## Fix 2: 613→629 (+16) — MISSING (REGRESSES on current branch)

**Commit:** `bb5a4d7b2`
**Message:** `sexp: switch to stack-based cycle detection for type expressions`
**File:** `sexp_typedtree.rs`
**What:** Switched from permanent-marking (HashSet) to stack-based cycle detection (add on entry, remove on exit). Permanent marking produces false `<cycle>` markers due to node sharing differences between OCaml and Rust.
**Tests fixed:** 16 files including `b.res`, `belt_list_test.res`, `bs_abstract_test.res`, `for_loop_test.res`, `miss_colon_test.res`, `rbset.res`, `bdd.res`, `functor_ffi.res`, `bs_stack_test.res`, `record_type_spread.res`, `belt_internal_test.res`, `test_list.res`, `test_seq.res`, `variantsMatching.res`
**WARNING:** On current branch causes 607→220 regression. Only try after all other fixes applied.

---

## Fix 3: 629→630 (+1) — MISSING → DONE (611→612)

**Commit:** `9c50c0ad5`
**Message:** `typecore: add coercion subtype approximation and qualified label lookup`
**File:** `typecore.rs`
**What:** In `Pexp_coerce` handler, unify coercion result type with `from_ty` when `from_ty` is still a Tvar (unresolved). Guard: only when from_ty hasn't been resolved yet.
**Test:** `type_coercion_free_vars.res`

---

## Fix 4: 630→631 (+1) — PARTIAL

**Commit:** `3508b51b5`
**Message:** `typecore: fix qualified label lookup to return last-defined type`
**File:** `typecore.rs`
**What:** In `lookup_label_in_module`, when multiple record types define the same field name, return the LAST match (most recently defined). OCaml's `comp_labels` stores labels with most-recently-defined first.
**Test:** `Stdlib_Intl_DateTimeFormatTest.res`

---

## Fix 5: 631→634 (+3) — MISSING

**Commit:** `d75afe709`
**Message:** `typecore: shallow-copy pattern variable types to preserve path identity`
**File:** `typecore.rs`
**What:** Create shallow Tconstr copies for env entries when pattern types have non-empty args. Applied in `type_function` (only for non-simple-variable patterns) and `type_case_impl` (always). This gives the body its own type node to unify against while the pattern type node is preserved.
**Tests:** 3 files including Belt-related tests where `Belt.List.forEach` was linking `list` to `Belt.List.t`.

---

## Fix 6: 634→636 (+2) — PRESENT

**Commit:** `750e3335a`
**Message:** `typecore: use deep copy in type_newtype to preserve pattern types`
**Files:** `typecore.rs`, `ctype.rs`
**What:** In `Pexp_newtype`, switched to `copy_type_deep` (full structural copy). Previous `copy_type` only copies generic-level nodes, causing shared non-generic nodes to be corrupted by `replace_newtype_path`'s `link_type` calls.
**Tests:** `bench.res`, `earger_curry_test.res`

---

## Fix 7: 636→637 (+1) — MISSING

**Commit:** `d74b94a6f`
**Message:** `typecore: protect scrutinee type from pattern unification in match`
**File:** `typecore.rs`
**What:** When `instance()` returns the scrutinee's `exp_type` by identity (non-generic predef Tconstr), pattern unification against constructor result types can corrupt the scrutinee's recorded type path (e.g., `option` becoming `u`). Creates a shallow copy of the Tconstr node when `instance()` returns the same node.
**Test:** `option_repr_test.res`

---

## Fix 8: 637→638 (+1 net) — MISSING

**Commit:** `a66dcf40f`
**Message:** `ctype: force-generalize module signature value types to fix Tvar over-resolution`
**Files:** `ctype.rs`, `typemod.rs`
**What:** Module signature types from `copy_type_deep` end up at non-generic levels. Added `force_generalize()` which walks all reachable types in a module signature and promotes to GENERIC_LEVEL. Guard: exclude nullary Tconstr to avoid `find_simple_abbrev` remap.
**Tests:** `inline_map2_test.res` (+1), `set_gen.res` (+1), `LetUnwrap.res` (-1 regression). Net +1.

---

## Fix 9: 638→639 (+1) — MISSING

**Commit:** `01a5aec01`
**Message:** `ctype: expand abbreviations before structural matching for same-path Tconstr`
**File:** `ctype.rs`
**What:** When both Tconstr types have same path and `n_args > 0`, expand both. If they expand away from Tconstr (e.g., to Tvariant for polymorphic variant aliases), unify expanded forms directly instead of unifying args. Do NOT link `t1→t2` in expansion path.
**Tests:** `unboxed_use_case.res`, `ExternalArity.res`

---

## Fix 10: 639→640 (+1) — PRESENT

**Commit:** `8ae9fd571`
**Message:** `typecore: add pressure_variants for let binding patterns`
**File:** `typecore.rs`
**What:** Added `close_variant_row_for_pat_type` to let binding patterns, matching OCaml's `pressure_variants` call from `type_let` (typecore.ml:4117-4121).
**Test:** `fun_pattern_match.res`

---

## Fix 11: 640→641 (+1) — PRESENT

**Commit:** `de510f693`
**Message:** `typecore: add unify_pats re-unification for polyvariant match cases`
**File:** `typecore.rs`
**What:** After `pressure_variants` and `finalize_variant`, re-unify all pattern types with scrutinee type when patterns contain polymorphic variants (matching OCaml type_cases line 3993).
**Test:** `gpr_4280_test.res`

---

## Fix 12: 641→642 (+1) — PRESENT

**Commit:** `a5d01f7e3`
**Message:** `typecore: fix poly variant row closure to use unification for top-level patterns`
**File:** `typecore.rs`
**What:** Used unify-based closure for top-level variant patterns (matching OCaml's `close_variant` parmatch.ml:808-832). Used `set_row_field_link` for `Reither → Rabsent` conversion.
**Test:** `set_gen.res`

---

## Fix 13: 642→643 (+1) — MISSING

**Commit:** `b622d705b`
**Message:** `ctype: deep-copy Tvariant/Tobject/Tfield in copy_type_deep`
**File:** `ctype.rs`
**What:** `copy_type_deep_inner` was returning Tvariant, Tobject, Tfield via `_ => ty` catch-all. Added proper deep copying for:
- **Tvariant**: Copy `row_fields`, `row_more`, `row_name`
- **Tobject**: Copy fields and row variable
- **Tfield**: Copy field components
**Test:** `jsxv4_newtype.res`

---

## Fix 14: 643→644 (+1) — MISSING

**Commit:** `29e4c2885` + `342f2eeb8`
**Messages:** `typecore: fix poly variant tag ordering in build_or_pat` + `typecore: implement build_as_type for Tpat_variant and Tpat_or`
**File:** `typecore.rs`
**What:** (1) Fixed poly variant tag ordering in `build_or_pat`. (2) Added `build_as_type` cases for:
- **Tpat_variant**: Create single-field open row with Rpresent
- **Tpat_or**: Open the row (`row_closed=false`, fresh `row_more`)
**Test:** `more_poly_variant_test.res`

---

## Fix 15: 644→645 (+1) — MISSING

**Commit:** `95e8141e5`
**Message:** `typecore: implement per-case pattern generalization for type alias identity`
**Files:** `typecore.rs`, `ctype.rs`
**What:** Replaced shallow copy hack (fix 5) with proper `begin_def/end_def/generalize` around pattern typing in `type_case_impl`. Also added guard in `update_level_expand` to preserve nullary local type alias identity (e.g., `type key = Ord.t`). Constructor descriptions use `new_generic_constr` for `cstr_res`.
**Test:** 1 additional file

---

## Fix 16: 645→646 (+1) — MISSING

**Commit:** `1d940b052`
**Message:** `typecore: shallow copy nullary pattern var types to prevent scrutinee contamination`
**File:** `typecore.rs`
**What:** When body typing unifies a pattern variable (e.g., `raw`) with a module-qualified alias (e.g., `Js.String.t`), the unification contaminates the shared scrutinee type node. Creates a shallow copy of nullary Tconstr pattern variable types for the body env.
**Test:** `reasonReactRouter.res`

---

## Fix 17: 646→647 (+1) — MISSING

**Commit:** `7957bdca3`
**Message:** `typecore: fix label type param sharing for first-class module record fields`
**File:** `typecore.rs`
**What:** When building `LabelDescription`, `lbl_arg` and `lbl_res` could reference different Tvar nodes for the same type parameter. Added `remap_label_type_to_params` to walk label type and replace Tvar nodes with corresponding `type_params` entries by name matching.
**Test:** `gpr_4274_test.res`

---

## Fix 18: 647→648 (+1) — MISSING → DONE (parity-neutral at 611)

**Commit:** `06049811b`
**Message:** `env: fix predef type variance lookup and add missing variances`
**File:** `env.rs`
**What:** Fixed predef type variance lookup. `option`, `list`, `result` etc. need correct covariant variance annotations.
**Test:** `ext_array_test.res`

---

## Fix 19: 648→649 (+1) — MISSING → DONE (612→613)

**Commit:** `b589ea199`
**Message:** `persistent_env: depth-restricted prefix rewriting for sub-module types`
**File:** `persistent_env.rs`
**What:** Used depth-restricted rewriting (`min_depth=2`) that only rewrites paths where old module name appears as a module prefix, but preserves paths where it directly prefixes a type name.
**Test:** `Stdlib_TempTests.res`

---

## Fix 20: 649→650 (+1) — PARTIAL

**Commit:** `c89d6d802`
**Message:** `Fix spurious type alias expansion in update_level_expand (650/656 parity)`
**File:** `ctype.rs`
**What:** Skip expansion in `update_level_expand` for nullary Pdot paths with local roots. Current branch only handles specific `.t`/`.cmp` paths, needs ALL nullary Pdot with local roots.
**Test:** `topsort_test.res` (also reduced mario_game.res from 7926 to 33 lines)

---

## Fix 21: 650→651 (+1) — MISSING

**Commit:** `6660a316f`
**Message:** `Implement GADT equation support for locally abstract types (651/657 parity)`
**Files:** `ctype.rs`, `typecore.rs`
**What:** GADT-aware unification. Key additions:
- `UnifyState` with `gadt_equations`
- `with_gadt_mode`, `add_gadt_equation`
- `is_newtype_path` in ctype
- `copy_case_type` keeps locally abstract types as Tconstr (not Tvar)
- `type_case_impl` propagates GADT equations to case env
**Test:** `js_json_test.res`

---

## Fix 22: 651→652 (+1) — PRESENT

**Commit:** `567f71168`
**Message:** `Fix label disambiguation: try type-based lookup before leaf-name fallback (652/657 parity)`
**File:** `typecore.rs`
**What:** Added `lookup_from_type` fallback that looks up label directly from expected type's declaration BEFORE trying loose leaf-name match.
**Test:** `jsx_preserve_test.res`

---

## Fix 23: 652→653 (+1) — PRESENT

**Commit:** `2a252e63f`
**Message:** `Fix non-generic Tarrow/Tobject/Tfield/Tnil identity in copy_type_cached (653/657 parity)`
**File:** `ctype.rs`
**What:** Added `CopyAction::ReturnSelf` for non-generic `Tarrow`, `Tobject`, `Tfield`, `Tnil`.
**Tests:** `test_bs_this.res`, `obj_type_test.res`

---

## Fix 24: 653→654 (+1) — MISSING

**Commit:** `4c45ce41b`
**Message:** `Fix ticker.res parity: begin_def/generalize/instance cycle in type_function (654/657)`
**Files:** `typecore.rs`, `ctype.rs`
**What:** Added `begin_def/end_def/generalize` around pattern typing in `type_function`. Extended `update_level_expand` guard to skip ALL local Pident types.
**Test:** `ticker.res`

---

## Summary

| Status | Count | Fixes |
|--------|-------|-------|
| PRESENT | 7 | 1, 6, 10, 11, 12, 22, 23 |
| PARTIAL | 2 | 4, 20 |
| MISSING | 13 | 2, 5, 7, 8, 9, 13, 14, 15, 16, 17, 21, 24 |
| DONE (applied on this branch) | 2 | 3 (611→612), 18 (parity-neutral), 19 (612→613) |

## Parity-Neutral Infrastructure Commits

Between the numbered fixes, several parity-neutral infrastructure commits were made:
- `275543520` — RowFieldRef infrastructure for poly variant link resolution
- `464436406` — Shared RowFieldRef linking for Reither/Reither unification
- `3ffe67c47` — Poly variant row field handling and closing logic improvements
- `cf020e79f` — GADT existential newtypes in instance_constructor_in_pattern
- `f509f073a` — Recursively rewrite module prefix in submodule signatures
- `7b1848f6d` — Includemod signature matching (propagate .resi interface constraints)
- `82356e9f7` — Record spread unify_kept (connect base type params to expected type)
