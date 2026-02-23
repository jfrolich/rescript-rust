# Ralph Guidance: 607 → 657 (100% Parity)

**Last Updated:** 2026-02-23
**Current:** 607/657 (50 failures) on `typed-tree-parity-2`
**Previous Best:** 654/657 on `typed-ast-parity` (lost in repo reconstruction)

---

## CRITICAL: Do NOT Change the Sexp Serializer's Cycle Detection

**The sexp_typedtree.rs serializer uses permanent marking. This is CORRECT. Do NOT change it.**

Five alternative serializer approaches have been tried. ALL failed or regressed:

| Approach | Result |
|----------|--------|
| Stack-based (temporary) marking | 607 → 220 (massive regression) |
| One-level look-ahead | No improvement |
| Hybrid marking | No improvement |
| Raw TypeExprRef keys | No improvement |
| Leaf-node skip | 607 → 239 (massive regression) |

**Why serializer changes don't work:** The root cause of cycle diffs is NOT in the serializer — it's in the **type checker's sharing semantics**. OCaml's `instance()`/`copy()` creates more separate physical type nodes than Rust does. When two subtrees share the same arena node in Rust but have separate physical objects in OCaml, the Rust serializer correctly detects a "cycle" (revisited node) while OCaml expands both independently. Conversely, when OCaml has a real cycle through Tlink chains, Rust may not share the same nodes. The fix is to make Rust's type checker produce the **same sharing pattern** as OCaml.

**Currently-passing tests rely on Rust's "false cycles" to coincidentally match OCaml's real cycles.** Stack-based marking removes all false cycles, destroying these coincidental matches → massive regression.

---

## Executive Summary

The 50 failing tests are caused by differences in type checker behavior, NOT the serializer. The path from 607 → 654 was previously achieved on the `typed-ast-parity` branch through **11 specific type checker fixes**. These need to be re-applied in order.

The fixes fall into 3 phases:
1. **Type sharing fixes** (~38 tests) — Make `copy_type_cached` and `instance()` produce same sharing as OCaml
2. **Scoping/level fixes** (~6 tests) — `type_function` begin_def/generalize/instance, non-generic identity
3. **Infrastructure fixes** (~6 tests) — Interface constraints, module typing, supporting infrastructure

Plus 3 "hard" failures that were never solved (same 3 from 654/657):
- `mario_game.res`, `reasonReact.res`, `defunctor_make_test.res`

---

## Phase 1: Type Checker Sharing Fixes (607 → ~645)

These are the highest-impact fixes. They change how `copy_type_cached` and `instance()` create/reuse type nodes, making Rust's type graph sharing match OCaml's. These fixes were the core of the typed-ast-parity branch's journey from 330 → 654.

### 1A. `copy_type_cached` Generic Sharing via Placeholders (~40 tests)

**This is the single highest-impact fix. Do this FIRST.**

**Problem:** When `copy_type_cached` copies a generic type node, it currently recurses into children first, then creates the copy. OCaml's `copy` (ctype.ml ~line 863) uses `Tsubst` as a placeholder — it allocates the copy node FIRST, caches it with `Tsubst`, then fills in children. This means if the same generic node is encountered again during recursion, it returns the already-allocated placeholder instead of creating a second copy.

Rust's approach creates separate copies for each encounter of the same generic node → different sharing pattern → different cycle detection results.

**What to change in `compiler-rust/src/types/ctype.rs` `copy_type_cached`:**

1. For generic types that need structural copying (Tconstr with args, Ttuple, Tarrow, etc.), **allocate a placeholder node FIRST** and insert it into the copy cache
2. Then recurse into children
3. Then fill in the placeholder with the real children
4. If the same node is encountered during recursion, return the cached placeholder

This matches OCaml's pattern:
```ocaml
(* OCaml ctype.ml copy *)
let t = newty2 ty.level Tnil in  (* allocate placeholder *)
For_copy.redirect_desc scope ty (Tsubst t);  (* cache it *)
(* ... recurse into children ... *)
t.desc <- Tconstr(p, List.map copy tl, ref Mnil);  (* fill in *)
```

**Previously achieved:** On typed-ast-parity branch this was the first fix applied (from 330 baseline). Current branch already has partial sharing fixes, so the delta will be different.

**OCaml reference:** `compiler/ml/ctype.ml` function `copy` — look for the `Tsubst` pattern.

---

### 1B. `Pexp_ident` Local Monomorphic Type Sharing (~80 tests)

**This is the second highest-impact fix.**

**Problem:** When typing `Pexp_ident` (variable references), Rust calls `instance()` on every value type. For non-generic (monomorphic) types, OCaml's `instance()` returns the ORIGINAL type node by identity (since `copy` returns immediately for non-generic types). Rust's `copy_type_cached` does this selectively but misses important cases.

For local values with non-generic types (especially nullary `Tconstr` and `Tarrow`), Rust should reuse the source type directly instead of creating a copy.

**What to change in `compiler-rust/src/types/typecore.rs` around `Pexp_ident`:**

When the value's type is non-generic:
- For nullary `Tconstr` (especially predef types like `int`, `string`, `float`): return source type by identity
- For `Tarrow`: return source type by identity if non-generic

This reduces the number of distinct arena nodes → reduces false sharing differences → fewer cycle detection mismatches.

**Previously achieved:** Major impact on typed-ast-parity branch (combined with 1A).

**OCaml reference:** `compiler/ml/typecore.ml` `type_ident` → `Ctype.instance` → `copy` which returns identity for non-generic types.

---

### 1C. Non-Generic Identity in `copy_type_cached` (~6 additional tests)

**Problem:** OCaml's `copy` returns the original node for ALL non-generic types (ctype.ml line ~863: `if ty.level != generic_level then ty`). Rust does this selectively. Currently missing: `Tarrow`, `Tobject`, `Tfield`, `Tnil`.

**What to change in `compiler-rust/src/types/ctype.rs` `copy_type_cached`:**

Add `ReturnSelf` cases for non-generic:
- `Tarrow` (when level is non-generic)
- `Tobject` (when level is non-generic)
- `Tfield` (when level is non-generic)
- `Tnil` (when level is non-generic)

**IMPORTANT:** This fix may regress if applied WITHOUT fixes 1A and 1B already in place. On the current branch (without 1A/1B), it caused 607→604 regression. On the typed-ast-parity branch (with 1A/1B), it worked correctly (652→654).

**WARNING:** Do NOT extend to ALL types. `Tvariant` identity causes 1 regression. ALL non-generic types identity causes defunctor compile failure + 3 regressions.

**Previously achieved:** Final polish on typed-ast-parity branch (652 → 654/657), but only AFTER 1A and 1B were in place.

**OCaml reference:** `compiler/ml/ctype.ml` `copy` function — the `if ty.level != generic_level` check.

---

## Phase 2: Scoping and Level Fixes (~6 tests)

### 2A. `type_function` begin_def/generalize/instance Cycle (~3 tests)

**Problem:** OCaml's `type_cases` (typecore.ml:3906-4024) follows a specific pattern:
1. `begin_def()` — raise the definition level
2. Type the pattern (at elevated level)
3. `end_def()` — lower the level back
4. `generalize` the pattern type — mark type vars at elevated level as generic
5. `instance()` creates fresh copies for body environment

Rust's `type_function` doesn't do this cycle. Pattern types leak into the body at wrong level.

**What to change in `compiler-rust/src/types/typecore.rs` `type_function`:**

```rust
// Before typing each function case pattern:
ctx.begin_def();

// ... type the pattern ...

ctx.end_def();
generalize(ctx, pat_type);

// Create fresh instance for the body environment
let body_type = instance(ctx, pat_type);
```

**ALSO REQUIRED:** Extend the `update_level_expand` guard in `ctype.rs` to skip expansion for ALL local `Pident` types (not just nullary). Without this guard, the elevated level from `begin_def` triggers cascading `update_level_expand` issues causing 20+ regressions.

**Previously achieved:** Fixed `ticker.res` on typed-ast-parity branch (combined with 1C).

**WARNING:**
- `begin_def` WITHOUT the `update_level_expand` guard = 20+ regressions
- Copying ALL Tconstr in body env = 7 regressions
- The `update_level_expand` guard for local Pident is essential

**OCaml reference:** `compiler/ml/typecore.ml` lines 3906-4024 (`type_cases`)

---

### 2B. `type_function` exp_type Instantiation (~2 tests)

**Problem:** OCaml's `type_function` creates the expected function type as a generic arrow and then instantiates it, producing fresh type variables for pattern and body. Rust may construct the arrow type differently.

**What to change:** In `type_function`, create the expected type via:
```rust
let exp_type = instance(ctx, new_generic_arrow(param_ty, body_ty));
```
Then re-anchor the pattern type and body type from the instantiated arrow.

**Previously achieved:** Significant impact on typed-ast-parity branch (combined with 1A, 1B).

**OCaml reference:** `compiler/ml/typecore.ml` `type_function` — look for how `ty_arg` and `ty_res` are derived from the expected type.

---

## Phase 3: Infrastructure and Module Fixes (~6 tests)

### 3A. `force_generalize` Skip for `Pmod_structure` in typemod.rs

**Problem:** OCaml skips `force_generalize` for `Pmod_structure` to preserve non-generic levels from value restriction. This allows `instance()` to return identity for Tvars, enabling correct signature matching.

**What to change in `compiler-rust/src/types/typemod.rs`:** Find the `Pmod_structure` handler and skip the `force_generalize` call.

**OCaml reference:** `compiler/ml/typemod.ml` `type_module_aux` — the `Pmod_structure` case.

---

### 3B. Interface Constraint Propagation in driver.rs (~3 tests)

**Problem:** When a `.resi` exists, OCaml propagates type constraints from interface to implementation through weak type variables.

**What to add to `compiler-rust/src/driver.rs`:**

1. `apply_interface_constraints`: After typing implementation, read CMI, walk impl and sig types in parallel, link non-generic Tvars from impl to sig types
2. `propagate_sig_types`: Walk module signatures recursively for nested modules
3. `try_alias_param_propagation`: Handle parametric type aliases with different arities

**OCaml reference:** `compiler/ml/typemod.ml` `check_sig_item` and Includemod signature matching.

---

### 3C. Supporting Infrastructure

**In `context.rs`:**
- `current_stamp()` accessor (Rust equivalent of OCaml's `Ident.current_time()`)
- `new_row_field_ref` public method

**In `btype.rs`:**
- `row_field_repr_ctx` / `row_field_repr_ctx_aux`: Follow RowFieldRef links through TypeContext

**In `persistent_env.rs`:**
- Recursive module prefix rewriting: descend into SigModule submodules when rewriting flattened module names

**In `typemod.rs`:**
- `init_def(current_time())` synchronization before structure/signature items
- `transl_signature` environment threading through open statements

**WARNING:** `init_def(current_time())` before structure items WITHOUT proper guards = 11 compile failures + ~20 regressions. The Rust level system doesn't work identically to OCaml's.

---

### 3D. Additional Type Checker Fixes (from typed-ast-parity branch)

These smaller fixes were applied on the typed-ast-parity branch and contributed to parity improvements:

1. **Float identity freshening**: For repeated application idents involving floats
2. **`link_type` name propagation**: Ensure type names propagate correctly during unification linking
3. **`type_variables` reset**: Stop clearing `type_variables` in `type_function` (OCaml does NOT clear it)
4. **`Pexp_constraint` generalization ordering**: `var_level` after `end_def`
5. **`exp_extra` prepend ordering**: Insert at position 0 (not append)
6. **Object field fold ordering**: Use `ocaml_hashtbl_fold_order` for deterministic output
7. **Signature path substitution identity in persistent_env.rs**
8. **Recursive module `Tmod_constraint` location fix** (490→497/653)

---

## Phase 4: Hard Failures (654 → 657)

After re-applying all Phase 1-3 fixes, you should be at ~654/657. The remaining 3 are deep structural issues that were never solved.

### mario_game.res (248 hunks)

**Root Cause A (246 hunks):** Path normalization `Pident → Pdot(Actors)`. Inside `mario_game.res`, types from local module `Actors` are referenced. OCaml preserves `Pdot(Pident("Actors"), "xy")` while Rust resolves to `Pident("xy")`.

**Root Cause B (2 hunks):** Type alias `xy` expanded to `(float, float)`. OCaml preserves `Tconstr(xy, [])` but Rust expands it.

### reasonReact.res (36 hunks)

5 distinct sub-issues: (A) over-resolution Tvar→Tconstr(element), (B) location diffs, (C) under-resolution in WrapProps module, (D) componentSpec vs component alias, (E) Pdot(ReasonReact) path normalization.

### defunctor_make_test.res (80 hunks)

Functor application substitution missing. When OCaml types `Pmod_apply(F, Arg)`, it substitutes functor parameter types throughout the result. Rust returns placeholder. Plus Tvar→Tconstr under-resolution for functor params.

---

## Recommended Fix Order

**The order matters.** Later fixes depend on earlier ones being in place.

1. **1A: `copy_type_cached` placeholder caching** — Highest impact, independent
2. **1B: `Pexp_ident` monomorphic sharing** — Depends on 1A for full effect
3. **2B: `type_function` exp_type instantiation** — Can be done in parallel with 1B
4. **3D: Small type checker fixes** (link_type, exp_extra ordering, etc.) — Independent
5. **3A: force_generalize skip** — Independent
6. **3B: Interface constraints** — Independent
7. **3C: Supporting infrastructure** — Supports 2A and 3B
8. **2A: type_function begin_def/generalize/instance** — Requires `update_level_expand` guard
9. **1C: Non-generic Tarrow/Tobject/Tfield/Tnil identity** — REQUIRES 1A, 1B, 2A to be in place first (otherwise regresses)
10. **Phase 4: Hard failures** — After everything else

---

## Known Anti-Patterns (DO NOT RETRY)

| Approach | Result | Why |
|----------|--------|-----|
| **Stack-based cycle detection in serializer** | **607 → 220** | **Removes false cycles that coincidentally match OCaml's real cycles** |
| **Leaf-node cycle exemption in serializer** | **607 → 239** | **Same reason** |
| Ancestor-path tracking in serializer | Massive regression | Same reason |
| ALL non-generic types → identity | 650/656 | defunctor compile failure + 3 regressions |
| Non-generic Tvariant → identity | 1 regression | |
| Blanket unify_var on pattern nodes | 619/657 | Modifies shared nodes |
| Fresh Tvar for all pattern vars | 622/657 | Over-generalizes |
| init_def before structure items (no guards) | 11 compile failures | Level system differences |
| begin_def + raising param_ty level | 20+ regressions | Cascading update_level_expand |
| Copy ALL Tconstr in type_function body | 7 regressions | Contamination |
| Stdlib flattened-path probes | 612→606 | Over-broad normalization |
| UnifyMode::Pattern routing | 609→602 | Over-broad |
| Broad non-generic Tarrow identity (alone) | 609→607 | Needs 1A/1B first |
| Removing arg_expr_is_apply gate | Over-sharing | Worsens call sites |
| Skipping SigValue path substitution | Parity 431/622 | Load-bearing |
| Broad Ctype.copy all non-generic identity | Parity 585/651 | |

---

## Diagnostic Recipes

### Quick single-file comparison
```bash
cd tests/tests/lib/bs
args=$(cd ../.. && timeout 10 ../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args "src/FILE.res")
timeout 10 ../../../../packages/@rescript/darwin-arm64/bin/bsc.exe $args -dtyped-sexp-locs "../../src/FILE.res" > /tmp/ocaml.sexp 2>&1
timeout 10 ../../../../compiler-rust/target/release/bsc $args -dtyped-sexp-locs "../../src/FILE.res" > /tmp/rust.sexp 2>&1
diff /tmp/ocaml.sexp /tmp/rust.sexp | head -80
```

### Count diff hunks
```bash
diff /tmp/ocaml.sexp /tmp/rust.sexp | grep "^[0-9]" | wc -l
```

### Check if failure is cycle-related
```bash
diff /tmp/ocaml.sexp /tmp/rust.sexp | grep -c "cycle"
```

---

## Key Architecture Notes

- **OCaml `copy` uses `Tsubst` placeholder pattern** — allocate first, cache, recurse, fill in. This is the key to correct sharing.
- **OCaml `instance()` returns identity for ALL non-generic types** via `copy`. Rust can only do this selectively (some types cause regressions).
- **OCaml `type_cases` processes ALL patterns before ALL bodies** (batch). Rust processes each case independently.
- **CMI value-type path substitution is load-bearing** — can't remove without fixing type identity system.
- **Sexp permanent marking is CORRECT** — the cycle detection differences come from the type checker, not the serializer.
- **Record pattern fields must be sorted by `lbl_pos`** (OCaml invariant).
- **OCaml Reither has mutable `ref option` link** — set during unification, followed by `row_field_repr`. Rust's `RowFieldRef` link is allocated but NEVER set.

---

## Key Files Reference

| File | Key Functions | Notes |
|------|--------------|-------|
| `compiler-rust/src/types/ctype.rs` | `copy_type_cached`, `update_level_expand`, `instance` | **Primary fix target** |
| `compiler-rust/src/types/typecore.rs` | `type_function`, `type_case_impl`, Pexp_ident | Sharing + scoping |
| `compiler-rust/src/types/sexp_typedtree.rs` | Cycle detection | **DO NOT CHANGE** |
| `compiler-rust/src/types/typemod.rs` | `force_generalize`, `type_structure` | Module-level fixes |
| `compiler-rust/src/driver.rs` | Interface constraints | New code needed |
| `compiler-rust/src/types/context.rs` | `begin_def`, `end_def`, `new_var` | Supporting |
| `compiler/ml/ctype.ml` | `copy` (Tsubst pattern) | OCaml reference |
| `compiler/ml/typecore.ml` | `type_cases`, `type_function` | OCaml reference |
