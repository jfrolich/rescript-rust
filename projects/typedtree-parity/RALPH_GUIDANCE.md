# Ralph Guidance: 607 → 657 (100% Parity)

**Last Updated:** 2026-02-22
**Current:** 607/657 (50 failures) on `typed-tree-parity-2`
**Previous Best:** 654/657 on `typed-ast-parity` (lost in repo reconstruction)

This document provides actionable, prioritized guidance for reaching 100% typedtree parity. It is organized by root cause cluster, ordered by impact (most tests fixed first).

---

## Executive Summary

The 50 failing tests are caused by **4 root causes**, each with a known fix strategy:

| # | Root Cause | Tests Affected | Fix Location | Previously Working? |
|---|-----------|---------------|-------------|-------------------|
| 1 | Sexp cycle detection (permanent vs stack-based marking) | ~38 tests | `sexp_typedtree.rs` | YES — was fixed on typed-ast-parity |
| 2 | Missing non-generic identity for Tarrow/Tobject/Tfield/Tnil | ~6 tests | `ctype.rs` | YES — was fixed on typed-ast-parity |
| 3 | Missing begin_def/generalize/instance in type_function | ~3 tests | `typecore.rs` | YES — was fixed on typed-ast-parity |
| 4 | Missing driver.rs interface constraint propagation | ~3 tests | `driver.rs` | YES — was fixed on typed-ast-parity |

Plus 3 "hard" failures that were never solved (same 3 from the 654/657 state):
- `mario_game.res`, `reasonReact.res`, `defunctor_make_test.res`

---

## Phase 1: Re-apply Lost Fixes (607 → ~654)

These fixes were verified working on the `typed-ast-parity` branch but were lost in reconstruction. The files `typemod.rs`, `sexp_typedtree.rs`, `context.rs`, `driver.rs`, `btype.rs`, `persistent_env.rs` are at Feb 18 state (~611/657) and need fixes re-applied.

### 1A. Stack-Based Cycle Detection in sexp_typedtree.rs (~38 tests)

**This is the single highest-impact fix. Do this FIRST.**

**Problem:** The current sexp serializer uses **permanent marking** for cycle detection — once a type node is visited, it's marked forever and shows `<cycle>` on all subsequent visits. OCaml uses **stack-based (temporary) marking** — a node is only marked while it's an ancestor on the current traversal path. When you exit a subtree, the mark is removed, so the same node can be fully expanded again in a sibling subtree.

**What to change in `compiler-rust/src/types/sexp_typedtree.rs`:**

1. Change the `visited: &mut HashSet<TypeId>` parameter to act as a **stack** (add on entry, remove on exit) instead of a permanent set (add and never remove).

   ```
   // BEFORE (permanent marking — WRONG):
   if !visited.insert(type_id) {
       return write!(f, "<cycle>");
   }
   // type_id stays in visited forever

   // AFTER (stack-based marking — CORRECT):
   if visited.contains(&type_id) {
       return write!(f, "<cycle>");
   }
   visited.insert(type_id);
   // ... serialize children ...
   visited.remove(&type_id);  // Remove on exit!
   ```

2. **Evaluation order matters**: OCaml traverses type children left-to-right. Ensure:
   - `Tarrow`: label → arg → ret (left to right)
   - `Tfield`: name → kind → type → rest (left to right)
   - `Tpoly`: type → constraints (left to right)

3. **Row field representation**: Use `row_field_repr_ctx` (which follows `RowFieldRef` links through `TypeContext`) instead of `row_field_repr` when printing `Reither` fields. This ensures `Reither` that has been unified to `Rpresent` is printed as `Rpresent`.

**OCaml reference:** `compiler/ml/sexp_typedtree.ml` — the OCaml serializer naturally gets stack-based behavior because it's a recursive function without a visited set (OCaml's GC handles the graph traversal). The Rust version needs explicit stack tracking because we can't rely on the same sharing semantics.

**Tests this should fix (pure cycle-only):**
- `update_record_test.res`, `bs_mutable_set_test.res`, `bs_poly_map_test.res`, `bs_queue_test.res`, `bs_stack_test.res`, `earger_curry_test.res`, `functor_ffi.res`, `miss_colon_test.res`, `variantsMatching.res`, `rbset.res`, `test_set.res`, `inline_map_test.res`, `inline_map2_test.res`, `large_record_duplication_test.res`, `test_seq.res`, `flexible_array_test.res`, `bs_set_int_test.res`

**Tests this should partially fix (cycle + other issues):**
- `exception_raise_test.res`, `ext_array_test.res`, `string_set.res`, `js_string_test.res`, `reasonReactRouter.res`, `ticker.res`, `topsort_test.res`, `jsx_preserve_test.res`, `jsxv4_newtype.res`, `more_poly_variant_test.res`, `fun_pattern_match.res`, `set_gen.res`, `test_bs_this.res`, `pipe_send_readline.res`, `defunctor_make_test.res`, `mario_game.res`, `reasonReact.res`, `type_coercion_free_vars.res`, `UntaggedVariants.res`, `Stdlib_Intl_DateTimeFormatTest.res`

**WARNING:** Previous attempts at alternative cycle detection strategies (leaf-node exemption, ancestor-path tracking) caused **massive regressions** (504→207 and 504→194). The ONLY strategy that works is the simple stack-based add-on-entry/remove-on-exit approach described above.

---

### 1B. Non-Generic Tarrow/Tobject/Tfield/Tnil Identity in ctype.rs (~6 tests)

**Problem:** OCaml's `instance()` / `copy()` returns the **original type node** for ALL non-generic types. The Rust version (`copy_type_cached`) only does this selectively for Tvar, Tunivar, Ttuple, and some Tconstr. It's missing identity returns for Tarrow, Tobject, Tfield, and Tnil.

**What to change in `compiler-rust/src/types/ctype.rs` `copy_type_cached`:**

Add `ReturnSelf` cases for non-generic:
- `Tarrow` (when level is non-generic)
- `Tobject` (when level is non-generic)
- `Tfield` (when level is non-generic)
- `Tnil` (when level is non-generic)

```rust
// In copy_type_cached, add before the existing Tarrow match arm:
TypeDesc::Tarrow(_, _, _, _) if !is_generic(ty.level()) => {
    return CopyResult::ReturnSelf;
}
TypeDesc::Tobject(_, _) if !is_generic(ty.level()) => {
    return CopyResult::ReturnSelf;
}
TypeDesc::Tfield(_, _, _, _) if !is_generic(ty.level()) => {
    return CopyResult::ReturnSelf;
}
TypeDesc::Tnil if !is_generic(ty.level()) => {
    return CopyResult::ReturnSelf;
}
```

**OCaml reference:** `compiler/ml/ctype.ml` `copy` function — the `if ty.level != generic_level` check at the top returns the original node for ALL non-generic types before doing any structural copy.

**Tests this should fix:**
- `test_bs_this.res` (object types with `Tfield`)
- `pipe_send_readline.res` (object types)
- Other tests with arrow/object type sharing differences

**WARNING:** Do NOT extend this to ALL types. Adding Tvariant identity causes 1 regression. Adding ALL non-generic types to identity causes 650/656 (defunctor compile failure + 3 regressions).

---

### 1C. begin_def/generalize/instance in type_function (~3 tests)

**Problem:** OCaml's `type_cases` (typecore.ml:3906-4024) follows a specific pattern for function parameters:
1. `begin_def()` — raise the definition level
2. Type the pattern (at elevated level)
3. `end_def()` — lower the level back
4. `generalize` the pattern type — mark type vars at the elevated level as generic
5. `instance()` creates fresh copies for the body environment

Rust's `type_function` doesn't do this cycle. Pattern types leak into the body at the wrong level.

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

Also: extend the `update_level_expand` guard in `ctype.rs` to skip expansion for ALL local `Pident` types (not just nullary ones). Without this, the elevated level from `begin_def` triggers cascading `update_level_expand` issues.

**OCaml reference:** `compiler/ml/typecore.ml` lines 3906-4024 (`type_cases`)

**Tests this should fix:** `ticker.res` (primary), possibly others with pattern/body type contamination

**WARNING:**
- `begin_def` + raising `param_ty` level WITHOUT the update_level_expand guard causes 20+ regressions
- Copying ALL Tconstr in the body env causes 7 regressions (map/topsort)
- The update_level_expand guard for local Pident is essential

---

### 1D. force_generalize Skip for Pmod_structure in typemod.rs

**Problem:** OCaml skips `force_generalize` for `Pmod_structure` to preserve non-generic levels from value restriction. This allows `instance()` to return identity for Tvars, enabling correct signature matching.

**What to change in `compiler-rust/src/types/typemod.rs`:**

Find the `Pmod_structure` handler and skip the `force_generalize` call. In OCaml, `type_module` calls `Ctype.force_generalize` on the module type, but NOT for structures.

**OCaml reference:** `compiler/ml/typemod.ml` `type_module_aux` — the `Pmod_structure` case doesn't call `force_generalize`.

---

### 1E. Interface Constraint Propagation in driver.rs

**Problem:** When a `.resi` (interface) file exists, OCaml propagates type constraints from the interface to the implementation through weak type variables. This is how types that are `Tvar None` in the implementation get resolved to concrete types like `int` or `string`.

**What to add to `compiler-rust/src/driver.rs`:**

1. **`apply_interface_constraints`**: After typing the implementation, read the CMI file, walk impl and sig types in parallel, and link non-generic Tvars from the implementation to the corresponding types in the signature.

2. **`propagate_sig_types`**: Recursively walk module signatures to handle nested modules.

3. **`try_alias_param_propagation`**: Handle parametric type aliases with different arities (e.g., `component<3>` vs `componentSpec<5>`).

**OCaml reference:** `compiler/ml/typemod.ml` `check_sig_item` and the Includemod signature matching flow.

**Tests this should help:** `reasonReact.res` (partially), `Stdlib_ObjectTests.res`, others with Tvar→Tconstr under-resolution

---

### 1F. Other Missing Fixes to Re-Apply

**In `context.rs`:**
- Add `current_stamp()` accessor (Rust equivalent of OCaml's `Ident.current_time()`)
- Add `new_row_field_ref` public method

**In `btype.rs`:**
- Add `row_field_repr_ctx` / `row_field_repr_ctx_aux` functions that follow RowFieldRef links through TypeContext

**In `persistent_env.rs`:**
- Recursive module prefix rewriting — recursively descend into SigModule submodule signatures when rewriting flattened module names

**In `typemod.rs`:**
- `init_def(current_time())` synchronization before structure/signature items
- `transl_signature` environment threading through open statements

---

## Phase 2: Fix Remaining Issues (654 → 657)

After re-applying Phase 1 fixes, you should be at ~654/657 with 3 remaining failures. These are deep structural issues.

### 2A. mario_game.res (248 → ~31 diff lines)

**Root Cause A (246 hunks): Path normalization Pident → Pdot(Actors)**

Inside `mario_game.res`, types defined in a local module `Actors` are referenced. OCaml preserves the qualified path `Pdot(Pident("Actors"), "xy")` while Rust resolves to the canonical `Pident("xy")`.

**Fix strategy:** This is about how the type environment stores and retrieves type paths for locally-defined types within modules. When typing an expression inside the `mario_game` structure that references types from the `Actors` submodule, the path should be stored as `Pdot(Actors, ...)` not `Pident(...)`.

**OCaml behavior:** When a module `M` defines type `t`, and code later refers to `M.t`, the path stored in the typed tree is `Pdot(Pident "M", "t")`. OCaml's `find_type` in `env.ml` returns the path as found in the environment, which preserves the module qualification.

**Hint:** Look at how `typecore.rs` `Pexp_ident` constructs the path for value lookups. The `val_type` path comes from `Env.find_value` which may be returning a flattened path. Compare with OCaml's `Env.lookup_value` to see how the path is preserved through module scoping.

**Root Cause B (2 hunks): Type alias `xy` expanded to `(float, float)`**

OCaml preserves `Tconstr(xy, [])` but Rust expands it to `Ttuple(float, float)`. This is about unification link direction in `unify_after_expansion` — when both sides expand, OCaml's `unify3` preserves the original (unexpanded) type as the canonical node.

---

### 2B. reasonReact.res (36 hunks)

This has 5 distinct sub-issues:

**(A) 7 hunks: Tvar→Tconstr(element) over-resolution**
Rust resolves a type variable to `React.element` where OCaml leaves it as `Tvar None`. This is likely from the interface constraint propagation being too aggressive — check that `apply_interface_constraints` only links Tvars that are actually non-generic and at the correct level.

**(B) 4 hunks: Location diffs (col 47→14)**
The locations differ because the Rust parser or PPX produces different column offsets for certain expressions. Compare the AST locations between OCaml and Rust for these specific expressions.

**(C) ~20 hunks: `actionless` Tvar→Tconstr under-resolution in WrapProps module**
OCaml resolves `actionless` type variables inside the `WrapProps` module to concrete types, but Rust leaves them as `Tvar None`. This is because the Tvars are inside a nested module and not reachable from the top-level signature propagation.

**Fix strategy:** The `apply_interface_constraints` function needs to recursively descend into nested modules (via `propagate_sig_types`) to link Tvars inside `WrapProps` to the corresponding concrete types from the interface.

**(D) 1 hunk: `componentSpec` vs `component` alias**
OCaml uses the alias `component` where Rust uses `componentSpec`. This is about `try_alias_param_propagation` handling the arity difference (component has 3 params, componentSpec has 5).

**(E) 2 hunks: Pdot(ReasonReact) path normalization**
Same type of issue as mario_game.res — qualified paths not preserved.

---

### 2C. defunctor_make_test.res (80 hunks)

**Root Cause: Functor application substitution missing**

When OCaml types `Pmod_apply(F, Arg)`, it substitutes the functor parameter types with the argument types throughout the result module type. Rust returns a placeholder or incomplete substitution.

**Fix strategy:** In `typemod.rs`, the `Pmod_apply` handler needs to:
1. Type the functor and the argument
2. Match the argument against the functor parameter (Includemod)
3. Perform type substitution through the functor body's module type, replacing parameter paths with argument paths

**OCaml reference:** `compiler/ml/typemod.ml` `type_module_aux` case `Pmod_apply`, which calls `Includemod.modtypes` + `Mtype.strengthen` + substitution

**Additional issue:** Tvar→Tconstr under-resolution for functor parameter types — the functor's parameter types remain as Tvars instead of being resolved to the argument's concrete types.

---

## Phase 3: Path Normalization Issues (Cross-Cutting)

Several tests have path normalization as a secondary issue. These are places where OCaml preserves a qualified path like `Pdot(Belt.List, "t")` but Rust resolves to `Pident("list")`.

### Known Sub-Patterns

| Pattern | Example | Tests | Notes |
|---------|---------|-------|-------|
| Belt.X.t → base type | `Belt.List.t → list` | gpr_1701_test, splice_test, ext_array_test | Belt aliases standard library types |
| Stdlib.X → Stdlib_X | `Stdlib.JSON → Stdlib_JSON` | json_decorders, Stdlib_JsonTests, Stdlib_TempTests | Flattened module names |
| Js.X.t → base type | `Js.String2.t → string` | js_string_test, reasonReactRouter | Js bindings |
| Local module paths | `Pdot(Actors, "xy") → Pident("xy")` | mario_game, topsort_test | Module-scoped types |
| Module alias | `M → Path` | variant | Module aliases not expanded |

**Fix approach:** These are fundamentally about how `Env.find_type` / `lookup_type` returns paths. OCaml's environment stores types with their original qualified paths as inserted during module typing. The Rust environment may be flattening or canonicalizing paths at insertion time instead of preserving the original module-qualified form.

**WARNING:** A previous attempt at stdlib flattened-path normalization caused a 612→606 regression. The fix needs to be targeted, not blanket.

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

### Count diff hunks for a file
```bash
diff /tmp/ocaml.sexp /tmp/rust.sexp | grep "^[0-9]" | wc -l
```

### Compare specific type node sharing
If you suspect a sharing/identity issue, add temporary debug prints in `sexp_typedtree.rs` to show type node IDs alongside the sexp output.

### Check if a test failure is cycle-related
```bash
diff /tmp/ocaml.sexp /tmp/rust.sexp | grep -c "cycle"
```
If > 0, the test is (at least partially) affected by the cycle detection issue.

---

## Priority Order

1. **sexp_typedtree.rs cycle detection** — Do this FIRST. Highest impact (~38 tests). Well-understood fix. Was working before.
2. **ctype.rs non-generic identity** — Second. Well-understood, ~6 tests.
3. **typecore.rs begin_def/generalize/instance** — Third. ~3 tests. Requires care with update_level_expand guard.
4. **driver.rs interface constraints** — Fourth. ~3 tests. New code needed.
5. **typemod.rs remaining fixes** — Fifth. init_def, force_generalize, env threading.
6. **context.rs, btype.rs, persistent_env.rs** — Sixth. Supporting infrastructure.
7. **mario_game.res** — Path normalization + alias preservation. Hard.
8. **reasonReact.res** — Multiple sub-issues. Hard.
9. **defunctor_make_test.res** — Functor substitution. Hard.

---

## Known Anti-Patterns (DO NOT RETRY)

These approaches have been tried and cause regressions. They are documented here to prevent wasted effort:

| Approach | Result | Why |
|----------|--------|-----|
| Permanent cycle marking (current state) | 607/657 | Over-aggressive <cycle> detection |
| Leaf-node cycle exemption | Massive regression | Under-aggressive, creates infinite output |
| Ancestor-path tracking | Massive regression | Same problem |
| ALL non-generic types → identity | 650/656 | defunctor compile failure |
| Non-generic Tvariant → identity | 1 regression | |
| Blanket unify_var on pattern nodes | 619/657 | Modifies shared nodes |
| Fresh Tvar for all pattern vars | 622/657 | Over-generalizes |
| init_def before structure items (without guards) | 11 compile failures | Level system differences |
| begin_def + raising param_ty level | 20+ regressions | Cascading update_level_expand |
| Copy ALL Tconstr in type_function body | 7 regressions | Contamination |
| Stdlib flattened-path probes | 612→606 | Over-broad normalization |
| UnifyMode::Pattern routing | 609→602 | Over-broad |
| Removing React-element memoization skip | 607→606 | async_jsx regression |
| N.eq sharing broadening | Over-sharing | Worsens specific call sites |
| type_cases post-finalization unify_pats | 608→601 | Too aggressive threading |
| Pexp_constraint generalized ctyp_type | Regression | option_repr_test.res |

---

## All 50 Failing Tests — Categorized

### Pure Cycle Detection (17 tests)
These should ALL be fixed by Phase 1A (stack-based cycle detection):

| # | Test | Diff Lines | Pattern |
|---|------|-----------|---------|
| 1 | update_record_test.res | 7 | `Tconstr(Pident "t")` vs `<cycle>` |
| 2 | bs_mutable_set_test.res | 9 | `<cycle>` vs `Tconstr(Pdot(N) "t")` |
| 3 | bs_poly_map_test.res | 11 | cycle depth difference |
| 4 | bs_queue_test.res | 99 | `<cycle>` vs `Tconstr(Pdot(Q) "t")` |
| 5 | bs_stack_test.res | 119 | `<cycle>` vs `Tconstr(Pident "node")` |
| 6 | earger_curry_test.res | 14 | `<cycle>` vs `Tconstr(Pident "float")` |
| 7 | functor_ffi.res | 28 | `<cycle>` vs `Tconstr(Pident "int")` |
| 8 | miss_colon_test.res | 42 | bidirectional cycle |
| 9 | variantsMatching.res | 203 | `<cycle>` vs `Tconstr(Pident "t")` |
| 10 | rbset.res | 196 | `Tconstr(Pident "t")` vs `<cycle>` |
| 11 | test_set.res | 1251 | `Tconstr(Pident "t")` vs `<cycle>` (163 hunks) |
| 12 | inline_map_test.res | 350 | bidirectional |
| 13 | inline_map2_test.res | 375 | bidirectional |
| 14 | large_record_duplication_test.res | 28 | `Tconstr(Pident "t"/"exn")` vs `<cycle>` |
| 15 | test_seq.res | 14 | cycle depth difference (Ttuple) |
| 16 | flexible_array_test.res | 60 | cycle depth + Tconstr |
| 17 | bs_set_int_test.res | 27 | bidirectional `Tconstr(Pdot(N))` vs `<cycle>` |

### Pure Path Normalization (7 tests)
These need path preservation fixes in env/typemod:

| # | Test | Diff Lines | Pattern |
|---|------|-----------|---------|
| 18 | json_decorders.res | 8 | `Stdlib.JSON` → `Stdlib_JSON` |
| 19 | option_repr_test.res | 24 | `Pdot(N, "t")` vs `Pident("list")` |
| 20 | gpr_1701_test.res | 240 | `Belt.List.t` vs `list` |
| 21 | splice_test.res | 330 | `Belt.Array.t` vs `array` |
| 22 | Stdlib_JsonTests.res | 136 | `Stdlib.JSON` vs `Stdlib_JSON` |
| 23 | Stdlib_TempTests.res | 64 | `Stdlib.JSON` vs `Stdlib_JSON` |
| 24 | variant.res | 44 | module name `M` vs `Path` |

### Type Resolution (2 tests)
Need interface constraint propagation or type identity fixes:

| # | Test | Diff Lines | Pattern |
|---|------|-----------|---------|
| 25 | Stdlib_ObjectTests.res | 24 | `Tvar None` vs `Tconstr("string")` |
| 26 | gpr_4274_test.res | 250 | bidirectional Tvar vs Tconstr + paths |

### Polymorphic Variant Rows (1 test)

| # | Test | Diff Lines | Pattern |
|---|------|-----------|---------|
| 27 | gpr_4280_test.res | 1252 | `Rpresent/closed` vs `Reither/open` |

### Module Structure (1 test)

| # | Test | Diff Lines | Pattern |
|---|------|-----------|---------|
| 28 | async_jsx.res | 42396 | Fundamentally different JSX async desugaring |

### Other (1 test)

| # | Test | Diff Lines | Pattern |
|---|------|-----------|---------|
| 29 | unboxed_use_case.res | 122 | `Tunivar` vs `Tvar` + type under-resolution |

### Multi-Category (21 tests)
Tests with overlapping root causes. Fix cycle detection first, then the secondary issues:

| # | Test | Primary | Secondary | Notes |
|---|------|---------|-----------|-------|
| 30 | exception_raise_test.res | path | cycle | Belt.List.t + tuple cycle |
| 31 | ext_array_test.res | path + cycle | type | Belt.List.t + <cycle> + Tvar |
| 32 | string_set.res | cycle + path | | Set_gen.t cycle + Belt.List |
| 33 | js_string_test.res | cycle + path | | Js.String2.t cycle |
| 34 | reasonReactRouter.res | path + cycle | | string vs Js.String.t |
| 35 | ticker.res | cycle + path | type | multiple cycles + paths |
| 36 | topsort_test.res | path + cycle | | String_set paths + cycle |
| 37 | js_json_test.res | path + type | | dict paths + type var names |
| 38 | jsx_preserve_test.res | path + cycle | other | React.element + field order |
| 39 | jsxv4_newtype.res | cycle + type | | Tvar name + cycle |
| 40 | more_poly_variant_test.res | poly + type + cycle | | Rpresent vs Reither |
| 41 | fun_pattern_match.res | type + poly | | Tvariant vs Tvar |
| 42 | set_gen.res | cycle + poly | | recursive type + open/closed |
| 43 | test_bs_this.res | cycle + object + type | | cycle + Tobject + Tvar |
| 44 | pipe_send_readline.res | cycle + object | | cycle + Tobject |
| 45 | defunctor_make_test.res | cycle + type + path | | Functor substitution |
| 46 | mario_game.res | path + cycle + type | | Pdot(Actors) + alias |
| 47 | reasonReact.res | type + path + cycle + obj | | 5 sub-issues |
| 48 | Stdlib_Intl_DateTimeFormatTest.res | cycle + type | | Stdlib.Date cycle |
| 49 | UntaggedVariants.res | type + path + cycle | | bidirectional Tvar/Tconstr |
| 50 | type_coercion_free_vars.res | cycle + type | | cycle + under-resolution |

---

## Recovery Resources

If you need to reference the previous working implementation:
- Recovery artifacts at `~/dev/recovery/` (3.6 GB)
- The `typed-ast-parity` branch may still exist on the remote
- `/tmp` snapshots may contain pre-reconstruction source files

## Key Files Reference

| File | Key Functions | Lines |
|------|--------------|-------|
| `compiler-rust/src/types/sexp_typedtree.rs` | Cycle detection, type serialization | ~line 397+ |
| `compiler-rust/src/types/ctype.rs` | `copy_type_cached`, `update_level_expand`, `instance` | ~2600-2900 |
| `compiler-rust/src/types/typecore.rs` | `type_function`, `type_case_impl`, `type_record` | ~6260+, ~6461+, ~7431+ |
| `compiler-rust/src/types/typemod.rs` | `force_generalize`, `type_structure`, `Pmod_apply` | ~6389+ |
| `compiler-rust/src/driver.rs` | `apply_interface_constraints`, `propagate_sig_types` | ~713+, ~767+ |
| `compiler-rust/src/types/context.rs` | `begin_def`, `end_def`, `new_var` | ~595-625 |
| `compiler/ml/typecore.ml` | `type_cases` (OCaml reference) | 3906-4024 |
| `compiler/ml/ctype.ml` | `copy`, `generalize_expansive` (OCaml reference) | 717-742 |
| `compiler/ml/typemod.ml` | Module typing (OCaml reference) | |
| `compiler/ml/sexp_typedtree.ml` | Sexp serialization (OCaml reference) | |
