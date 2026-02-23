# Typed Tree Parity TODO

## Goal

Achieve 100% parity on `-dtyped-sexp-locs` output between OCaml and Rust compilers on all 657 files in `tests/tests/src/`.

## Instructions for Agents

1. **NEVER revert commits made by other agents or humans.**
2. **Commit your changes frequently** — follow CLAUDE.md.
3. **Follow the OCaml reference implementation exactly** — this is a 1:1 port.
4. **GET TO THE ROOT CAUSE — DO NOT GIVE UP.**
5. **Update this TODO when you discover work is already done.**
6. **One task per session** — complete one task, commit, stop.
7. **Ignore generated JS output files** — `*.js`, `*.mjs`, `*.cjs` are not part of this work.
8. **No docs-only revalidation loops** — don't create commits that only re-run baselines.
9. **Cite OCaml sources for every fix.**

---

## ALWAYS USE TIMEOUTS

The Rust type checker **WILL hang/infinite loop** on many inputs.

- Single file: `timeout 10 ./compiler-rust/target/release/bsc ...`
- Test scripts: `timeout 300 ./scripts/test_typedtree_parity.sh ...`
- Cargo: `timeout 120 cargo test ...`

---

## How to Test

```bash
# Build
cargo build --manifest-path compiler-rust/Cargo.toml --release

# Full parity suite
timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1

# Single file
timeout 10 ./scripts/test_typedtree_parity.sh --with-locs --no-build tests/tests/src/a.res

# Quick mode (stop on first failure)
timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --quick
```

---

## Current Status

**611/657 (46 failures)**

---

## Repo Reconstruction Context

This repo was reconstructed after accidental deletion. The base comes from a `/tmp/rescript_head_clean/` worktree (Feb 18, ~611/657 state on HEAD branch, NOT the `typed-ast-parity` branch which had reached ~654/657). The two most-modified files were overlaid from more recent `/tmp` snapshots:
- `typecore.rs` from `/tmp/typecore_with_fix.rs` (Feb 22, 12,595 lines)
- `ctype.rs` from `/tmp/ctype_current.rs` (Feb 21, 4,121 lines)

**Other files (`typemod.rs`, `sexp_typedtree.rs`, `context.rs`, `driver.rs`) are at the Feb 18 worktree state and may be missing fixes applied between Feb 18-22.** Recovery artifacts are saved at `~/dev/recovery/` (3.6 GB).

### Fixes Applied Between 611/657 → 654/657 (may need re-applying)

**⚠️ CRITICAL CORRECTION (Feb 23):** Many claims in this section were WRONG. Verified against `origin/typed-ast-parity` branch using `git show`. Key corrections:
- **Stack-based cycle detection NEVER existed on typed-ast-parity** — it uses permanent marking (same as current branch)
- **`apply_interface_constraints`, `propagate_sig_types`, `force_generalize` do NOT exist on typed-ast-parity** — these were invented in recovery docs
- **Tarrow/Tfield/Tnil should be COPIED, not ReturnSelf** — typed-ast-parity copies them (less sharing = fewer false cycles)

#### In `ctype.rs` (overlaid from Feb 21 — PARTIALLY CORRECT)
- **`copy_type_cached` selective non-generic identity**: Return `ReturnSelf` for Tvar, Tunivar, predef Tconstr (nullary + concrete args), Ttuple, Tobject. **COPY (not ReturnSelf) Tarrow, Tfield, Tnil** — verified on typed-ast-parity. Do NOT return identity for all Tconstr, Tvariant, or Tpackage.
- **`update_level_expand` path preservation guards**: Skip expansion for nullary Pident local types and nullary Pdot paths with local roots.
- **`try_expand_head` split**: Into `try_expand_head` (with normalization) and `try_expand_head_inner` (without) for level updates.
- **Shared RowFieldRef linking**: Reither/Reither unification creates shared refs (OCaml ctype.ml:2700-2704).

#### In `typecore.rs` (overlaid from Feb 22 — should have all fixes)
- **`type_function` begin_def/generalize/instance cycle**: begin_def before pattern typing, end_def after, generalize pattern types, instance() for body env. (OCaml typecore.ml:3906-4024)
- **`type_function` stop clearing `type_variables`**: OCaml does NOT clear in type_function.
- **`type_argument` re-unification**: Preserve type alias identity in record field values.
- **Pattern variable shallow copy**: Protect from body unification contamination.
- **Scrutinee type protection**: Shallow-copy Tconstr when instance() returns identity.
- **`close_variant_row_for_pat_type` rewrite**: Match OCaml parmatch.ml:808-832.
- **Label disambiguation `lookup_from_type`**: Add before leaf-name fallback.

#### In `typemod.rs` (at Feb 18 state)
- **`init_def(current_time())` synchronization**: Before each structure item in `type_structure`, before each signature item in `transl_signature`, in functor body, and in rec module. (OCaml typemod.ml lines ~1598, ~750, ~1291, ~950)
- **`transl_signature` environment threading**: Thread env through open statements.
- ~~**`force_generalize` skip for `Pmod_structure`**~~ — **DOES NOT EXIST on typed-ast-parity.** May have been on current branch's typecore.rs overlay.

#### In `sexp_typedtree.rs` — DO NOT CHANGE CYCLE DETECTION
- ~~**Stack-based cycle detection**~~ — **WRONG. Typed-ast-parity uses PERMANENT marking (same as current branch).** Stack-based was tried and causes 610→220 regression. The 654/657 achievement was NOT from changing cycle detection.
- **Evaluation order** (MAY NEED RE-APPLYING): Tarrow, Tfield, Tpoly → left-to-right child evaluation.
- **Reither faithful printing** (MAY NEED RE-APPLYING): Use `row_field_repr_ctx` instead of `row_field_repr`.

#### In `context.rs` (MAY NEED RE-APPLYING — at Feb 18 state)
- **`current_stamp()` accessor**: Rust equivalent of OCaml's `Ident.current_time()`.
- **`new_row_field_ref` public method**: For shared RowFieldRef linking.

#### In `driver.rs` (at Feb 18 state)
- ~~**`apply_interface_constraints`**~~ — **DOES NOT EXIST on typed-ast-parity.** May have been on current branch's overlay.
- ~~**`propagate_sig_types`**~~ — **DOES NOT EXIST on typed-ast-parity.**
- ~~**`try_alias_param_propagation`**~~ — **DOES NOT EXIST on typed-ast-parity.**

#### In `btype.rs` (MAY NEED RE-APPLYING)
- **`row_field_repr_ctx` / `row_field_repr_ctx_aux`**: Follow RowFieldRef links through TypeContext.

#### In `persistent_env.rs` (MAY NEED RE-APPLYING)
- **Recursive module prefix rewriting**: Recursively descend into SigModule submodule signatures when rewriting flattened module names.

---

## Re-apply Tasks (611 → ~654)

- [x] **1A. ~~Stack-based cycle detection~~ INVALID** — Typed-ast-parity uses permanent marking. Stack-based causes 610→220 regression. DO NOT ATTEMPT.
- [x] **1B. Non-generic Tarrow/Tfield/Tnil: COPY not identity** — Verified typed-ast-parity COPIES these types. Reverted from ReturnSelf to copy. Result: 610→611 (gained bal_set_mini.res). Tobject stays ReturnSelf for stack overflow safety.
- [ ] **1C. begin_def/generalize/instance in typecore.rs type_function (~3 tests)** — Add begin_def before pattern typing, end_def after, generalize pattern types, instance() for body env. Also extend update_level_expand guard to skip ALL local Pident types.
- [ ] **1D. ~~force_generalize skip for Pmod_structure~~ NEEDS VERIFICATION** — Does NOT exist on typed-ast-parity branch. May have been added independently.
- [ ] **1E. ~~Interface constraint propagation in driver.rs~~ NEEDS VERIFICATION** — `apply_interface_constraints`, `propagate_sig_types`, `try_alias_param_propagation` do NOT exist on typed-ast-parity branch.
- [ ] **1F. Supporting infrastructure in context.rs, btype.rs, persistent_env.rs, typemod.rs** — `current_stamp()`, `new_row_field_ref`, `row_field_repr_ctx`, recursive module prefix rewriting, `init_def(current_time())` synchronization, `transl_signature` env threading.
- [ ] **NEW: Apply remaining fixes from RALPH_GUIDANCE.md** — Fix 18 (predef variances), Fix 19 (depth-restricted prefix rewriting), Fix 3 (coercion subtype), Fix 13 (deep-copy Tvariant), Fix 9 (expand before structural match), Fix 14 (build_as_type), Fix 17 (label type param sharing), Fix 5 (shallow-copy pattern vars), Fix 7 (scrutinee type protection), Fix 16 (shallow copy nullary pattern vars), Fix 8 (force-generalize module sig), Fix 21 (GADT equations), Fix 15 (per-case generalization), Fix 24 (begin_def in type_function), Fix 4 (qualified label lookup), Fix 20 (local Pdot expansion guard).

---

## Remaining Failure Root Causes

All remaining failures are deep structural issues:

### 1. Cycle detection (~20 tests)
Rust's type sharing differs from OCaml's. The sexp printer's `HashSet<TypeExprRef>` permanent marking catches shared-but-not-cyclic nodes as false cycles. Multiple serializer approaches tried (temporary marking, leaf-skip, ancestor-path tracking) — all caused massive regressions. Root cause is in type checker sharing semantics, not the serializer.

### 2. Path normalization (~22 tests)
Rust's CMI loading (`substitute_type_paths_in_sig`) rewrites paths differently from OCaml. OCaml's `prefix_idents` + `Subst` only affects module component tables, not value type expressions. Removing value-type substitution causes massive regression because Rust type checker relies on qualified paths for unification. Root cause: Rust uses path equality for type identity; OCaml uses stamp-based identity.

### 3. Polyvariant rows (~3 tests)
Rust prematurely resolves `Reither` to `Rpresent`. OCaml keeps `Reither` until finalization. Also open/closed row differences. Fix requires porting OCaml's full row unification semantics.

### 4. Tvar vs Tconstr (~18 tests)
Rust eagerly resolves type variables through unification links while OCaml preserves unresolved `Tvar None` in certain scoping contexts. Fix requires more precise generalization level tracking.

### 5. Specific hard files
- **mario_game.res**: Path normalization Pident→Pdot(Actors) (246 hunks) + type alias `xy` expansion
- **reasonReact.res**: Over-resolution, locations, under-resolution in WrapProps, alias, paths
- **defunctor_make_test.res**: Functor application substitution missing (Pmod_apply)
- **async_jsx.res**: JSX async desugaring produces fundamentally different tree structure

---

## Known Failed Approaches (DO NOT RETRY)

| Approach | Result | Why It Failed |
|----------|--------|---------------|
| Blanket `unify_var` on all pattern nodes in type_case | 619/657 | Too aggressive, modifies shared nodes |
| Fresh env Tvar for all pattern variables | 622/657 | Breaks cases where type SHOULD be resolved |
| Targeted Tlink interposition for pattern Tvars | 624/657 | Still too many matches |
| `init_def(current_time())` before structure items (without guards) | 11 compile failures + ~20 regressions | Rust level system works differently |
| ALL non-generic types returning identity in copy_type_cached | 650/656 | defunctor compile failure + 3 new failures |
| Non-generic Tvariant returning identity | 652/657 (1 regression) | |
| Removing Pdot-local-root skip in update_level_expand | 652/657 | topsort_test regression |
| begin_def in type_function + raising param_ty level | 20+ regressions | Cascading update_level_expand issues |
| Copying ALL Tconstr in type_function body env | 7 map/topsort regressions | |
| Leaf-node cycle detection exemption | 504→207 | Massive regression |
| Ancestor-path tracking cycle detection | 504→194 | Massive regression |
| `unify_after_expansion` pre-link ordering (OCaml `unify3`) | Stack overflow on DictInference.res | |
| Stdlib flattened-path normalization probes | 612→606 regression | |
| UnifyMode::Pattern disabling structural link_type | 609→602 regression | |
| Broad non-generic `Tarrow` identity in copy_type_cached | 609→607 regression | |
| Removing `arg_expr_is_apply` gate in adjacent-argument linking | Over-shared further | |
| Skipping SigValue path substitution in persistent_env | Rust bsc 622/657, Parity 431/622 | |
| Broad Ctype.copy non-generic identity (all nodes) | Rust bsc 651/657, Parity 585/651 | |
| Stack-based cycle detection on current branch | 610→220 | OCaml also uses permanent marking; typed-ast-parity confirmed |
| Nullary Tconstr cycle detection exemption | 1→4 hunks on update_record_test | Creates new false under-detections |
| ReturnSelf for non-generic Tarrow/Tfield/Tnil | 610 (neutral→worse) | More sharing = more false cycles; typed-ast-parity COPIES them |

---

## Key Architecture Notes

- **OCaml `type_cases` processes ALL patterns before ALL bodies** (batch). Rust processes each case independently. OCaml's batch approach enables `unify_var` + `end_def` + `generalize` cycle.
- **OCaml `Pexp_record` `unify_kept`** creates TWO label instances per field to connect base_type ↔ label1 ↔ label2 ↔ expected_type.
- **OCaml `instance()` returns identity for ALL non-generic types** in `copy`. Rust can only do this selectively.
- **CMI value-type path substitution is load-bearing** — can't remove without fixing type identity system.
- **Sexp cycle detection must use permanent marking** — verified on typed-ast-parity (654/657). Stack-based (610→220), leaf-skip, ancestor-path all cause massive regressions. The path to fixing cycle parity is through reducing type sharing in the type checker (fewer shared nodes = fewer false cycles).
- **Record pattern fields must be sorted by `lbl_pos`** (OCaml invariant).
- **OCaml Reither has mutable `ref option` link** — `set_row_field` sets it during unification, `row_field_repr` follows links. Rust's `RowFieldRef` link is allocated but NEVER set.

---

## Key OCaml Reference Files

| File | Purpose |
|------|---------|
| `compiler/ml/typecore.ml` | Expression/pattern type checking |
| `compiler/ml/typemod.ml` | Module type checking |
| `compiler/ml/ctype.ml` | Core type operations / unification |
| `compiler/ml/sexp_typedtree.ml` | S-expression printer — what we must match |
| `compiler/ml/env.ml` | Type environment |
| `compiler/ml/types.ml` / `.mli` | Core type representation |
| `compiler/ml/btype.ml` | Basic type operations |

## Key Rust Files

| File | Purpose |
|------|---------|
| `compiler-rust/src/types/typecore.rs` | Expression/pattern type checking |
| `compiler-rust/src/types/typemod.rs` | Module type checking |
| `compiler-rust/src/types/ctype.rs` | Core type operations (unify, generalize) |
| `compiler-rust/src/types/sexp_typedtree.rs` | S-expression printer |
| `compiler-rust/src/types/context.rs` | TypeContext with arena-based allocation |
| `compiler-rust/src/driver.rs` | Driver, interface constraint propagation |

---

## Debugging Tips

1. **Start with simple files** — test with `let x = 1`, `let f = x => x` before complex files.
2. **Compare sexp output side by side** — pipe through `diff -u`.
3. **Read the OCaml type checker code** — when Rust output is wrong, trace through OCaml to understand expected behavior.
4. **The sexp printer skips `Env.t` and `Types.signature`** — never prints environments.
5. **Ident stamps are skipped** — only names are printed for determinism.
6. **`type_expr` follows `Tlink` chains** via `Btype.repr` in OCaml.
