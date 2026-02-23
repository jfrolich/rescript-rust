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

**607/657 (50 failures)**

---

## Repo Reconstruction Context

This repo was reconstructed after accidental deletion. The base comes from a `/tmp/rescript_head_clean/` worktree (Feb 18, ~611/657 state on HEAD branch, NOT the `typed-ast-parity` branch which had reached ~654/657). The two most-modified files were overlaid from more recent `/tmp` snapshots:
- `typecore.rs` from `/tmp/typecore_with_fix.rs` (Feb 22, 12,595 lines)
- `ctype.rs` from `/tmp/ctype_current.rs` (Feb 21, 4,121 lines)

**Other files (`typemod.rs`, `sexp_typedtree.rs`, `context.rs`, `driver.rs`) are at the Feb 18 worktree state and may be missing fixes applied between Feb 18-22.** Recovery artifacts are saved at `~/dev/recovery/` (3.6 GB).

### Fixes Applied Between 611/657 → 654/657 (may need re-applying)

#### In `ctype.rs` (overlaid from Feb 21 — should have most fixes)
- **`copy_type_cached` selective non-generic identity**: Return `ReturnSelf` for Tvar, Tunivar, predef Tconstr (nullary + concrete args), Ttuple, Tarrow, Tobject, Tfield, Tnil. Do NOT return identity for all Tconstr, Tvariant, or Tpackage.
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

#### In `typemod.rs` (MAY NEED RE-APPLYING — at Feb 18 state)
- **`init_def(current_time())` synchronization**: Before each structure item in `type_structure`, before each signature item in `transl_signature`, in functor body, and in rec module. (OCaml typemod.ml lines ~1598, ~750, ~1291, ~950)
- **`transl_signature` environment threading**: Thread env through open statements.
- **`force_generalize` skip for `Pmod_structure`**: Preserve non-generic levels from value restriction.

#### In `sexp_typedtree.rs` — DO NOT CHANGE CYCLE DETECTION
- **Permanent marking is CORRECT** — do NOT change to stack-based/temporary marking (causes 607→220 regression). The "+87 file improvement" from the original TODO was WRONG — cycle diffs come from type checker sharing, not the serializer.
- **Evaluation order** (MAY NEED RE-APPLYING): Tarrow, Tfield, Tpoly → left-to-right child evaluation.
- **Reither faithful printing** (MAY NEED RE-APPLYING): Use `row_field_repr_ctx` instead of `row_field_repr`.

#### In `context.rs` (MAY NEED RE-APPLYING — at Feb 18 state)
- **`current_stamp()` accessor**: Rust equivalent of OCaml's `Ident.current_time()`.
- **`new_row_field_ref` public method**: For shared RowFieldRef linking.

#### In `driver.rs` (MAY NEED RE-APPLYING — at Feb 18 state)
- **`apply_interface_constraints`**: Read CMI, walk impl/sig types in parallel, link non-generic Tvars.
- **`propagate_sig_types`**: Walk module signatures recursively.
- **`try_alias_param_propagation`**: Handle parametric type aliases with different arities.

#### In `btype.rs` (MAY NEED RE-APPLYING)
- **`row_field_repr_ctx` / `row_field_repr_ctx_aux`**: Follow RowFieldRef links through TypeContext.

#### In `persistent_env.rs` (MAY NEED RE-APPLYING)
- **Recursive module prefix rewriting**: Recursively descend into SigModule submodule signatures when rewriting flattened module names.

---

## Re-apply Tasks (607 → ~654)

**IMPORTANT: The cycle detection diffs are caused by type checker sharing differences, NOT the serializer. Do NOT change sexp_typedtree.rs cycle detection. See RALPH_GUIDANCE.md for full explanation.**

**Fix order matters — later fixes depend on earlier ones.**

- [ ] **1A. `copy_type_cached` generic sharing via placeholders in ctype.rs (~40 tests)** — Allocate placeholder node FIRST, cache it, THEN recurse into children, THEN fill in. This matches OCaml's `Tsubst` pattern in `copy` (ctype.ml ~line 863). Currently Rust recurses first then creates copy, causing different sharing. This is the HIGHEST IMPACT fix. See RALPH_GUIDANCE.md Phase 1 Section 1A.
- [ ] **1B. `Pexp_ident` local monomorphic type sharing in typecore.rs (~80 tests)** — For non-generic value types (especially nullary Tconstr and Tarrow), reuse source type by identity instead of calling `instance()`. OCaml's `instance()` → `copy` returns identity for all non-generic types. See RALPH_GUIDANCE.md Phase 1 Section 1B.
- [ ] **1C. `type_function` exp_type instantiation in typecore.rs** — Create expected function type as `instance(new_generic_arrow(...))` and re-anchor pattern/body types from it. See RALPH_GUIDANCE.md Phase 2 Section 2B.
- [ ] **1D. Small type checker fixes** — `link_type` name propagation, `type_variables` reset (don't clear in type_function), `Pexp_constraint` generalization ordering (var_level after end_def), `exp_extra` prepend ordering (insert at pos 0), object field fold ordering. See RALPH_GUIDANCE.md Phase 3 Section 3D.
- [ ] **1E. `force_generalize` skip for Pmod_structure in typemod.rs** — Skip force_generalize in Pmod_structure to preserve non-generic levels from value restriction.
- [ ] **1F. Interface constraint propagation in driver.rs (~3 tests)** — Add `apply_interface_constraints`, `propagate_sig_types`, `try_alias_param_propagation`.
- [ ] **1G. Supporting infrastructure in context.rs, btype.rs, persistent_env.rs, typemod.rs** — `current_stamp()`, `new_row_field_ref`, `row_field_repr_ctx`, recursive module prefix rewriting, `init_def(current_time())` synchronization, `transl_signature` env threading. WARNING: `init_def` without guards causes 11 compile failures.
- [ ] **1H. `type_function` begin_def/generalize/instance in typecore.rs (~3 tests)** — Add begin_def before pattern typing, end_def after, generalize pattern types, instance() for body env. REQUIRES `update_level_expand` guard for ALL local Pident types. WARNING: Without guard = 20+ regressions.
- [ ] **1I. Non-generic Tarrow/Tobject/Tfield/Tnil identity in ctype.rs (~6 tests)** — Return `ReturnSelf` for non-generic Tarrow, Tobject, Tfield, Tnil. **MUST be done AFTER 1A, 1B, 1H are in place** — without them, this regresses (607→604). WARNING: Do NOT extend to Tvariant or ALL types.

---

## Remaining Failure Root Causes

All remaining failures trace back to type checker sharing differences:

### 1. Type checker sharing (~38 tests)
Rust's `copy_type_cached` and `instance()` create different node sharing than OCaml's `copy`. OCaml uses `Tsubst` placeholder pattern (allocate first, cache, recurse, fill in) which ensures generic types are shared correctly. Rust recurses first then creates copies, causing MORE sharing of arena nodes than OCaml → false `<cycle>` marks AND missing `<cycle>` marks. **Fix is in the type checker (copy_type_cached, Pexp_ident sharing), NOT the serializer.** Five serializer approaches tried, ALL regressed.

### 2. Path normalization (~22 tests)
Rust's CMI loading (`substitute_type_paths_in_sig`) rewrites paths differently from OCaml. OCaml's `prefix_idents` + `Subst` only affects module component tables, not value type expressions. Removing value-type substitution causes massive regression because Rust type checker relies on qualified paths for unification. Root cause: Rust uses path equality for type identity; OCaml uses stamp-based identity.

### 3. Polyvariant rows (~3 tests)
Rust prematurely resolves `Reither` to `Rpresent`. OCaml keeps `Reither` until finalization. Also open/closed row differences. Fix requires porting OCaml's full row unification semantics.

### 4. Tvar vs Tconstr (~18 tests)
Rust eagerly resolves type variables through unification links while OCaml preserves unresolved `Tvar None` in certain scoping contexts. Fix requires `type_function` begin_def/generalize/instance cycle and correct non-generic identity in `copy_type_cached`.

### 5. Specific hard files (never solved, even at 654/657)
- **mario_game.res**: Path normalization Pident→Pdot(Actors) (246 hunks) + type alias `xy` expansion
- **reasonReact.res**: Over-resolution, locations, under-resolution in WrapProps, alias, paths
- **defunctor_make_test.res**: Functor application substitution missing (Pmod_apply)
- **async_jsx.res**: JSX async desugaring produces fundamentally different tree structure

---

## Known Failed Approaches (DO NOT RETRY)

### CRITICAL: Serializer Cycle Detection Changes — ALL FAIL

**Do NOT modify sexp_typedtree.rs cycle detection.** The permanent marking is correct. Five approaches tried:

| Serializer Approach | Result | Why It Failed |
|----------|--------|---------------|
| **Stack-based (temporary) marking** | **607 → 220** | **Removes false cycles that coincidentally match OCaml's real cycles** |
| **Leaf-node cycle exemption** | **607 → 239** | **Same reason — different false cycles removed** |
| **Ancestor-path tracking** | **Massive regression** | **Same reason** |
| One-level look-ahead | No improvement | |
| Hybrid marking | No improvement | |

The cycle diffs are caused by type checker sharing, not the serializer. Fix `copy_type_cached` and `Pexp_ident` sharing instead.

### Type Checker Approaches That Failed

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
| Non-generic Tarrow/Tobject/Tfield/Tnil identity (WITHOUT 1A/1B) | 607→604 | Needs placeholder caching + Pexp_ident sharing first |
| `unify_after_expansion` pre-link ordering (OCaml `unify3`) | Stack overflow on DictInference.res | |
| Stdlib flattened-path normalization probes | 612→606 regression | |
| UnifyMode::Pattern disabling structural link_type | 609→602 regression | |
| Broad non-generic `Tarrow` identity in copy_type_cached (alone) | 609→607 regression | Needs 1A/1B first |
| Removing `arg_expr_is_apply` gate in adjacent-argument linking | Over-shared further | |
| Skipping SigValue path substitution in persistent_env | Rust bsc 622/657, Parity 431/622 | |
| Broad Ctype.copy non-generic identity (all nodes) | Rust bsc 651/657, Parity 585/651 | |

---

## Key Architecture Notes

- **SEXP CYCLE DETECTION IS CORRECT** — permanent marking in `sexp_typedtree.rs` must NOT be changed. Cycle diffs come from type checker sharing differences, not the serializer. Five serializer alternatives tried, all regressed. See "Known Failed Approaches" above.
- **OCaml `copy` uses `Tsubst` placeholder pattern** — allocate copy node FIRST, cache via `Tsubst`, recurse children, fill in. This is the KEY to correct sharing. Rust must match this pattern in `copy_type_cached`.
- **OCaml `instance()` returns identity for ALL non-generic types** in `copy`. Rust can only do this selectively — doing it for ALL types causes defunctor crash + regressions.
- **OCaml `type_cases` processes ALL patterns before ALL bodies** (batch). Rust processes each case independently. OCaml's batch approach enables `unify_var` + `end_def` + `generalize` cycle.
- **OCaml `Pexp_record` `unify_kept`** creates TWO label instances per field to connect base_type ↔ label1 ↔ label2 ↔ expected_type.
- **CMI value-type path substitution is load-bearing** — can't remove without fixing type identity system.
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
