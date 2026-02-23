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

**~610/657 (47 failures)**

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

---

## Key Architecture Notes

- **OCaml `type_cases` processes ALL patterns before ALL bodies** (batch). Rust processes each case independently. OCaml's batch approach enables `unify_var` + `end_def` + `generalize` cycle.
- **OCaml `Pexp_record` `unify_kept`** creates TWO label instances per field to connect base_type ↔ label1 ↔ label2 ↔ expected_type.
- **OCaml `instance()` returns identity for ALL non-generic types** in `copy`. Rust can only do this selectively.
- **CMI value-type path substitution is load-bearing** — can't remove without fixing type identity system.
- **Sexp cycle detection must use permanent marking** — stack-based marking and leaf-skip both cause massive regressions.
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
