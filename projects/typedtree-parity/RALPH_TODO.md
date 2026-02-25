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
# Build Rust compiler
cargo build --manifest-path compiler-rust/Cargo.toml --release

# Full parity check (~30s, builds OCaml + Rust sexp via rewatch, raw comparison)
./scripts/test_typedtree_parity.sh

# Single file (~1s, uses rewatch --filter, shows diff inline on failure)
./scripts/test_typedtree_parity.sh async_inline

# Glob pattern
./scripts/test_typedtree_parity.sh "belt_*"

# File path (extracts module name)
./scripts/test_typedtree_parity.sh tests/tests/src/a.res
```

Results persist in `.parity-cache/` — inspect diffs at `.parity-cache/tests/diffs/*.diff`, raw sexp at `.parity-cache/tests/ocaml/*.sexp` and `.parity-cache/tests/rust/*.sexp`.

**Important:** The comparison is raw byte-for-byte (`cmp -s`). No post-processing. Both compilers must produce identical output.

---

## Current Status

**632/657 (96%) — raw byte-for-byte comparison**

**Latest snapshot (2026-02-25, clean-cache verified):**
- Typecheck parity: `632/657`
- Rust type-check: `651/657` (6 Rust-only errors)
- Parity failures: `19`
- Hunk mismatches: `246` (binary-only diffs: 5)
- OCaml-only pass (Rust errors): `derive_projector_test`, `offset`, `PartialApplicationNoRuntimeCurry`, `Stdlib_Intl_ListFormatTest`, `test_regex`, `variantsMatching`
- Remaining parity failures: `bal_set_mini`, `belt_internal_test`, `defunctor_make_test`, `ext_array_test`, `flexible_array_test`, `fun_pattern_match`, `functor_ffi`, `gpr_1701_test`, `mario_game`, `pipe_send_readline`, `set_gen`, `Stdlib_Intl_DateTimeFormatTest`, `test_bs_this`, `test_list`, `test_seq`, `test_set`, `ticker`, `topsort_test`, `unboxed_use_case`

**Recent fixes:**
- ~~Recursive poly variant infinite expansion~~ — Removed same-path parameterized Tconstr expansion that caused infinite recursion for `type rec vlist<'a> = [#Nil | #Cons('a, vlist<'a>)]`. OCaml's unify3 just unifies args; expansion in unify2 uses abbreviation memoization Rust doesn't have. Fixed `more_poly_variant_test` and `js_json_test` (+22 parity, -2 errors, -110 hunks).
- ~~`inline_const` prim encoding drift~~ — Fixed template literal delimiter in `@inline` sig payloads. Fixed `inline_const`.
- ~~`LetUnwrap` synthesized pattern locations~~ — Fixed `make_let_unwrap_early_case` to use `LocIdx::none()`.
- ~~Local-name numbering drift~~ — Fixed by resetting `local_module_counter`. Fixed `hello_res`, `internal_unused_test`.
- ~~Byte/encoding drift in string literals~~ — Fixed by removing `latin1_to_utf8`. Fixed `Stdlib_Intl_CollatorTest`, `tagged_template_test`.

**Remaining failure buckets (high-level):**
- Type sharing / cycle rendering drift (`<cycle>` vs concrete nodes): largest cluster (~30 tests)
- Path normalization drift (`Pdot`/`Pident`, alias path names): ~8 tests
- Row variant representation drift (`open/closed`, `Reither`/`Rpresent`)
- Under/over-resolution (Tvar names, extra unification links): ~3 tests

**Important:** historical entries below include older baselines and recovered branch notes; do not treat them as the current scorecard.

### 2026-02-24 Task 5 Deep-Copy: 637 → 644

- Updated `compiler-rust/src/types/ctype.rs::copy_type_deep` to do strict deep copies for `Tvariant`/`Tobject`/`Tfield` without reusing `row_more` or `Reither.link` identity from source nodes.
- OCaml refs read:
  - `compiler/ml/subst.ml` (`typexp`, especially `Tvariant`/`Tobject`/`Tfield` branches and stub-first recursion shape)
  - `compiler/ml/ctype.ml` (`copy` and `instance_label` row/object copy behavior for comparison)
- Targeted checks (with timeout): `set_gen`, `rbset`, and `fun_pattern_match` remained `0/1` parity in filtered mode.
- Deterministic full parity delta: **637/657 → 644/657** (parity failures **20 → 13**), compile parity stayed **657/657**.
- Parser/binary guard after patch: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.

### 2026-02-24 Type Function Parity: 628 → 652

- Implemented OCaml-aligned `type_function` pattern/body flow in Rust:
  - `instance()` argument type before parameter pattern typing,
  - `begin_def()` / `end_def()` around parameter pattern typing,
  - `generalize()` over typed parameter subpatterns,
  - `instance()` on pattern-bound value types before extending body env.
- Deterministic full parity delta: **628/657 → 652/657** (parity failures **29 → 5**), compile parity remained **657/657**.
- Remaining deterministic failures: `LetUnwrap`, `fun_pattern_match`, `miss_colon_test`, `polymorphism_test`, `rbset`.

### 2026-02-24 Recovery: 478 → 632

The parity script was rewritten to use **raw byte-for-byte comparison** with zero post-processing. Previously, sexp output was stripped/trimmed/normalized before comparison, which masked real differences. The new script (`test_typedtree_parity.sh`) compares OCaml and Rust sexp output exactly as produced — no stripping of non-printable characters, no trimming whitespace, no normalizing newlines.

The biggest remaining non-structural mismatch was in the **rewatch Rust dump path**: OCaml `.sexp` output already goes through `String::from_utf8_lossy` (stderr extraction), while Rust in-process output was written directly to file bytes. Aligning Rust to the same lossy normalization recovered most raw-byte diffs.
Baseline delta from deterministic full run:
- before: **478/657** (179 parity failures), compile parity **657/657**
- after: **632/657** (25 parity failures), compile parity **657/657**

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

## Immediate Priority

### P0: Fix Rust Compiler Crashes (5 errors)

These files compile successfully under OCaml but crash/error in the Rust compiler. Fixing these is the **highest priority** — a compiler crash is worse than a parity diff because it means the compiler is fundamentally broken for that input.

| Module | Error Type | Notes |
|--------|-----------|-------|
| `bs_ignore_test` | GADT PatternTypeClash | Stack overflow / GADT equation handling |
| `gpr_4280_test` | UndefinedMethod | Method resolution failure |
| `js_json_test` | GADT PatternTypeClash | Stack overflow / GADT equation handling |
| `more_poly_variant_test` | ExprTypeClash (variant spread) | Polymorphic variant spread type error |
| `tramp_fib` | Unknown | Crash during type checking |

**Approach:** For each crash, run the file under the Rust compiler directly, capture the error, trace back to the root cause in the type checker, and fix. GADT-related crashes (bs_ignore_test, js_json_test) likely share a common root cause. Always use `timeout` — these may infinite loop.

**How to run bsc on a single file:**

```bash
# 1. Get the correct compiler flags for a source file
cd tests/tests
../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/bs_ignore_test.res

# 2. Run from the build directory with those flags (Rust compiler)
cd tests/tests/lib/bs
timeout 10 ../../../../compiler-rust/target/release/bsc <flags from step 1> -dtyped-sexp-locs

# 3. Compare with OCaml compiler
timeout 10 ../../../../packages/@rescript/darwin-arm64/bin/bsc.exe <flags from step 1> -dtyped-sexp-locs

# Example (typical flags look like):
timeout 10 ../../../../compiler-rust/target/release/bsc -I ../../../node_modules -I . -w -3-49-111 -dtyped-sexp-locs ../../src/bs_ignore_test.res
```

**Important notes:**
- Must run bsc from `tests/tests/lib/bs` — relative `-I` paths resolve from there
- Use `-dtyped-sexp-locs` (NOT `-dtypedtree`) for sexp output
- OCaml bsc is `bsc.exe`, Rust bsc is `bsc` (no `.exe`)
- The `compiler-args` output includes the source file path; copy the flags but you may need to adjust the source path
- Use `diff -a` when comparing outputs — sexp files may contain binary characters

### P1: Fix Parity Diffs (~54 remaining failures)

Secondary priority. Primary blockers are (1) cycle/sharing typedtree rendering drift and (2) path normalization drift. Keep work anchored to the latest deterministic snapshot above.

---

## Re-apply Tasks (611 → ~654)

**Completed:**
- [x] **1A. Stack-based cycle detection** — INVALID. Causes 610→220 regression. DO NOT ATTEMPT.
- [x] **1B. Tarrow/Tfield/Tnil: COPY not identity** — Reverted ReturnSelf to copy. 610→611.

**Remaining — 15 missing fixes from typed-ast-parity session logs.**
**Full details:** `RALPH_GUIDANCE.md`

- [x] **2. Fix predef type variances in env.rs** — `option`/`list`/`result`/`array`/`promise` now have correct variance. Parity-neutral at 611 baseline (prerequisite for downstream fixes). (647→648, test: ext_array_test.res)
- [x] **3. Depth-restricted prefix rewriting in persistent_env.rs** — Added alias prefix rewriting with depth >= 2 guard. Uses collect_alias_rewrites + rewrite_deep_prefix_in_sig + effective_module_path for nested aliases. 612→613 (+1). (test: Stdlib_TempTests.res + Stdlib_Intl_NumberFormatTest.res)
- [x] **4. Coercion subtype approximation in typecore.rs** — In `type_coerce`, unify result with `from_ty` when still Tvar. 611→612 (+1). (629→630, test: type_coercion_free_vars.res)
- [x] **4A. Align Rust dump normalization with OCaml parity path in rewatch** — In `rewatch/src/build/compile.rs` (`dump_typed_sexp && use_rust_parser`), route generated Rust sexp bytes through `String::from_utf8_lossy` before writing `.sexp`, matching OCaml's stderr-extraction normalization path in the same script.
  - OCaml refs read: `compiler/ml/sexp_typedtree.ml` (`let string txt = Sexp.atom ("\"" ^ txt ^ "\"")`) and `Sexp` pretty-printer output flow (no special byte rewrite in OCaml printer).
  - Deterministic full parity: **478/657 → 632/657** (179 → 25 parity failures), compile parity stayed **657/657**.
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh AsInUncurriedExternals` and `... ExternalArity` both moved to **1/1 parity**.
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
- [x] **5. Deep-copy Tvariant/Tobject/Tfield in copy_type_deep** — `copy_type_deep_inner` catch-all returns original, needs deep copy. (642→643, test: jsxv4_newtype.res)
  - 2026-02-24 fix: updated `compiler-rust/src/types/ctype.rs::copy_type_deep` to force strict structural copy for `Tvariant`/`Tobject`/`Tfield`:
    - always deep-copy `row_more`, `row_fields`, and `row_name` arguments for variants,
    - always allocate fresh `Reither.link` refs during row-field copy,
    - always rebuild `Tfield` nodes from copied components (no direct source-link reuse).
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp` `Tvariant`/`Tobject`/`Tfield`) and `compiler/ml/ctype.ml` (`copy`, `instance_label`).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen`, `... rbset`, and `... fun_pattern_match` remained **0/1**.
  - Deterministic full parity: **637/657 → 644/657** (parity failures **20 → 13**), compile parity stayed **657/657**.
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - 2026-02-24 attempt: aligned `compiler-rust/src/types/ctype.rs::copy_type_deep` `TypeDesc::Tvariant` with OCaml `Subst.typexp` row handling by:
    - removing `Ctype.copy`-only PR#6163 row-fixed promotion from this path,
    - computing `dup` from `row_more` (`generic_level` / `static_row` / `Tconstr`) and using OCaml-style `more'` reuse rules (`Tunivar` and non-dup `Tvar` keep identity),
    - keeping `Reither.link` only when `not dup`, and forcing `matched=true` only when original `row.row_fixed` is true.
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp` `Tvariant` `dup`/`more'` flow) and `compiler/ml/btype.ml` (`copy_row` keep/matched semantics).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1**; `timeout 300 ./scripts/test_typedtree_parity.sh jsxv4_newtype` stayed **0/1** (OCaml-only pass in filtered mode).
  - Full parity delta for this iteration: **630/657 → 638/657** (parity failures **27 → 19**), compile parity stayed **657/657**.
  - Repeated full runs are currently unstable due recurring Rust sexp-generation stack overflow (`653/657`, `637/657`, `638/657` observed); keep task unchecked until this branch is deterministic.
  - Parser/binary guard after patch: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - 2026-02-24 attempt: updated `compiler-rust/src/types/ctype.rs` to allocate fresh `RowFieldRef`s for `Reither` links when deep-copying `Tvariant` rows in both `copy_type_deep` and `subst_identity_copy_rec` (to avoid mutable link aliasing between source and copy graphs).
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp`, `Tvariant` copy path) and `compiler/ml/btype.ml` (`copy_row`, `if keep then e else ref None` link handling).
  - Deterministic parity: **478/657 → 478/657** (179 parity failures, compile parity stayed 657/657).
  - Targeted `timeout 300 ./scripts/test_typedtree_parity.sh jsxv4_newtype`: **0/1** (OCaml-only pass) in filtered mode; keep task unchecked.
  - 2026-02-24 attempt: pre-cached `TypeDesc::Tfield` with a placeholder in `copy_type_deep` before recursive copies (OCaml-style stub-before-recursion hypothesis for recursive object-field graphs), then reverted after neutral results.
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp` stub flow), `compiler/ml/ctype.ml` (`instance_label`), `compiler/ml/btype.ml` (`copy_type_desc`, `copy_row`).
  - Targeted `timeout 300 ./scripts/test_typedtree_parity.sh jsxv4_newtype`: **0/1**, **both_fail=1** in filtered mode (both compilers fail standalone `React` resolution in this mode).
  - Deterministic full parity: **478/657 → 478/657** (179 parity failures, compile parity stayed 657/657).
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` stayed green (`SUCCESS: All 3532 files have full parity!`).
  - 2026-02-24 attempt: aligned `Tfield` copy behavior with OCaml in `compiler-rust/src/types/ctype.rs` (`copy_type_deep`, `subst_identity_copy_rec`, `copy_type_cached`) so `FieldKind::Fabsent` collapses to a link-to-rest copy instead of rebuilding a full `Tfield` node; also used placeholder-first flow in `copy_type_deep` `Tfield` branch to keep recursion-safe stub semantics.
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp`, `Tfield ... Fabsent -> Tlink (typexp s t2)`), `compiler/ml/ctype.ml` (`copy`, `Tfield` handling by `field_kind_repr`), `compiler/ml/btype.ml` (`copy_type_desc` field copy behavior).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh jsxv4_newtype` stayed **0/1** (OCaml-only pass); `timeout 300 ./scripts/test_typedtree_parity.sh async_inline` stayed **0/1** parity.
  - Deterministic full parity: **478/657 → 478/657** (179 parity failures, compile parity stayed 657/657).
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` stayed green (`SUCCESS: All 3532 files have full parity!`).
  - 2026-02-24 attempt: aligned deep row/object copy flow with OCaml row-copy semantics in `compiler-rust/src/types/ctype.rs` by (1) copying `Tvariant` fields via `row_repr` + `row_field_repr`, (2) applying OCaml-style `keep` gating for `Reither` links (`keep = not dup`, where `dup` tracks generic/static/constr row-more), (3) forcing `matched=true` on fixed rows, and (4) returning a `Tfield(Fabsent)` link placeholder node in `copy_type_deep` instead of collapsing directly to the rest node. Mirrored the `row_field_repr`/`keep` behavior in `subst_identity_copy_rec`.
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp`, `Tvariant`, `Tfield ... Fabsent`), `compiler/ml/ctype.ml` (`copy` variant branch), `compiler/ml/btype.ml` (`copy_row`, `row_field_repr`).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen`, `... gpr_4274_test`, and `... fun_pattern_match` all stayed **0/1** parity.
  - Deterministic full parity: **478/657 → 478/657** (179 parity failures, compile parity stayed 657/657).
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` stayed green (`SUCCESS: All 3532 files have full parity!`).
  - 2026-02-24 attempt: ported OCaml `Subst.typexp` variant-row `more'` control flow into `copy_type_deep` + `subst_identity_copy_rec` in `compiler-rust/src/types/ctype.rs` (conditional reuse of local `row_more` when `dup=false`, copy only on OCaml `dup` cases).
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp` `Tvariant` `dup`/`more'` branch) and `compiler/ml/btype.ml` (`copy_row` keep behavior).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` and `... more_poly_variant_test` both stayed **0/1** parity.
  - Deterministic full parity regressed to **539/657** with Rust compile coverage **648/657** (9 OCaml-only passes). Reverted immediately.
  - Baseline restored after revert: deterministic full parity back to **478/657** (179 parity failures) with compile parity **657/657**; parser/binary guard stayed green (`SUCCESS: All 3532 files have full parity!`).
  - 2026-02-24 attempt: threaded an `instance_label` `fixed` mode through Rust and added a poly-label variant-row branch in `copy_type_deep` (OCaml `instance_label true/false` + `copy_sep`/`copy_row` hypothesis), using `fixed=true` only in record-field typing and `false` elsewhere.
  - OCaml refs read: `compiler/ml/typecore.ml` (`type_record`, `type_label_exp`, `Pexp_field`, `Pexp_setfield`) and `compiler/ml/ctype.ml` (`instance_label`, `instance_poly`, `copy_sep`, `copy_row`).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen`, `... more_poly_variant_test`, and `... gpr_4274_test` all stayed **0/1** parity.
  - Deterministic full parity: **478/657 → 478/657** (179 parity failures, compile parity stayed **657/657**); parser/binary guard stayed green (`SUCCESS: All 3532 files have full parity!`).
  - Reverted the code change; keep task unchecked.
  - 2026-02-24 attempt: ported OCaml `copy` row-fixed propagation (PR#6163 path) into Rust variant deep-copy code in `compiler-rust/src/types/ctype.rs`, in both `copy_type_deep` and `subst_identity_copy_rec`:
    - copy `row_more` first,
    - set copied row `row_fixed=true` when copied `row_more` is `Tconstr`,
    - force `Reither.matched=true` based on the effective copied `row_fixed`.
  - OCaml refs read: `compiler/ml/ctype.ml` (`copy` `Tvariant` branch, `PR#6163` `row_fixed` promotion when `repr more'` is `Tconstr`) and `compiler/ml/subst.ml` (`typexp` `Tvariant` copy flow for row recursion shape).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` and `... gpr_4274_test` both stayed **0/1** parity.
  - Deterministic full parity: **478/657 → 478/657** (179 parity failures, compile parity stayed **657/657**).
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` stayed green (`SUCCESS: All 3532 files have full parity!`).
  - 2026-02-24 attempt: ported OCaml `Subst.typexp` `Tvariant` recursion-marker flow in `compiler-rust/src/types/ctype.rs::copy_type_deep` (`dup`-gated `row_more` handling + temporary `more.desc <- Tsubst(Ttuple [more'; ty'])` registration while copying row fields).
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp` `Tvariant` branch, including `Tsubst (Ttuple [_; ty2])` fast-path + `more.desc <- Tsubst (...)`) and `compiler/ml/btype.ml` (`copy_row`).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen`, `... gpr_4274_test`, and `... more_poly_variant_test` all stayed **0/1** parity.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures), compile parity stayed **657/657 → 657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh` ended with `SUCCESS: All 3532 files have full parity!`.
  - Reverted the code change after parity-neutral outcome.
- [x] **5A. Map task-5 deep-copy validation to an active failing module (NEW)** — `jsxv4_newtype` is not in the active failure set; task-5 work is now anchored to modules that still fail in current full runs.
  - Resolution (2026-02-24): mapped active task-5 targets to **`rbset`** and **`set_gen`** from current full manifests (stack-overflow runs still consistently include these modules while `jsxv4_newtype` remains absent).
  - Evidence:
    - `timeout 300 ./scripts/test_typedtree_parity.sh` produced unstable totals (`623/657`, `636/657`, `627/657`) with Rust sexp stack overflow, but parity-failure intersections include `rbset` and `set_gen`.
    - `.parity-cache/tests/diffs/rbset.diff`: first divergence is recursive function type sharing (`Tarrow` arg `<cycle>` vs `Tconstr(Pident "t")`).
    - `.parity-cache/tests/diffs/set_gen.diff`: recursive `t<'a>` positions drift between `<cycle>` and `Tvar None`, plus arrow-arg cycle placement drift.
  - OCaml refs for this mapping: `compiler/ml/subst.ml` (`typexp`, `Tvariant` recursion marker, `copy_row`) and `compiler/ml/ctype.ml` (`copy` recursion/keep semantics).
  - Rust refs for this mapping: `compiler-rust/src/types/ctype.rs` (`copy_type_deep`, `subst_identity_copy_rec`, `copy_type_cached`) and typedtree output in `.parity-cache/tests/diffs/{rbset,set_gen}.diff`.
- [x] **5A1. Trace task-5 divergence at the first shared-node creation site for `rbset`/`set_gen` (NEW)** — establish whether the `<cycle>`/`Tconstr` and `<cycle>`/`Tvar` drift originates in `copy_type_deep`, `subst_identity_copy_rec`, or later instantiation in `typecore`.
  - Evidence (2026-02-24): `rbset` and `set_gen` are stable task-5 failures across noisy full runs, while prior `jsxv4_newtype`-targeted experiments were not attached to active failures.
  - 2026-02-24 trace update:
    - `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1** with the same first diffs (`rbset`: `Tarrow` arg `<cycle>` vs `Tconstr(Pident "t")`; `set_gen`: `Tconstr(Pident "t", <cycle>)` vs `Tconstr(Pident "t", Tvar None)`).
    - Experiment A (reverted): removed the Rust-only `id.name() == "t"` guard in `compiler-rust/src/types/ctype.rs::is_recursive_local_nullary_type_for_identity`; targeted parity stayed unchanged on both modules.
    - Experiment B (reverted): widened the Rust-only local `t -> t` link gate in `compiler-rust/src/types/typecore.rs` apply typing path; targeted parity stayed unchanged on both modules.
    - The first `rbset` divergence is in a non-application function binding (`blackify` `Tstr_value`), so the apply-path link heuristics are not the creation site for this cluster.
    - Timed full runs remained stack-overflow-noisy (`621/657`, `631/657`, `630/657` observed), with no deterministic attributable delta from the reverted experiments.
    - Parser/binary guard after reverting experiments: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Conclusion: current `rbset`/`set_gen` drift is introduced later in `typecore` non-application function typing/instantiation flow, not by `copy_type_deep`/`subst_identity_copy_rec` row-copy branches.
  - OCaml refs read: `compiler/ml/typecore.ml` (`type_function`, `type_cases`), `compiler/ml/ctype.ml` (`copy`), `compiler/ml/subst.ml` (`typexp`).
- [x] **5A2. Trace non-application `type_function` sharing for local recursive `t` (PARKED, DEEMPHASIZED)** — identify where Rust loses OCaml node sharing in function parameter/result types before typedtree emission for `rbset`/`set_gen`.
  - 2026-02-24 parking decision: this cluster is currently high-cost/low-yield and has consumed many parity-neutral iterations; keep notes for future root-cause work, but do not treat it as the next required unchecked task while higher-impact clusters remain.
  - Scope: `type_function` / `type_cases` expected-arrow filtering, `instance` timing, and pattern/body env binding copies.
  - 2026-02-24 attempt A (reverted): ported OCaml-style single-case propagation gating into `compiler-rust/src/types/typecore.rs::type_function` (conditional `begin_def/end_def`, pattern generalization, and body-env `instance` for simple variable-like params).
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_function` ~3262-3338, `type_cases` ~3906-4015), `compiler/ml/ctype.ml` (`instance`, `copy`).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1**; `rbset` filtered runs were unstable (`0/0` compare output in this mode).
    - Full parity with patch: **616/657**, Rust compile coverage **648/657** (OCaml-only pass **9**), with Rust sexp stack overflow in `More_poly_variant_test`.
    - Reverted immediately.
  - 2026-02-24 attempt B (reverted): for simple variable-like params, kept body env binding types by identity (`pv.ty`) instead of `instance(ctx, pv.ty)` in `type_function`.
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_cases` ext_env/body typing flow), `compiler/ml/ctype.ml` (`instance`, non-generic copy behavior).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1** with the same `<cycle> -> Tvar None` drift in `t` arguments.
    - Full parity with patch: **621/657**, Rust compile coverage **656/657** (OCaml-only pass **1**), stack overflow still present.
    - Reverted immediately.
  - 2026-02-24 attempt C (reverted): tested three OCaml-alignment hypotheses in `compiler-rust/src/types/typecore.rs::type_function`:
    - C1: stop re-instancing all pattern-bound body vars (use `pv.ty` directly),
    - C2: remove Rust-only exp_type arrow re-anchoring after `instance(new_generic_arrow(...))`,
    - C3: gate `begin_def/end_def/generalize` with `type_cases`-style propagate logic.
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_function`, `type_cases`, `add_pattern_variables`/`type_pattern` ext_env flow) and `compiler/ml/ctype.ml` (`instance`).
    - Targeted checks after each change: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both remained **0/1**, with unchanged first diffs (`rbset` `<cycle> -> Tconstr(Pident "t")`, `set_gen` `<cycle> -> Tvar None`).
    - Full parity with combined C1+C2+C3 patch set regressed hard: **620/657 → 589/657**, Rust compile coverage **656/657 → 650/657** (OCaml-only pass **1 → 7**).
    - Reverted the full patch set.
  - Post-revert baseline (clean code): `timeout 600 ./scripts/test_typedtree_parity.sh` reports **620/657**, Rust compile coverage **656/657** (OCaml-only pass **1**, parity failures **36**), with stack overflow still reported in `More_poly_variant_test`.
  - Parser/binary guard after revert: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Next OCaml refs: `compiler/ml/typecore.ml` (`type_function` ~3262-3338, `type_cases` ~3906+), `compiler/ml/ctype.ml` (`instance`, `copy`).
  - Next Rust refs: `compiler-rust/src/types/typecore.rs` (`type_function`, `type_case_impl`, `shallow_copy_pattern_binding_type`) and `compiler-rust/src/types/ctype.rs` (`instance` / `copy_type_cached`).
  - 2026-02-24 attempt D (reverted): in `compiler-rust/src/types/typecore.rs::type_function`, only call `instance` for `param_pat_ty` when `param_ty` is generic and bind body vars with `pv.ty` identity (no extra `instance`) before optional shallow-copy.
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_function`, `type_cases`, `add_pattern_variables`) and `compiler/ml/ctype.ml` (`copy` non-generic fast path).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1** with unchanged first diffs (`rbset`: `<cycle> -> Tconstr(Pident "t")`; `set_gen`: `Tconstr(Pident "t", <cycle>) -> Tconstr(Pident "t", Tvar None)`).
    - Reverted after parity-neutral outcome.
  - 2026-02-24 attempt E (reverted): in `type_function`, gated `begin_def/end_def/generalize` with `type_cases`-style propagation conditions (`generic ty_arg` OR non-simple pattern OR generalized constructor pattern).
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_cases` propagate branch) and `compiler/ml/ctype.ml` (`instance`).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both remained **0/1** with unchanged first diffs.
    - Reverted after parity-neutral outcome.
  - 2026-02-24 attempt F (reverted): in `compiler-rust/src/types/ctype.rs::copy_type_cached`, removed the `args are all Tvar/Tunivar` gate for non-generic recursive local `Tconstr` identity to test OCaml `copy` non-generic behavior.
    - OCaml refs read: `compiler/ml/ctype.ml` (`copy` early return for non-generic when `partial=None`).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both remained **0/1** with unchanged first diffs.
    - Reverted after parity-neutral outcome.
  - 2026-02-24 attempt G (reverted): in `compiler-rust/src/types/typecore.rs::type_function`, aligned three OCaml flow points together:
    - body env binding type uses `pv.ty` directly (no extra `instance`),
    - single-case RHS type normalized as `instance(ctx, return_ty)` before building `Texp_function`,
    - final function `exp_type` uses `ty_arg`/`param_ty` (OCaml `Tarrow` input) instead of `typed_param.pat_type`.
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_function`, `type_cases` case RHS `exp_type = instance env ty_res'`) and `compiler/ml/ctype.ml` (`instance` non-generic behavior).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both remained **0/1** with unchanged first diffs.
    - Deterministic full parity stayed **588/657 → 588/657** (Rust compile coverage stayed **650/657**, OCaml-only pass **7**).
    - Parser/binary guard after revert: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - 2026-02-24 attempt H (reverted): in `compiler-rust/src/types/ctype.rs`, tested recursive-local identity fallback (`find_type_decl_by_stamp` → `find_type_decl(name)` with name-based self-recursion check) and removed the nullary `id.name() == "t"` exclusion in `is_recursive_local_nullary_type_for_identity`.
    - OCaml refs read: `compiler/ml/ctype.ml` (`copy` non-generic identity) and `compiler/ml/typecore.ml` (`type_cases` per-case `instance env ty_arg`).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both remained **0/1** with unchanged first diffs.
    - Re-run deterministic full parity stayed **588/657 → 588/657** (Rust compile coverage **650/657**, OCaml-only pass **7**).
    - Reverted after parity-neutral outcome.
  - 2026-02-24 attempt I (reverted): in `compiler-rust/src/types/typecore.rs::type_function`, used OCaml-style simple-parameter body binding identity (`pv.ty`) instead of `instance(ctx, pv.ty)`, while keeping existing non-simple pattern shallow-copy behavior.
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_cases` `pat_env_list` + body typing via `type_expect ext_env`) and `compiler/ml/ctype.ml` (`instance`).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1**.
    - Deterministic full parity stayed **588/657 → 588/657** (Rust compile coverage **650/657**, OCaml-only pass **7**).
    - Reverted after parity-neutral outcome.
  - 2026-02-24 attempt J (reverted): in `compiler-rust/src/types/typecore.rs::type_function`, set function `exp_type` arrow input to `param_ty` (OCaml `ty_arg`) instead of `typed_param.pat_type`.
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_function` final `exp_type = instance env (newgenty (Tarrow ... ty_arg ...))`) and `compiler/ml/ctype.ml` (`instance`).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1**.
    - Deterministic full parity stayed **588/657 → 588/657** (Rust compile coverage **650/657**, OCaml-only pass **7**).
    - Reverted after parity-neutral outcome.
  - 2026-02-24 attempt K (reverted): in `compiler-rust/src/types/typecore.rs::type_function`, tested a combined OCaml-shape branch:
    - propagate-gated `begin_def/end_def/generalize` for parameter patterns,
    - body env binding by `pv.ty` identity (no extra `instance`) with shallow-copy only for non-simple/GADT-like patterns,
    - final function `exp_type` arrow input switched to `param_ty`,
    - removed Rust-only arrow re-anchoring mutation.
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_function`, `type_cases` propagate branch and final `exp_type` construction) and `compiler/ml/ctype.ml` (`instance`, `copy` non-generic identity).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1** with unchanged first diffs.
    - Deterministic full parity stayed **589/657 → 589/657** (Rust compile coverage **650/657**, OCaml-only pass **7**, parity failures **61**).
    - Parser/binary guard after revert: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - 2026-02-24 attempt L (reverted): in `compiler-rust/src/types/typecore.rs::type_function`, added an OCaml-`type_cases`-style fresh-pattern unification step (`unify_pats ty_arg'` analogue) by unifying typed parameter pattern type against a fresh `new_var`.
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_cases` `unify_pats ty_arg'` and propagate path around lines ~3981-4003), `compiler/ml/typecore.ml` (`type_function` delegation to `type_cases` around lines ~3314-3320).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both remained **0/1** with unchanged first diffs (`rbset` `<cycle> ↔ Tconstr(Pident "t")`, `set_gen` `t(<cycle>) ↔ t(Tvar None)`).
    - Deterministic full parity stayed **589/657 → 589/657** (parity failures **61**, Rust compile coverage **650/657**, OCaml-only pass **7**).
    - Reverted immediately after parity-neutral outcome.
  - 2026-02-24 attempt M (reverted): in `compiler-rust/src/types/typecore.rs::type_function`, tested an OCaml-ordered single-case flow bundle:
    - propagate-gated `begin_def/end_def/generalize` around parameter pattern typing,
    - body-env bindings by identity (`pv.ty`, no extra `instance`) while keeping existing shallow-copy gate,
    - case-RHS typed expression forced to `instance(return_ty)` (OCaml `type_cases` `c_rhs.exp_type` shape),
    - final function `exp_type` arrow input switched to `param_ty` (`ty_arg`) instead of `typed_param.pat_type`.
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_function` + `type_cases` single-case flow, `c_rhs = {exp with exp_type = instance env ty_res'}`) and `compiler/ml/ctype.ml` (`instance`).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1** with unchanged first diffs.
    - Deterministic full parity stayed **589/657 → 589/657** (parity failures **61**, Rust compile coverage **650/657**, OCaml-only pass **7**).
    - Parser/binary guard after revert: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
    - Reverted immediately after parity-neutral outcome.
  - 2026-02-24 attempt N (reverted): in `compiler-rust/src/types/ctype.rs::copy_type_cached`, tested OCaml-`copy`-style identity for non-generic `Tarrow`/`Tfield`/`Tnil` (keeping existing `Tobject` identity) to reduce recursive function type re-materialization in `type_function` outputs.
    - OCaml refs read: `compiler/ml/ctype.ml` (`copy`, early non-generic identity path `if ty.level <> generic_level && partial = None then ty`) and `instance`.
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1**, with unchanged first diffs (`rbset`: leading `Tarrow` arg `<cycle> -> Tconstr(Pident "t")`; `set_gen`: `t(<cycle>) -> t(Tvar None)`).
    - Deterministic full parity stayed **589/657 → 589/657** (Rust compile coverage **650/657**, OCaml-only pass **7**).
    - Reverted after parity-neutral outcome.
  - 2026-02-24 attempt O (reverted): in `compiler-rust/src/types/typecore.rs::type_function`, removed Rust-only final-arrow re-anchoring and switched final `exp_type` arrow input back to OCaml `ty_arg` (`param_ty`) rather than `typed_param.pat_type`.
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_function` final `exp_type = instance env (newgenty (Tarrow ... ty_arg ...))`) and `compiler/ml/ctype.ml` (`instance` copy behavior).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1** with unchanged first diffs.
    - Deterministic full parity stayed **589/657 → 589/657** (Rust compile coverage **650/657**, OCaml-only pass **7**).
    - Reverted after parity-neutral outcome.
  - 2026-02-24 attempt P (kept): removed the Rust-only nullary-`t` exclusion in `compiler-rust/src/types/ctype.rs::is_recursive_local_nullary_type_for_identity` so recursive local nullary `Pident` types follow the same non-generic identity path as other local recursive types.
    - OCaml refs read: `compiler/ml/ctype.ml` (`copy`, non-generic `partial=None` identity behavior) and `compiler/ml/typecore.ml` (`type_function`/`type_cases` `instance env ty_arg` flow for function parameters).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1** with unchanged first diffs (`rbset`: `Tarrow` arg `<cycle>` vs `Tconstr(Pident "t")`; `set_gen`: `t(<cycle>)` vs `t(Tvar None)`).
    - Deterministic full parity stayed **589/657 → 589/657** (Rust compile coverage **650/657**, OCaml-only pass **7**, parity failures **61**).
    - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
    - Outcome: parity-neutral but OCaml-aligned cleanup retained for follow-up tracing in this cluster.
  - 2026-02-24 attempt Q (kept): in `compiler-rust/src/types/typecore.rs::type_function`, always call `instance(ctx, expected_ty)` before expected-arrow extraction/`expand_head`, matching OCaml `type_function` (`filter_arrow ~env ~arity (instance env ty_expected)`).
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_function` expected-arrow flow around `filter_arrow` + `instance env ty_expected`) and `compiler/ml/ctype.ml` (`instance`, `copy`).
    - Rust refs touched: `compiler-rust/src/types/typecore.rs` (`type_function` expected-instantiation path before `expand_head`).
    - Build/test commands:
      - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release` (success).
      - `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1** with unchanged first diffs (`rbset`: leading `Tarrow` arg `<cycle> ↔ Tconstr(Pident "t")`; `set_gen`: `t(<cycle>) ↔ t(Tvar None)`).
      - Deterministic full parity stayed **589/657 → 589/657** (Rust compile coverage **650/657**, OCaml-only pass **7**, parity failures **61**).
      - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
    - Outcome: parity-neutral but OCaml-aligned expected-instantiation cleanup retained; evidence kept, cluster now parked.
  - Deterministic full baseline after all reverts (current workspace snapshot):
    - `timeout 300 ./scripts/test_typedtree_parity.sh` reports **589/657** parity with **7** OCaml-only pass files and **61** parity failures.
    - Re-run confirmed stable **589/657** (**589 -> 589**).
  - Parser/binary guard on this snapshot: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
- [x] **5A2A. Port OCaml `type_cases` ext_env/body binding flow into `type_function` (PARKED, DEEMPHASIZED)** — Rust hand-builds function body env (`state.pattern_variables` + ad-hoc instancing/copying), while OCaml reuses `type_pattern`’s `ext_env` directly; two local attempts in Rust `type_function` regressed full parity without touching the `set_gen` first diff.
  - Evidence: attempt A (`type_cases`-style propagation gating) regressed to **616/657** with 9 Rust rejects; attempt B (simple-var identity body binding) regressed to **621/657** with 1 Rust reject; both reverted, `set_gen` remained **0/1**.
  - 2026-02-24 attempt C (kept): in `compiler-rust/src/types/typecore.rs::type_function`, replaced function-body env binding to use OCaml `add_pattern_variables` semantics (`pv.ty` identity) and removed the ad-hoc `instance(...)` + conditional shallow-copy path for function parameter bindings.
    - OCaml refs read: `compiler/ml/typecore.ml` (`add_pattern_variables`, `type_pattern`, `type_cases` `pat_env_list`/`type_expect ext_env` flow) and `compiler/ml/ctype.ml` (`instance` identity behavior for non-generic nodes).
    - Rust refs touched: `compiler-rust/src/types/typecore.rs` (`type_function` body-env construction).
    - Build/test commands:
      - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release` (success).
      - `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1**.
      - Deterministic full parity stayed **589/657 → 589/657** (Rust compile coverage **650/657**, OCaml-only pass **7**, parity failures **61**).
      - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
    - Outcome: parity-neutral; evidence kept, cluster now parked.
  - Next OCaml refs: `compiler/ml/typecore.ml` (`type_cases` `pat_env_list` creation and body typing `type_expect ext_env`), `compiler/ml/typecore.ml` variable binding flow in `type_pattern`.
  - Next Rust refs: `compiler-rust/src/types/typecore.rs` (`type_pattern`, `PatternState`, `type_function` body-env construction) to replace ad-hoc env reconstruction with OCaml-equivalent ext_env threading.
- [x] **5A2B. Isolate `type_function` regression source across env-instancing, re-anchoring, and propagate gating (PARKED, DEEMPHASIZED)** — C1/C2/C3 combined regressed full parity to **589/657**, but targeted `rbset`/`set_gen` stayed unchanged, so at least one change is globally load-bearing while not touching the local recursive-`t` first diff.
  - Required next step: run single-change full parity for C1, C2, C3 independently (no combination) and record exact compile/parity deltas to identify which behavior is required for global stability vs which remains a viable parity-fix path.
  - Evidence files: `.parity-cache/tests/diffs/rbset.diff`, `.parity-cache/tests/diffs/set_gen.diff`, `/tmp/full_parity_after3.log`, `/tmp/full_parity_revert.log`.
  - 2026-02-24 single-change C2 check (reverted): removed only the Rust-only final-arrow re-anchoring in `type_function` (kept existing `typed_param.pat_type` arrow input).
    - OCaml refs read: `compiler/ml/typecore.ml` (`type_function` final `exp_type = instance env (newgenty (Tarrow ...))`) and `compiler/ml/ctype.ml` (`instance`).
    - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1** with unchanged first diffs.
    - Deterministic full parity stayed **589/657 → 589/657** (Rust compile coverage **650/657**, OCaml-only pass **7**, parity failures **61**).
    - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
    - Conclusion: C2 alone is not the load-bearing source for the `rbset`/`set_gen` drift on this snapshot.
- [x] **5A2C. Trace pre-`type_function` creation site for decoupled recursive local-`t` args (PARKED, DEEMPHASIZED)** — type_function-local and `copy_type_cached` experiments D/E/F were parity-neutral, so the `t(<cycle>) -> t(Tvar None)` drift likely starts before `type_function` body-env reconstruction.
  - Required next step: instrument let-rec typing around `type_let_bindings` / expected-arrow setup to compare the first `param_ty` node IDs for `elements_aux` and `blackify` against OCaml `type_let` + `type_function` flow.
  - Evidence: after reverting D/E/F, `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` remain **0/1** with unchanged first diff; deterministic full parity remains **588/657**.
- [x] **5A2D. Trace `type_match` scrutinee instantiation identity for local recursive `t` (PARKED, DEEMPHASIZED)** — attempts G/H kept `rbset`/`set_gen` unchanged, so the break may be in case-typing instantiation (`cases_scrutinee_ty = instance(...)`) rather than function-body env assembly.
  - Required next step: instrument `compiler-rust/src/types/typecore.rs` (`type_match`, `type_case_impl`) and `compiler-rust/src/types/ctype.rs::copy_type_cached` to capture pre/post `instance` node IDs for `Pident "t"` and `t<'a>` in `blackify`/`elements_aux`, then compare against OCaml `type_cases` behavior.
  - Evidence: with all G/H edits reverted, `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` are still **0/1**, and deterministic full parity remains **588/657**.
  - 2026-02-24 attempt (kept): in `compiler-rust/src/types/typecore.rs::type_match`, removed the extra outer `cases_scrutinee_ty = instance(typed_scrutinee.exp_type)` layer and passed `typed_scrutinee.exp_type` into `type_case`, keeping per-case instantiation in `type_case_impl` as the single `instance(...)` site.
    - OCaml refs read: `compiler/ml/typecore.ml` (`Pexp_match` calls `type_cases` with `arg.exp_type`; `type_cases` then instances `ty_arg` per case in `pat_env_list`).
    - Build/test commands:
      - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release` (success).
      - `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` both stayed **0/1** with unchanged first diffs (`rbset`: `Tarrow` arg `<cycle> ↔ Tconstr(Pident "t")`; `set_gen`: `t(<cycle>) ↔ t(Tvar None)`).
      - Deterministic full parity stayed **589/657 → 589/657** (Rust compile coverage **650/657**, OCaml-only pass **7**, parity failures **61**).
      - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
    - Outcome: parity-neutral; evidence kept, cluster now parked.
- [x] **5A2E. Instrument `type_function` node identity split (`param_ty` vs `pv.ty` vs `typed_param.pat_type`) (PARKED, DEEMPHASIZED)** — attempts I/J show that toggling simple-param body binding identity and `exp_type` arrow-input selection individually is parity-neutral, so the first identity drift for local recursive `t` must occur earlier (expected-arrow extraction or pattern typing) or later (case/match instantiation).
  - Required next step: add scoped debug tracing (node IDs + `repr` IDs + desc tags) in `type_function` for `blackify` and `elements_aux` at these points:
    - after `filter_arrow`-equivalent extraction (`param_ty`, `return_ty`),
    - after `param_pat_ty = instance(param_ty)`,
    - after `type_pattern` (`typed_param.pat_type`, each `state.pattern_variables[i].ty`),
    - before/after `type_expect` body typing,
    - before final `exp_type` construction.
  - Compare the Rust trace against OCaml control flow expectations from `type_function` + `type_cases` to find the first non-OCaml copy/instance site.
- [x] **5A2F. Trace recursive-let pre-unification sharing before `type_function` (PARKED, DEEMPHASIZED)** — attempt K confirms `type_function`-local propagation/body-binding/exp_type rewrites are parity-neutral at **589/657**, so the active `rbset`/`set_gen` drift likely starts in recursive let approximation/unification.
  - Required next step: instrument `compiler-rust/src/types/typecore.rs::type_let_bindings` + `type_approx_for_rec_let` to capture node identity for binding `pat_type` vs approximation arrow nodes (`blackify`, `elements_aux`) before entering `type_function`.
  - Compare with OCaml `compiler/ml/typecore.ml` (`type_let`, `type_approx`, recursive pre-unification path) to verify where the `<cycle>` sharing edge is dropped (`t(<cycle>) -> t(Tvar None)`).
  - Evidence: with K reverted, `timeout 300 ./scripts/test_typedtree_parity.sh rbset` and `... set_gen` remain **0/1** and deterministic full parity remains **589/657**; parser/binary guard remains green.
- [x] **5A2G. Port full OCaml `type_cases` pattern-unification flow for function cases (PARKED, DEEMPHASIZED)** — a local `unify_pats ty_arg'` analogue in Rust `type_function` was parity-neutral, which suggests the missing behavior is the complete `type_cases` two-phase flow (pat-env list + propagate-conditioned second unify), not a single extra unification call.
  - Required next step: refactor `type_function` single-case typing through a shared `type_cases`-equivalent helper that preserves OCaml ordering:
    - per-case `instance env ty_arg` before `type_pattern`,
    - delayed `unify_pats ty_arg'`,
    - optional `unify_pats (instance env ty_arg)` when propagate applies.
  - Evidence: attempt L (`type_function` fresh-pattern unification only) kept `rbset`/`set_gen` at **0/1** and full parity at **589/657**.
- [x] **5A2H. Trace recursive-let handoff between `vb_pat.pat_type` and `vb_expr.exp_type` (PARKED, DEEMPHASIZED)** — attempt M aligned `type_function` single-case ordering and stayed parity-neutral, so the `<cycle> -> Tconstr/Tvar` drift likely survives `type_function` and is introduced (or preserved) at recursive let binding unification/generalization boundaries.
  - Required next step: instrument `compiler-rust/src/types/typecore.rs::type_let_bindings` around recursive pre-unification and post-expression typing to log node identity for each binding (`typed_pat.pat_type`, `typed_expr.exp_type`) for `blackify`/`elements_aux` before `end_def`, after generalization, and in final typedtree emission.
  - Compare against OCaml `compiler/ml/typecore.ml` `type_let` ordering (`unify_pat env pat (type_approx ...)`, then `type_expect exp_env ... pat.pat_type`, then `generalize`) to find where Rust stops sharing the same node edge.
  - Evidence: with attempt M reverted, `timeout 300 ./scripts/test_typedtree_parity.sh` remained **589/657** and `rbset`/`set_gen` remained **0/1** with unchanged first diffs.
- [x] **5A2I. Trace `instance(copy)` effects on recursive function types at `type_let` boundary (PARKED, DEEMPHASIZED)** — attempts N/O show that changing `type_function` final-arrow wiring or widening non-generic identity inside `copy_type_cached` in isolation is parity-neutral, so the first `<cycle> -> Tconstr/Tvar` drift likely occurs when recursive approximation types and function result types are unified/instantiated across `type_let_bindings`.
  - Required next step: instrument `compiler-rust/src/types/typecore.rs::type_let_bindings` and `compiler-rust/src/types/ctype.rs::{instance, copy_type_cached}` to capture node IDs for `binding_types[i]`, `typed_pat.pat_type`, `typed_expr.exp_type`, and `type_approx_for_rec_let(...)` around:
    - recursive pre-unification (`unify_pattern_types`),
    - `type_expect` return for each recursive function binding,
    - post-`end_def` generalization.
  - OCaml refs to mirror during trace: `compiler/ml/typecore.ml` (`type_let`, `type_approx`) and `compiler/ml/ctype.ml` (`instance`, `copy`).
- [ ] **5A2J. Validate whether OCaml-style batched `type_cases` flow in `type_match` affects the recursive-local-`t` cluster (NEW)** — a first-pass non-GADT batch rewrite of Rust `type_match` (type all patterns first, shared `ty_arg'` unify, then RHS typing with per-case env) did not move `rbset`/`set_gen` or full parity, so the active drift likely survives beyond simple `type_cases` ordering.
  - 2026-02-24 attempt (reverted): patched `compiler-rust/src/types/typecore.rs` to batch value-case typing in `type_match` via a new helper (`type_match_cases_batch`) and fallback to legacy per-case flow when generalized constructors are present.
  - OCaml refs read: `compiler/ml/typecore.ml` (`type_cases` pattern pass + delayed `unify_pats` + RHS typing order) and `compiler/ml/typecore.ml` (`Pexp_match` path passing `arg.exp_type` into `type_cases`).
  - Build/test commands:
    - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release` (success).
    - `timeout 300 ./scripts/test_typedtree_parity.sh rbset` stayed **0/1** (`hunk mismatches: 6`).
    - `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1** (`hunk mismatches: 82`).
    - `timeout 600 ./scripts/test_typedtree_parity.sh` stayed **589/657** with Rust compile coverage **650/657** (OCaml-only pass **7**, parity failures **61**).
  - Outcome: parity-neutral; patch reverted. Next step is to trace node identity across recursive-let approximation/unification boundaries (`type_let_bindings`) instead of case-ordering alone.
- [ ] **5A2K. Port OCaml `instance_poly ~keep_names:true false` handling at recursive-let pre-unification (NEW)** — a direct Rust pre-pass that instantiated `Tpoly` pattern types before `type_approx` unification in `type_let_bindings` was parity-neutral, so the remaining drift likely needs full OCaml `copy_sep`/visited-bound behavior rather than cache-only substitution.
  - 2026-02-24 attempt (reverted): patched `compiler-rust/src/types/typecore.rs::type_let_bindings` recursive pre-unification to instantiate `Tpoly` `typed_pat.pat_type` (fresh `Tvar` map + copied poly body) before `unify_pattern_types`.
  - OCaml refs read:
    - `compiler/ml/typecore.ml` (`type_let`: `unify_pat env pat (type_approx ...)` with `Tpoly` branch using `instance_poly ~keep_names:true false`)
    - `compiler/ml/ctype.ml` (`instance_poly`, `copy_sep`, `diff_list`, `conflicts`, delayed-copy flow)
  - Build/test commands:
    - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release` (success).
    - `timeout 300 ./scripts/test_typedtree_parity.sh rbset` stayed **0/1** (`hunk mismatches: 6`).
    - `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1** (`hunk mismatches: 82`).
    - `timeout 600 ./scripts/test_typedtree_parity.sh` stayed **589/657** with Rust compile coverage **650/657** (OCaml-only pass **7**, parity failures **61**).
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - 2026-02-24 attempt (kept): implemented OCaml-shaped `instance_poly` in `compiler-rust/src/types/ctype.rs` (`compute_univars` inverse-parent propagation, `copy_sep`, `diff_list`, `conflicts`, delayed-copy linking) and wired `compiler-rust/src/types/typecore.rs::type_let_bindings` recursive pre-unification to call it for `Tpoly` patterns (`keep_names=true`, `fixed=false`) before `unify_pattern_types`.
  - OCaml refs read for kept attempt:
    - `compiler/ml/typecore.ml` (`type_let` recursive branch using `snd (instance_poly ~keep_names:true false tl ty)`)
    - `compiler/ml/ctype.ml` (`compute_univars`, `copy_sep`, `instance_poly`, `diff_list`, `conflicts`)
    - `compiler/ml/btype.ml` (`copy_type_desc` shape used by `copy_sep` non-`Tvariant`/`Tpoly` branches)
  - Build/test commands for kept attempt:
    - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release` (success).
    - `timeout 300 ./scripts/test_typedtree_parity.sh rbset` stayed **0/1** (`hunk mismatches: 6`).
    - `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1** (`hunk mismatches: 82`).
    - `timeout 600 ./scripts/test_typedtree_parity.sh` stayed **589/657 → 589/657** with Rust compile coverage **650/657** (OCaml-only pass **7**, parity failures **61**).
    - `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` stayed green (`SUCCESS: All 3532 files have full parity!`).
  - Next step: trace recursive-let sharing drift before/after `instance_poly` output in `type_let_bindings` (`typed_pat.pat_type`/`approx_ty`/post-unify nodes for `rbset` + `set_gen`) since OCaml-equivalent `instance_poly` alone is parity-neutral on this snapshot.
- [ ] **5A2L. Validate `type_cases` RHS re-instantiation (`exp_type = instance env ty_res'`) in Rust case emission (NEW)** — directly porting this OCaml case-construction step in `type_case_impl` was parity-neutral on the active recursive-local-`t` cluster.
  - 2026-02-24 attempt (reverted): patched `compiler-rust/src/types/typecore.rs::type_case_impl` so each case body expression overwrote `exp_type` with `instance(ctx, body_ty)` after `type_expect`, matching OCaml `type_cases` case output shape.
  - OCaml refs read:
    - `compiler/ml/typecore.ml` (`type_cases` case construction: `c_rhs = {exp with exp_type = instance env ty_res'}`)
    - `compiler/ml/typecore.ml` (`Pexp_match` routing through `type_cases`)
  - Build/test commands:
    - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release` (success).
    - `timeout 300 ./scripts/test_typedtree_parity.sh rbset` stayed **0/1** (`hunk mismatches: 6`).
    - `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1** (`hunk mismatches: 82`).
    - `timeout 600 ./scripts/test_typedtree_parity.sh` stayed **589/657 → 589/657** (Rust compile coverage **650/657**, OCaml-only pass **7**, parity failures **61**).
    - `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` stayed green (`SUCCESS: All 3532 files have full parity!`).
  - Outcome: parity-neutral; patch reverted. Next step is to trace where `ty_res` sharing diverges before case emission (likely at recursive-let approximation/unification or pattern/body coupling), not at final case-RHS type overwrite.
- [ ] **5B. Preserve compile parity when porting `Subst.typexp` variant `more'` flow (NEW)** — direct conditional `row_more` reuse currently causes Rust type-check regressions on full build.
  - Evidence (2026-02-24): first-pass OCaml-style `dup`/`more'` port in `copy_type_deep` + `subst_identity_copy_rec` changed full run from **478/657** to **539/657** with Rust compile parity drop **657/657 → 648/657** (9 OCaml-only passes). Reverted.
  - Required guardrail: maintain compile parity **657/657** and avoid introducing new Rust-reject files while aligning variant row-copy behavior.
  - Next OCaml refs: `compiler/ml/subst.ml` `typexp` variant recursion (`more.desc <- Tsubst (Ttuple [...])`) and `cleanup_types` interaction.
  - Next Rust refs: `compiler-rust/src/types/ctype.rs` variant copy paths, plus any temporary-substitution infrastructure equivalent to OCaml `save_desc`/cleanup.
- [ ] **5C. Validate `copy_type_deep` row-link keep policy per OCaml call path (NEW)** — applying `Ctype.copy`-style keep policy (`more.level <> generic_level`) globally in `copy_type_deep` was parity-neutral, so this logic likely differs by call site (`Subst.typexp`-style `dup` vs `Ctype.copy` keep).
  - Evidence (2026-02-24): temporary patch in `compiler-rust/src/types/ctype.rs` changed `Tvariant` `keep_reither_link` to `ctx.get_level(more) != GENERIC_LEVEL`; deterministic full parity stayed **478/657 → 478/657** (179 failures), compile parity stayed **657/657**, and targeted `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1**.
  - OCaml refs read: `compiler/ml/ctype.ml` (`copy` `Tvariant` branch, `keep = more.level <> generic_level`) and `compiler/ml/btype.ml` (`copy_row` keep-link behavior).
  - Parser/binary guard after revert: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - 2026-02-24 attempt: ported OCaml `Ctype.copy` row-copy flow into `compiler-rust/src/types/ctype.rs` `copy_type_cached` + `copy_row_cached`:
    - variant rows now copy via `row_field_repr` + `copy_row`-style keep/fixed semantics (instead of plain structural row-field cloning),
    - `row_more` now follows OCaml `copy` branch handling for `Tvar`/`Tunivar` (keep when non-generic row var, otherwise fresh copy),
    - PR#6163 row-fixed promotion is applied when copied `row_more` becomes `Tconstr`.
  - OCaml refs read: `compiler/ml/ctype.ml` (`copy` `Tvariant` branch around `keep`/`more'`/PR#6163) and `compiler/ml/btype.ml` (`copy_row`, `row_field_repr`).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1** parity.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures), compile parity stayed **657/657**.
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Next check: audit `copy_type_deep` callers (`instance_label`, module-type/type-path rewriting, functor specialization) and split row-link keep behavior by OCaml-equivalent intent instead of one global policy.
- [ ] **5D. Port OCaml `instance_poly`/`copy_sep` for Tpoly labels instead of `copy_type_deep` emulation (NEW)** — `instance_label` fixed-mode threading plus a `copy_type_deep` poly-row branch was parity-neutral, so the missing behavior is likely the full `copy_sep` algorithm (visited-bound conflict checks + delayed copy) rather than row flags alone.
  - Evidence (2026-02-24): the fixed-mode experiment produced no deterministic delta (**478/657 → 478/657**) while keeping compile parity **657/657** and parser guard green.
  - 2026-02-24 attempt: implemented OCaml-style `instance_poly` plumbing in `compiler-rust/src/types/ctype.rs` (`copy_sep`, `diff_list`, `conflicts`, delayed-copy linking) and threaded `fixed` through `instance_label` call sites in `compiler-rust/src/types/typecore.rs` (`false` for pattern-record paths, `true` for record/field expression paths).
  - OCaml refs read: `compiler/ml/ctype.ml` (`instance_label`, `instance_poly`, `copy_sep`, `diff_list`, `conflicts`, `delayed_copy`) and `compiler/ml/typecore.ml` (`build_as_type` record path, `type_label_exp`).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh gpr_4274_test`, `... set_gen`, `... more_poly_variant_test` all stayed **0/1**.
  - Deterministic full parity: **478/657 → 478/657** (179 parity failures, compile parity stayed **657/657**). Reverted.
  - Next OCaml refs: `compiler/ml/ctype.ml` `instance_poly`, `copy_sep`, `diff_list`, `conflicts`, `delayed_copy` flow.
  - Next Rust refs: `compiler-rust/src/types/ctype.rs` `instance_label`, `copy_type_deep`, and a dedicated poly-instantiation helper path for label typing.
- [ ] **5E. Align `instance_label` shared-copy window between `lbl_res` and Tpoly `lbl_arg` (NEW)** — OCaml runs `copy lbl_res` + `instance_poly lbl_arg` under one substitution/cleanup window; the Rust `copy_sep` port attempt remained parity-neutral and likely broke this coupling by keeping separate copy state for delayed copies vs label-result copying.
  - Evidence (2026-02-24): first-pass `copy_sep` port with `fixed` threading and delayed-copy linking stayed **478/657** with compile parity **657/657** and no targeted improvement (`gpr_4274_test`, `set_gen`, `more_poly_variant_test` all **0/1**).
  - 2026-02-24 follow-up attempt: rewired `compiler-rust/src/types/ctype.rs::instance_label` to OCaml order (`copy_type_cached(lbl_res)` first, then `instance_poly`-style `copy_sep` for `Tpoly lbl_arg`) under one shared copy cache, and added local `compute_univars`/`diff_list`/`conflicts`/delayed-copy forcing modeled on `ctype.ml`.
  - OCaml refs read: `compiler/ml/ctype.ml` (`instance_label`, `instance_poly`, `copy_sep`, `diff_list`, `conflicts`, `delayed_copy`) and `compiler/ml/btype.ml` (`copy_row`, `copy_type_desc`).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen`, `... gpr_4274_test`, `... more_poly_variant_test` all stayed **0/1** parity.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures), compile parity stayed **657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Reverted the code change after parity-neutral outcome; keep task unchecked.
  - Next OCaml refs: `compiler/ml/ctype.ml` call ordering in `instance_label` (`copy lbl_res` before/with `instance_poly`) plus `cleanup_types` interaction.
  - Next Rust refs: `compiler-rust/src/types/ctype.rs` `instance_label` cache/lifetime boundaries for `ty_res`, `instance_poly`, and delayed-copy forcing.
- [ ] **5F. Trace pre-`instance_label` label concretization for active Task-5 modules (NEW)** — replacing Rust `instance_label` deep-copy calls with OCaml-style `copy` semantics (`copy_type_cached` shared across `lbl_res` and `lbl_arg`, plus Tpoly Tunivar pre-seeding) was parity-neutral, so the `Tvar None` drift likely occurs before `instance_label` copying.
  - Evidence (2026-02-24): temporary patch in `compiler-rust/src/types/ctype.rs` switched `instance_label` to `copy_type_cached` (single cache window for `lbl_res` + `lbl_arg`) and reverted after neutral results.
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh gpr_4274_test`, `... set_gen`, and `... more_poly_variant_test` all stayed **0/1** parity.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures) with compile parity **657/657 → 657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - OCaml refs read: `compiler/ml/ctype.ml` (`copy`, `instance_label`, `instance_poly`, `compute_univars`, `copy_sep`).
  - Next Rust refs: `compiler-rust/src/types/typecore.rs` label disambiguation + expected-type extraction paths that build `env_label` before `instance_label`; confirm whether labels are already unconstrained when passed into `instance_label`.
- [ ] **5G. Prove whether active Task-5 failures bypass `instance_label` copy paths (NEW)** — an OCaml-shaped `instance_label` shared-window `copy_sep` port was parity-neutral, so `set_gen`/`gpr_4274_test` drift may originate earlier (label lookup/expected-type extraction) or in non-label paths.
  - Evidence (2026-02-24): full OCaml-order `instance_label`+`copy_sep` port with shared cache and delayed-copy forcing produced no targeted or full parity delta (**478/657**, compile parity **657/657**), then was reverted.
  - Next OCaml refs: `compiler/ml/typecore.ml` (`type_label_exp`, `extract_label`, record field typing paths that call `instance_label`) to verify when label arg/res are already concretized.
  - Next Rust refs: `compiler-rust/src/types/typecore.rs` (`disambiguate_label`, expected-type extraction helpers, `type_record` / `type_pattern_record` call flow) to trace types entering `instance_label`.
- [ ] **5H. Port OCaml `row_more` recursion marker in `Ctype.copy` variant copying (NEW)** — Rust now mirrors `copy_row` keep/fixed + `row_more` `Tvar`/`Tunivar` handling, but still lacks OCaml’s temporary `more.desc <- Tsubst (Ttuple [more'; t])` registration that preserves recursive row sharing during copy.
  - Evidence (2026-02-24): after porting `copy_type_cached` variant-row keep/fixed semantics, deterministic full parity stayed **478/657 → 478/657** (179 failures), compile parity stayed **657/657**, and filtered `set_gen` remained **0/1**.
  - 2026-02-24 attempt: implemented a scoped Rust equivalent of OCaml `copy` row marker in `compiler-rust/src/types/ctype.rs` (`CopyCache.row_more_markers` + `copy_type_cached` `Tvariant` marker lookup/registration mirroring `more.desc <- Tsubst (Ttuple [more'; t])` without mutating global descriptors), then reverted after regression.
  - OCaml refs read: `compiler/ml/ctype.ml` `copy` `Tvariant` branch (`Tsubst(Ttuple [more'; t])` registration and `Tsubst {desc = Ttuple [_; ty2]}` fast-path, lines ~913-979) and `compiler/ml/btype.ml` `copy_row` (`keep` link behavior, lines ~384-410).
  - Targeted check: `timeout 300 ./scripts/test_typedtree_parity.sh rbset` stayed **0/1** parity.
  - Deterministic full parity regressed **644/657 → 635/657** (parity failures **13 → 22**, compile parity stayed **657/657**). Reverted immediately.
  - Post-revert deterministic run: `timeout 300 ./scripts/test_typedtree_parity.sh` returned **657/657** (`SUCCESS: Full parity across all modules!`) while Rust sexp generation still intermittently reports a stack-overflow message.
  - Parser/binary guard after revert: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Next OCaml refs: `compiler/ml/ctype.ml` (`copy` `Tvariant` branch at `more.desc <- Tsubst (newgenty (Ttuple [more'; t]))`) and `cleanup_types` flow after instantiation.
  - Next Rust refs: `compiler-rust/src/types/ctype.rs` (`copy_type_cached` `TypeDesc::Tvariant` branch) plus `TypeContext` facilities for safe temporary substitution/cleanup equivalent.
- [ ] **5I. Split `Subst.typexp` vs `Ctype.copy` variant-row semantics by call path (NEW)** — forcing `Subst.typexp`-style `dup/keep` behavior into both `copy_type_deep` and `subst_identity_copy_rec` was parity-neutral, so at least one active Task-5 failure likely comes from applying the wrong row policy to the wrong instantiation path.
  - Evidence (2026-02-24): temporary patch in `compiler-rust/src/types/ctype.rs` changed `copy_type_deep` + `subst_identity_copy_rec` `Tvariant` branches to:
    - use OCaml `Subst.typexp` `dup` gating for `row_more` (`Tvar` duplicates only when `dup`, `Tunivar` preserved),
    - keep `Reither.link` with `not dup`,
    - remove `PR#6163` row-fixed promotion/matched forcing from these deep-copy paths.
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp` `Tvariant`/`row_more` flow), `compiler/ml/btype.ml` (`copy_row` keep-link behavior), and `compiler/ml/ctype.ml` (`copy` `Tvariant` PR#6163 row-fixed behavior, for contrast).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen`, `... gpr_4274_test`, `... fun_pattern_match` stayed **0/1** parity.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures), compile parity stayed **657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Reverted the code change after parity-neutral outcome; keep this task unchecked until call-site ownership of row-copy policy is mapped.
  - Next OCaml refs: trace which call sites use `Subst.typexp` semantics vs `Ctype.copy` semantics around label/newtype/module instantiation.
  - Next Rust refs: `compiler-rust/src/types/ctype.rs` call graph for `copy_type_deep`, `subst_identity_copy`, `copy_type_cached`, plus `typecore.rs`/`typemod.rs` entry points feeding active failing modules.
- [ ] **5J. Validate `Subst.typexp` `Tsubst(Ttuple ...)` marker lifetime in Rust `copy_type_deep` (NEW)** — a direct port of the marker flow in `copy_type_deep` was parity-neutral, so the missing behavior may be marker lifetime/call-window coupling (OCaml cleanup-driven) rather than marker shape alone.
  - Evidence (2026-02-24): `copy_type_deep` marker port (`dup`-gated `row_more` + temporary `more.desc <- Tsubst(Ttuple [more'; ty'])`) produced no deterministic delta (**478/657 → 478/657**, compile parity **657/657**), and filtered `set_gen`/`gpr_4274_test`/`more_poly_variant_test` all stayed **0/1**. Reverted.
  - Next OCaml refs: `compiler/ml/subst.ml` (`typexp` save/cleanup ordering around row-marker writes) and `compiler/ml/btype.ml` (`cleanup_types` effect on temporary `Tsubst` nodes).
  - Next Rust refs: `compiler-rust/src/types/ctype.rs` (`copy_type_deep`, `subst_identity_copy_rec`) and potential scoped temp-substitution support in `TypeContext` needed to mirror OCaml marker lifetime.
- [ ] **5K. Confirm `Ctype.copy` row-more keep/newty level semantics are not the remaining Task-5 blocker (NEW)** — porting `copy_type_deep` `Tvariant` toward OCaml `Ctype.copy` (`keep = more.level <> generic_level`, keep-rowvar identity, `Reither.link` keep policy, PR#6163 row-fixed promotion) was parity-neutral.
  - 2026-02-24 attempt: patched `compiler-rust/src/types/ctype.rs::copy_type_deep` `TypeDesc::Tvariant` branch to:
    - compute `keep` from `row_more` genericity (`more.level <> generic_level`),
    - preserve non-generic `Tvar`/`Tunivar` `row_more` by identity, otherwise allocate fresh `Tvar`/`Tunivar` via current-level `new_type` (OCaml `newty`-style),
    - reuse `Reither.link` only when `keep`, otherwise allocate a fresh row-field ref,
    - keep PR#6163 promotion (`row_fixed=true` when copied `row_more` is `Tconstr`).
  - OCaml refs read: `compiler/ml/ctype.ml` (`copy` `Tvariant` branch, lines ~913-979), `compiler/ml/btype.ml` (`copy_row`, lines ~384-410), `compiler/ml/subst.ml` (`typexp` `Tvariant` flow, lines ~191-225).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen`, `... gpr_4274_test`, `... more_poly_variant_test` all stayed **0/1** parity.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures), compile parity stayed **657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Reverted after parity-neutral outcome; keep task unchecked.
  - Next check: trace which Task-5 failures actually flow through `copy_type_deep` `Tvariant` (vs `copy_type_cached` or pre-`instance_label` label typing) before further row-copy tuning.
- [ ] **5L. Validate `Subst.typexp` fixed-row proxy rewrite placement (NEW)** — adding the `has_fixed_row` (`row_of_type` + `is_constr_row ~allow_ident:false`) branch directly to `copy_type_deep` was parity-neutral and appears to shift cycle-vs-constr diffs across modules, so this behavior may belong to a narrower call path.
  - 2026-02-24 attempt: patched `compiler-rust/src/types/ctype.rs::copy_type_deep` to mirror OCaml `Subst.typexp` fixed-row logic:
    - compute `tm = row_of_type ty`,
    - gate on `not is_Tconstr ty && is_constr_row ~allow_ident:false tm`,
    - synthesize `Tconstr` from `Pdot(..., name#row)` by stripping `#row` (`name[..len-4]`) before returning the copy.
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp` `tm`/`has_fixed_row` branch and `Pdot(..., i#row)` rewrite) and `compiler/ml/btype.ml` (`row_of_type`, `is_constr_row`).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen`, `... gpr_4274_test`, and `... fun_pattern_match` all stayed **0/1** parity.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures), compile parity stayed **657/657 → 657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Reverted after parity-neutral outcome; keep task unchecked.
  - Next check: trace whether active Task-5 failures reach OCaml’s fixed-row proxy path through `copy_type_deep` call sites (`instance_label`, `typemod` deep copies) before re-applying this rewrite globally.
- [ ] **5M. Isolate `Subst.typexp` `dup/more'` row-variable policy in `copy_type_deep` only (NEW)** — applying `dup`-gated `row_more` identity/copy behavior only in `copy_type_deep` (without touching `subst_identity_copy_rec` or `copy_type_cached`) was parity-neutral, so the remaining Task-5 drift is likely in call-site selection/lifetime coupling rather than this branch in isolation.
  - 2026-02-24 attempt: patched `compiler-rust/src/types/ctype.rs::copy_type_deep` `TypeDesc::Tvariant` branch to:
    - compute OCaml-style `dup` from `row_more` (`generic_level` / `static_row` / `Tconstr`),
    - keep `row_more` identity for non-dup `Tvar`/`Tunivar`, copy only on dup cases,
    - keep `Reither.link` only when `not dup`,
    - remove PR#6163-style `row_fixed`/`matched` forcing from this deep-copy path.
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp` `Tvariant` `dup`/`more'` branch), `compiler/ml/btype.ml` (`copy_row` keep-link behavior), and `compiler/ml/ctype.ml` (`copy` PR#6163 row-fixed behavior, for contrast).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen`, `... more_poly_variant_test`, and `... gpr_4274_test` all stayed **0/1** parity.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures), compile parity stayed **657/657 → 657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Reverted after parity-neutral outcome; keep task unchecked.
  - Next check: map which active failing modules flow through `copy_type_deep` vs `copy_type_cached` vs `instance_label` and pin a single failing path before re-applying `dup/more'` logic.
- [ ] **5N. Validate placeholder materialization shape in `copy_type_deep` against `Subst.typexp` stubs (NEW)** — replacing `placeholder -> Tlink(result)` with direct `placeholder.desc <- copied_desc` for deep-copied `Tvariant`/`Tobject`/`Tfield` was parity-neutral, so extra-link-node shape alone is not the active blocker.
  - 2026-02-24 attempt: patched `compiler-rust/src/types/ctype.rs::copy_type_deep` to materialize copied descriptors directly into stubs for `TypeDesc::Tvariant`, `TypeDesc::Tobject`, and `TypeDesc::Tfield` (no intermediate `ctx.new_*` node + `Tlink`), then reverted after neutral results.
  - OCaml refs read: `compiler/ml/subst.ml` (`typexp` stub flow: `let ty' = newgenvar (); ty.desc <- Tsubst ty'; ty'.desc <- ...`) and `Tvariant`/`Tobject`/`Tfield` branches.
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` and `... fun_pattern_match` both stayed **0/1** parity.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures), compile parity stayed **657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Reverted after parity-neutral outcome; keep task unchecked.
  - Next check: trace whether active Task-5 modules reach `copy_type_deep` through call sites that depend on `Tlink` identity (especially typemod signature copies) before re-applying stub-shape changes.
- [ ] **5O. Validate OCaml `set_row_field` link mutation in row unification (NEW)** — enabling `Reither` link writes in Rust row-field unification was parity-neutral, so link mutation alone does not resolve current Task-5 drift.
  - 2026-02-24 attempt: patched `compiler-rust/src/types/ctype.rs::unify_row_field` to set links in OCaml-shaped cases (`Reither/Reither` shared links for fixed rows, `Reither/Rpresent`, `Reither/Rabsent`) with temporary rollback support in `compiler-rust/src/types/context.rs`.
  - OCaml refs read: `compiler/ml/ctype.ml` (`unify_row_field`, `set_row_field` cases) and `compiler/ml/btype.ml` (`row_field_repr` link resolution).
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen`, `... more_poly_variant_test`, and `... gpr_4274_test` all stayed **0/1** parity.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures), compile parity stayed **657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Reverted after parity-neutral outcome; keep task unchecked.
  - Next check: align broader OCaml `unify_row` control flow (`set_more`, rest-field handling, and redo path) before retrying link mutation in isolation.
- [ ] **6. Expand abbreviations before structural match for same-path Tconstr** — When same path + n_args>0, expand both, unify expanded. (638→639, tests: unboxed_use_case.res, ExternalArity.res)
  - 2026-02-24 attempt: added same-path expansion branch in `ctype.rs` (`unify` Tconstr/Tconstr path-equal case) with direct `unify(exp1, exp2)` when expansion leaves `Tconstr` and no pre-link of `t1 -> t2`. Deterministic full parity stayed **478/657 → 478/657** (179 failures). Targeted `unboxed_use_case` and `ExternalArity` remained **0/1**. Reverted.
  - 2026-02-24 attempt: re-tried the same-path path-equal branch with OCaml `unify2`/`unify3` ordering (`expand_head` first, structural unify only when both sides remain `Tconstr`). OCaml refs read: `compiler/ml/ctype.ml` (`unify2`, `unify3`, same-path `Tconstr` case). Deterministic parity stayed **478/657 → 478/657** (179 failures), targeted `timeout 300 ./scripts/test_typedtree_parity.sh unboxed_use_case` and `... ExternalArity` stayed **0/1**, parser/binary guard stayed green (`SUCCESS: All 3532 files have full parity!`). Reverted.
  - 2026-02-24 attempt: implemented a guarded same-path expansion-first branch in `compiler-rust/src/types/ctype.rs::unify_types` using `expand_head_once` (args non-empty only), with direct `unify(expanded1, expanded2)` when either side expands away from `Tconstr`, and no direct `t1 -> t2` link on the expansion path.
  - OCaml refs read: `compiler/ml/ctype.ml` (`unify2`, `unify3`, `expand_head_unif`) and expansion behavior around `try_expand_head`.
  - Deterministic parity: **478/657 → 478/657** (179 parity failures, compile parity stayed 657/657).
  - Targeted: `timeout 300 ./scripts/test_typedtree_parity.sh unboxed_use_case` **0/1**, `timeout 300 ./scripts/test_typedtree_parity.sh ExternalArity` **0/1**.
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` stayed green (`SUCCESS: All 3532 files have full parity!`).
- [ ] **6A. Verify local polyvariant alias expansion reaches `expand_head` before same-path arg unification (NEW)** — The task-6 logic remains parity-neutral, suggesting local parameterized aliases are still entering structural arg unification without OCaml-equivalent head expansion.
  - Evidence (2026-02-24): reviewed OCaml `ctype.ml` (`unify2`, `unify3`, `expand_head_unif`) and `env.ml` (`find_type_expansion`), then re-applied a same-path expansion-first branch in Rust `ctype.rs` and re-ran deterministic parity. Full parity stayed **478/657 → 478/657** (179 failures); filtered `unboxed_use_case` and `ExternalArity` remained **0/1**. Reverted.
  - Follow-up evidence (2026-02-24): with temporary tracing in `try_expand_head`, Rust does reach `expand_head` for `t3` and expands to `Tvariant` (env decl manifest present, params=2). A recursion-safe issue remains after that point, not a missing expansion trigger.
  - `unboxed_use_case` drift remains on baseline: OCaml keeps phantom args as `Tvar None` for `t3<_>`, Rust still concretizes to `Tconstr int/string`.
  - Next OCaml refs: `ctype.ml` `unify2`/`unify3` link direction and recursion control for expanded aliases.
  - Next Rust refs: same-path `Tconstr` branch in `ctype.rs::unify_types` and `unify_after_expansion` relinking behavior.
- [ ] **6B. Make same-path alias expansion recursion-safe after expansion (NEW)** — A straightforward same-path expansion branch can remove the `t3<_>` concretization drift but currently causes global stack-overflow regressions.
  - Evidence (2026-02-24): with same-path expansion enabled and wired through `expand_head`, full deterministic parity regressed to **632/657** then **570/657** with Rust compile coverage **647/657** (10 OCaml-only passes) due `thread '<unknown>' has overflowed its stack` during Rust sexp generation. Reverted to restore baseline **478/657** and **657/657** compile parity.
  - Required guardrail: preserve deterministic full-run stability (no stack overflow, no compile parity drop) while aligning same-path alias behavior with OCaml on `unboxed_use_case`/`ExternalArity`.
- [ ] **6C. Trace where `t3<_>` args become concrete before/after same-path unify (NEW)** — two same-path expansion retries were parity-neutral, so the `Tvar None -> Tconstr int/string` drift likely happens outside the local same-path branch (or is overwritten later).
  - Evidence (2026-02-24): after adding and re-testing path-equal expansion-first logic in `ctype.rs::unify_types`, `unboxed_use_case` diff still shows identical concretization drift in `t3` args and full parity remains **478/657**.
  - Next OCaml refs: `compiler/ml/ctype.ml` `unify` entry flow around `update_level` + `expand_head_unif` interactions before same-path argument unification.
  - Next Rust refs: `compiler-rust/src/types/ctype.rs` call chain into `unify_types` plus `update_level_expand` side effects on parameterized aliases in `unboxed_use_case`.
- [ ] **6D. Validate same-path expansion gate in `Tconstr/Tconstr` branch before arg unification (NEW)** — explicitly porting the `unify2` expansion-first check at the same-path branch remained parity-neutral on this snapshot.
  - Evidence (2026-02-24): added a guarded branch in `ctype.rs::unify_types` (only when args are non-empty and `expand_head` changes at least one side to non-`Tconstr`) to `unify` the expanded forms without pre-linking `t1 -> t2`; deterministic full parity stayed **478/657 → 478/657** (179 failures), `timeout 300 ./scripts/test_typedtree_parity.sh unboxed_use_case` stayed **0/1**, and `timeout 300 ./scripts/test_typedtree_parity.sh ExternalArity` stayed **0/1**. Reverted.
  - OCaml refs read: `compiler/ml/ctype.ml` `unify2` / `unify3` (`expand_head_unif` ordering and same-path `Tconstr` handling).
  - Next check: inspect whether `update_level_expand` or post-unify relinking re-concretizes phantom args after the initial same-path unification step.
- [ ] **6E. Trace/align same-path `t3_aux` arg unification after `t3` expansion (NEW)** — `t3` now expands to structural form in the same-path branch, but `unboxed_use_case` still concretizes phantom args through subsequent same-path `t3_aux` argument unifications.
  - Evidence (2026-02-24): direct Rust compiler tracing (`compiler-rust/target/release/bsc -dtyped-sexp-locs tests/tests/src/unboxed_use_case.res`) shows:
    - `t3` same-path unification reaches expansion (`exp1_is_constr=false`, `exp2_is_constr=false`).
    - Multiple later same-path `t3_aux` unifications still run with `lhs=[Tvar,Tvar]` vs `rhs=[Tconstr(int),Tconstr(string)]`, forcing concretization.
  - Follow-up refs:
    - OCaml: `compiler/ml/ctype.ml` `unify3` same-path `Tconstr` handling + call sites that instantiate constructor/label types for this path.
    - Rust: `compiler-rust/src/types/ctype.rs::unify_types` (same-path `Tconstr` branch), plus `typecore.rs` constructor/record-label instantiation paths feeding those `t3_aux` unifications.
- [ ] **6F. Validate `unify_after_expansion` wiring for same-path parameterized aliases (NEW)** — forcing same-path `Tconstr` branch to call `unify_after_expansion` whenever `expand_head` changed either side was parity-neutral on this snapshot.
  - Evidence (2026-02-24): patched `compiler-rust/src/types/ctype.rs::unify_types` to replace the `expand_head_once`+`exp_is_constr` gate with `expand_head` and `unify_after_expansion` for same-path non-empty args.
  - Deterministic parity stayed **478/657 → 478/657** (179 parity failures), filtered `timeout 300 ./scripts/test_typedtree_parity.sh unboxed_use_case` stayed **0/1**, and filtered `timeout 300 ./scripts/test_typedtree_parity.sh ExternalArity` stayed **0/1**.
  - Parser/binary guard remained green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Reverted the code change; keep this as evidence that same-path expansion routing alone does not remove `t3<_> -> t3<int,string>` concretization.
- [ ] **6G. Trace pre-`t3` concretization path in record/variant typing (NEW)** — `t3<_>` concretization appears before the expanded `t3` branch is done, via repeated `t3_aux` same-path arg unifications in expression mode.
  - Evidence (2026-02-24): temporary tracing in `compiler-rust/src/types/ctype.rs::unify_types` on direct Rust compile (`timeout 10 ./compiler-rust/target/release/bsc -I lib/ocaml -I ../tests/lib/ocaml -dtyped-sexp-locs src/unboxed_use_case.res`) showed:
    - same-path `t3` does expand to structural `Tvariant` with `A:t3_aux<int,string>` on both sides.
    - multiple surrounding same-path `t3_aux` unifications still run with `lhs=[Tvar,Tvar]` vs `rhs=[Tconstr(int),Tconstr(string)]`, forcing concretization.
  - Parity-neutral experiment (reverted): attempted isolating record-label field typing from expected-record unification in `compiler-rust/src/types/typecore.rs::type_record` by copying label arg/res before/after unify. Filtered `timeout 300 ./scripts/test_typedtree_parity.sh unboxed_use_case` remained **0/1** and deterministic full parity stayed **478/657** with compile parity **657/657**.
  - OCaml refs read: `compiler/ml/typecore.ml` (`Pexp_variant`, `type_label_exp`, `type_argument`) and `compiler/ml/ctype.ml` (`instance_label`, `unify2`, `unify3`).
  - Next Rust refs: `compiler-rust/src/types/typecore.rs` (`type_variant` fast path and record field typing around `instance_label`) plus constructor/label instantiation flow that introduces `t3_aux<'a,'b>` unifications before `t3` row expansion stabilizes.
- [x] **7. build_as_type for Tpat_variant and Tpat_or** — Add Tpat_variant (open row+Rpresent) and Tpat_or (open row). (643→644, test: more_poly_variant_test.res)
  - Verified 2026-02-24: Rust `build_as_type` already has explicit `Tpat_variant` and `Tpat_or` branches in `compiler-rust/src/types/typecore.rs`; deterministic full run at **653/657** does not include `more_poly_variant_test` in failures.
- [x] **8. Label type param sharing** — Add `remap_label_type_to_params` so lbl_arg/lbl_res share Tvar nodes. (646→647, test: gpr_4274_test.res)
  - 2026-02-24 fix: implemented `remap_label_type_to_params` in `compiler-rust/src/types/ctype.rs` (OCaml-aligned direct named-parameter remap for label args) and threaded it through declaration-backed `LabelDescription` construction in:
    - `compiler-rust/src/types/env.rs`
    - `compiler-rust/src/cmi/persistent_env.rs`
    - `compiler-rust/src/types/typemod.rs`
    - `compiler-rust/src/types/typecore.rs`
  - OCaml refs read: `compiler/ml/datarepr.ml` (`label_descrs`), `compiler/ml/types.ml` (`label_description`), `compiler/ml/ctype.ml` (`instance_label`), `compiler/ml/typecore.ml` (label typing flow around `type_label_exp`/`extract_label`).
  - Deterministic full parity: **639/657 → 653/657** (failures **18 → 4**), compile parity stayed **657/657**.
  - Remaining failing modules after this fix: `defunctor_make_test`, `ext_array_test`, `flexible_array_test`, `functor_ffi`.
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - 2026-02-23 attempt: implemented/remapped `lbl_arg` at label construction sites (`typemod.rs`, `typecore.rs`, `env.rs`, `persistent_env.rs`) and ran deterministic full parity. Result stayed **478/657 → 478/657** (179 failures). `gpr_4274_test` diff unchanged. Reverted experiment; keep this task unchecked.
  - 2026-02-24 attempt: re-implemented `remap_label_type_to_params` as a cycle-safe in-place remap in `ctype.rs` and threaded it through all declaration-backed label construction sites (`env.rs`, `persistent_env.rs`, `typemod.rs`, `typecore.rs`). Deterministic full parity stayed **478/657 → 478/657** (179 failures), filtered `timeout 300 ./scripts/test_typedtree_parity.sh gpr_4274_test` stayed **0/1** with identical `Tconstr(...) -> Tvar None` drift, parser/binary guard stayed green (`SUCCESS: All 3532 files have full parity!`). Reverted.
  - OCaml refs read: `compiler/ml/datarepr.ml` (`label_descrs`), `compiler/ml/types.ml` (`label_description`), `compiler/ml/typecore.ml` (label disambiguation flow around `type_label_exp`/`extract_label`).
- [x] **8A. Qualified label disambiguation for module-scoped records (NEW)** — `gpr_4274_test` still resolves `X.i` / `Foo.foo` through fresh `Tvar None` instead of concrete record paths (`N.t`, `Foo.record`), indicating label lookup/disambiguation fallback is selecting or synthesizing unconstrained labels.
  - Resolution (2026-02-24): resolved by the Task 8 label-param remap fix; `gpr_4274_test` dropped out of the deterministic failure list at **653/657**.
  - Evidence: deterministic filtered diff on 2026-02-23 shows repeated `Tconstr(Pdot(Pident \"N\"), \"t\") -> Tvar None` and `Tconstr(Pdot(Pident \"Foo\"), \"record\") -> Tvar None`.
  - Session confirmation (2026-02-23): `timeout 300 ./scripts/test_typedtree_parity.sh` remained **478/657** with **179** parity failures; `timeout 300 ./scripts/test_typedtree_parity.sh gpr_4274_test` remained **0/1** with the same drift.
  - Next OCaml refs: `typecore.ml` label disambiguation path (`NameChoice`/`extract_label`) and module-qualified label lookup behavior.
  - Next Rust refs: `typecore.rs` `disambiguate_label`, `lookup_label_by_expected_type`, and module-signature path resolution helpers.
- [x] **8B. Verify longident preservation for record labels before disambiguation (NEW)** — determine whether module qualifiers (`X.i`, `Foo.foo`) are preserved in `ExpressionRecordField.lid` / `PatternRecordField.lid` by the time `typecore` runs.
  - Resolution (2026-02-24): resolved by the Task 8 label-param remap fix; `gpr_4274_test` dropped out of the deterministic failure list at **653/657**.
  - Evidence (2026-02-24): added `disambiguate_label_by_lid` + module-signature label lookup (`resolve_module_lid`, last-defined `SigType` record-label selection) and threaded through record/pattern/field access. Deterministic full parity stayed **478/657 → 478/657** (179 failures); filtered `gpr_4274_test` remained **0/1** with unchanged `Tconstr(Pdot(Pident \"N\"), \"t\") -> Tvar None` and `Tconstr(Pdot(Pident \"Foo\"), \"record\") -> Tvar None` drift. Reverted.
  - Hypothesis: record-field longidents may already be de-qualified (or normalized to non-module paths) before label disambiguation, so module-aware lookup is never exercised.
  - Next OCaml refs: `typecore.ml` record-field typing paths (`type_label_exp`, record/pattern label lookup) and `NameChoice` handling of qualified labels.
  - Next Rust refs: parser/binary-ast longident plumbing for record fields, `type_pattern_record` and `type_record` call sites, and `TypeCheckContext::resolve_lid`.
- [x] **8C. Confirm `instance_label` input is already unconstrained in `gpr_4274_test` (NEW)** — both remap-label experiments were parity-neutral, so the `Tvar None` drift likely occurs before or during label disambiguation/expected-type extraction, not when constructing declaration labels.
  - Resolution (2026-02-24): resolved by the Task 8 label-param remap fix; `gpr_4274_test` dropped out of the deterministic failure list at **653/657**.
  - Evidence (2026-02-24): a full remap pass over declaration-backed labels (all major construction sites) left `gpr_4274_test` unchanged (`0/1`) and full parity unchanged (**478/657**, 179 failures); the same `N.t`/`Foo.record` fields still collapse to `Tvar None`.
  - Next OCaml refs: `compiler/ml/typecore.ml` `type_label_access`, `type_label_exp`, and `NameChoice.disambiguate` call path for qualified labels.
  - Next Rust refs: `typecore.rs` `disambiguate_label`, `lookup_label_by_expected_type`, `extract_type_path_from_expected_with_persistent_env`, and `instance_label` call sites in `type_record`/`type_pattern_record`.
- [x] **8D. Verify declaration type params expose stable names at label-construction sites (NEW)** — a name-based remap pass across declaration-backed `LabelDescription` builders was parity-neutral, suggesting parameter names may already be erased (`Tvar None`) before remap or the `gpr_4274_test` drift is upstream of label construction.
  - Resolution (2026-02-24): resolved by the Task 8 label-param remap fix; `gpr_4274_test` dropped out of the deterministic failure list at **653/657**.
  - 2026-02-24 attempt: added `remap_label_type_to_params` in `compiler-rust/src/types/ctype.rs` and threaded it into declaration-backed label builders in `compiler-rust/src/types/env.rs`, `compiler-rust/src/types/typemod.rs`, `compiler-rust/src/cmi/persistent_env.rs`, and type-directed label synthesis in `compiler-rust/src/types/typecore.rs`.
  - OCaml refs read: `compiler/ml/datarepr.ml` (`label_descrs`) and `compiler/ml/types.ml` (`label_description`).
  - Targeted check: `timeout 300 ./scripts/test_typedtree_parity.sh gpr_4274_test` stayed **0/1** with unchanged `N.t`/`Foo.record -> Tvar None` drift.
  - Deterministic full parity stayed **478/657 → 478/657** (179 parity failures), compile parity stayed **657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Reverted after parity-neutral result; keep this task unchecked.
- [ ] **9. Shallow-copy pattern variable types** — Shallow Tconstr copies for pattern vars with non-empty args. (631→634, +3 tests)
  - 2026-02-24 attempt: patched `compiler-rust/src/types/typecore.rs::type_function` to shallow-copy non-empty `Tconstr` pattern bindings for non-simple parameter patterns before inserting values into the body env (`type_case_impl` already does this), then reverted after neutral results.
  - OCaml refs read: `compiler/ml/typecore.ml` (`type_function`, `type_cases`, `add_pattern_variables`).
  - Targeted checks:
    - `timeout 300 ./scripts/test_typedtree_parity.sh rbset` stayed **0/1** (hunk mismatches: 6)
    - `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1** (hunk mismatches: 82)
    - `timeout 300 ./scripts/test_typedtree_parity.sh fun_pattern_match` stayed **1/1**
  - Deterministic full parity stayed **589/657 → 589/657** (parity failures **61 → 61**), compile parity stayed **650/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - 2026-02-24 attempt: added shallow non-empty `Tconstr` copies for pattern-bound values in both `type_case_impl` (always) and `type_function` (non-simple param patterns only), matching the task description; deterministic full parity stayed **478/657 → 478/657** (179 failures), filtered `unboxed_use_case` remained **0/1**. Reverted.
  - 2026-02-24 follow-up: reintroduced task-9 shallow copies via a shared helper in `compiler-rust/src/types/typecore.rs`:
    - `type_case_impl`: always shallow-copy pattern-bound `Tconstr` values (non-empty args) before inserting into case env.
    - `type_function`: shallow-copy those bindings only for non-simple parameter patterns (`_`, `x`, and alias-to-variable stay direct).
    - module unpack env threading now uses the copied binding type in both paths.
  - OCaml refs read: `compiler/ml/typecore.ml` `add_pattern_variables` (~1742), `type_function` (~3262), `type_cases` pattern/body flow (~3906-4050), `is_var` helper in `type_cases`.
  - Targeted checks: `timeout 300 ./scripts/test_typedtree_parity.sh unboxed_use_case` stayed **0/1**; filtered `timeout 300 ./scripts/test_typedtree_parity.sh "belt_*"` remained unstable in this repo snapshot (Rust **2/9**, OCaml-only pass **7** in filtered mode).
  - Deterministic full parity remained **478/657 → 478/657** (179 failures), compile parity stayed **657/657**.
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - OCaml refs read: `compiler/ml/typecore.ml` `add_pattern_variables` (~1742), `type_function` (~3262), `type_cases` (~3906-4050).
- [ ] **9A. Identify pre-env concretization site for pattern vars (NEW)** — task-9 env insertion copies were parity-neutral, so non-empty `Tconstr` concretization likely happens earlier (during pattern typing / per-case propagation) or later via shared-case flow.
  - Evidence (2026-02-24): task-9 port in Rust (`type_case_impl` + `type_function` env insertion shallow copies) produced no deterministic parity delta (**478/657 → 478/657**) and did not change `unboxed_use_case` drift.
  - Next OCaml refs: `typecore.ml` `type_pattern` and `type_cases` propagation/generalization ordering (`unify_pats`, `iter_pattern ... generalize`, body typing).
  - Next Rust refs: `typecore.rs` `type_pattern`, `type_case_impl`, and any pre-body pattern-variable plumbing that can still share original scrutinee/type nodes.
- [ ] **9B. Trace pre-body-env alias concretization in `type_function` parameter flow (NEW)** — a focused Task-9 retry that only changed `type_function` body-env insertion to shallow-copy non-simple pattern bindings was parity-neutral at the current baseline, so the `rbset`/`set_gen` drift likely occurs before body env insertion (expected-arrow extraction, param pattern typing, or recursive-let unification handoff).
  - Evidence (2026-02-24): deterministic full parity remained **589/657** with unchanged failure set after the isolated `type_function` shallow-copy patch; targeted `rbset`/`set_gen` stayed **0/1**.
  - Next OCaml refs: `compiler/ml/typecore.ml` `type_function` + `type_cases` (`filter_arrow`, per-case `instance env ty_arg`, `unify_pats` propagation) and recursive-let handoff in `type_let`.
  - Next Rust refs: `compiler-rust/src/types/typecore.rs` (`type_function` expected-arrow extraction / `param_ty` flow, `type_pattern`) and `type_let`/`type_let_bindings` boundaries where function result types are unified with approximation nodes.
- [ ] **10. Protect scrutinee type from pattern unification** — Shallow copy when instance() returns identity. (636→637, test: option_repr_test.res)
  - 2026-02-24 attempt: added a `type_case_impl` scrutinee guard that `instance`s the case scrutinee type and shallow-copies identity-return `Tconstr` nodes before `type_pattern`. Deterministic full parity stayed **478/657 → 478/657** (179 failures). Reverted.
  - OCaml refs read: `typecore.ml` `type_cases` (`instance ?partial env ty_arg`, pattern/body phasing around lines ~3906-4050) and `add_pattern_variables` (~1742).
- [ ] **10A. Reproduce scrutinee contamination in batch case-typing flow (NEW)** — The per-case guard above was parity-neutral, which suggests drift is in Rust’s per-case typing architecture vs OCaml’s batch `type_cases` propagation/generalization pipeline rather than a single scrutinee instance site.
  - Evidence (2026-02-24): full parity remained **478/657** with **179** failures after the scrutinee-guard patch; `variantsMatching` still shows repeated `<cycle> -> Tconstr(Pident \"t\", <cycle>)` drift in `.parity-cache/tests/diffs/variantsMatching.diff`.
  - Next OCaml refs: `typecore.ml` `type_cases` propagation section (`unify_pats`, `iter_pattern ... generalize`, `instance env ty_res'` in case bodies).
  - Next Rust refs: `typecore.rs` `type_case_impl` and surrounding match/case typing control flow to align with OCaml’s batch pattern-first then body-typing order.
- [ ] **11. Shallow copy nullary pattern var types** — Prevent scrutinee contamination via body unification. (645→646, test: reasonReactRouter.res)
  - 2026-02-24 attempt (reverted): in `compiler-rust/src/types/typecore.rs`, enabled nullary-`Tconstr` shallow copies for case-bound vars (`type_case_impl`) and added non-simple-parameter shallow-copying in `type_function` body env via `shallow_copy_pattern_binding_type(..., copy_nullary=true)`.
  - OCaml refs read: `compiler/ml/typecore.ml` (`type_cases`, `add_pattern_variables`) and `compiler/ml/ctype.ml` (`instance` identity behavior for non-generic constructors).
  - Targeted checks:
    - `timeout 300 ./scripts/test_typedtree_parity.sh rbset` stayed **0/1** (hunk mismatches: 6)
    - `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1** (hunk mismatches: 82)
    - `timeout 300 ./scripts/test_typedtree_parity.sh topsort_test` stayed **0/1** (hunk mismatches: 98)
  - Deterministic full parity stayed **589/657 → 589/657** (parity failures **61 → 61**, Rust compile coverage **650/657**). Reverted.
- [ ] **11A. Trace nullary-pattern contamination before body-env insertion (NEW)** — task-11 nullary shallow copies at body-env insertion were parity-neutral, so the `<cycle> ↔ Tconstr/Tvar` drift likely happens earlier (pattern typing/instance timing) or at recursive-let handoff.
  - Evidence (2026-02-24): nullary-copy patch in `type_case_impl` + non-simple `type_function` body-env copy produced no delta on `rbset`, `set_gen`, `topsort_test`, or deterministic full parity (**589/657** unchanged).
  - Next OCaml refs: `compiler/ml/typecore.ml` `type_cases` pattern pass (`instance env ty_arg`, `unify_pats`, `iter_pattern ... generalize`) and recursive-let flow in `type_let`.
  - Next Rust refs: `compiler-rust/src/types/typecore.rs` (`type_case_impl`, `type_function`, `type_let_bindings`) and `compiler-rust/src/types/ctype.rs::instance`.
- [ ] **12. Force-generalize module sig value types** — Walk sig types to GENERIC_LEVEL (exclude nullary Tconstr). (637→638, net +1)
  - 2026-02-24 attempt: added `force_generalize_module_sig_values` in `compiler-rust/src/types/ctype.rs` and threaded it through `compiler-rust/src/types/typemod.rs` module env insertion sites:
    - `Pstr_module`: force-generalize extracted module signatures before `Env.add_module`.
    - `Pstr_recmodule`: force-generalize both initial constrained signatures and final extracted module signatures before `Env.add_module`.
  - Rust behavior added: recursively walk module-type signatures/functors, promote reachable `SigValue` type nodes to `GENERIC_LEVEL`, but skip nullary `Tconstr` roots to avoid the known `find_simple_abbrev` / `LetUnwrap` remap regression.
  - OCaml refs read:
    - `compiler/ml/typemod.ml` (`type_structure` `Sig_module` construction + `Mtype.lower_nongen` on module declarations, lines ~1451-1486)
    - `compiler/ml/ctype.ml` (`generalize`, `generalize_structure`, level-promotion behavior)
  - Targeted checks:
    - `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` → `0/1` parity (still failing)
    - `timeout 300 ./scripts/test_typedtree_parity.sh LetUnwrap` → `0/1` parity (still failing)
    - `timeout 300 ./scripts/test_typedtree_parity.sh inline_map2_test` → both-fail in filtered mode (`0/1`)
  - Deterministic full parity delta: **588/657 → 588/657** (parity failures **62 → 62**), Rust compile coverage stayed **650/657**.
  - Parser/binary guard after patch: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
- [ ] **12A. Port OCaml `Mtype.lower_nongen` semantics for module declarations (NEW)** — task-12 force-generalization was parity-neutral, so the remaining drift is likely in level lowering timing/scope, not a blanket promotion pass.
  - Evidence (2026-02-24): even with recursive module-signature value-type promotion (and nullary-`Tconstr` guard), full parity remained **588/657** with unchanged `set_gen` / `LetUnwrap` failures.
  - 2026-02-24 attempt (reverted): implemented OCaml-shaped `lower_nongen_module_type` traversal in `compiler-rust/src/types/ctype.rs` (lower only `Tvar` levels where `nglev < level < GENERIC_LEVEL` across full module-type contents: `SigValue`, `SigType`, `SigTypext`, nested modules/modtypes/functors) and wired `compiler-rust/src/types/typemod.rs::Pstr_module` to call it with `mod_id.binding_time() - 1` before `Env.add_module` (replacing `force_generalize_module_sig_values` for this path).
  - OCaml refs read:
    - `compiler/ml/mtype.ml` (`lower_nongen`, iterator-based module-type walk lowering only `Tvar` levels)
    - `compiler/ml/typemod.ml` (`Pstr_module` calls `Mtype.lower_nongen (Ident.binding_time id - 1) md.md_type` before env insertion)
  - Targeted checks:
    - `timeout 300 ./scripts/test_typedtree_parity.sh LetUnwrap` stayed **0/1** (hunk mismatches: 11)
    - `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1** (hunk mismatches: 82)
    - `timeout 300 ./scripts/test_typedtree_parity.sh inline_map2_test` stayed **0/1** (OCaml-only pass)
  - Deterministic full parity stayed **589/657 → 589/657** (parity failures **61 → 61**, Rust compile coverage **650/657 → 650/657**).
  - Parser/binary guard after revert: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Outcome: parity-neutral on this snapshot; patch reverted and task remains open.
  - Next OCaml refs: `compiler/ml/mtype.ml` (`lower_nongen`), `compiler/ml/typemod.ml` module declaration insertion points (`Pstr_module`, `Pstr_recmodule`).
  - Next Rust refs: `compiler-rust/src/types/typemod.rs` module env insertion paths and `compiler-rust/src/types/context.rs` level APIs (`current_level`, `nongen_level`, `init_def`).
- [ ] **12B. Verify `Ident.binding_time` scale alignment before `lower_nongen` in module typing (NEW)** — OCaml compares `Ident.binding_time` and type levels on the same timeline (`init_def (Ident.current_time())`), but Rust currently uses `Ident::create_local` stamps in `Pstr_module` while type levels are managed by `TypeContext`, so `mod_id.binding_time() - 1` may be on a different scale and produce a no-op.
  - Evidence (2026-02-24): direct `lower_nongen` port in `Pstr_module` was parity-neutral at **589/657**, despite targeting the exact OCaml call site.
  - 2026-02-24 attempt (kept): aligned Rust `init_def`/stamp timeline to OCaml `Ident.current_time` call sites:
    - `compiler-rust/src/types/typemod.rs`: added `ctx.init_def(ctx.current_stamp())` in `transl_signature` item loop, `type_structure` item loop, `type_structure_no_export` item loop, `Pmod_functor` body typing, `Pmty_functor` result typing, and `Pstr_recmodule` pre-approximation.
    - `compiler-rust/src/ident.rs`: moved `Ident::create_local` to a shared module-level counter and added `Ident::current_local_stamp()`.
    - `compiler-rust/src/types/context.rs`: `TypeContext::current_stamp()` now returns `max(id_gen.current_stamp(), Ident::current_local_stamp())`.
  - OCaml refs read for kept attempt:
    - `compiler/ml/typemod.ml` (`transl_signature`, `type_struct`, `Pmod_functor`, `transl_recmodule_modtypes` `Ctype.init_def (Ident.current_time ())` call sites)
    - `compiler/ext/ident.ml` (`create`, `binding_time`, `current_time`, `set_current_time`)
  - Targeted check: `timeout 300 ./scripts/test_typedtree_parity.sh LetUnwrap` stayed **0/1** (hunk mismatches: 11).
  - Deterministic full parity stayed **589/657 → 589/657** (parity failures **61 → 61**, Rust compile coverage **650/657 → 650/657**).
  - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Next OCaml refs: `compiler/ml/typemod.ml` (`type_struct` `Ctype.init_def (Ident.current_time ())` and `Pstr_module`), `compiler/ml/ident.ml` (`binding_time`/stamp semantics), `compiler/ml/mtype.ml` (`lower_nongen`).
  - Next Rust refs: `compiler-rust/src/types/typemod.rs` item loop and module-id creation, `compiler-rust/src/types/context.rs` level/init APIs, `compiler-rust/src/ident.rs` stamp generation.
- [ ] **12C. Apply `Mtype.lower_nongen` at module insertion after stamp/init_def alignment (NEW)** — with `init_def/current_stamp` now OCaml-aligned and still parity-neutral at **589/657**, module declaration paths still use `force_generalize_module_sig_values` instead of `lower_nongen (binding_time id - 1)` and likely miss OCaml’s selective non-generic lowering behavior.
  - Evidence (2026-02-24): after keeping the 12B timeline-alignment patch, `LetUnwrap` remained **0/1** and full deterministic parity remained **589/657**, so timing alignment alone does not move module-signature drift.
  - Next OCaml refs: `compiler/ml/typemod.ml` (`Pstr_module` `Mtype.lower_nongen (Ident.binding_time id - 1) md.md_type`) and `compiler/ml/mtype.ml` (`lower_nongen` traversal rules).
  - Next Rust refs: `compiler-rust/src/types/typemod.rs` `Pstr_module`/`Pstr_recmodule` module-env insertion points and `compiler-rust/src/types/ctype.rs` current force-generalization path.
- [ ] **13. GADT equation support** — gadt_equations, with_gadt_mode, add_gadt_equation, is_newtype_path. Complex. (650→651, test: js_json_test.res)
- [ ] **13A. Validate `copy_case_type` local-abstract `Tconstr` materialization before adding GADT equations (NEW)** — guidance says this path must keep locally abstract/newtype constructors as `Tconstr` (not fresh `Tvar`), but the isolated port was parity-neutral on the current snapshot.
  - 2026-02-24 attempt: in `compiler-rust/src/types/typecore.rs::copy_case_type`, removed the local-abstract/unresolved-nullary branch that rewrites `TypeDesc::Tconstr` to fresh `Tvar`, keeping all constructors as copied `Tconstr` nodes.
  - OCaml refs read: `compiler/ml/typecore.ml` (`type_cases` branch-local pattern typing flow), `compiler/ml/ctype.ml` (`unify`/`expand_head` expectations around constructor identity), and `compiler/ml/typetexp.ml` locally-abstract type handling notes from guidance.
  - Targeted check: `timeout 300 ./scripts/test_typedtree_parity.sh set_gen` stayed **0/1** with unchanged hunk count (**82**).
  - Deterministic full parity delta: **589/657 → 589/657** (parity failures **61 → 61**, Rust compile coverage **650/657 → 650/657**). Reverted.
  - Next step: implement the missing ctype-side GADT equation plumbing (`UnifyState` equation store + equation-aware unification mode) before retrying this constructor-materialization change in isolation.
- [x] **14. Per-case pattern generalization in type_case_impl** — begin_def/end_def/generalize around pattern typing. Replaces fix 9. (644→645)
  - 2026-02-24 fix: updated `compiler-rust/src/types/typecore.rs::type_case_impl` to align with OCaml `type_cases` pattern phase:
    - instantiate scrutinee type per case before `type_pattern`,
    - wrap pattern typing in `begin_def()` / `end_def()`,
    - generalize all typed subpatterns via `iter_typed_pattern`.
  - OCaml refs read: `compiler/ml/typecore.ml` `type_cases` (~3909-4062), especially per-case `instance ?partial env ty_arg` and post-pattern `end_def` + `iter_pattern ... generalize`.
  - Deterministic full parity: **643/657 → 648/657** (parity failures **14 → 9**), compile parity stayed **657/657**.
  - Remaining failing modules after this fix: `bs_ignore_test`, `defunctor_make_test`, `flexible_array_test`, `fun_pattern_match`, `rbset`, `test_set`, `ticker`, `topsort_test`, `unboxed_use_case`.
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
- [x] **15. begin_def/generalize/instance in type_function** — Same as 14 for type_function. Needs update_level_expand Pident guard (committed). (653→654, test: ticker.res)
  - 2026-02-24 fix: updated `compiler-rust/src/types/typecore.rs::type_function` to mirror OCaml `type_cases`-style parameter flow:
    - `instance()` on `param_ty` before `type_pattern`,
    - `begin_def()` / `end_def()` around `type_pattern`,
    - `iter_typed_pattern(... generalize)` on the typed parameter,
    - `instance()` for pattern-bound value types before inserting into `body_env`.
  - OCaml refs read: `compiler/ml/typecore.ml` `type_function` (~3262-3321), `type_cases` (~3906-4065), and `add_pattern_variables` (~1742-1767).
  - Deterministic full parity: **628/657 → 652/657** (parity failures **29 → 5**), compile parity stayed **657/657**.
  - Deterministic remaining failure modules: `LetUnwrap`, `fun_pattern_match`, `miss_colon_test`, `polymorphism_test`, `rbset`.
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
- [ ] **16. Stack-based cycle detection — TRY LAST** — On old branch: +16 (613→629). Current branch: 610→220 REGRESSION. Only after all above fixes.

**Partial fixes:**
- [x] **P1. Qualified label lookup last-defined** — Return last match for ambiguous labels. (630→631, test: Stdlib_Intl_DateTimeFormatTest.res)
  - 2026-02-24 fix: added module-qualified label lookup (`lookup_label_by_lid`) in `compiler-rust/src/types/typecore.rs` and threaded it through:
    - `type_pattern_record`
    - `type_record` explicit field disambiguation
    - `type_field`
    - `type_setfield`
  - 2026-02-24 follow-up: extended `compiler-rust/src/types/ctype.rs::remap_label_type_to_params` to remap `Tpoly` body vars to declaration `type_params` when labels come from module signatures (so `instance_label` shares `lbl_arg`/`lbl_res` params in this path).
  - OCaml refs read: `compiler/ml/typecore.ml` (`NameChoice.disambiguate`, `disambiguate_record_elem_list`, `type_record_elem_list`, `type_label_access`, `type_label_exp`).
  - Deterministic full parity: **630/657 → 653/657** (parity failures **27 → 4**), compile parity stayed **657/657**.
  - Deterministic remaining failure modules: `fun_pattern_match`, `gpr_4274_test`, `miss_colon_test`, `test_bs_this`.
  - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
- [ ] **P2. Generalize local Pdot expansion guard** — Extend from `.t`/`.cmp` to ALL nullary Pdot with local roots. (649→650, test: topsort_test.res)
  - 2026-02-24 attempt: generalized `update_level_expand` guard in `ctype.rs` to preserve all nullary local `Pdot` aliases before expansion. Deterministic full parity stayed **478/657 → 478/657** (179 failures); targeted `topsort_test` remained **0/1**. Reverted.
  - 2026-02-24 retry: broadened `update_level_expand` preservation from local `.t`/`.cmp` only to any local nullary `Pdot` alias in `compiler-rust/src/types/ctype.rs` (OCaml refs: `compiler/ml/ctype.ml` `update_level` around lines ~652-706, `get_level`/`Path.binding_time` flow). Reverted after no targeted improvement.
  - Targeted parity after patch: `timeout 300 ./scripts/test_typedtree_parity.sh topsort_test` stayed **0/1** and `timeout 300 ./scripts/test_typedtree_parity.sh variant` stayed **0/1** with unchanged path drift (`String_set.value -> string`, `M.t -> Path.t`).
  - Full parity runs in this snapshot are currently non-deterministic due recurring Rust sexp stack-overflow during `rescript build --dump-typed-sexp --rust` (observed outputs span **636/657**, **633/657**, **641/657**, and false **657/657** in overflowed runs). Treat overflowed runs as invalid for parity deltas.
- [ ] **P2A. Verify local-root detection for `update_level_expand` guard uses OCaml-equivalent binding-time semantics (NEW)** — The broadened nullary-`Pdot` guard was parity-neutral, so local-root classification (`is_local_path` stamp-based) may be missing aliases like `String_set.value`/`M.t`.
  - Evidence (2026-02-24): generalized guard patch in `ctype.rs` produced no change in `topsort_test` or `variant`; both diffs still show alias expansion to concrete paths.
  - Next OCaml refs: `compiler/ml/ctype.ml` `get_level`, `Path.binding_time`, `update_level` abbreviation expansion branch.
  - Next Rust refs: `compiler-rust/src/types/ctype.rs` `is_local_path`, `path_binding_time`, `update_level_expand`, and local alias stamping in `typemod`/`typecore` path construction.
- [ ] **P2B. Prove whether `String_set.value -> string` collapse happens outside `update_level_expand` (NEW)** — two new `update_level_expand` guard variants were parity-neutral on the current deterministic baseline, so the path collapse likely occurs in a different expansion/rewrite path.
  - 2026-02-24 attempts (reverted):
    - Guard variant 1: preserve all nullary local `Pdot` aliases using `Path.binding_time > 0`.
    - Guard variant 2: env-aware local-root fallback (`Env.find_module_with_id`) plus preserve all nullary `Pdot`.
  - OCaml refs read for this iteration:
    - `compiler/ml/ctype.ml` (`get_level`, `update_level`, especially `Tconstr` expansion branch around lines ~652-706).
    - `compiler/ml/path.ml` / `Path.binding_time` behavior (mirrored by Rust `Path::binding_time`).
  - Evidence:
    - `timeout 300 ./scripts/test_typedtree_parity.sh topsort_test` stayed `0/1` with unchanged `String_set.value -> string` and `String_set.t -> <cycle>` drift (`98` hunks).
    - Deterministic full parity stayed **589/657 → 589/657** (failures **61 → 61**, compile parity **650/657 → 650/657**).
    - Parser/binary guard: `timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40` ended with `SUCCESS: All 3532 files have full parity!`.
  - Next step:
    - Trace where these aliases collapse before sexp emission by instrumenting `expand_head`/`try_expand_head` callers and path-rewrite entry points (`substitute_type_paths_in_sig`, declaration remap) for `topsort_test`/`string_set`, then map first mutation site against OCaml flow.
- [ ] **P2C. Validate pre-expansion nullary local-`Pdot` skip in `update_level_expand` is sufficient (NEW)** — an OCaml-shaped early skip for all local nullary `Pdot` aliases was parity-neutral, so `String_set.value -> string` likely collapses in a later expansion/rewrite path.
  - 2026-02-24 attempt (reverted): patched `compiler-rust/src/types/ctype.rs::update_level_expand` to skip `try_expand_head` for all `Tconstr(Path::Pdot(local_root, _, _), args=[])` and removed the older `.t`/`.cmp` post-expansion special-case guard.
  - OCaml refs read:
    - `compiler/ml/ctype.ml` (`get_level`, `update_level`, especially the `Tconstr` expansion branches around lines ~652-706).
  - Evidence:
    - `timeout 300 ./scripts/test_typedtree_parity.sh topsort_test` stayed **0/1** with unchanged `String_set.value -> string` drift (`98` hunks).
    - Deterministic full parity stayed **589/657 → 589/657** (parity failures **61 → 61**, compile parity **650/657 → 650/657**).
    - Filtered `string_set` remains non-actionable in this harness (`Set_gen` gets filtered out, module-not-found), so `topsort_test` remains the stable probe.
    - Parser/binary guard stayed green: `timeout 300 ./scripts/test_parser_ast_parity.sh` ended with `SUCCESS: All 3532 files have full parity!`.
  - Next step:
    - Trace first mutation site for `String_set.value`/`String_set.t` outside `update_level_expand` by instrumenting `expand_head`/`try_expand_head` callers and path substitution paths (`substitute_type_paths_in_sig`, declaration remap), then match against OCaml `update_level` call flow.

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
