# Ralph TODO: Raw Lambda Parity

**Last Updated:** 2026-04-11
**Status:** 648/657 (98.6%), 7 failures, 14 hunks

## Goal

Achieve **100% unoptimized lambda parity** between the Rust compiler and the OCaml reference implementation using:

```bash
CANONICAL_STAMPS=1 ./scripts/test_lambda_parity.sh --raw
```

## Current Baseline

- OCaml compile coverage: **657/657**
- Rust compile coverage: **655/657** on the 16-way authoritative run
- Unoptimized lambda parity: **648/657**
- Parity hunks: **14**
- Canonicalization: per-function stamp/exit reset (`scripts/canonicalize_lambda_stamps.py`)
- Focused raw runs for `Import.res` and `global_module_alias_test.res` both pass; the
  full 16-way baseline still times those two files out intermittently.

## Working Rules

1. **Read the OCaml source first.** Do not invent raw-lambda behavior from the diff output.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Use hunk count as a navigation signal.** File count alone hides structural progress.
5. **Log in BOTH compilers to compare behavior.** Add eprintln in Rust, Printf.eprintf in OCaml.
6. **The typed trees are identical.** ALL remaining differences are in the lambda conversion stage.

## Remaining 7 Failures by Category

### Module coercion / alias resolution (4 files)
coercion_module_alias_test(7), derive_projector_test(1), pr6726(1), recmodule(1)

**Issues:**
- `coercion_module_alias_test` is the remaining direct module-coercion diff after fixing
  implicit structure signature simplification and package arg-module extraction
- `pr6726` still resolves through the wrong alias/runtime slot path
- `derive_projector_test` still carries extra include/signature structure from deriving
- `recmodule` still needs the OCaml recursive module init/runtime shape

### Dict pattern compilation (2 files)
json_decorders(1), stdlib_Stdlib_DictTests(1)

**Issue:** OCaml's Dict path mutates `lbl_all` with synthetic per-field labels and only strips
`Some(...)` wrappers in the narrow `Parmatch.all_record_args` cases. Rust now matches that
for the resolved Dict files, but two Dict-focused lambda diffs remain.

### Other (1 file)
bs_poly_map_test(2)

**Issue:** remaining library-specific lambda shape difference outside the main
module/Dict clusters

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

### nonrecursive irrefutable lets now use Matching.for_let
OCaml's `transl_let` always routes non-simple nonrecursive bindings through
`Matching.for_let`, even when the pattern is irrefutable. Rust was still sending
irrefutable tuple/record patterns through `raw_simple_for_let`, which eagerly bound fields
instead of letting the matching compiler/lower_bind path place them where OCaml does.

The Rust converter now uses `full_matching::for_let` for those irrefutable non-simple
bindings too.

**Result:** full raw baseline improves to **629/657** with **69** hunks. `inline_map2_test`
now reaches full raw parity.

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

### 2026-04-11 (Dict synthetic labels + narrow optional wrapper stripping)

OCaml's Dict patterns do two things that Rust still wasn't matching:

1. `typecore.ml` does not just rename `dictValuesType`; it synthesizes a fresh label for each
   Dict field lookup, preserving the hidden `dictValuesType/0` slot and growing `lbl_all`
   with per-field positions (`.../1`, `.../2`, etc.).
2. `parmatch.ml` only strips `Some(...)` wrappers for optional record labels in narrow cases:
   `Some(<constant>)`, or `Some(<constructor>)` when the untagged payload block cannot be
   `undefined`.

Rust now:
- caches synthetic Dict pattern labels in `TypeContext`, seeded with hidden
  `dictValuesType/0`
- materializes those synthetic labels during Dict pattern typing instead of only renaming the
  magic field
- resolves Dict record labels from that synthetic cache in raw matching / conversion so
  `lbl_all`-style expansion matches OCaml's field positions
- ports the narrow `Parmatch.all_record_args` optional-wrapper stripping rule for Dict fields
- names match temporaries through the typed-context identifier source in raw matching, aligning
  the remaining Dict record/constructor binder shapes with OCaml

**Result:** full authoritative raw baseline improves to **648/657** with **14** hunks.
Resolved Dict files: `DictInternalRepresentation`, `DictPatternMatchingOptimization`,
`pattern_match_json`, and `stdlib/Stdlib_JsonTests`. The remaining Dict cluster is down to
`json_decorders` and `stdlib/Stdlib_DictTests`.

### 2026-04-11 (module type simplification for implicit structure constraints)

OCaml `typemod.ml` wraps `Pmod_structure` results in an implicit `Tmod_constraint` when
`simplify_signature sg` removes duplicate value entries. Rust was only approximating that
decision from structure bindings and then exposing the inner unsimplified structure
signature again when later module-path and package code extracted semantic module types.

Rust now:
- uses `simplify_signature(structure.str_type)` directly to decide when a structure needs
  an implicit constraint
- treats `Tmod_constraint(..., Tmodtype_implicit)` over a structure as exposing the
  simplified structure signature during module-type extraction
- restores the OCaml `type_package` data flow by preferring the typed module expression's
  extracted module type before falling back to parsed semantic lookup
- short-circuits inclusion/coercion checks on exact-equal module declarations and module
  type declarations, backed by `PartialEq/Eq` derives on declaration types
- removes module aliases under `module type of` the same way OCaml's `Mtype.remove_aliases`
  does for this path

**Result:** full authoritative raw baseline improves to **644/657** with **19** hunks.
`Import.res`, `DynamicImportModuleWithAlias.res`, `global_module_alias_test.res`, and the
first-class module pack crash cluster now pass focused raw parity. The only remaining
direct module-coercion regression is `coercion_module_alias_test`.

### 2026-04-11 (thread real pattern locations through raw matching)

OCaml's `do_compile_matching` and tuple/record divider helpers thread `pat.pat_loc`
through the raw matcher (`combine_constant`, `combine_constructor`, `combine_array`,
`combine_variant`, `make_tuple_matching`, `make_record_matching`). Rust was still using
`Location::none()` in those paths, and `call_switcher` / clustered `Lswitch` building was
dropping the caller location too. That made `Lambda.make_key` collapse branch-local switch
actions that OCaml keeps distinct by location, which is why `mario_game` still shared the
wrong nested catch/switch handler even after the optional-shape fixes.

Rust now:
- threads `ParseArena` through the raw matching compiler so pattern-driven switch builders
  use `arena.to_location(pat.pat_loc)` where OCaml uses `pat.pat_loc`
- uses real pattern locations for tuple and record projection helpers instead of ghost locs
- carries `Lswitch` locations in raw lambda, preserves them in `make_key`, and threads the
  switcher API/builders with the caller location instead of hardcoding `Location::none()`

**Result:** full raw baseline improves to **640/657** with **29** hunks. `mario_game`
now reaches full parity, removing the final failure from the inner matching cluster.

### 2026-04-11 (pre-register local module types for optional-shape checks)

`mario_game` still had two `makeblock some` vs `makeblock some_not_nested` mismatches for
`Actors.dir_1d`, even though OCaml boxes those payloads as non-nested options. Direct
`-drawlambda` tracing showed the raw-lambda optional-shape path was consulting envs that
could not yet resolve local qualified module types like `Actors.dir_1d` / `Actors.dir_2d`
at those sites, even though the same declarations became available later in the compile.

Rust now:
- pre-registers local module type declarations from `structure.str_type` into `TypeContext`
  before raw-lambda conversion starts
- threads the enclosing constructor expression env into raw constructor optional-shape checks
- uses the existing no-env fast path when a typed env still is not available
- lets `typeopt` consult `lookup_type_decl_for_path_pub` before falling back to cached/name
  lookups

**Result:** full raw baseline stays **639/657** with **31** hunks. `mario_game` drops from
**4** hunks to **2**, removing the local-module optional-boxing mismatches. The remaining
`mario_game` diff is now only the shared catch/switch handler shape.

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

### 2026-04-11 (irrefutable let patterns through Matching.for_let)

The remaining `test_set` normalized diff showed Rust eagerly binding tuple fields that OCaml
delayed until they were actually needed. The cause was in `convert_let_with_body_raw`:
Rust still used `raw_simple_for_let` for irrefutable non-simple bindings, while OCaml's
`transl_let` always calls `Matching.for_let` for every non-simple nonrecursive binding.

Routing those irrefutable bindings through `full_matching::for_let` fixes the lower-bind
placement for that path.

**Baseline after change:** **628/657 -> 629/657**, **79 -> 69 hunks**.

**Takeaway:** one more non-matching shortcut has been removed. The remaining cluster is
now concentrated in deeper inner matching differences plus the module/dict/JSX buckets.

### 2026-04-11 (approx_present globals no longer block lower_bind)

The remaining `test_set` raw diff showed Rust still hoisting tuple-field aliases out of
branches where OCaml keeps them local. Tracing `lower_bind` on `test_set` showed the
unexpected blocker: Rust `approx_present` treated `LglobalModule` as `_ -> true`, so a
branch like `raise (makeblock ext (global Assert_failure) ...)` looked as if it used the
bound variable. OCaml represents that same global reference as `Lprim (Pgetglobal ...)`,
which `approx_present` naturally treats as argument-free and therefore absent.

Updating Rust `approx_present` to treat `LglobalModule` like OCaml's `Pgetglobal` restores
the expected `(false, true, false)` / `(false, false, true)` lowering behavior.

**Baseline after change:** **629/657 -> 632/657**, **69 -> 47 hunks**.

**Takeaway:** the `lower_bind` placement logic now matches OCaml for global-reference
branches too. This clears `test_set`, `set_gen`, and `gpr_1150`, and leaves a smaller
inner-matching cluster centered on the remaining polymorphic-variant and branch-shape
cases.

### 2026-04-11 (polyvariant action grouping uses make_key normalization)

Rust's polyvariant helper `convert_polyvar_list` was grouping actions with
`format!("{:?}", act)` instead of the same `make_key`-normalized comparison OCaml gets
through `Switcher.test_sequence` / `as_interval`. That prevented alpha-equivalent actions
with different local ids from being merged, which forced extra tag tests for
`#...myvariant`-style matches.

Switching the grouping key to `make_key_string` aligns the helper with OCaml's normalized
action equality.

**Baseline after change:** **632/657 -> 634/657**, **47 -> 43 hunks**.

**Takeaway:** the remaining matching files are no longer in the polyvariant action-sharing
bucket. The next matching work should stay focused on the remaining branch/catch shaping in
`mario_game`, `UntaggedVariants`, and inline-record-related paths.

### 2026-04-11 (shared-action handler extraction skips identity wrappers)

Rust `share_actions_tree` was reconstructing handler bodies by applying each delayed wrapper
to a dummy `0` lambda. When the wrapper was actually the identity function
(`make_catch_delayed` on an action that was already a simple exit), that dummy became a real
handler body, producing bogus inner catches like `with (1) 0`, `with (1) 0n`, or
`with (1) 0a`.

The fix is to probe wrappers with `make_exit(i)` instead and skip them entirely when the
wrapper is identity. That matches OCaml's `handle_shared`, which never materializes a fake
handler for already-simple exits.

**Baseline after change:** **634/657 -> 636/657**, **43 -> 37 hunks**.

**Takeaway:** the remaining matching files no longer include the shared-action `with (...) 0`
artifact. The next matching work is concentrated in `mario_game`,
`inline_record_test`, `exception_raise_test`, and the remaining bigint ordering issue.

### 2026-04-11 (bigint constant ordering uses numeric compare)

Rust `const_compare` was ordering bigint constants by sign plus raw digit-string
lexicographic comparison. OCaml calls `Bigint_utils.compare`, so negative values like
`-2n` and `-1n` sort by numeric magnitude, not by plain string order.

Switching Rust bigint constant ordering to a numeric sign/length/lexicographic compare
aligns `sort_lambda_list` and the generated test-sequence order with OCaml.

**Baseline after change:** **636/657 -> 637/657**, **37 -> 35 hunks**.

**Takeaway:** the remaining raw-matching bucket is now just `mario_game`,
`inline_record_test`, and `exception_raise_test`.

### 2026-04-11 (extension inline-record labels resolve from constructor paths)

Rust `resolve_labels_from_type` only reconstructed inline-record label sets from
parent-type `Pdot` paths. Exception/extension inline records use the constructor path
itself (for example `A0`) and keep their full field set in `cstr_inlined`, so Rust was
falling back to just the explicitly mentioned labels and dropping OCaml's unused field
binds in raw matching.

Teaching raw matching to recover extension inline-record labels from the matching
constructor path aligns it with OCaml's `lbl_all`-driven record expansion for
exception/extension payloads.

**Baseline after change:** **637/657 -> 638/657**, **35 -> 34 hunks**.

**Takeaway:** `inline_record_test` is now clean. The remaining matching bucket is reduced
to `mario_game` plus the residual `exception_raise_test` inner default/handler shape.

### 2026-04-11 (cross-shape may_compat now matches OCaml)

Rust `may_compat` had a catch-all `_ => true` branch, so constructor-vs-tuple,
constructor-vs-record, tuple-vs-array, and other cross-shape pairs were treated as
potentially compatible. OCaml's `Parmatch.Compat.compat` returns `false` for those
unhandled shape combinations.

Switching Rust to the OCaml behavior removes impossible default-chain leakage between
different pattern shapes. In practice that cleaned the residual `exception_raise_test`
catch/default mismatch without widening the remaining raw-lambda baseline.

**Baseline after change:** **638/657 -> 639/657**, **34 -> 33 hunks**.

**Takeaway:** the matching bucket is now down to `mario_game` only.

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
