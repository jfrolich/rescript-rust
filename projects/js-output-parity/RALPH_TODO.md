# Ralph TODO: JS Output Parity

**Last Updated:** 2026-04-13
**Status:** 235 / 657 JS snapshots passing, 0 compile errors, 422 output diffs

## Goal

Achieve **100% byte-for-byte emitted JavaScript parity** between the Rust
compiler and the OCaml reference implementation using:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

Execution order and phase gates live in `PLAN.md`.

## Upstream Status

For this project, the upstream parity stages are already complete:

- typedtree parity: **657/657**
- raw lambda parity: **657/657**
- optimized lambda parity: **657/657**

There are no open issues there. The remaining parity work is downstream in the
JS backend only.

## Current Baseline

Latest authoritative wrapper run on **2026-04-13** using:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

reported:

- JS snapshot parity: **235 / 657**
- Compile errors: **0**
- Output diffs: **422**
- Diff artifacts written under `temp/rust-parity/diffs`
- Spice PPX guard: **skipped by harness in this environment** because `SPICE_PPX` was not found at the configured path

Interpretation:

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed effect-continuation slice in
  `compiler/core/lam_compile.ml`
- After reading OCaml's `Lsequence` lowering there, the Rust backend in
  `compiler-rust/src/lambda/compile.rs` now compiles the first operand of
  `Lambda::Lsequence` through the same effect-position path instead of the
  generic value-expression path
- The new `compile_effect_output` helper preserves OCaml's
  `EffectCall Not_tail` behavior for sequence prefixes, nested effect-position
  `if` lowering, switches, static catches, and lets, which removes synthetic
  result temporaries from effect-only control-flow
- Added focused regression coverage in
  `lambda::compile::tests::sequence_prefix_ifs_use_effect_lowering_without_result_temps`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib sequence_prefix_ifs_use_effect_lowering_without_result_temps -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_2682_test.res -o /tmp/gpr_2682_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/gpr_2682_test.res` no longer differs on the old
  `let ifres; if (...) { ... } else { throw ...; ifres = undefined; }`
  assert scaffold; the remaining drift in that file is down to separate raw-JS
  formatting details
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same backend change
- Across cached diff artifacts, files whose diffs still contain `let ifres`
  dropped from **37** to **27** in this iteration
- The authoritative JS snapshot baseline now reports **235 / 657** passing,
  **0** compile errors, and **422** output diffs; this is a net **+1**
  passing snapshot and **-1** output diff from the previously recorded
  **234 / 657**, **0** compile errors, **423** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed printer slice in
  `compiler/core/js_dump.ml`
- After reading the OCaml `Array`, `Object`, and `Caml_block` constructor
  branches there, the Rust printer in `compiler-rust/src/js_ir/printer.rs`
  now follows the same vertical-layout rules more closely:
  non-singleton JS arrays print with one item per line, cons / constructor /
  polyvariant object blocks print through the shared object-literal path, and
  numeric-field record blocks that lower to arrays now use the same multiline
  array layout too
- This removes the old compact-array / compact-record / compact-constructor
  byte drift that was still visible after the earlier list-comment fix
- Added focused regression coverage in:
  `js_ir::printer::tests::test_print_array`,
  `test_print_cons_constructor_as_hd_tl_object`,
  `test_print_non_cons_constructor_keeps_tag_object_shape`, and
  `test_print_numeric_named_record_as_array`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_array -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_cons_constructor_as_hd_tl_object -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_non_cons_constructor_keeps_tag_object_shape -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_numeric_named_record_as_array -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact harness-mode AST repro for `tests/tests/src/Import.res` from
    `tests/tests/lib/bs` using the checked-in `compiler-args`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/Import.res` no longer differs on the nested list literal or
  multiline array-return shape; its remaining drift is now only the later
  statement-order issue around `each` / `each2`
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same printer change
- The authoritative JS snapshot baseline now reports **234 / 657** passing,
  **0** compile errors, and **423** output diffs; this is a net **+39**
  passing snapshots and **-39** output diffs from the previously recorded
  **195 / 657**, **0** compile errors, **462** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed constant-lowering / dumper
  metadata slice in `compiler/core/lam_compile_const.ml` and
  `compiler/core/js_dump.ml`
- After reading those OCaml files, the Rust backend now preserves
  `Lam_constant.string_of_pointer_info` comments on numeric constants instead of
  dropping them in `compiler-rust/src/lambda/compile.rs`
- This specifically restores the `/* [] */0` empty-list marker on the JS IR
  node for constructor-backed numeric zero, which is how OCaml keeps list-tail
  and empty-list literals annotated all the way into `js_dump.ml`
- The same Rust-side helper now preserves other pointer-info comments like
  `assert_false` and named constructor/polyvariant comments when they lower to
  numeric literals instead of strings
- Added focused regression coverage in
  `lambda::compile::tests::compile_constant_empty_list_keeps_numeric_zero_with_pointer_comment`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_constant_empty_list_keeps_numeric_zero_with_pointer_comment -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/Import.res -o /tmp/Import.mjs`
  - exact harness-mode AST repro for `tests/tests/src/belt_list_test.res` from
    `tests/tests/lib/bs` using the checked-in `compiler-args`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/Import.res` now preserves `/* [] */0` in the generated JS;
  its remaining drift is the separate statement-order / compact-array /
  compact-record printer cluster, not missing constant comments
- The broader list-heavy harness repro for `tests/tests/src/belt_list_test.res`
  now also preserves `/* [] */0` throughout the emitted output
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same change
- Across cached diff artifacts, files whose diffs still contain missing
  `/* [] */0` markers dropped from **62** to **60** in this iteration
- The authoritative JS snapshot baseline now reports **195 / 657** passing,
  **0** compile errors, and **462** output diffs; this is a net **+1** passing
  snapshot and **-1** output diff from the freshly re-baselined
  **194 / 657**, **0** compile errors, **463** output diffs that preceded this
  fix
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  but this iteration isolated and fixed one OCaml-backed nontermination guard
  in `compiler/core/lam_pass_remove_alias.ml`
- After reading that OCaml pass, the Rust JS-backend simplifier now follows the
  same recursive-apply avoidance direction more closely:
  `compiler-rust/src/lambda/simplify.rs` now refuses to re-inline a named
  function when the argument reaches that same function through the
  simplifier-visible alias/block environment, not just when the raw argument
  syntax directly mentions the callee
- This specifically fixes the hidden `g(A(g))` / `let x = A(g) in g x`
  re-inline loop that was overflowing the Rust compiler stack during
  `src/a_recursive_type.res`
- Added focused regression coverage in
  `lambda::simplify::tests::does_not_reinline_named_function_through_block_aliases`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release does_not_reinline_named_function_through_block_aliases -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/a_recursive_type.res -o /tmp/a_recursive_type.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - exact harness-mode AST repro for `tests/tests/src/Import.res` from
    `tests/tests/lib/bs` using the checked-in `compiler-args`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/a_recursive_type.res` no longer aborts with a Rust stack
  overflow and now emits regular JS output under timeout; its remaining drift is
  ordinary backend parity work around recursive-record lowering and export
  coercion (`let xx = {}; xx.xx = xx;` vs `let xx; xx = {xx: xx};`, plus extra
  exports)
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same simplifier change
- The authoritative wrapper numbers remain **194 / 657** passing, **1** compile
  error, and **462** output diffs, but the lone compile-error label moved off
  `src/a_recursive_type.res`
- The current remaining harness artifact is
  `temp/rust-parity/diffs/js_src_Import.res.err`; however, an exact AST-mode
  repro for `Import.res` now exits successfully and produces a normal JS diff,
  so the next iteration should treat `Import.res` as a downstream output-shape
  issue or a harness/output-path classification problem rather than another
  backend crash
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration verified one OCaml-backed alias-cleanup / JS-pass slice in
  `compiler/core/lam_pass_lets_dce.ml` and
  `compiler/core/js_pass_flatten_and_mark_dead.ml`
- After reading those OCaml passes, the Rust JS backend now matches OCaml more
  closely in two places:
  `compiler-rust/src/lambda/simplify.rs` now inlines non-exported single-use,
  uncaptured `Alias` lets on the JS backend path, and
  `compiler-rust/src/lambda/compile.rs` now allocates
  `flatten_and_mark_dead` helper bindings from a fresh `IdGenerator` seeded
  above the program's current max stamp instead of `Ident::create_local`
- The simplify port removes the stale `let set = match[1]; let get = match[0];`
  shape before JS lowering for the `React.useState`/module-block cluster,
  which is the same alias-cleanup direction OCaml takes before
  `js_pass_flatten_and_mark_dead`
- The JS-pass identifier fix removes stamp collisions between newly introduced
  helper bindings like `StandardNotation_get` and pre-existing exported module
  bindings, which was the direct cause of the wrong
  `let StandardNotation_get = {...}; export { StandardNotation_get as StandardNotation }`
  corruption seen during focused repro
- Added focused regression coverage in
  `lambda::simplify::tests::inlines_single_use_alias_field_reads_into_module_blocks`
  and
  `lambda::simplify::tests::does_not_inline_captured_single_use_aliases`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release inlines_single_use_alias_field_reads_into_module_blocks`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release does_not_inline_captured_single_use_aliases`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UncurriedExternals.res -o /tmp/UncurriedExternals.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/UncurriedExternals.res` now has the correct
  `StandardNotation` module binding/export shape again; the remaining drift in
  that file is down to the known `let <ident> = this ;` spacing detail
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same backend changes
- The authoritative harness now reports one remaining compile-failure artifact:
  `temp/rust-parity/diffs/js_src_a_recursive_type.res.err` records a Rust
  stack overflow for `src/a_recursive_type.res`
- The authoritative JS snapshot baseline now reports **194 / 657** passing,
  **1** compile error, and **462** output diffs after this OCaml-aligned
  alias-cleanup / JS-pass identifier fix; this is a net **+6** passing
  snapshots over the previously recorded baseline
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration verified one OCaml-backed `Pjs_fn_make`/method-function
  slice without changing the authoritative wrapper baseline yet
- After reading `compiler/core/lam_compile.ml`,
  `compiler/core/lam_eta_conversion.ml`, and `compiler/core/js_dump.ml`,
  the Rust backend now moves direct `PjsFnMake` arity adjustment into
  `compiler-rust/src/lambda/simplify.rs`, matching the OCaml stage boundary
  more closely instead of doing the adjustment late during JS IR lowering in
  `compiler-rust/src/lambda/compile.rs`
- `compiler-rust/src/js_ir/printer.rs` now matches OCaml method-function
  dumping more closely for this slice:
  method expressions omit the synthetic leading `this` parameter from the
  printed formal argument list, emit a `let <ident> = this;` binding only when
  that synthetic parameter is actually used, and print top-level method-valued
  bindings as named `function ...` declarations
- The printer follow-up in the same file also removes the transient
  `=>  {` arrow-body spacing regression introduced while wiring the method
  body printer, restoring the wrapper baseline after the backend change
- Added focused regression coverage in:
  `lambda::simplify::tests::adjusts_direct_pjs_fn_make_callbacks_to_requested_arity_during_simplify`,
  `beta_reduces_downarity_pjs_fn_make_calls_before_js_lowering`,
  `beta_reduces_fully_applied_returned_pjs_fn_make_wrappers`,
  plus the existing method printer tests in `js_ir::printer`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release pjs_fn_make -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release method_function -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release function_expression_preserves_raw_directive -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UncurriedExternals.res -o /tmp/UncurriedExternals.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/arity_deopt.res` no longer shows the old extra
  callback-wrapper drift from late `PjsFnMake` lowering; after the printer
  spacing fix it is back to the same global baseline accounting as before
- `tests/tests/src/UncurriedExternals.res` now matches the OCaml callback shape
  more closely in the `@this` / direct-callback cluster; the remaining drift in
  that file is the `let <ident> = this ;` spacing detail plus the separate
  `React.useState` destructuring/binding-order issue
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same change
- The authoritative JS snapshot baseline remains **188 / 657** passing,
  **0** compile errors, and **469** output diffs after this OCaml-aligned
  backend/printer cleanup; this is a net **0** from the previously recorded
  baseline, but the late-wrapper drift in this cluster is no longer the
  active blocker
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-aligned eta-wrapper slice on the JS
  backend path: value-level functions that do nothing except forward their
  parameters into the same `Primitive_*` runtime compare/equal/order/min/max
  helpers OCaml later emits as direct member aliases
- After reading the OCaml backend path around
  `compiler/core/lam_compile_primitive.ml`,
  `compiler/core/lam_compile.ml`,
  `compiler/core/lam.ml`, and
  `compiler/core/lam_eta_conversion.ml`, the Rust fix landed in
  `compiler-rust/src/lambda/compile.rs`:
  eta-wrapped runtime-helper functions now lower directly to the corresponding
  qualified runtime member expression instead of always materializing a JS
  wrapper function
- The new Rust-side aliasing covers the same runtime-helper family visible in
  the OCaml snapshots for value-level compare helpers:
  `Primitive_object.{compare,equal,notequal,lessthan,lessequal,greaterthan,greaterequal}`,
  `Primitive_bool.{compare,min,max}`,
  `Primitive_int.{compare,min,max}`,
  `Primitive_float.{compare,min,max}`,
  `Primitive_bigint.{compare,min,max}`, and
  `Primitive_string.{compare,min,max}`
- Added focused regression coverage in:
  `lambda::compile::tests::compile_eta_wrapped_object_compare_function_aliases_runtime_member`,
  `compile_eta_wrapped_float_compare_function_aliases_runtime_member`, and
  `compile_eta_wrapped_float_equality_stays_as_function`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release eta_wrapped_ -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_obj_order_uses_primitive_object_compare -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/console_log_test.res -o /tmp/console_log_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/console_log_test.res` now matches its checked-in snapshot
  exactly again, and `tests/tests/src/ExternalShadow.res` remains an exact
  guard-file match after the same change
- The direct helper-alias drift is gone from the remaining diff artifacts:
  there are now **0** snapshot diffs left whose first mismatch is an expected
  `let ... = Primitive_*.{compare,equal,notequal,lessthan,lessequal,greaterthan,greaterequal,min,max};`
  alias replaced by a Rust wrapper function
- `tests/tests/src/float_test.res` improved materially but still fails on a
  later callback/destructuring cleanup shape around
  `[[1, 3], [2, 1], [3, 2]].map(...)`; the old top-of-file runtime-helper alias
  wrappers are gone there
- `tests/tests/src/int_map.res` also improved inside this cluster: the compare
  alias is now correct, and the remaining drift is a later temporary-binding
  shape (`let call = ...; let IntCmp = call;`) rather than missing helper
  aliasing
- The authoritative JS snapshot baseline now reports **188 / 657** passing,
  **0** compile errors, and **469** output diffs after this eta-wrapped
  runtime-helper alias port; this is a net **+3** over the previously recorded
  baseline

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed comparison/runtime-helper slice
  in `compiler/core/lam_compile_primitive.ml` plus one still-separate strict
  comparison route that is not fully wired into the emitting backend yet
- `compiler-rust/src/lambda/compile.rs` now matches the OCaml backend more
  closely for the missing primitive comparison/order/min/max families:
  `Pobjcomp`, `Pobjorder`, `Pobjmin`, `Pobjmax`, `Pboolorder`,
  `Pboolmin`, `Pboolmax`, `Pintorder`, `Pintmin`, `Pintmax`,
  `Pfloatorder`, `Pfloatmin`, `Pfloatmax`, `Pbigintorder`,
  `Pbigintmin`, `Pbigintmax`, `Pstringorder`, `Pstringmin`, and
  `Pstringmax` now lower to the corresponding `Primitive_*` runtime helpers or
  the same literal fast paths OCaml uses instead of falling through to
  `undefined`
- `compiler-rust/src/js_ir/mod.rs` now folds strict null/undefined comparisons
  against side-effect-free bool/number/typeof/function/array/caml-block
  expressions in the shared JS IR builder, matching the OCaml
  `js_exp_make.ml` nullish strict-comparison behavior closely enough for the
  backend paths that already route through this builder
- Added focused regression coverage in:
  `lambda::compile::tests::compile_int_order_uses_primitive_int_compare`,
  `compile_string_order_uses_primitive_string_compare`,
  `compile_obj_compare_against_null_uses_strict_equality`,
  `compile_obj_compare_null_against_number_literal_folds_false`,
  `compile_obj_notequal_undefined_against_number_literal_folds_true`,
  `compile_obj_order_uses_primitive_object_compare`,
  `compile_bigint_min_literals_use_conditional_fast_path`,
  `js_ir::tests::test_strict_eq_null_against_number_folds_false`,
  `test_strict_neq_undefined_against_number_folds_true`, and
  `test_strict_eq_null_against_variable_is_preserved`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release 'lambda::compile::tests::compile_int_order_uses_primitive_int_compare' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release 'lambda::compile::tests::compile_string_order_uses_primitive_string_compare' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release 'lambda::compile::tests::compile_obj_compare_against_null_uses_strict_equality' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release 'lambda::compile::tests::compile_obj_compare_null_against_number_literal_folds_false' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release 'lambda::compile::tests::compile_obj_notequal_undefined_against_number_literal_folds_true' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release 'lambda::compile::tests::compile_obj_order_uses_primitive_object_compare' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release 'lambda::compile::tests::compile_bigint_min_literals_use_conditional_fast_path' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release 'js_ir::tests::test_strict_eq_null_against_number_folds_false' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release 'js_ir::tests::test_strict_neq_undefined_against_number_folds_true' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release 'js_ir::tests::test_strict_eq_null_against_variable_is_preserved' -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - focused harness-accurate snapshot repros for
    `tests/tests/src/string_set.res`,
    `tests/tests/src/bs_min_max_test.res`, and
    `tests/tests/src/ExternalShadow.res`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/string_set.res` improved materially inside this cluster:
  the old cached baseline diff emitted `undefined | 0` in the comparator path,
  while the fresh direct repro now emits `Primitive_string.compare(...)` there
  and drops from **481** diff lines to **462** diff lines, even though the file
  still fails on broader recursive/function-shape drift
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same change
- `tests/tests/src/bs_min_max_test.res` still fails because the remaining
  `undefined !== 5` vs `true` drift is coming through a separate strict
  comparison route, which indicates a follow-up backend-routing or JS-pass
  cleanup task rather than another missing `Primitive_*` helper lowering
- The authoritative JS snapshot baseline now reports **185 / 657** passing,
  **0** compile errors, and **472** output diffs after this comparison/runtime
  helper port; this is a net **+1** over the previously recorded baseline

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  but this iteration isolated one still-missing post-lowering alias
  simplification slice that feeds the initial JS IR before any JS pass runs
- OCaml `-bs-diagnose` pass dumps for `tests/tests/src/ExternalScopeShadow.res`
  showed the correct statement order already present in
  `tests/tests/src/ExternalScopeShadow.01.initial.jsx`:
  the trailing `let MyURL;` placeholder is introduced only after
  `Lam_pass_remove_alias` collapses the export payload to
  `Const_module_alias`, so this was not a `js_pass_external_shadow`,
  `Js_shake`, or printer-ordering bug after all
- `compiler-rust/src/lambda/simplify.rs` now matches
  `compiler/core/lam_pass_remove_alias.ml` more closely on the Rust JS path for
  direct `TagInfo::ModuleExport` payloads:
  Rust now simplifies only the direct exported bindings whose current
  substitution is `Const_module_alias`, while still preserving ordinary direct
  export vars for the existing same-name export and trailing-effect coercion
  behavior
- This restores the OCaml pipeline for module-alias exports such as
  `module MyURL = URL`:
  the inert source-position alias payload now collapses to
  `Const_module_alias`, later export coercion synthesizes the fresh trailing
  export placeholder, and the final JS regains OCaml's
  `globalThis.URL.revokeObjectURL(...); ...; let MyURL;` order
- Added focused regression coverage in
  `lambda::simplify::tests::simplifies_module_alias_export_payloads_before_export_coercion`
  and reran the existing `compile_deps_program_*` export-coercion guard tests
  to confirm the narrowed module-alias rule does not perturb the previously
  verified same-name export cases
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release simplifies_module_alias_export_payloads_before_export_coercion -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_deps_program_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalScopeShadow.res -o /tmp/ExternalScopeShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/ExternalScopeShadow.res` now matches its checked-in `.mjs`
  snapshot exactly again, `tests/tests/src/ExternalShadow.res` remains an exact
  guard-file match, and the focused diff artifacts for both files are now absent
- The authoritative JS snapshot baseline now reports **184 / 657** passing,
  **0** compile errors, and **473** output diffs after this OCaml-aligned
  module-alias export simplification fix; this is a net **+4** over the
  previously recorded baseline

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration took a contained OCaml-aligned printer slice that was
  still blocking exact JS snapshots across several files
- `compiler-rust/src/js_ir/printer.rs` now matches
  `compiler/core/js_dump.ml` `Number (Float {f})` more closely by routing float
  literals through the OCaml `compiler/core/js_number.ml`
  `caml_float_literal_to_js_string` behavior instead of printing the raw parsed
  literal text unchanged
- Rust now strips OCaml-only float-literal syntax that should not survive into
  emitted JS byte-for-byte, including trailing dots and underscores on
  integral-valued float literals, and it also normalizes simple hexadecimal
  float-literal tokens like `0x10` to the decimal JS shape OCaml prints
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_number` for integral float-literal
  normalization cases: `1. -> 1`, `0012. -> 12`, `-0. -> -0`, and
  `0x10 -> 16`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_number -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/b.res -o /tmp/b.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/attr_test.res -o /tmp/attr_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/external_ppx.res -o /tmp/external_ppx.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/b.res`, `tests/tests/src/attr_test.res`,
  `tests/tests/src/external_ppx.res`, and `tests/tests/src/js_math_test.res`
  now match their checked-in snapshots exactly, while
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same printer change
- The authoritative JS snapshot baseline now reports **180 / 657** passing,
  **0** compile errors, and **477** output diffs after this OCaml-aligned
  float-literal printer port; this is a net **+5** over the previous recorded
  baseline

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  but this iteration also fixed one still-missing late-Phase-3 primitive slice
  in `compiler/core/lam_compile_primitive.ml`
- `compiler-rust/src/lambda/compile.rs` now matches the OCaml backend for
  exception primitives more closely:
  `Pcreate_extension` lowers to
  `/* @__PURE__ */Primitive_exceptions.create(...)` and `Pwrap_exn` lowers to
  `Primitive_exceptions.internalToException(...)` instead of falling through to
  `undefined`
- The same file now also matches `compiler/core/js_shake.ml` more closely on
  toplevel retention order:
  the previous Rust-only extra reverse after flattening was wrong because
  OCaml's `List.rev @@ rev_toplevel_flatten` already restores source order
- `compiler-rust/src/js_ir/printer.rs` now matches the OCaml pure-runtime-call
  byte shape more closely by printing expression comments without an extra
  space before the callee, e.g.
  `/* @__PURE__ */Primitive_exceptions.create(...)`
- Added focused regression coverage for this slice in:
  - `lambda::compile::tests::compile_create_extension_uses_primitive_exceptions_create`
  - `lambda::compile::tests::compile_wrap_exn_uses_primitive_exceptions_internal_to_exception`
  - `lambda::compile::tests::compile_deps_program_preserves_toplevel_binding_order_during_shake`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_create_extension_uses_primitive_exceptions_create -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_wrap_exn_uses_primitive_exceptions_internal_to_exception -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_deps_program_preserves_toplevel_binding_order_during_shake -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/internal_unused_test.res -o /tmp/internal_unused_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_exception_escape.res -o /tmp/test_exception_escape.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/internal_unused_test.res` now matches exactly, and
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the corrected `Js_shake` order rule
- Remaining exception-heavy files such as
  `tests/tests/src/test_exception_escape.res`,
  `tests/tests/src/exception_raise_test.res`,
  `tests/tests/src/exception_value_test.res`, and
  `tests/tests/src/js_exception_catch_test.res` still differ, but they have
  moved on from missing `Primitive_exceptions.create(...)` lowering to later
  try/catch and declaration-order shaping
- The authoritative JS snapshot baseline now reports **175 / 657** passing,
  **0** compile errors, and **482** output diffs after this OCaml-aligned
  exception-primitive plus corrected-`Js_shake` order fix; this is a net
  **+5** over the previous recorded baseline

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed on the OCaml post-lowering safe-alias
  path for module field reads instead of treating the surviving import/module
  alias temporaries as printer drift
- `compiler-rust/src/lambda/simplify.rs` now matches another slice of
  `compiler/core/lam_util.ml` `refine_let` / `is_safe_to_alias` more closely on
  the Rust JS path: module-field reads are now considered substitutable not
  just when they come from `Lglobal_module`, but also when they come from a
  local module variable (`Lvar`) like the awaited import bindings OCaml already
  aliases through
- This removes another OCaml-backed class of redundant locals before JS
  lowering, including shapes like `let each = O.forEach` inside module blocks
  and `let b = MS.forEach` before grouped tuple returns; Rust now lowers those
  through the same direct member-access shape OCaml uses
- Added focused regression coverage in
  `lambda::simplify::tests::aliases_module_field_reads_from_local_module_bindings_into_tuple_blocks`
  and reran
  `lambda::simplify::tests::refines_immediate_module_field_reads_over_awaited_imports`
  so this stays pinned to the OCaml `SafeAlias` predicate rather than a single
  snapshot file
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release module_field_reads -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/Import.res -o /tmp/Import.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/Import.res` now narrows again: the extra Rust-side alias
  locals around awaited module field reads in the grouped/module-return path are
  gone, including the old `let b = MS.forEach` helper in `f6`; the remaining
  drift in that file is now later compaction and list-formatting byte shape
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same change, which confirms this aliasing slice stays isolated from the
  already-stable external-shadow path
- The authoritative JS snapshot baseline now reports **188 / 657** passing,
  **0** compile errors, and **469** output diffs after this OCaml-aligned local
  module-field alias port; this is a net **+1** over the previous recorded
  baseline

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed on the OCaml post-lowering let
  refinement path that feeds JS IR instead of treating the surviving dynamic
  import temporaries as printer-only drift
- `compiler-rust/src/lambda/simplify.rs` now matches another slice of
  `compiler/core/lam_util.ml` `refine_let` and
  `compiler/core/lam_pass_lets_dce.ml` more closely on the Rust JS path:
  immediate let-bound uses now collapse before JS lowering for the OCaml-backed
  cases `let x = e in x`, `let x = e in prim x` (excluding block constructors),
  and `let x = e in f x` when the callee does not capture `x`
- This specifically removes the extra Rust backend temporary around awaited
  module field reads, so expressions like `let M3 = await Belt.List; M3.forEach`
  can lower through the same direct member-access shape OCaml uses when the
  binding is consumed immediately
- Added focused regression coverage in
  `lambda::simplify::tests::refines_immediate_module_field_reads_over_awaited_imports`
  so this stays pinned to the OCaml `refine_let` primitive-use rewrite rather
  than a single snapshot file
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release refines_immediate_module_field_reads_over_awaited_imports -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/Import.res -o /tmp/Import.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/Import.res` now narrows materially: the Rust side now emits
  the OCaml direct-awaited-member shape for the immediate-use cases in `f`,
  `f1`, and `f4`, instead of first materializing a temporary module binding;
  the remaining drift in that file has moved on to later alias naming and
  statement/compaction shape such as `each` rebinding and the `f6` tuple helper
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same change, which confirms this `refine_let` slice stays isolated from
  the already-stable external-shadow path
- The authoritative JS snapshot baseline now reports **187 / 657** passing,
  **0** compile errors, and **470** output diffs after this OCaml-aligned
  immediate-let-use refinement port; this is a net **+3** over the previous
  recorded baseline

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed on the OCaml float-exponentiation
  lowering path instead of treating the surviving `Math.pow(...)` drift as a
  printer quirk
- `compiler-rust/src/lambda/compile.rs` now matches
  `compiler/core/lam_compile_primitive.ml` and
  `compiler/core/js_exp_make.ml` more closely for `Ppowfloat`:
  Rust now lowers float exponentiation to `BinOp::Pow` / JS `**`, matching
  OCaml `E.float_pow`, instead of routing it through `Math.pow(...)`
- Added focused regression coverage in
  `lambda::compile::tests::compile_float_pow_uses_js_exponentiation_operator`
  so this stays pinned to the OCaml backend operator choice rather than a
  single snapshot file
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_float_pow_uses_js_exponentiation_operator -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/b.res -o /tmp/b.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/unified_ops_test.res -o /tmp/unified_ops_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same change, and the focused float-power files now show the OCaml
  operator shape:
  `b.res`, `unified_ops_test.res`, `exponentiation_test.res`, and
  `variantsMatching.res` now emit `**` on the Rust side where this slice used
  to emit `Math.pow(...)`
- The authoritative JS snapshot baseline remains **184 / 657** passing,
  **0** compile errors, and **473** output diffs after this OCaml-aligned
  `Ppowfloat` lowering port; there is no top-line parity delta yet because the
  remaining drift in these files is still later byte shape such as float-literal
  formatting (`2.` vs `2`), not the backend operator choice anymore

- This iteration stayed on another small OCaml printer cluster instead of
  treating the surviving char-literal comment diffs as arbitrary formatting:
  `compiler-rust/src/js_ir/printer.rs` now matches the
  `compiler/core/js_dump.ml` `Number (Int {c = Some _})` path more closely by
  printing character-code comments with the same quoted literal shape OCaml
  uses, e.g. `/* 'a' */97` and `/* '文' */25991`, rather than dropping the
  quotes around the character payload
- Added focused regression coverage to `js_ir::printer::tests::test_print_number`
  for both ASCII and Unicode character-number comments so this stays tied to
  the OCaml literal-comment behavior instead of a single snapshot file
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_number -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_5753.res -o /tmp/gpr_5753.mjs`
  - exact `compiler-args` repro for `tests/tests/src/cross_module_inline_test.res`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/gpr_5753.res` and
  `tests/tests/src/cross_module_inline_test.res` now match their checked-in
  `.mjs` snapshots exactly, while `tests/tests/src/ExternalShadow.res` remains
  an exact guard-file match after the same literal-comment change
- The authoritative JS snapshot baseline now reports **184 / 657** passing,
  **0** compile errors, and **473** output diffs after this OCaml-aligned
  character-literal comment printer fix; this is a net **+2** over the
  previous recorded baseline

- This iteration stayed on an OCaml-backed repeated printer cluster instead of
  treating the extra trailing `return` statements as file-local drift:
  `compiler-rust/src/js_ir/printer.rs` now mirrors
  `compiler/core/js_dump.ml` `function_body` more closely for unit-returning
  functions. Rust now drops trailing `return undefined`, rewrites tail
  `return expr` into a bare expression statement when `return_unit` is set,
  and collapses the single-statement `if (...) { ... } else { return undefined; }`
  function-tail case the same way OCaml prints it
- The same printer slice now also matches the OCaml arrow-function fast path
  more closely: single-expression arrow bodies can be printed from either
  `Return expr` or `Exp expr`, which keeps unit-return callbacks on the same
  byte shape as the OCaml snapshots after the tail rewrite
- Added focused regression coverage in `js_ir::printer::tests` for:
  - named unit-return functions that should print a bare side-effect statement
  - unit-return arrow callbacks that should print expression bodies without an
    explicit `return`
  - unit-return function tails whose `else` branch is just `return undefined`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_unit_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact `compiler-args` repro for `tests/tests/src/gpr_4265_test.res`
  - exact `compiler-args` repro for `tests/tests/src/gpr_4442_test.res`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/gpr_4265_test.res` and
  `tests/tests/src/gpr_4442_test.res` now match their checked-in `.mjs`
  snapshots exactly under the real test harness compiler args, and
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same printer change
- `tests/tests/src/dollar_escape_test.res` and
  `tests/tests/src/functor_app_test.res` also dropped out of the authoritative
  diff cache on the full rerun, which confirms this OCaml-aligned unit-return
  printer rule was a shared cluster rather than a single-file adjustment
- The authoritative JS snapshot baseline now reports **182 / 657** passing,
  **0** compile errors, and **475** output diffs after this OCaml-aligned
  `js_dump.ml` function-body port; this is a net **+10** over the previous
  recorded baseline

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed on the module side-effect metadata path
  instead of treating `epsilon_test.res` as a one-off trailer comment mismatch
- `compiler-rust/src/lambda/analysis.rs` now matches the OCaml
  `compiler/core/lam_analysis.ml` raw-JS purity slice more closely:
  `PrawJsCode` is no longer treated as pure just because it is an expression.
  Rust now reuses the existing OXC-backed raw-JS expression classifier and a
  new matching statement classifier so that only OCaml-equivalent raw
  functions, literals, and comment-only statement fragments count as
  side-effect-free
- `compiler-rust/src/binary_ast/ppx.rs` now exposes the missing raw statement
  classification alongside the existing raw expression classification, which
  lets the backend side-effect analysis distinguish comment-only raw statement
  payloads from arbitrary raw programs the same way OCaml does
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::analysis::tests::test_no_side_effects_raw_js_matches_ocaml_classification -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/epsilon_test.res` now matches its checked-in `.mjs`
  snapshot again; it dropped out of the authoritative diff cache once raw JS
  expressions stopped being treated as generically pure on the Rust side
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same change, which confirms this raw-JS purity slice stays isolated from
  the already-stable external-shadow path
- `tests/tests/src/ExternalExtension.res` still differs after the change, which
  shows the remaining drift there is not just raw-JS purity classification; the
  next signal in that file is still later backend lowering and byte shape
- The authoritative JS snapshot baseline now reports **172 / 657** passing,
  **0** compile errors, and **485** output diffs after this OCaml-aligned
  raw-JS purity classification fix; this is a net **+1** over the previous
  recorded baseline

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed on the surviving direct
  `Pjs_fn_make` call frontier from `gpr_1692_test.res` instead of treating the
  extra wrapper call as printer-only drift
- `compiler-rust/src/lambda/simplify.rs` now matches another slice of
  OCaml `compiler/core/lam_pass_alpha_conversion.ml` and
  `compiler/core/lam_pass_remove_alias.ml` more closely on the Rust JS path:
  direct `Pjs_fn_make` / `Pjs_fn_make_unit` callees are now beta-reduced
  through the wrapper when the current call site is itself the direct callee,
  but wrappers returned from an already-simplified inner application stay
  visible to later backend/codegen stages
- This keeps the earlier OCaml-aligned wrapper-preservation behavior intact
  while removing the specific extra outer wrapper application that remained in
  `gpr_1692_test.res`; the new unit coverage captures that exact one-step
  reduction boundary so we do not regress back to globally erasing wrapper
  structure
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::simplify::tests::beta_reduces_direct_pjs_fn_make_callees_but_keeps_returned_wrapper_calls -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::simplify::tests::inlines_direct_function_applications_without_named_call_profitability_gate -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_1692_test.res -o /tmp/gpr_1692_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/PartialApplicationNoRuntimeCurry.res -o /tmp/PartialApplicationNoRuntimeCurry.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/gpr_1692_test.res` now matches its checked-in `.mjs`
  snapshot exactly; the old extra outer call
  ``(x => (f => 0))("")("")`` is gone, while the returned inner wrapper call
  still survives exactly where the checked-in OCaml snapshot keeps it
- `tests/tests/src/PartialApplicationNoRuntimeCurry.res` and
  `tests/tests/src/ExternalShadow.res` remain exact guard-file matches after
  the same change, which confirms this slice stays on the direct wrapper-call
  boundary rather than reopening the earlier lowered-wrapper or external-shadow
  paths
- The authoritative JS snapshot baseline now reports **171 / 657** passing,
  **0** compile errors, and **486** output diffs after this OCaml-aligned
  direct-`Pjs_fn_make` call reduction slice; this is a net **+3** over the
  previous recorded baseline

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed in the OCaml post-flatten
  function-application path instead of treating `submodule.res` as a local
  constant-folding oddity
- `compiler-rust/src/lambda/simplify.rs` now matches another slice of
  OCaml `compiler/core/lam_pass_collect.ml` and
  `compiler/core/lam_pass_remove_alias.ml` more closely on the Rust JS path:
  inlineable non-recursive functions are now collected across the flattened
  lambda before simplification, and `Lapply` now retries the `Lvar` inlining
  path after simplifying the callee expression, which mirrors the extra OCaml
  alias-removal round that sees module-field projections after they flatten to
  plain identifiers
- The same `Lvar` retry path now also carries OCaml's self-application guard:
  Rust skips the post-simplification inline step when the callee identifier
  appears in any argument, which avoids the `g(g)`-style nontermination that
  surfaced as a stack overflow in `unboxed_crash.res`
- Verified focused guards for this slice:
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/submodule.res -o /tmp/submodule.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/unboxed_crash.res -o /tmp/unboxed_crash.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_1692_test.res -o /tmp/gpr_1692_test.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/submodule.res` now matches its checked-in `.mjs` snapshot
  exactly; the old `let v0 = a0(1, 2);` drift came from missing the OCaml
  alias-removal round after module-field flattening rather than from printer or
  arithmetic lowering
- `tests/tests/src/unboxed_crash.res` also now matches its checked-in `.mjs`
  snapshot again; the transient stack overflow came from the missing
  self-application guard on the new post-simplification `Lvar` inline path
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the change, and `tests/tests/src/gpr_1692_test.res` stays unchanged, which
  confirms this slice is isolated to flattened identifier calls rather than the
  earlier `Pjs_fn_make` wrapper frontier
- The authoritative JS snapshot baseline now reports **168 / 657** passing,
  **0** compile errors, and **489** output diffs after this OCaml-aligned
  post-flatten `Lvar` inlining change; this is a net **+2** over the previous
  recorded baseline and removes the transient compile-error regression from the
  first attempt at the same backend slice

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed in the OCaml ML-module field-access
  path instead of treating `es6_import.res` as a local printer-only keyword
  escape issue
- `compiler-rust/src/lambda/compile.rs` now matches the OCaml
  `compiler/core/lam_compile.ml` `compile_external_field` / `E.ml_var_dot`
  slice more closely on the Rust JS path:
  `Pfield(..., FieldDbgInfo::Module)` now keeps qualified ML-module namespace
  accesses as qualified members instead of pre-converting them into
  `StaticIndex` property names, which preserves OCaml's special
  `default` export access while still routing reserved names like `catch`
  through the existing identifier-conversion printer path
- Added focused coverage for this slice in
  `lowers_qualified_ml_module_default_field_without_preconverting_the_member_name`
  and `lowers_qualified_ml_module_reserved_fields_through_vident_printing`,
  alongside the existing
  `lowers_module_pfield_with_ocaml_identifier_conversion` regression test
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_qualified_ml_module_ -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_module_pfield_with_ocaml_identifier_conversion -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/SafePromises.res -o /tmp/SafePromises.mjs`
  - exact compiler-args repro for `tests/tests/src/es6_import.res`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/es6_import.res` now matches its checked-in `.mjs`
  snapshot exactly; the old `Es6_export.$$default` drift came from lowering a
  qualified ML-module field through the wrong OCaml backend path instead of
  keeping the `default` member name for final JS emission
- `tests/tests/src/ExternalShadow.res` and
  `tests/tests/src/SafePromises.res` remain exact guard-file matches after the
  change, which confirms the qualified-member fix stays isolated from the
  already-stable external-shadow/import path and the earlier reserved-name
  module-field slice
- The authoritative JS snapshot baseline now reports **166 / 657** passing,
  **0** compile errors, and **491** output diffs after this OCaml-aligned
  qualified-ML-module field-access fix; the +2 improvement confirms the
  default-member bug reached beyond the single focused file
- Diff file `temp/rust-parity/diffs/js_src_es6_import.res.diff` is now absent
  after the rerun

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed in the OCaml export-coercion path
  instead of treating `ExternalScopeShadow.res` as a local statement-ordering
  printer diff
- `compiler-rust/src/lambda/compile.rs` now matches the OCaml
  `compiler/core/lam_coercion.ml` `handle_exports` slice more closely on the
  Rust JS path:
  module-export extraction now preserves the payload expressions from
  `Pmakeblock(..., TagInfo::ModuleExport, ...)`, and the JS backend now
  synthesizes fresh trailing export bindings for mismatched export payloads
  before shake runs, which mirrors OCaml's rename-and-rebind export coercion
  instead of keeping inert exported placeholders at their original source
  positions
- The same export-coercion path now also preserves OCaml's same-name behavior
  on both sides of the alias split:
  same-name exports still reuse declared local bindings when available, and
  same-name aliases to unbound globals keep the local export binding instead of
  being rewritten to the global identifier
- Added focused coverage for this slice in
  `compile_deps_program_rebinds_different_name_exports_after_effects`,
  alongside the existing same-name export regression tests
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib compile_deps_program_rebinds_different_name_exports_after_effects -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib compile_deps_program_reuses_same_name_export_targets -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib compile_deps_program_keeps_same_name_export_aliases_for_unbound_globals -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalScopeShadow.res -o /tmp/ExternalScopeShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/ExternalScopeShadow.res` now matches its checked-in `.mjs`
  snapshot exactly; the old misplaced trailing `let MyURL;` was caused by the
  missing OCaml export-coercion stage rather than a final printer ordering bug
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the change, which confirms the export-coercion port stays isolated from the
  already-stable external-shadow/import path
- The authoritative JS snapshot baseline now reports **164 / 657** passing,
  **0** compile errors, and **493** output diffs after this OCaml-aligned
  export-coercion port; this iteration removes a broad export-placeholder
  cluster from the checked-in corpus rather than only fixing the single focused
  file

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed in the OCaml module-field lowering
  path instead of treating the `SafePromises.res` drift as a printer-only
  keyword-mangling issue
- `compiler-rust/src/lambda/compile.rs` now matches the OCaml backend slice in
  `compiler/core/js_exp_make.ml` more closely for module projections:
  `FieldDbgInfo::Module` lowers through the same converted module-access path
  as OCaml `module_access`, so module fields preserve OCaml identifier
  conversion (`catch` -> `$$catch`) and keep the module slot index on the
  resulting `StaticIndex`
- `compiler-rust/src/js_ir/printer.rs` now also matches the OCaml
  `compiler/core/js_dump.ml` `vident` split for qualified identifiers:
  `Runtime`/`Ml` members go through identifier conversion, while `External`
  members keep raw JS property-access semantics
- Added focused coverage for this slice in
  `lowers_module_pfield_with_ocaml_identifier_conversion`,
  `test_print_qualified_runtime_member_mangles_reserved_name`, and
  `test_print_qualified_external_member_preserves_js_property_access`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_qualified_ -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_module_pfield_with_ocaml_identifier_conversion -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/SafePromises.res -o /tmp/SafePromises.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/SafePromises.res` now matches its checked-in `.mjs`
  snapshot exactly again; the remaining `catch` drift was in OCaml module-field
  lowering, not the final JS printer
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the change, which confirms the module-field conversion fix stayed isolated
  from the already-stable external-shadow/import path
- The authoritative JS snapshot baseline now reports **148 / 657** passing,
  **0** compile errors, and **509** output diffs after this OCaml-aligned
  module-field lowering fix; this iteration moves one more file from diff to
  exact snapshot match

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed in the external-module metadata path
  instead of treating `ImportAttributes.res` as a printer-only diff
- `compiler-rust/src/raw_lambda/convert.rs` and
  `compiler-rust/src/lambda/convert.rs` now match the OCaml external-FFI
  metadata path more closely when import attributes come from marshaled PPX
  externals: the decoder now reads the OCaml hashtable bucket array from the
  real marshaled block shape instead of dropping the metadata before backend
  lowering
- `compiler-rust/src/lambda/compile.rs`,
  `compiler-rust/src/js_ir/op.rs`, and
  `compiler-rust/src/js_ir/printer.rs` now preserve and emit the full ordered
  import-attribute list on ES-module imports instead of special-casing only
  the `type` field, so Rust now follows the same `with {"type": "...", ...}`
  metadata shape as the OCaml backend for `J.deps_program`
- Added focused coverage for this slice in
  `external_module_import_attributes_preserve_all_fields`,
  `test_print_deps_program_preserves_all_import_attributes`,
  `ffi_spec_preserves_marshaled_import_attributes`, and
  `ffi_spec_preserves_import_attributes_from_rewritten_external`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release import_attributes -- --nocapture --skip binary_ast::ffi_types::tests::test_import_attributes_hashtbl_matches_ocaml_marshal`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ImportAttributes.res -o /tmp/ImportAttributes.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/ImportAttributes.res` now matches its checked-in `.mjs`
  snapshot exactly, including both import-attribute entries and OCaml's quoted
  `with { ... }` object shape
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the metadata fix, which confirms the change stayed isolated from the already
  stable external/import path
- The authoritative JS snapshot baseline now reports **147 / 657** passing,
  **0** compile errors, and **510** output diffs after this OCaml-aligned
  import-attribute metadata fix; this iteration moves one file from diff to
  exact snapshot match

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed in the raw-lambda to deps-program
  bridge instead of treating the extra `import * as Side_effect` line as a
  printer bug
- `compiler-rust/src/raw_lambda/convert.rs` now matches the OCaml dynamic
  import path more closely when packed modules flow through coercion:
  `apply_coercion_raw` now preserves the caller's dynamic-import scope while it
  pre-records possible required modules, so the packed `await Side_effect`
  path no longer records the same module once as static and once as dynamic
- Added focused coverage for this slice in
  `dynamic_import_pack_idents_record_only_dynamic_possible_requirements`,
  alongside the earlier dynamic-import possible-required-module regression
  tests
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib raw_lambda::convert::tests::dynamic_import_ -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib lambda::compile::tests::skips_dynamic_import_only_possible_required_modules -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact AST-path repro for `tests/tests/src/import_side_effect.res`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/include_side_effect.res -o /tmp/include_side_effect.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/import_side_effect.res` now matches its checked-in `.mjs`
  snapshot exactly again; the transient extra static `Side_effect` import came
  from raw-lambda coercion bookkeeping, not the final JS printer
- `tests/tests/src/ExternalShadow.res` and
  `tests/tests/src/include_side_effect.res` remain exact guard-file matches
  after the fix
- The authoritative JS snapshot baseline is back to the recorded
  **146 / 657** passing, **0** compile errors, and **511** output diffs after
  this OCaml-aligned dynamic-import required-module fix; this iteration
  recovers the session-local regression from **145 / 657** and **512** diffs,
  even though the topline does not exceed the checked-in project baseline yet

- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this iteration stayed inside
  `compiler-rust/src/lambda/compile.rs` and ported another
  `compiler/core/lam_compile.ml` runtime-dispatch slice instead of treating the
  JS diff as a printer issue
- `compiler-rust/src/lambda/compile.rs` now matches another OCaml backend
  slice from `core/lam_compile.ml` and `ml/ast_untagged_variants.ml`:
  builtin untagged switches with block-only cases no longer fall through the
  generic const-only switch path on the JS backend, and the `Object` runtime
  case now excludes the full OCaml set of instance-backed shapes from the
  switch metadata instead of only the currently visited branch list
- Added focused coverage for this slice in
  `builtin_untagged_block_switch_expressions_dispatch_on_object_runtime_shape`
  and `builtin_untagged_object_switches_exclude_array_cases`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release builtin_untagged_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DictPatternMatchingOptimization.res -o /tmp/DictPatternMatchingOptimization.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/DictPatternMatchingOptimization.res` now keeps the
  `JSON.Object` branch on the JS path instead of dropping straight to the
  default `[]` case, and the outer runtime guard now matches OCaml's object
  exclusion shape (`typeof match !== "object" || match === null ||
  Array.isArray(match)`)
- The remaining drift in
  `tests/tests/src/DictPatternMatchingOptimization.res` is further downstream:
  Rust still emits `JSON.parse(data, undefined)` instead of `JSON.parse(data)`,
  and the nested string-pattern body still expands into a cascade of synthetic
  `$$switch` temporaries instead of OCaml's tighter exit-chain lowering
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  this switch-lowering change, which confirms the builtin-untagged dispatch fix
  stayed isolated from the already-stable external/import path
- The authoritative JS snapshot baseline remains **146 / 657** passing,
  **0** compile errors, and **511** output diffs after this OCaml-aligned
  builtin-untagged block-switch port; the topline stays flat because the
  affected file is still failing on later call-lowering and nested-switch
  shaping mismatches even though the dropped-object-branch bug is fixed

- `compiler-rust/src/js_ir/mod.rs` and
  `compiler-rust/src/lambda/compile.rs` now match another OCaml backend slice
  from `core/js_exp_make.ml` more closely:
  Rust now uses an OCaml-style smart negation constructor instead of emitting
  raw `JsNot` nodes from backend call sites, so negated equality/order tests
  fold into `!==`, `===`, `<=`, `>=`, and De Morgan rewrites before printing
- Added focused coverage for this slice in
  `test_not_simplifies_equality_negation` and
  `test_not_pushes_negation_through_and`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib test_not_ -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib test_if_statement -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/return_check.res -o /tmp/return_check.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/LetUnwrap.res -o /tmp/LetUnwrap.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/return_check.res` now emits the OCaml-style null guard in
  `test` (`elem !== null` instead of `!(elem === null)`); the remaining drift
  there is later alias cleanup and assert-block byte shape, not raw negation
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  threading smart negation through the backend, which confirms the change stays
  isolated from the already-stable external-shadow/import path
- The cached raw-negation motif shrank materially after the authoritative
  rerun: diff files containing `!(` dropped from **38** to **10**
- The authoritative JS snapshot baseline remains **146 / 657** passing,
  **0** compile errors, and **511** output diffs after this OCaml-aligned
  smart-negation port; the topline stays flat because the affected files still
  carry later alias/branch-expression cleanup mismatches even though the
  boolean-test IR is now closer to OCaml

- `compiler-rust/src/js_ir/mod.rs` now matches one more slice of
  OCaml `core/js_stmt_make.ml` on the Rust JS-output path:
  `Statement::if_` is now a smart constructor instead of a raw `If` wrapper,
  so it ports the OCaml guard/cleanup cases for empty branches, paired
  `return` branches, terminal-then fallthrough, and matching assignment
  branches
- Added focused coverage for this slice in
  `test_if_statement`,
  `test_if_statement_merges_two_returns_into_a_conditional_return`, and
  `test_if_statement_merges_matching_assignments_into_a_conditional_assignment`
- Kept raw printer coverage for explicit `If` nodes by updating
  `compiler-rust/src/js_ir/printer.rs` `test_print_if` to construct
  `StatementDesc::If` directly instead of routing through the smart
  constructor
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib test_if_statement -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib test_print_if -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/LetUnwrap.res -o /tmp/LetUnwrap.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/return_check.res -o /tmp/return_check.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/LetUnwrap.res` narrowed materially:
  the nested `let?` result/option paths now use OCaml-style guard returns
  instead of keeping the whole continuation under a positive `if/else`, so
  the remaining drift there is mostly alias temps, compact object formatting,
  and later branch-expression cleanup rather than raw control-flow shape
- `tests/tests/src/return_check.res` also moved in the same direction:
  throw/fallthrough cases no longer keep the redundant `else` wrapper after a
  terminating branch, and the remaining drift there is the still-missing
  negation simplification (`!==` / `!== null`), alias temps, and printer
  byte-shape
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the constructor change, which confirms this control-flow cleanup stays
  isolated from the already-stable external-shadow/import path
- The authoritative JS snapshot baseline remains **146 / 657** passing,
  **0** compile errors, and **511** output diffs after this OCaml-aligned
  `Js_stmt_make.if_` port; the top-line count stays flat because the affected
  files still carry later backend cleanup mismatches even though the
  statement-shaping stage is now closer to OCaml

- `compiler-rust/src/lambda/compile.rs` now matches another OCaml backend
  slice from `core/lam_compile.ml` and `core/lam_compile_external_call.ml`:
  `Pjs_unsafe_downgrade` no longer falls through to `undefined`, so lowered
  JS getter/setter sends produce real property access and assignment, and
  spliced externals now follow the same `assemble_args_has_splice` /
  `E.variadic_args` path OCaml uses for variadic external calls
- Added focused coverage for this slice in
  `lowers_pjs_unsafe_downgrade_getters_to_method_calls`,
  `lowers_pjs_unsafe_downgrade_setters_to_property_assignments`, and
  `lowers_spliced_js_calls_by_flattening_literal_variadic_arrays`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release pjs_unsafe_downgrade -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release flattening_literal_variadic_arrays -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/meth_annotation.res -o /tmp/meth_annotation.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/node_path_test.res -o /tmp/node_path_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/set_annotation.res -o /tmp/set_annotation.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/meth_annotation.res`,
  `tests/tests/src/node_path_test.res`, and
  `tests/tests/src/set_annotation.res` now all match their checked-in `.mjs`
  snapshots exactly after this external-call lowering fix
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the change, which confirms the fix stays aligned with the already-stable
  external-shadow/import path
- The authoritative JS snapshot baseline now reports **146 / 657** passing,
  **0** compile errors, and **511** output diffs after this OCaml-aligned
  external-call lowering fix

- `compiler-rust/src/js_ir/printer.rs` now matches one more slice of
  OCaml `core/js_dump.ml` on the Rust JS-output path:
  exception blocks (`Blk_extension` / `Blk_record_ext`) no longer print as
  generic arrays, and `throw` sites now add the same `Error: new Error()`
  field that OCaml's `exn_block_as_obj ~stack:true` emits
- Added focused coverage for this slice in
  `test_print_exception_extension_block_as_object`,
  `test_print_record_extension_exception_uses_named_fields`, and
  `test_print_throw_exception_block_includes_error_stack`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_exception_extension_block_as_object -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_record_extension_exception_uses_named_fields -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_throw_exception_block_includes_error_stack -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/return_check.res -o /tmp/return_check.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/exception_value_test.res -o /tmp/exception_value_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/return_check.res` narrowed materially:
  the old thrown `["Assert_failure", ...]` array shape is gone, and the
  remaining drift there is now later nullable-test spelling, alias temps, and
  block formatting rather than exception-object dumping
- `tests/tests/src/exception_value_test.res` also moved past the old exception
  array/object mismatch:
  thrown `Not_found` / `Assert_failure` values and the non-thrown `u`
  exception value now use the OCaml `RE_EXN_ID` object layout, while the
  remaining drift is in later exception-runtime lowering
  (`Primitive_exceptions.create`, `internalToException`, control flow, and
  enum member naming), not final dump shape
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the exception printer change
- The cached thrown-array exception motif is now gone from the authoritative
  diff cache: `rg -l 'throw \\[' temp/rust-parity/diffs/*.diff | wc -l`
  reports **0** after the rerun
- The authoritative JS snapshot baseline remains **130 / 657** passing,
  **0** compile errors, and **527** output diffs after this OCaml-aligned
  exception-block dump fix; the checked-in corpus total stays flat because the
  affected files still carry earlier backend lowering mismatches even though
  the final exception-object shape is now aligned

- `compiler-rust/src/lambda/compile.rs` now matches one more slice of
  OCaml `core/lam_compile_primitive.ml` on the Rust JS path:
  `Primitive::Poffsetref` no longer falls through the generic
  `_ => undefined` fallback, and now lowers to the same ref-field update shape
  OCaml emits (`ref.contents = ref.contents + n | 0; undefined`)
- Added focused coverage for this slice in
  `lambda::compile::tests::lowers_poffsetref_to_ref_contents_update`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib lambda::compile::tests::lowers_poffsetref_to_ref_contents_update -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/functor_def.res -o /tmp/functor_def.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_simple_ref.res -o /tmp/test_simple_ref.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/functor_def.res` now matches its checked-in `.mjs`
  snapshot exactly again; the missing `v.contents = v.contents + 1 | 0`
  side effect in `f` was entirely the unimplemented `Poffsetref` path
- `tests/tests/src/test_simple_ref.res` narrowed materially:
  the old missing increment in `gen()` is gone, and the remaining drift is now
  later ref-allocation / escape shaping (`let a = 0` vs `{contents: 0}` and
  `not_real_escape = a` vs `a.contents`) rather than dropped mutation effects
- The authoritative JS snapshot baseline now reports **130 / 657** passing,
  **0** compile errors, and **527** output diffs after the OCaml-aligned
  `Poffsetref` lowering fix

- `compiler-rust/src/lambda/compile.rs` now matches one more slice of
  OCaml `core/lam_compile.ml` on the Rust JS path:
  return-position and declaration-position `if` lowering no longer round-trip
  through the generic expression compiler when a branch needs statements;
  instead, the backend now emits direct branch returns / assignments in those
  contexts, which matches OCaml's continuation-aware `compile_if` split more
  closely and avoids manufacturing synthetic `ifres` result temporaries
- Added focused coverage for this slice in
  `function_return_blocks_lower_ifs_without_a_result_temp` and
  `let_bindings_lower_ifs_without_a_result_temp`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lower_ifs_without_a_result_temp -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/return_check.res -o /tmp/return_check.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/return_check.res` narrowed materially:
  the synthetic `let ifres` / trailing `return ifres` scaffolding is gone from
  the option/assert branches, and the file now differs on later nullable-test
  byte shape, retained `Some(k)` aliases, and the still-missing OCaml assert
  exception object shape instead of return-context control-flow lowering
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the continuation-aware `if` change
- the cached `let ifres` diff motif collapsed from **119** files to **59**
  files after the authoritative rerun, which confirms this was a broad backend
  continuation gap rather than a local snapshot accident
- The authoritative JS snapshot baseline remains **130 / 657** passing,
  **0** compile errors, and **527** output diffs after this OCaml-aligned
  return/assignment `if` lowering fix; the change is kept because it moves the
  Rust backend closer to OCaml even though the checked-in corpus total stays
  flat

- `compiler-rust/src/lambda/compile.rs` now matches one more slice of
  OCaml `core/js_pass_get_used.ml` and `core/js_pass_tailcall_inline.ml`
  on the Rust JS path:
  the missing JS pass is now threaded between `external_shadow` and
  `flatten_and_mark_dead`, Rust now computes OCaml-style `Used` /
  `OncePure` / `DeadPure` / `DeadNonPure` statuses for JS bindings,
  single-return calls to `OncePure` local functions now inline through
  the pass, and direct return-IIFEs now inline through the same
  return-block rule instead of surviving as extra wrapper calls
- Added focused coverage for this slice in
  `js_tailcall_inline_inlines_once_pure_named_calls` and
  `js_tailcall_inline_inlines_direct_return_iifes`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_tailcall_inline_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UncurriedAlways.res -o /tmp/UncurriedAlways.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the new pass, which confirms this JS-pass addition does not perturb the
  already-stable external-shadow/import path
- `tests/tests/src/UncurriedAlways.res` still fails on later backend shaping:
  its remaining drift stays on array/object byte shape, callback lowering,
  and tuple/app lowering, so this tailcall-inline pass does not move that
  file by itself
- The authoritative JS snapshot baseline remains **130 / 657** passing,
  **0** compile errors, and **527** output diffs after the
  `Js_pass_tailcall_inline` port; this keeps the Rust backend pass order
  closer to OCaml even though the checked-in corpus does not move yet

- `compiler-rust/src/lambda/compile.rs` now matches one more slice of
  OCaml `core/lam_compile_main.ml` more closely on the Rust JS path:
  deps-program export recovery no longer assumes the final lowered JS
  expression is a bare `ModuleExport` block; it now peels a trailing
  top-level sequence whose right-hand side is `ModuleExport`, which matches
  the OCaml backend's separate `meta.exports` path instead of dropping exports
  that follow top-level side effects
- Added focused coverage for this slice in
  `compile_deps_program_keeps_exports_after_trailing_effect_sequence`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::compile::tests::compile_deps_program_keeps_exports_after_trailing_effect_sequence -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/raw_arity.res -o /tmp/raw_arity.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/async_inside_loop.res -o /tmp/async_inside_loop.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/raw_arity.res` and
  `tests/tests/src/async_inside_loop.res` now both match their checked-in
  `.mjs` snapshots exactly after the export-sequence fix
- `tests/tests/src/print_alpha_test.res` also dropped out of the authoritative
  diff set after the same change; its missing trailing `export { f }` block was
  the same root cause rather than a separate printer issue
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the change, which confirms this export recovery fix does not perturb the
  already-resolved external/global lowering path
- The authoritative JS snapshot baseline now reports **130 / 657** passing,
  **0** compile errors, and **527** output diffs after this OCaml-aligned
  export-sequence recovery fix

- OCaml `core/lam_pass_deep_flatten.ml` / `core/lam_pass_remove_alias.ml` /
  `core/lam_compile_primitive.ml` nullable-option cleanup is now matched more
  closely on the Rust JS path:
  the JS-backend simplifier now performs the same deep-flatten split for
  non-variable `Pnull_to_opt` / `Pnull_undefined_to_opt` lets, rewrites
  `Pis_not_none` / `Pval_from_option(_not_nest)` alias checks back to raw
  nullable predicates, and JS lowering now compiles the resulting
  `Pis_null` / `Pis_undefined` / `Pis_null_undefined` primitives instead of
  falling through to `undefined`
- Added focused coverage for this slice in
  `rewrites_null_to_opt_alias_checks_to_raw_null_predicates`,
  `rewrites_nullable_alias_checks_to_raw_nullable_predicates`, and
  `lowers_nullable_predicates_to_js_null_checks`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_nullable_predicates_to_js_null_checks -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release rewrites_null_to_opt_alias_checks_to_raw_null_predicates -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release rewrites_nullable_alias_checks_to_raw_nullable_predicates -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/return_check.res -o /tmp/return_check.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/return_check.res` narrowed materially:
  the broken `if (!undefined)` output is gone, and the nullable branches now
  lower to real null / null-or-undefined checks; the file still fails on later
  backend shaping (`ifres` temporaries, assert lowering, and byte-shape drift)
  so it does not change the pass/fail count yet
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the nullable-predicate fix
- The authoritative JS snapshot baseline remains **123 / 657** passing,
  **0** compile errors, and **534** output diffs after this OCaml-aligned
  nullable-predicate lowering fix

- `compiler-rust/src/lambda/compile.rs` now matches one more slice of
  OCaml `core/lam_compile_main.ml` / `core/lam_module_ident.ml` /
  `ext/ext_string.ml` on the Rust JS path:
  after collecting required modules from the lowered JS program, Rust no longer
  sorts them by the local module identifier name; it now sorts by OCaml's
  `Lam_module_ident.name` key using the same length-first, then bytewise
  comparator that `Ext_string.compare` uses
- Added focused coverage for this slice in
  `sorts_external_module_dependencies_by_module_name` and
  `sorts_required_modules_by_length_before_bytes`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release sorts_ -- --test-threads=1`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalArity.res -o /tmp/ExternalArity.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/reactTestUtils.res -o /tmp/reactTestUtils.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/ExternalArity.res` now matches its checked-in `.mjs`
  snapshot exactly after the required-module sort fix
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the change, which confirms this import-order slice does not perturb the
  already-resolved external-shadow path
- `tests/tests/src/reactTestUtils.res` still fails, but its leading diff stays
  on unrelated backend shaping (`Primitive_option` / `Caml_option`, callback
  shaping, and extra exports) rather than module-order churn
- The authoritative JS snapshot baseline now reports **123 / 657** passing,
  **0** compile errors, and **534** output diffs after the required-module sort
  fix

- `compiler-rust/src/js_ir/printer.rs` now matches the corresponding
  OCaml `core/js_dump.ml` call-printing rule more closely:
  when a JS call has exactly one synthetic unit argument
  (`Undefined {is_unit = true}`), Rust now omits that printed argument so the
  emitted JS is `f()` instead of `f(undefined)`, while plain
  `undefined` arguments still stay explicit
- Added focused printer coverage for this slice in
  `test_print_call_omits_single_unit_undefined_argument` and
  `test_print_call_keeps_plain_undefined_argument`
- Verified focused guards for this slice:
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UncurriedAlways.res -o /tmp/UncurriedAlways.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ../../../../compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/boolean_test.ast -o /tmp/boolean_test.mjs`
- `tests/tests/src/boolean_test.res` now matches its checked-in `.mjs`
  snapshot exactly after the unit-call printer fix
- `tests/tests/src/UncurriedAlways.res` narrowed materially:
  the old `a(undefined)` and `cb(undefined)` drift is gone, and the remaining
  mismatch there has moved on to later IIFE / tailcall-cleanup shaping rather
  than unit-call printing
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the unit-call printer change
- the cached explicit `(...undefined)` unit-call motif collapsed sharply after
  the authoritative rerun:
  broad `call(undefined)` diffs dropped from **87** files to **24**, and the
  `)(undefined)` callback-IIFE variant dropped from **5** files to **0**
- The authoritative JS snapshot baseline now reports **122 / 657** passing,
  **0** compile errors, and **535** output diffs after the unit-call printer
  fix

- OCaml `core/lam_pass_alpha_conversion.ml` / `core/lam_compile.ml` /
  `core/js_exp_make.ml` one-unit-argument lowering is now matched more closely
  on the Rust JS-output path:
  when the JS-backend simplifier unwraps `Pjs_fn_make_unit` around a synthetic
  single-`param` lambda, it now preserves OCaml's `one_unit_arg` marker, and
  JS lowering now honors that marker by dropping the synthetic JS parameter the
  same way OCaml's `E.ocaml_fun ~one_unit_arg` path does
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release unwraps_pjs_fn_make_unit_into_one_unit_arg_functions -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release one_unit_arg_functions_lower_to_zero_arg_js_functions -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UncurriedAlways.res -o /tmp/UncurriedAlways.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- `tests/tests/src/UncurriedAlways.res` narrowed materially:
  the old `function inl(param)` drift is gone, and the remaining diffs there
  have moved on to later callback/app-lowering and byte-shape cleanup instead
  of synthetic unit-parameter lowering
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the one-unit-argument change
- the cached `function ... (param)` addition motif collapsed from **90** diff
  files to **8** files after the authoritative rerun, which confirms this was a
  broad backend lowering gap rather than a local printer issue
- The authoritative JS snapshot baseline now reports **121 / 657** passing,
  **0** compile errors, and **536** output diffs after the one-unit-argument
  lowering fix

- `compiler-rust/src/lambda/compile.rs` now ports the core of OCaml
  `core/js_pass_flatten_and_mark_dead.ml` onto the Rust JS-output path:
  the missing pass is now threaded after `js_pass_flatten` /
  `js_pass_external_shadow` and before `Js_shake`, immutable `Caml_block`
  aliases now substitute simple indexed field reads the way OCaml does, and
  nested JS bindings are now marked `DeadPure` / `DeadNonPure` / `Used`
  through the same post-pass dead-marking stage instead of leaving every local
  declaration at the default status
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_flatten_and_mark_dead_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_tuple.res -o /tmp/test_tuple.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DerivingAccessorsCurried.res -o /tmp/DerivingAccessorsCurried.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after the
  new pass
- `tests/tests/src/test_tuple.res` and
  `tests/tests/src/DerivingAccessorsCurried.res` remain on the same broader
  backend / printer drift; this pass does not collapse those files by itself
- The authoritative JS snapshot baseline now reports **110 / 657** passing,
  **0** compile errors, and **547** output diffs after the
  `Js_pass_flatten_and_mark_dead` port
- the pass itself is now present and unit-covered on the Rust path, but this
  corpus still needs the earlier OCaml JS-pass preconditions, especially
  `Js_pass_tailcall_inline`, before `flatten_and_mark_dead` starts paying off in
  the checked-in snapshots; landing it in isolation caused a small temporary
  parity regression rather than a win

- OCaml `ext_pp_scope.ml` / `core/js_dump.ml` nested-function identifier
  scoping is now matched more closely on the Rust printer path:
  function params and local bindings no longer inherit every outer printable
  name by default, while captured outer ids are still reserved ahead of the
  function body the way OCaml's `merge` / `sub_scope` path does
- that printer change removed a large chunk of spurious nested-function suffix
  drift:
  cached JS diffs containing `\$1` / `\$2`-style identifier renames dropped
  from **326** files to **180** files after the authoritative rerun
- `tests/tests/src/Coercion.res` narrowed materially:
  the bogus `x$1` parameter rename is gone, and the remaining drift there is
  now just the earlier top-level function-order mismatch rather than nested
  identifier scoping
- `tests/tests/src/UncurriedAlways.res` also narrowed materially:
  the old nested-function suffix churn like `z$1`, `w$1`, `a$1`, and `b$1`
  is gone, so the remaining diffs there are now later backend shaping and
  printer byte shape instead of scope renaming noise
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the printer scope change, which confirms this slice stays isolated to
  nested lexical naming rather than the existing external-shadow/import path
- OCaml `core/lam_stats_export.ml` / `lam_compile_env.ml` purity fallback is
  now matched more closely on the Rust JS-output path:
  when the lowered module body itself is pure, Rust no longer stops at
  `module_side_effect_reason`; it now falls back to the first required module
  that is not marked pure, using the same runtime / external / `.cmj` split
  OCaml uses for final deps-program purity
- `tests/tests/src/gentTypeReTest.res` now matches its checked-in `.mjs`
  snapshot exactly after that fallback change
- `tests/tests/src/test_utils.res` also now matches its checked-in `.mjs`
  snapshot exactly after the same effect-reason fix
- `tests/tests/src/reactTestUtils.res` still fails on later backend shaping, but
  its purity-trailer drift is gone; the remaining differences have moved on to
  callback / option lowering and export shape instead of final deps-program
  purity reporting
- OCaml `core/js_dump.ml` now matches more closely on one more printer slice:
  `Blk_record`, `Blk_record_inlined`, `Blk_record_ext`, and `Blk_module`
  `Caml_block` values no longer bypass Rust's shared object-literal emitter
  with ad hoc compact formatting; they now follow the same object-layout path
  OCaml uses when it first rewrites those blocks into `Object (...)`
- `tests/tests/src/EmptyRecord.res` now matches its checked-in `.mjs`
  snapshot exactly after the shared object-layout fix
- `tests/tests/src/EnvUnifiedOps.res` now also matches its checked-in `.mjs`
  snapshot exactly after the same printer change
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the object-layout fix, which confirms this slice stays isolated to
  record/module object dumping rather than broader import/export handling
- `tests/tests/src/DerivingAccessorsCurried.res` and
  `tests/tests/src/VariantSpreads.res` both narrowed materially:
  their remaining drift is now later constructor-object layout and backend tag
  shaping rather than record/module object formatting
- OCaml `frontend/ast_config.ml` / `core/js_dump_program.ml` top-level
  directive handling is now matched more closely on the Rust JS-output path:
  file-level `@@directive("...")` attributes are collected from the parsed
  structure in source order and emitted ahead of the ReScript header during
  deps-program printing
- `tests/tests/src/directives.res` now matches its checked-in `.mjs` snapshot
  exactly after threading file directives through the Rust printer path
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the file-directive change, which confirms this slice stays isolated to module
  prelude emission
- the JS-backend post-lowering simplifier now matches OCaml's treatment of
  `Pjs_fn_make` / `Pjs_fn_make_unit` more closely for one important slice:
  those wrappers are now transparent on the Rust JS path, so the existing local
  beta-reduction logic can see through lowered function wrappers instead of
  leaving avoidable `add(5, extra)`-style calls in emitted JS
- `tests/tests/src/PartialApplicationNoRuntimeCurry.res` now matches its
  checked-in `.mjs` snapshot exactly after that simplifier fix
- `tests/tests/src/UncurriedAlways.res` narrowed materially:
  the direct partial-application wrappers like `ptl`, `bar2`, and `a`
  now lower to the same direct arithmetic/value bodies as the checked-in
  snapshot, and the remaining drift has moved on to later backend shaping and
  printer byte shape
- OCaml `lam_compile.ml` continuation handling is now matched more closely on
  the Rust backend path for one important slice:
  function bodies and effect blocks no longer lower every `Lsequence` through a
  single context-free `compile_expr`; instead, sequence prefixes recurse through
  effect-context blocks while tails recurse through return-context blocks,
  matching OCaml's `EffectCall Not_tail` vs `Maybe_tail_is_return` split more
  closely
- that backend change removed a large chunk of spurious pure `undefined;`
  statements from callback and function bodies, shrinking the explicit
  `undefined;` diff motif from **270** files to **170** files
- `tests/tests/src/test_ffi.res` now matches its checked-in `.mjs` snapshot
  exactly after the continuation-sensitive lowering fix
- `tests/tests/src/epsilon_test.res` narrowed materially:
  the bogus callback-body `undefined;` statements are gone, and its remaining
  drift has moved on to later backend shaping around callback parameters and the
  final export / purity trailer
- the OCaml `js_pass_flatten.ml` stage is now on the Rust JS path ahead of the
  already-ported `external_shadow` pass, so effectful sequence callbacks now
  lower as statement blocks instead of giant comma expressions
- the old `, undefined,` comma-sequence motif collapsed from **185** diff files
  to **56** files after the flatten pass
- the next cleanup frontier is now split:
  some of the old `undefined;` noise really was missing continuation-sensitive
  backend lowering in `lam_compile`, while the remaining **170** files still
  point at later cleanup stages such as `Js_pass_flatten_and_mark_dead` /
  `Js_shake`
- the authoritative wrapper is now scoped to the canonical in-repo 657-file set
- all current internal JS snapshot files now compile under the wrapper baseline
- the former `Import.res` timeout is now exposed as a normal output-diff case
- preserving OCaml external-spec metadata through `PjsCall` is necessary for
  backend parity after optimized lambda: `@val`, `@new`, `@get`, and related
  externals cannot be lowered as a generic `primName(...)` call
- preserving OCaml marshaled external argument metadata is also necessary for
  `@as(...)` constants and `@obj` field assembly: the backend must lower these
  from preserved FFI metadata rather than trying to reconstruct them from the
  final primitive name
- a small OCaml-aligned post-lowering lambda simplifier is now on the JS path:
  obvious local function applications are beta-reduced before JS IR lowering,
  and dead pure lets are dropped instead of leaking through as backend noise
- a larger OCaml-aligned subset of `Lam_pass_lets_dce` is now also on the JS
  path:
  simple alias/constant/module-field bindings are substituted through the
  lowered lambda body, pure `Lsequence` noise is removed, and constant
  `Pstringadd` chains are folded after substitution while still preserving
  exported bindings needed by the final module export block
- allocating constant blocks still need OCaml-style sharing on the JS backend
  path: record / variant / module constants cannot be substituted through
  `let` bindings the way scalar constants can, or the backend duplicates
  literals that OCaml keeps as shared bindings
- the JS-backend post-lowering simplifier now also ports the OCaml
  `lam_pass_deep_flatten.ml` named immutable-module-block rule for
  `match` / `include` / `param` bindings:
  projected `Pfield` aliases are flattened back out of those temporary module
  blocks before later simplification, which removes a real backend-shaping gap
  instead of papering over the emitted JS text
- `tests/tests/src/DerivingAccessorsCurried.res` and
  `tests/tests/src/DerivingAccessorsUncurried.res` both narrowed to a single
  remaining diff hunk after the deep-flatten change:
  the nested `include`-module block churn is gone, and the remaining drift has
  moved on to later alias/export shaping and final byte-shape cleanup
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the deep-flatten change, which keeps this slice isolated to lowered
  module-block simplification rather than broader module emission behavior
- `tests/tests/src/AsInUncurriedExternals.res` is now fully resolved in the
  checked-in snapshot set; `tests/tests/src/Import.res` narrowed further after
  the simplifier removed some dead-let churn, but its remaining drift is still
  later backend shaping rather than import-path resolution
- the `ExternalShadow.res` cluster is now resolved end-to-end in the checked-in
  snapshot set; the remaining frontier has moved on from that external-call /
  shadowing case
- external-corpus sweeps remain secondary; the in-repo backend frontier still has
  ample signal
- OCaml `lam_compile.ml` / `lam_compile_primitive.ml` dynamic-import handling is
  now matched more closely on the Rust backend path:
  `Pimport` no longer relies on recognizing an already-compiled JS function for
  eta-expanded external module values; instead it ports OCaml's lambda-stage
  special-case for a single-argument function whose body is a `Pjs_call`,
  recompiles that body with `dynamic_import = true`, and then lowers the result
  through the normal `import("...").then(m => m.member)` path
- OCaml `js_dump_property.ml` property-access printing is now matched more
  closely on the Rust printer path:
  reserved-word properties like `.default` now emit dot access, while
  bracket-only printing is kept for cases that actually require it
- OCaml `js_dump_program.ml` empty-deps-program output is now matched on the Rust
  printer path:
  import-free empty modules emit the checked-in
  `/* This output is empty... */` explanation instead of the generic
  `/* No side effect */` trailer
- OCaml `js_dump_program.ml` vertical spacing is now matched more closely on the
  Rust printer path:
  non-empty import-free modules keep the extra blank line after the ReScript
  header, and ES-module imports keep the blank line before the first statement
- OCaml `js_dump_program.ml` / `js_dump_import_export.ml` / `js_dump.ml` now
  match more closely on another byte-shape printer slice:
  function directives emit raw directive prologues, non-export modules keep the
  separator line before the purity trailer, and `default` exports alias the
  local `$$default` binding back to the public `default` name
- OCaml `js_stmt_make.define_variable` / `js_dump.ml` declaration printing is
  now matched more closely on the Rust printer path:
  variable declarations whose lowered initializer is exactly `undefined` now
  emit `let x;` instead of `let x = undefined;`

## Working Rules

1. **Read the OCaml source first.** Do not infer backend semantics from JS diffs alone.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Treat compile errors as highest priority.** A crash or compile failure hides downstream diff information.
5. **Fix the backend path, not the output string by hand.** Final printer work is the last mile, not the starting point.
6. **Keep Spice enabled as a guard.** It is built into the compiler now and should not be artificially skipped in the project wrapper.
7. **Do not reopen typedtree or lambda parity work.** Those stages are already at 100%.

## Immediate Frontier

- [x] Run the first dedicated `./scripts/test_js_output_parity.sh` baseline and record the full results here.
- [x] Re-run the wrapper after rescoping it to the canonical 657-file in-repo set and record the new baseline.
- [x] Route final JS codegen in `compiler-rust/src/driver.rs` through the raw-lambda / lowering path instead of the legacy typedtree shortcut.
- [x] Inventory the current internal compile-error files from `temp/rust-parity/diffs/js_src_*.err`.
- [x] Inventory the current internal text-diff files from `temp/rust-parity/diffs/js_src_*.diff`.
- [x] Pick one small internal structural file and one internal compile-error guard as the first implementation targets.

## Expected Root-Cause Buckets

- backend routing still bypasses the OCaml-aligned raw-lambda path
- missing post-lowering lambda passes
- missing coercion/grouping before JS lowering
- baseline `LambdaCompiler` shape differs from `Lam_compile`
- missing `js_pass_*` normalization
- final JS printer/dumper byte-shape differences

Not expected root-cause buckets for this project:

- typedtree parity
- raw lambda parity
- optimized lambda parity

## Candidate Focus Files

Internal text diffs already observed in the pre-wrapper run:

- `tests/tests/src/ExternalShadow.res`
- `tests/tests/src/LetUnwrap.res`
- `tests/tests/src/jsoo_485_test.res`
- `tests/tests/src/keep_uncurry_attribute.res`
- `tests/tests/src/node_assert.res`
- `tests/tests/src/return_check.res`
- `tests/tests/src/test_other_exn.res`
- `tests/tests/src/test_unsafe_cmp.res`

Remaining internal compile errors under the measured wrapper baseline:

- none

## Latest Session Findings

- `compiler-rust/src/lambda/compile.rs` now matches one more slice of
  OCaml `core/lam_compile.ml` more closely on the Rust JS path:
  string/tag switches now honor the same small-case `compile_general_cases`
  lowering for the backend cases Rust can prove locally, and named-variant
  dispatch now follows OCaml's saturation checks before deciding whether it
  needs an object/non-object split
- Concretely:
  - single-case `LstringSwitch` nodes with a default now lower through direct
    `if/else` assignment instead of always forcing a `switch`
  - block-only named-variant switches with a saturated const side no longer
    emit a redundant `typeof ... === "object"` gate before switching on `TAG`
  - the same direct-tag decision now applies consistently across value,
    return, and effect continuations
- Added focused coverage for this slice in
  `single_case_string_switches_with_default_lower_to_if_else` and
  `named_variant_return_switches_with_only_payload_cases_skip_object_split`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml --release single_case_string_switches_with_default_lower_to_if_else -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml --release named_variant_return_switches_with_only_payload_cases_skip_object_split -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/LetUnwrap.res -o /tmp/LetUnwrap.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/LetUnwrap.res` narrowed materially:
  the old `switch (s)` / `switch (x.TAG)` / `typeof x === "object"` scaffolding
  is gone from the result/option unwrap path, and the remaining drift has moved
  on to later backend or printer shaping such as branch polarity, compact object
  literal layout, and statement-vs-expression byte shape
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the small-case switch change, which confirms this `lam_compile` slice does
  not perturb the already-stable external-shadow path
- The authoritative JS snapshot baseline remains **130 / 657** passing,
  **0** compile errors, and **527** output diffs after this OCaml-aligned
  small-case string-switch / named-variant dispatch fix; the change is kept
  because it removes a real backend lowering gap even though the checked-in
  corpus total stays flat

- `compiler-rust/src/lambda/simplify.rs` now matches one more slice of
  OCaml `core/lam_pass_alpha_conversion.ml` /
  `core/lam_pass_lets_dce.ml` more closely on the Rust JS path:
  `Pjs_fn_make` wrappers are no longer erased globally during the
  JS-backend simplifier; instead, let-bound wrapped local functions still feed
  the existing local beta-reduction path, while direct `Pjs_fn_make`
  applications remain visible to later backend/codegen stages
- Added focused coverage for this slice in
  `unwraps_pjs_fn_make_bindings_before_beta_reducing_local_calls` and
  `keeps_direct_pjs_fn_make_applications_for_backend_codegen`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release pjs_fn_make -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release one_unit_arg -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ../../../../compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/gpr_1692_test.ast -o /tmp/gpr_1692_test.mjs`
  - `timeout 10 ../../../../compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/PartialApplicationNoRuntimeCurry.ast -o /tmp/PartialApplicationNoRuntimeCurry.mjs`
  - `timeout 10 ../../../../compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/ExternalShadow.ast -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/gpr_1692_test.res` narrowed materially:
  the old empty-module output is gone, and the remaining drift is now a single
  extra dead wrapper application (`(x => (f => 0))("")("")`) instead of the
  earlier full elision of the top-level call
- `tests/tests/src/PartialApplicationNoRuntimeCurry.res` remains an exact
  checked-in snapshot match after narrowing the `Pjs_fn_make` simplifier rule
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same change
- The authoritative JS snapshot baseline now reports **129 / 657** passing,
  **0** compile errors, and **528** output diffs after this OCaml-aligned
  `Pjs_fn_make` narrowing change; the local total regresses by one snapshot,
  but the change is kept because the previous global unwrap was erasing a
  backend-visible wrapper structure that OCaml still preserves

- `compiler-rust/src/lambda/compile.rs` now matches the OCaml
  `core/lam_compile.ml` `compile_ifthenelse` `EffectCall Not_tail` path more
  closely on the Rust JS backend:
  effect-context `LifThenElse` nodes no longer fall through the generic
  expression compiler and manufacture synthetic `let ifres` temporaries;
  instead, Rust now drops pure branch results, keeps direct effect-only `if`
  statements when one branch is pure, and preserves the conditional-expression
  form when both branches are effectful and statement-free, just as OCaml's
  continuation-sensitive split does
- Added focused coverage for this slice in
  `effect_blocks_lower_ifs_without_a_result_temp` and
  `effect_blocks_keep_conditional_expressions_when_both_branches_are_effectful`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release effect_blocks_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_4491_test.res -o /tmp/gpr_4491_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/gpr_4491_test.res` narrowed materially:
  the synthetic `let ifres` result temporary is gone, and the file now differs
  only on the still-missing OCaml empty `else {}` byte shape instead of
  backend continuation lowering
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the effect-context `if` change
- the cached `let ifres` diff motif collapsed from **59** files to **37**
  files after the authoritative rerun, which confirms this was a broad
  continuation-context backend gap rather than a local snapshot accident
- The authoritative JS snapshot baseline remains **130 / 657** passing,
  **0** compile errors, and **527** output diffs after this OCaml-aligned
  effect-context `if` lowering fix; the change is kept because it materially
  reduces a real backend drift cluster even though the checked-in corpus total
  stays flat

- `compiler-rust/src/lambda/compile.rs` now matches one more slice of
  OCaml `core/lam_compile.ml` on the Rust JS path:
  named variant switches no longer drop payload-carrying `sw_blocks` during
  JS lowering, and the backend now splits ordinary named variants the same way
  OCaml does between non-object constructor cases and object `TAG` cases across
  value, return, and effect continuations
- Added focused coverage for this slice in
  `named_variant_switch_expressions_split_const_and_block_dispatch` and
  `named_variant_effect_switches_keep_payload_cases`
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release named_variant -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/NondetPatterMatch.res -o /tmp/NondetPatterMatch.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/variant.res -o /tmp/variant.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/NondetPatterMatch.res` narrowed materially:
  the missing payload-constructor branch is gone, and the file now differs only
  on later case-grouping / byte-shape cleanup instead of dropping the switch
  body entirely
- `tests/tests/src/variant.res` also narrowed materially:
  ordinary named constructors no longer compile through raw integer switches,
  and the remaining drift is now later backend shaping around grouped cases,
  exception/runtime lowering, and other downstream gaps rather than this switch
  routing failure
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the named-switch change
- The authoritative JS snapshot baseline remains **123 / 657** passing,
  **0** compile errors, and **534** output diffs after this OCaml-aligned
  named-variant switch fix
- Interpretation:
  this is a real OCaml backend improvement in the `Lam_compile.compile_switch`
  stage. It removes one major structural backend bug by restoring named payload
  switch lowering on the JS path, but the current corpus still needs the later
  OCaml case-grouping and printer cleanup that collapse duplicated `case`
  bodies into the exact checked-in snapshot shape.

- `compiler-rust/src/lambda/compile.rs` now matches one more slice of
  OCaml `core/lam_compile_main.ml` / `core/lam_module_ident.ml` /
  `ext/ext_string.ml` on the Rust JS path:
  required modules are now sorted by `Lam_module_ident.name` using OCaml's
  length-first `Ext_string.compare` semantics rather than the Rust local
  identifier name
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release sorts_ -- --test-threads=1`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalArity.res -o /tmp/ExternalArity.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/reactTestUtils.res -o /tmp/reactTestUtils.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/ExternalArity.res` dropped out of the diff set after the
  sort fix; its import block now matches the checked-in snapshot exactly
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the change
- `tests/tests/src/reactTestUtils.res` still fails, but the remaining drift
  stays on unrelated backend shaping rather than module order
- The authoritative JS snapshot baseline now reports **123 / 657** passing,
  **0** compile errors, and **534** output diffs.
- Interpretation:
  this is a real OCaml backend parity improvement in the deps-program import
  ordering stage. The first attempt exposed that OCaml's comparator is not a
  plain lexical compare; matching the actual `Ext_string.compare`
  implementation resolves the `ExternalArity.res` import-order drift without
  regressing mixed `Mocha` / local-module snapshots.

- `compiler-rust/src/lambda/compile.rs`,
  `compiler-rust/src/js_ir/mod.rs`, and
  `compiler-rust/src/cmi/persistent_env.rs` now match one more slice of
  OCaml `core/lam_stats_export.ml` / `lam_compile_env.ml` on the Rust JS path:
  after JS-pass lowering collects required modules, Rust no longer treats a
  pure top-level lambda body as sufficient for `/* No side effect */`;
  it now falls back to the first required module that is not pure, using
  runtime modules as pure, external modules as impure, and `.cmj` metadata for
  ML modules
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release required_module_effect_reason_uses_external_module_name -- --test-threads=1`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release pure_ml_dependencies_do_not_mark_module_impure -- --test-threads=1`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release impure_ml_dependencies_use_module_name_as_effect_reason -- --test-threads=1`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gentTypeReTest.res -o /tmp/gentTypeReTest.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/reactTestUtils.res -o /tmp/reactTestUtils.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/gentTypeReTest.res` and `tests/tests/src/test_utils.res`
  both dropped out of the diff set after the purity-fallback change
- `tests/tests/src/reactTestUtils.res` still fails, but its diff no longer
  includes the final purity trailer; the remaining hunks are earlier backend
  mismatches
- The authoritative JS snapshot baseline now reports **108 / 657** passing,
  **0** compile errors, and **549** output diffs.
- Interpretation:
  this is a real OCaml backend parity improvement in deps-program purity
  reporting. It resolves the missing required-module fallback without touching
  printer-only string rewrites, and it leaves the remaining import/callback
  lowering gaps visible for later passes.

- `compiler-rust/src/js_ir/printer.rs` now matches one more slice of
  OCaml `core/js_dump.ml` more closely on the Rust JS-output path:
  record-like and module-like `Caml_block` variants (`Blk_record`,
  `Blk_record_inlined`, `Blk_record_ext`, and `Blk_module`) no longer use
  bespoke compact brace printing in Rust; they now flow through the shared
  object-literal emitter, which mirrors OCaml's `Caml_block -> Object (...)`
  rewrite before dumping
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_record_omits_optional_undefined_fields -- --test-threads=1`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_module_block_uses_object_layout -- --test-threads=1`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/EmptyRecord.res -o /tmp/EmptyRecord.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/EnvUnifiedOps.res -o /tmp/EnvUnifiedOps.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/VariantSpreads.res -o /tmp/VariantSpreads.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DerivingAccessorsCurried.res -o /tmp/DerivingAccessorsCurried.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/EmptyRecord.res` and `tests/tests/src/EnvUnifiedOps.res`
  now both match their checked-in snapshots exactly after the object-layout
  change
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the change, which confirms this printer slice does not perturb the already
  resolved external-shadow/import behavior
- `tests/tests/src/VariantSpreads.res` narrowed materially:
  record/module object literals now use the correct multi-line layout, and the
  remaining drift is later constructor-object formatting plus missing backend
  tag shaping on `q`
- `tests/tests/src/DerivingAccessorsCurried.res` narrowed materially in the
  same way:
  record/module object layout is now aligned, and the remaining drift is later
  constructor-object formatting and declaration ordering rather than this
  printer slice
- The authoritative JS snapshot baseline now reports **106 / 657** passing,
  **0** compile errors, and **551** output diffs.
- Interpretation:
  this is a real OCaml `js_dump` parity improvement on the final printer path.
  It resolves one high-volume object-layout motif without hiding the remaining
  constructor-specific and backend-shaping gaps that still need later passes.

- `compiler-rust/src/lambda/compile.rs` now matches OCaml
  `lam_compile_const.ml` more closely for constructor-tagged integer
  constants on the JS backend path:
  `Const_int` values carrying `Pt_constructor` metadata no longer drop that
  metadata when Rust lowers them into JS IR, so named nullary constructors now
  emit their constructor runtime representation (`"NoParam"`, `@as("...")`,
  `@as(null)`, etc.) instead of falling back to raw numeric tags
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::compile::tests::compile_constant_ -- --test-threads=1`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DerivingAccessorsCurried.res -o /tmp/DerivingAccessorsCurried.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DerivingAccessorsUncurried.res -o /tmp/DerivingAccessorsUncurried.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/VariantSpreads.res -o /tmp/VariantSpreads.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/DerivingAccessorsCurried.res` and
  `tests/tests/src/DerivingAccessorsUncurried.res` both moved off the wrong
  constant-constructor runtime shape:
  `noParam` and `_noParamAlias` now emit `"NoParam"` instead of `0`, so the
  remaining drift in those files is later declaration ordering and printer byte
  shape rather than this constructor-representation mismatch
- `tests/tests/src/VariantSpreads.res` also moved forward on the same slice:
  constant constructors such as `"Two"` / `"Six"` no longer fall back to `0`,
  and the remaining drift there is now in later block/object lowering and final
  printer shape
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the constant-constructor change, which confirms this slice stays isolated to
  constructor-constant translation rather than perturbing external/global
  lowering
- The authoritative JS snapshot baseline remains **90 / 657** passing, **0**
  compile errors, and **567** output diffs after the `lam_compile_const` port
- Interpretation:
  this resolves one real backend gap between optimized lambda and final JS
  emission even though the wrapper totals stayed flat. The unchanged totals mean
  the affected files still carry later backend / printer drift, not that the
  constructor-constant fix was spurious.

- `compiler-rust/src/lambda/compile.rs` now matches one more slice of
  OCaml `lam_coercion.ml` / `handle_exports` on the Rust JS backend path:
  final export selection follows same-name alias bindings only when the target
  is another declared top-level binding, which reuses real local bindings like
  OCaml's `Lvar`/same-name export case without collapsing aliases that preserve
  unbound-global shadowing behavior
- Verified focused guards for this cluster:
  - `RUSTFLAGS='-Awarnings' timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::compile::tests::compile_deps_program -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DerivingAccessorsCurried.res -o /tmp/DerivingAccessorsCurried.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DerivingAccessorsUncurried.res -o /tmp/DerivingAccessorsUncurried.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/DerivingAccessorsCurried.res` narrowed materially again:
  the redundant exported alias layer is gone, so the remaining drift is now the
  later constant-constructor representation / printer-shape slice rather than
  this earlier rebound-export mismatch
- `tests/tests/src/DerivingAccessorsUncurried.res` narrowed in the same way:
  the export block now reuses the real local bindings, and the remaining hunk
  is the later constructor/printer slice instead of alias/export churn
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  narrowing the rule to declared bindings only, which confirms the export
  remap does not break the `parseInt` global-shadowing case
- The authoritative JS snapshot baseline now reports **90 / 657** passing, **0**
  compile errors, and **567** output diffs.
- Interpretation:
  this resolves one more real post-lowering export/coercion gap on the Rust JS
  path and moves the remaining `DerivingAccessors*` drift fully past redundant
  rebound exports. The next signal in that cluster is the constant-constructor
  runtime representation and final printer byte shape, not export-id selection.

- `compiler-rust/src/lambda/simplify.rs` now ports the OCaml
  `lam_pass_deep_flatten.ml` named immutable-module-block rule onto the Rust
  JS backend path:
  lowered `match` / `include` / `param` bindings that build immutable module
  blocks are flattened back into projected field bindings before the existing
  JS-path simplifier runs, so later beta-reduction and alias cleanup see the
  same shape OCaml produces instead of getting stuck behind nested block churn
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::simplify::tests::deep_flattens_nested_include_blocks_before_beta_reducing_field_accessors -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::simplify::tests::flattens_immutable_module_block_field_aliases -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DerivingAccessorsCurried.res -o /tmp/DerivingAccessorsCurried.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DerivingAccessorsUncurried.res -o /tmp/DerivingAccessorsUncurried.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/DerivingAccessorsCurried.res` narrowed materially:
  the nested `include`-module block wrappers are gone, and the remaining drift
  is now one later-stage hunk around alias/export naming and final literal byte
  shape instead of this earlier backend-shaping mismatch.
- `tests/tests/src/DerivingAccessorsUncurried.res` narrowed materially in the
  same way:
  one remaining later-stage hunk is left after the nested immutable module
  block churn was flattened out of the lowered lambda.
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the deep-flatten change.
- The authoritative JS snapshot baseline now reports **89 / 657** passing, **0**
  compile errors, and **568** output diffs.
- Interpretation:
  this resolves one real OCaml backend-pass gap after lowering and moves the
  current accessors cluster forward without reopening earlier frontend or
  lambda-parity stages. The next signal in `DerivingAccessors*.res`,
  `Coercion.res`, and `ExternalArity.res` is now later alias/export shaping and
  final byte-shape cleanup, not the old nested immutable module-block shape.

- `compiler-rust/src/driver.rs` and `compiler-rust/src/js_ir/printer.rs` now
  port the OCaml file-directive path from `frontend/ast_config.ml` and
  `core/js_dump_program.ml`:
  top-level `@@directive("...")` attributes are collected from the parsed
  structure in source order and emitted before the version header in deps
  program output
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release driver::tests::extract_file_directives_preserves_source_order -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_deps_program_emits_top_level_directives_before_header -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/directives.res -o /tmp/directives.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- `tests/tests/src/directives.res` is now an exact snapshot match.
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the file-directive change.
- The authoritative JS snapshot baseline now reports **88 / 657** passing, **0**
  compile errors, and **569** output diffs.
- Interpretation:
  this resolves one remaining printer/metadata gap without touching later
  backend shaping. The next frontier is still in the larger backend-shaping
  clusters such as `Coercion.res`, `DerivingAccessors*.res`, and
  `ExternalArity.res`, not in top-level file directive emission.

- `compiler-rust/src/lambda/simplify.rs` now matches the OCaml JS backend path
  more closely for lowered function wrappers:
  `Pjs_fn_make` / `Pjs_fn_make_unit` are treated as transparent on the JS path,
  so local inlineable functions wrapped by those primitives re-enter the
  existing beta-reduction logic instead of leaking through to emitted JS as
  avoidable direct calls
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release unwraps_pjs_fn_make_bindings_before_beta_reducing_local_calls -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release inlines_known_local_function_applications -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/PartialApplicationNoRuntimeCurry.res -o /tmp/PartialApplicationNoRuntimeCurry.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UncurriedAlways.res -o /tmp/UncurriedAlways.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- `tests/tests/src/PartialApplicationNoRuntimeCurry.res` is now an exact
  snapshot match.
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the simplifier change.
- `tests/tests/src/UncurriedAlways.res` narrowed materially:
  direct wrapper calls through lowered `Pjs_fn_make` bindings are now reduced,
  and the remaining drift there is in later backend shaping and printer output
  rather than this function-wrapper slice.
- The authoritative JS snapshot baseline now reports **87 / 657** passing, **0**
  compile errors, and **570** output diffs.
- Interpretation:
  the remaining broad partial-application / wrapper-call cluster is not blocked
  on the release binary seeing through lowered `Pjs_fn_make` wrappers anymore.
  The next signal in files like `UncurriedAlways.res`, `bench.res`, and
  `ExternalArity.res` has shifted to later backend shaping after this
  simplifier slice, not to the old transparent-wrapper gap itself.

- `compiler-rust/src/lambda/compile.rs` now ports the OCaml
  `Js_shake.shake_program` top-level dead-code-elimination pass onto the Rust
  JS backend path after the existing `js_pass_flatten` /
  `js_pass_external_shadow` stages.
- The Rust pass now matches the OCaml `js_shake.ml` fixed-point shape for this
  slice:
  it flattens top-level blocks, computes the required identifier set from
  exports plus effectful statements, keeps transitive dependencies of exported
  bindings, and drops top-level pure unused statements / bindings while keeping
  impure initializers.
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_shake_pass_removes_unused_pure_toplevel_bindings_and_statements -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_shake_pass_keeps_export_dependencies_and_impure_bindings -- --nocapture`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/inner_unused.res -o /tmp/inner_unused.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the shake pass.
- `tests/tests/src/inner_unused.res` remains on the same small local
  byte-shape drift (`let f` vs `let f$1` / object-literal formatting), which
  confirms that this pass is not the active frontier for that file.
- The authoritative JS snapshot baseline remains **85 / 657** passing, **0**
  compile errors, and **572** output diffs after the `Js_shake` port.
- Interpretation:
  this verifies the OCaml-aligned top-level shake stage itself without
  regression, but it also shows that the current checked-in snapshot corpus is
  still bottlenecked earlier in the missing JS-pass pipeline. The next backend
  signal remains the pre-shake stages, especially
  `Js_pass_flatten_and_mark_dead` and `Js_pass_tailcall_inline`, not printer
  work.

- `compiler-rust/src/lambda/compile.rs` now matches the OCaml
  `lam_compile.ml` static-catch and continuation-sensitive switch lowering more
  closely on the Rust JS backend path:
  `LstaticCatch` handlers are threaded through expression, declaration,
  effect-block, and return-block lowering, and nested `Llet` values now preserve
  declaration / effect / return context when they eventually lower into
  `Lswitch` or `LstringSwitch`
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release staticcatch_wrapped_string_switches_use_the_handler_as_the_default_value -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release nested_let_values_preserve_declaration_context_for_wrapped_string_switches -- --nocapture`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_string_switch.res -o /tmp/test_string_switch.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/complete_parmatch_test.res -o /tmp/complete_parmatch_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- `tests/tests/src/test_string_switch.res` is no longer on the old backend
  temp-result path:
  Rust now emits the same direct `let version; switch (...) { version = ... }`
  structure as OCaml, and the remaining drift there is printer-only
  (`case "darwin":` spacing and the final purity-trailer name)
- `tests/tests/src/complete_parmatch_test.res` also moved off the old backend
  fallback path:
  it now lowers as a direct return-position switch, and its remaining drift is
  printer-only around character comments and `case` spacing
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the static-catch / continuation changes
- The authoritative JS snapshot baseline now reports **85 / 657** passing, **0**
  compile errors, and **572** output diffs.
- Interpretation:
  this confirms the remaining drift in the focused switch/static-catch cluster
  is no longer missing backend control-flow lowering in `lam_compile`; the next
  frontier on those files is printer byte-shape parity, while broader backend
  work still remains elsewhere in the 572-file diff set

- `compiler-rust/src/lambda/compile.rs` now matches the OCaml
  `lam_compile.ml` switch/result continuation shape more closely for the
  baseline Rust backend path:
  value-producing `Lswitch` and `LstringSwitch` branches now compile each case
  and default body in assign-to-temp style instead of pure effect style, so
  branch results are written into the switch temporary before `break`
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release int_switch_expressions_assign_branch_values_into_the_result_temp -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release string_switch_expressions_assign_branch_values_into_the_result_temp -- --nocapture`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_string_switch.res -o /tmp/test_string_switch.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/stringmatch_test.res -o /tmp/stringmatch_test.mjs`
- `tests/tests/src/test_string_switch.res` and
  `tests/tests/src/stringmatch_test.res` now emit explicit per-branch
  `$$switch = ...;` assignments instead of leaving the switch result temporary
  uninitialized through each case body
- The authoritative JS snapshot baseline remains **84 / 657** passing, **0**
  compile errors, and **573** output diffs after this OCaml-aligned switch-temp
  assignment fix
- Interpretation:
  this confirms the remaining switch-heavy drift is not just missing
  assign-context lowering in `lam_compile`; the current frontier in those files
  has moved outward to earlier pattern-match/default lowering and later cleanup
  of unreachable `throw undefined` / dead assignment noise
- `compiler-rust/src/lambda/compile.rs` now ports the OCaml
  `js_pass_flatten.ml` stage and runs it before the existing
  `external_shadow` pass on the Rust JS backend path.
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_flatten_pass -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release flattens_value_sequences_back_to_effect_statements_at_toplevel -- --nocapture`
  - `tests/tests/src/gpr_1946_test.res` now lowers Mocha callback bodies as
    statement blocks instead of giant comma expressions, though it still drifts
    on earlier missing record / object lowering and later dead-statement cleanup
  - `tests/tests/src/list_test.res` now lowers the `Mocha.describe` callback as
    a block with explicit statements instead of one giant comma expression, but
    it still needs later-pass cleanup and other backend fixes
  - `tests/tests/src/ExternalShadow.res` still matches its checked-in `.mjs`
    snapshot exactly after the pass ordering change
- The authoritative JS snapshot baseline now reports **82 / 657** passing, **0**
  compile errors, and **575** output diffs.
- The old `, undefined,` diff motif dropped from **185** files to **56** after
  the flatten pass; the newly-exposed frontier is dead-statement cleanup, with
  explicit `undefined;` statements now visible in **270** failing diff files.
- `compiler-rust/src/lambda/compile.rs` now ports the OCaml `Pimport`
  lambda-stage special-case for eta-expanded externals instead of trying to
  recover the pattern from compiled JS:
  when the dynamic-import argument is a single-argument function whose body is a
  `Pjs_call` (or that call followed by `undefined`), Rust now recompiles the
  body with `dynamic_import = true` and then lowers it through the same module
  path used for direct module values.
- `compiler-rust/src/js_ir/printer.rs` now matches the OCaml property-access
  printer for the `default` keyword:
  `Es6_export.default` stays a dot-access expression instead of drifting to
  `Es6_export["default"]`.
- Verified focused guards for this cluster:
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release dynamic_imports -- --nocapture`
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_property_access_uses_dot_for_default_keyword -- --nocapture`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/module_as_function.res -o /tmp/module_as_function.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/import_external.res -o /tmp/import_external.mjs`
- `tests/tests/src/module_as_function.res` and
  `tests/tests/src/import_external.res` now both match their checked-in `.mjs`
  snapshots exactly.
- The authoritative JS snapshot baseline now reports **79 / 657** passing, **0**
  compile errors, and **578** output diffs.
- `compiler-rust/src/js_ir/printer.rs` now matches the OCaml declaration-printing
  path for undefined-initialized bindings:
  when the lowered JS IR carries `Some(undefined)` for a variable declaration,
  the emitted JS now prints a bare declaration (`let x;`) instead of an
  explicit undefined initializer.
- Verified focused guards for this cluster:
  - `cargo test --manifest-path compiler-rust/Cargo.toml test_print_variable_declaration_omits_undefined_initializer -- --nocapture`
  - `cargo test --manifest-path compiler-rust/Cargo.toml test_print_deps_program_omits_undefined_initializer -- --nocapture`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ModuleWithAlias.res -o /tmp/ModuleWithAlias.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/keep_uncurry_attribute.res -o /tmp/keep_uncurry_attribute.mjs`
- `tests/tests/src/ModuleWithAlias.res` now matches its checked-in `.mjs`
  snapshot exactly, and the remaining `= undefined;` declaration motif in
  cached JS diffs dropped from **182** files to **108** files after the printer
  change.
- The authoritative JS snapshot baseline now reports **75 / 657** passing, **0**
  compile errors, and **582** output diffs.
- A dedicated wrapper script now exists at `scripts/test_js_output_parity.sh`.
- The wrapper keeps Spice enabled by default, but the authoritative runs still skip the Spice guard in this environment because the configured external `SPICE_PPX` binary is missing.
- The existing JS-output parity check already lived inside `scripts/test_rust_parity.sh`; the wrapper now exposes that section directly.
- `compiler-rust/src/driver.rs` now routes final JS generation through `raw_lambda::convert` + `raw_lambda::lower` instead of the legacy `lambda::convert::LambdaConverter` shortcut.
- `scripts/test_rust_parity.sh` now compiles JS snapshots with each file's owning ReScript project's `compiler-args` and runs `bsc` from that project's `lib/bs`.
- `compiler-rust/src/driver.rs` now normalizes CLI `-I` load-path entries against the current working directory and expands `+stdlib`-relative includes before building the persistent load path, matching the wrapper's per-project `lib/bs` invocation model.
- `compiler-rust/src/bin/bsc.rs` now enables a CLI-only post-emit fast-exit path so short-lived snapshot runs do not spend the harness timeout tearing down large typechecking arenas after the JS output is already produced.
- The former `tests/tests/src/Import.res` compile-error guard now completes under the measured wrapper invocation and has moved into the normal output-diff cluster.
- The canonical in-repo wrapper baseline now reports **29 / 657** passing, **0** compile errors, and **628** output diffs.
- A printer/module-emission pass is now wired through `DepsProgram` metadata in Rust:
  - recover `program.exports` from the lowered `module/exports` block instead of printing a trailing array
  - print the ReScript version header, ES module export block, and module purity trailer
  - print top-level function-valued bindings as function declarations
  - mangle local JS-reserved identifiers (`arguments`, `eval`, `exports`, `parseInt`, etc.) in emitted bindings
  - treat `TagInfo::Module` blocks as JS objects instead of arrays
  - lower `PjsFnMake`, `PjsFnMakeUnit`, and `PjsFnMethod` instead of dropping them to `undefined`
- Verified focused checks under the new project-context invocation:
  - `tests/tests/src/keep_uncurry_attribute.res` now matches its checked-in `.mjs` snapshot exactly
  - `tests/tests/src/ident_mangles.res` now matches its checked-in `.mjs` snapshot exactly
  - `tests/tests/src/ExternalShadow.res` now matches its checked-in `.mjs` snapshot exactly
- `compiler-rust/src/raw_lambda/convert.rs` and `compiler-rust/src/lambda/convert.rs` now preserve OCaml external-spec shape inside `PjsCall` instead of collapsing it to a lossy `prim_name` summary.
- `compiler-rust/src/lambda/compile.rs` now lowers preserved no-module external specs with OCaml-aligned JS semantics for:
  - `Js_var` value vs call
  - `Js_new`
  - `Js_get` / `Js_set`
  - `Js_get_index` / `Js_set_index`
  - `Js_send`
- `compiler-rust/src/lambda/convert.rs`, `compiler-rust/src/raw_lambda/convert.rs`, and `compiler-rust/src/raw_lambda/lower.rs` now preserve and route the OCaml external-object metadata needed for `@obj` lowering instead of collapsing it to a boolean/object-create hint.
- `compiler-rust/src/lambda/compile.rs` now lowers marshaled external argument constants and `PjsObjectCreate` fields directly from preserved FFI metadata, matching the OCaml backend's handling of `@as(...)` and `@obj`.
- Focused guards for this cluster:
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release --lib lowers_js_object_create_with_marshaled_fields`
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release --lib blank_js_call_to_object_create`
- The authoritative JS snapshot baseline now reports **39 / 657** passing, **0** compile errors, and **618** output diffs.
- `tests/tests/src/AsInUncurriedExternals.res` and `tests/tests/src/UncurriedExternals.res` both narrowed after the metadata port; the remaining drift in those files has moved on to later-pass/backend cleanup rather than missing `@as` / `@obj` lowering.
- `compiler-rust/src/lambda/compile.rs` now applies a port of `js_pass_external_shadow.ml`, so lexical shadowing of JS globals rewrites initializer/self-property reads through `globalThis` without rewriting unrelated uses like `parseInt`.
- `compiler-rust/src/js_ir/printer.rs` no longer reorders top-level function-valued bindings ahead of earlier statements; the Rust printer now preserves OCaml's block order.
- Typedtree parity and both lambda parity stages are considered complete for this project and are not part of the remaining frontier.
- `compiler-rust/src/js_ir/mod.rs`, `compiler-rust/src/lambda/compile.rs`, and `compiler-rust/src/js_ir/printer.rs` now carry OCaml-aligned module dependency metadata into `DepsProgram`, resolve runtime and local module ids to emitted JS paths, and lower `Pimport` to `import("...")` / `import("...").then(m => m.member)` instead of calling `import` on a qualified identifier.
- `compiler-rust/src/cmi/persistent_env.rs` now resolves sibling `.ast` / `.iast` metadata back to the original source file, which lets the JS backend recover relative local import paths like `./ModuleWithAlias.mjs`.
- Verified focused guards for this cluster:
  - `tests/tests/src/Import.res` now emits the correct static `Js_promise` import and correct dynamic `Belt_List` string paths; the remaining drift is later-stage backend shaping, not dependency-path lowering.
  - `tests/tests/src/DynamicImportModuleWithAlias.res` now emits `await import("./ModuleWithAlias.mjs")`; the remaining drift is the missing integer coercion in `return Utils.x + z | 0`.
- `compiler-rust/src/lambda/compile.rs` now ports the OCaml `E.int32_*` lowering for the primitives that were still using plain JS arithmetic or falling through to `undefined` on the JS backend path:
  - `Paddint`, `Psubint`, `Pmulint`, `Pdivint`, `Ppowint`, `Pnegint`
  - `Pandint`, `Porint`, `Pxorint`, `Pnotint`
  - `Plslint`, `Plsrint`, `Pasrint`
  - `Poffsetint`, `Pintoffloat`, `Pfloatofint`, `Pboolcomp`
- Verified focused guards for this cluster:
  - `tests/tests/src/DynamicImportModuleWithAlias.res` now matches its checked-in `.mjs` snapshot exactly.
  - `tests/tests/src/Import.res` still differs, but the dynamic-import path and int coercion route are no longer the active blocker there; the remaining drift is later-stage list/object/let shaping.
- `compiler-rust/src/lambda/simplify.rs` now ports a small OCaml-aligned subset
  of the post-lowering lambda cleanup used on the JS backend path:
  - inline obvious local `Lfunction` applications with the existing
    `lfunction_can_be_inlined` / beta-reduction utilities
  - remove dead pure lets and keep dead impure lets only as sequences
- `compiler-rust/src/lambda/compile.rs` now runs that simplifier before JS IR
  lowering and before computing the module side-effect reason, so the emitted JS
  path sees the same reduced lambda shape the OCaml backend expects at this
  stage.
- Focused guards for this cluster:
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::simplify::tests::inlines_known_local_function_applications --lib`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/AsInUncurriedExternals.res -o /tmp/AsInUncurriedExternals.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/Import.res -o /tmp/Import.mjs`
- The authoritative JS snapshot baseline now reports **46 / 657** passing, **0**
  compile errors, and **611** output diffs.
- `tests/tests/src/AsInUncurriedExternals.res` now matches its checked-in `.mjs`
  snapshot exactly.
- `tests/tests/src/Import.res` still differs, but the dead `let = undefined`
  churn is materially reduced; the remaining drift is still in later lambda/JS
  backend shaping.
- `compiler-rust/src/lambda/simplify.rs` now ports another OCaml-aligned subset
  of `Lam_pass_lets_dce` used on the JS backend path:
  - collect exported ids from the module-export block so exported bindings are
    preserved even when later substitution makes them look locally unused
  - substitute simple lowered-lambda aliases (`Lvar`, constants, and module
    field aliases) through the body instead of emitting long JS alias chains
  - drop pure `Lsequence` noise, which removes dead top-level coercion helper
    lambdas like the ones in `tests/tests/src/RecordCoercion.res`
  - fold constant `Pstringadd` chains after alias substitution
- Verified focused guards for this cluster:
  - `tests/tests/src/Coercion.res` now emits `let xx = 1;`; the remaining drift
    there is later backend shaping/order, not the alias value itself
  - `tests/tests/src/RecordCoercion.res` no longer emits the three dead
    top-level identity functions; the remaining drift is object/record shaping
  - previously passing `tests/tests/src/ExternalShadow.res` and
    `tests/tests/src/keep_uncurry_attribute.res` still match exactly
- The authoritative JS snapshot baseline now reports **49 / 657** passing, **0**
  compile errors, and **608** output diffs.
- A follow-up authoritative wrapper rerun after tightening allocating-constant
  substitution remained **49 / 657** passing, **0** compile errors, and **608**
  output diffs.
- `compiler-rust/src/lambda/simplify.rs` now keeps allocating `Lconst` values
  shared instead of substituting them through later `let` bindings on the JS
  backend path, matching the OCaml `Lam_pass_lets_dce` distinction between
  scalar constants and allocating blocks.
- Verified focused guards for this cluster:
  - `cargo test --manifest-path compiler-rust/Cargo.toml lambda::simplify::tests::keeps_allocating_constant_bindings_shared --lib`
  - `cargo test --manifest-path compiler-rust/Cargo.toml lambda::simplify::tests::keeps_exported_alias_binding_but_inlines_constant_rhs --lib`
  - `tests/tests/src/keep_uncurry_attribute.res` still matches its checked-in
    `.mjs` snapshot exactly
- `tests/tests/src/RecordCoercion.res` now keeps the shared record binding
  shape (`let a = ...; let name = a.name; ...`) instead of duplicating the same
  record literal into both the projected field and the exported module record;
  the remaining drift there is the later coercion/grouping naming shape
  (`TestInlining_a` / direct `"a"` propagation), not duplicated allocation.
- `compiler-rust/src/lambda/simplify.rs` now ports another OCaml-aligned slice
  of `Lam_pass_collect` + `Lam_pass_remove_alias`:
  - immutable block bindings created from both `Pmakeblock` and constant
    `Lconst` blocks are tracked in the JS-backend simplifier environment
  - `Pfield` over those tracked immutable blocks now resolves by named field
    metadata when available, matching OCaml's `field_flatten_get` behavior for
    records, inlined records, record extensions, and modules
  - direct `Pfield` reads from constant blocks now also fold non-allocating
    fields by name instead of trusting the raw numeric index
- Verified focused guards for this cluster:
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::simplify::tests::flattens_immutable_module_block_field_aliases --lib`
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::simplify::tests::flattens_record_field_aliases_by_name --lib`
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::simplify::tests::flattens_constant_record_block_bindings_by_name --lib`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/RecordCoercion.res -o /tmp/RecordCoercion.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- `compiler-rust/src/types/typecore.rs` now keeps `LabelDescription.lbl_optional`
  intact for optional record fields after wrapping them in `Some(...)` and after
  synthesizing omitted optional fields as `None`, matching OCaml's
  `typecore.ml` behavior. The JS backend can now still see which record fields
  are optional after type checking instead of treating them as required fields
  with explicit `undefined` values.
- `compiler-rust/src/js_ir/printer.rs` now matches the corresponding OCaml
  `js_dump.ml` record-dump rules more closely:
  - optional record and inlined-record fields with `undefined` values are
    omitted from printed object literals
  - numeric-name records dump with array syntax instead of object-property
    syntax
- Verified focused guards for this cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_record_omits_optional_undefined_fields -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_numeric_named_record_as_array -- --exact`
  - `tests/tests/src/RecordOrObject.res` now emits `let xxi = {x: 10};` instead
    of `let xxi = {x: 10, i: undefined};`; the remaining drift there is printer
    formatting only
  - `tests/tests/src/EmptyRecord.res` now emits `return b ? {n: 0} : {};`
    instead of `return b ? {n: 0, s: undefined} : {};`; the remaining drift
    there is later control-flow / formatting shaping, not optional-field
    presence
  - previously exact `tests/tests/src/ExternalShadow.res` still matches its
    checked-in `.mjs` snapshot exactly
- A follow-up authoritative wrapper rerun after the optional-record metadata fix
  remained **70 / 657** passing, **0** compile errors, and **587** output
  diffs. This change is still verified OCaml-aligned because it moves the
  affected files in the correct direction without regressing the global
  baseline.
- `compiler-rust/src/lambda/compile.rs` now lowers the OCaml option-wrapper
  primitive family on the JS backend path instead of dropping those cases to
  `undefined`:
  - `Psome`
  - `PsomeNotNest`
  - `PvalFromOption`
  - `PvalFromOptionNotNest`
  - `PnullToOpt`
  - `PnullUndefinedToOpt`
  - `PisNotNone`
- Verified focused guards for this cluster:
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_psome_not_nest_to_identity_optional_block --lib`
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_pval_from_option_optional_block_to_inner_value --lib`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/Equality_over_optimization.res -o /tmp/Equality_over_optimization.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- `tests/tests/src/Equality_over_optimization.res` now keeps the option payload
  shape (`[undefined]`) instead of collapsing the whole `Some` branch to bare
  `undefined`; the remaining drift there is now the still-missing
  continuation-sensitive sequence lowering for `(console.log("hello"), undefined)`.
- A follow-up authoritative wrapper rerun after the option-wrapper port remained
  **70 / 657** passing, **0** compile errors, and **587** output diffs.
- A follow-up authoritative wrapper rerun after the immutable-block field
  flattening slice remained **49 / 657** passing, **0** compile errors, and
  **608** output diffs.
- `tests/tests/src/RecordCoercion.res` now folds the projected record field to
  the direct string constant (`name: "a"`), so the active blocker there has
  narrowed further to the later JS/backend naming/lifting shape
  (`TestInlining_a` / grouped export emission).
- `tests/tests/src/DerivingAccessorsCurried.res` did not materially move yet;
  the remaining include-chain drift still needs a later OCaml-aligned step that
  can see through let-wrapped module blocks, not just directly bound immutable
  blocks.
- `compiler-rust/src/js_ir/printer.rs` now ports two OCaml-aligned
  `js_dump_program.ml` behaviors on the Rust JS-output path:
  - `deps_program_is_empty` now emits OCaml's checked-in empty-output
    explanation instead of falling through to the generic no-side-effect trailer
  - module-level spacing now matches the OCaml dump shape for the affected
    snapshot cluster:
    import-free non-empty modules keep the extra blank line after the header,
    and ES-module imports keep the blank line before the first statement
- Verified focused guards for this printer cluster:
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_deps_program --lib`
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_empty_deps_program_uses_ocaml_empty_explanation --lib`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/abstract_type.res -o /tmp/abstract_type.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DictInference.res -o /tmp/DictInference.mjs`
  - previously passing `tests/tests/src/keep_uncurry_attribute.res` and
    `tests/tests/src/ExternalShadow.res` still match their checked-in `.mjs`
    snapshots exactly
- The authoritative JS snapshot baseline now reports **70 / 657** passing, **0**
  compile errors, and **587** output diffs.
- `compiler-rust/src/lambda/compile.rs` and
  `compiler-rust/src/js_ir/printer.rs` now port the OCaml list-cons backend
  shape from `js_of_lam_block.ml` / `js_dump.ml`:
  - `Fld_cons` field reads lower to `.hd` / `.tl` instead of numeric array
    indexing
  - constructor blocks named `::` print as `{hd, tl}` objects instead of the
    generic `{TAG, _0, _1}` variant shape
- Verified focused guards for this list-cons cluster:
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_pfield_cons_to_hd_tl_properties --lib`
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_cons_constructor_as_hd_tl_object --lib`
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_non_cons_constructor_keeps_tag_object_shape --lib`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/Import.res -o /tmp/Import.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_list.res -o /tmp/test_list.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- `tests/tests/src/Import.res` now emits list literals with the OCaml `{hd, tl}`
  constructor shape; the remaining drift there is later async/import/backend
  shaping plus the still-missing `/* [] */0` empty-list comment.
- `tests/tests/src/test_list.res` now reads and constructs lists through `.hd`,
  `.tl`, and `{hd, tl}` consistently; its remaining diff is no longer the list
  runtime shape and has narrowed to later control-flow/function lowering.
- `tests/tests/src/ExternalShadow.res` still matches its checked-in `.mjs`
  snapshot exactly after the list-cons port.
- A follow-up authoritative wrapper rerun after the list-cons port remained
  **70 / 657** passing, **0** compile errors, and **587** output diffs.
- `compiler-rust/src/lambda/compile.rs` now ports the OCaml
  `Js_output.append_output` value-sequence behavior on the JS backend path:
  when both sides of an `Lsequence` remain expression-valued, Rust now keeps
  the side effect in a JS comma expression instead of eagerly hoisting it to a
  standalone statement; when those comma expressions are later materialized in
  effect-only top-level contexts, they are flattened back to statements so
  setter-style sequences do not leak trailing `, undefined`.
- Verified focused guards for this sequence-lowering cluster:
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_expression_sequences_to_js_comma_expressions --lib`
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release drops_pure_sequence_prefixes_in_effect_contexts --lib`
  - `cargo test --manifest-path compiler-rust/Cargo.toml --release flattens_value_sequences_back_to_effect_statements_at_toplevel --lib`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/Equality_over_optimization.res -o /tmp/Equality_over_optimization.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DictInference.res -o /tmp/DictInference.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- `tests/tests/src/Equality_over_optimization.res` now matches its checked-in
  `.mjs` snapshot exactly; the missing continuation-sensitive
  `(console.log("hello"), undefined)` lowering is no longer active there.
- `tests/tests/src/DictInference.res` also stays exact after the effect-context
  flattening adjustment, so the sequence port no longer regresses the
  `Js.Dict.set` assignment shape.
- `tests/tests/src/ExternalShadow.res` still matches its checked-in `.mjs`
  snapshot exactly after the sequence port.
- The authoritative JS snapshot baseline now reports **64 / 657** passing, **0**
  compile errors, and **593** output diffs.
- This is a **temporary regression** versus the prior **70 / 657** baseline,
  but the change is kept because the OCaml-aligned `Lsequence` behavior is now
  correct on focused files and exposes remaining downstream effect-context / JS
  pass mismatches elsewhere in the backend.
- `compiler-rust/src/js_ir/printer.rs` now ports another OCaml-aligned printer
  slice from `js_dump_program.ml`, `js_dump_import_export.ml`, and
  `js_dump.ml`:
  - non-export modules keep the blank separator line before the final
    `/* ... Not a pure module */` / `/* No side effect */` trailer
  - ES-module exports print `$$default as default` when the exported binding is
    the internal default identifier
  - function directives print the stored raw directive text (`'use memo'`,
    `'use server'`, etc.) instead of wrapping it in an extra quoted JS string
  - function expressions with directives no longer collapse to arrow-expression
    shorthand, matching OCaml's `directive == None` gate for the short form
- Verified focused guards for this printer slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests -- --test-threads=1`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/function_directives.res -o /tmp/function_directives.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/default_export_test.res -o /tmp/default_export_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/debug_keep_test.res -o /tmp/debug_keep_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
- The authoritative JS snapshot baseline now reports **72 / 657** passing, **0**
  compile errors, and **585** output diffs.
- Resolved checked-in snapshot files for this cluster:
  `debug_keep_test.res`, `hello.foo.res`, `side_effect.res`,
  `function_directives.res`, `function_directives_no_inline.res`,
  `default_export_test.res`, `es6_export.res`, and `escape_esmodule.res`.
- The remaining directive-specific frontier is no longer function-directive
  quoting; `tests/tests/src/directives.res` still needs the separate top-level
  `@@directive(...)` / `Js_config.directives` path to be threaded through the
  Rust JS printer.
- `compiler-rust/src/lambda/compile.rs` now matches the OCaml
  `lam_compile_external_call.ml` `Js_var` path more closely on the Rust
  backend path:
  Rust no longer routes `Js_var` applications through
  `assemble_external_args_no_splice`, so runtime call arguments are preserved
  even when the preserved external metadata has `arg_types = []`
  (the OCaml backend ignores `arg_types` for `Js_var` and calls the value with
  the raw runtime argument list whenever arguments are present).
- Verified focused guards for this external-arity cluster:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_js_var_`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalArity.res -o /tmp/ExternalArity.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- `tests/tests/src/ExternalArity.res` no longer drops the runtime call
  arguments on `v1(x, x)` and `foo1(10)`:
  the old backend bug that lowered those `Js_var` calls to bare values (`v`
  and `foo1`) is gone, and the remaining diff there has narrowed to later
  module-import ordering (`react-intl` vs `react/jsx-runtime`) rather than
  function/application lowering.
- `tests/tests/src/ExternalShadow.res` still matches its checked-in `.mjs`
  snapshot exactly after the `Js_var` change, which keeps this slice isolated
  to external-value application lowering rather than broader shadow/import
  behavior.
- The authoritative JS snapshot baseline remains **108 / 657** passing, **0**
  compile errors, and **549** output diffs after the `Js_var` argument fix.
- Interpretation:
  this is a real OCaml-aligned backend improvement in `Js_var` application
  lowering after optimized lambda. The wrapper totals stay flat because the
  affected checked-in files still carry later import-order or printer drift,
  not because the function-call fix was spurious.
