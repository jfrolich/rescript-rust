# Ralph TODO: JS Output Parity

**Last Updated:** 2026-04-13
**Status:** 130 / 657 JS snapshots passing, 0 compile errors, 527 output diffs

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

- JS snapshot parity: **130 / 657**
- Compile errors: **0**
- Output diffs: **527**
- Diff artifacts written under `temp/rust-parity/diffs`
- Spice PPX guard: **skipped by harness in this environment** because `SPICE_PPX` was not found at the configured path

Interpretation:

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
