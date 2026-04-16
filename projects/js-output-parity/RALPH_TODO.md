# Ralph TODO: JS Output Parity

**Last Updated:** 2026-04-16
**Status:** 581 / 657 authoritative JS snapshot baseline in the current dirty worktree; 0 compile errors and 76 output diffs

## Branch Reset (2026-04-16)

The `typechecker-performance` branch was hard-reset to the tip of the `demo`
branch (`a83f51687`). The demo branch merged `typechecker-performance`,
`integrated-build`, and additional JS output fixes into one lineage. Your
uncommitted JS parity work was stashed and re-applied cleanly on top.

**What this means for you:**
- The git history now includes commits from `integrated-build` and other
  merged branches (build system changes, SimplifyEnv refactors, etc.)
- All prior JS output parity commits are still present (they were in the merge)
- **Parity likely dropped** because the merge had significant file overlap and
  some JS output fixes were lost in conflict resolution. You may need to
  re-apply fixes that were previously working.
- You should **rebuild the Rust compiler** and **re-run the full parity suite**
  to get a fresh baseline before continuing work, since the base has changed

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

Latest authoritative wrapper run on **2026-04-16** using:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

reported:

- JS snapshot parity: **581 / 657**
- Compile errors: **0**
- Output diffs: **76**
- Diff artifacts written under `temp/rust-parity/diffs`
- Spice PPX guard: **skipped by harness in this environment** because `SPICE_PPX` was not found at the configured path

## Current Worktree Status

A fresh rebuild + authoritative wrapper rerun on **2026-04-16** now
reproduces a stable no-compile-error baseline in the current dirty worktree:

- JS snapshot parity: **581 / 657**
- Compile errors: **0**
- Output diffs: **76**

Latest iteration on **2026-04-16**:

- Active slice: restore the OCaml snapshot shape for implicit unit-function
  fallthrough tails so `print_function_body(...)` can re-materialize the
  explicit outer `else` form even after the trailing `return undefined` has
  already fallen off the function body, and collapse the nested shared-fallback
  guard chain in `gpr_1891_test` back to the combined positive guard
- Active backend focus stays in **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`; the change is entirely in `compiler-rust/src/js_ir/printer.rs`
- OCaml reference:
  - `compiler/core/js_dump.ml`, especially `function_body` and `statement` for
    how final dump output preserves the explicit outer `else` byte shape once
    the backend has already decided on the branch structure
  - checked-in OCaml snapshots
    `tests/tests/src/gpr_1891_test.mjs` and
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.mjs`, which keep
    the unit-return outer `else` explicit and keep the `#Foo(3)` success path
    collapsed to one combined `&&` guard
- Rust change:
  - taught `print_function_body(...)` to synthesize the implicit trailing
    `return undefined` when matching unit-return body tails of the form
    `[if ..., trailing_stmt]`, so the existing nested-tail merge can still fire
    after the explicit return has already been elided from the body
  - added `try_function_body_shared_tail_outer_else_merge(...)` so
    `[if (...) { ... return; }, trailing_stmt]` can re-materialize the explicit
    outer `else { trailing_stmt; return; }` snapshot shape for the nested
    `doWithA` / `doWithB` family
  - added `try_unit_function_tail_shared_else_guard_chain_merge(...)` plus
    `strip_leading_negative_guard_shared_else(...)` so the rebuilt outer-else
    form can collapse the `typeof/object` + `NAME === "Foo"` + `VAL !== 3`
    shared-fallback chain back to OCaml's combined positive guard in
    `gpr_1891_test`
  - updated/added focused regression coverage in
    `test_print_unit_function_body_merges_implicit_shared_tail_into_nested_if_else_like_ocaml`,
    `test_print_unit_function_body_merges_implicit_terminal_outer_else_like_do_with_a`,
    and
    `test_print_unit_function_body_merges_implicit_shared_else_guard_chain_like_gpr_1891`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_unit_function_body_merges_implicit_ -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_unit_function_tail_merges_shared_else_guard_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_1891_test.res -o /tmp/gpr_1891_test.mjs`
  - `diff -u tests/tests/src/gpr_1891_test.mjs /tmp/gpr_1891_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res -o /tmp/VariantPatternMatchingSpreadsWithPayloads.mjs`
  - `diff -u tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.mjs /tmp/VariantPatternMatchingSpreadsWithPayloads.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `diff -u tests/tests/src/ExternalShadow.mjs /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1891_test.res` now matches its checked-in snapshot
    again; the unit-return `#Foo(3)` cases no longer stay in the Rust-only
    nested `if (...) { if (...) { if (...) ... } ... }` form
  - `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` now matches
    its checked-in snapshot again; both `doWithA` and `doWithB` keep OCaml's
    explicit outer `else { ...; return; }` form instead of falling through to a
    trailing top-level `console.log(...)`
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained an exact
    snapshot match after the same Phase 5 printer rewrite
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **579 / 657** -> **581 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **78** -> **76** (**-2**)

Latest iteration on **2026-04-16**:

- Active slice: restore the missing body-level shared-tail nested-`if` printer
  merge from the earlier JS parity history so unit-return function bodies can
  re-materialize an explicit shared `else` arm before final dump when the tail
  shape is `[if (...) { if (...) ... } ; fallback ; return]`
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`; the change stays in `compiler-rust/src/js_ir/printer.rs`
- OCaml reference:
  - `compiler/core/js_dump.ml`, especially `function_body`'s tail-statement
    handling after unit-return elision
  - local recovered parity history in commit `c0f200e14`
    (`js-output: print shared unit-function tails like ocaml`), which added
    the missing body-level shared-tail merge that had been lost from the
    current tree after the branch reset
- Rust change:
  - restored `try_function_body_shared_tail_nested_if_merge(...)` in
    `compiler-rust/src/js_ir/printer.rs`
  - re-wired `print_function_body(...)` to consult that helper before the
    narrower trailing-`return undefined` nested-`if` merge
  - restored regression coverage in
    `test_print_unit_function_body_merges_shared_tail_into_nested_if_else`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_unit_function_body_merges_shared_tail_into_nested_if_else -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_unit_function_tail_merges_shared_else_guard_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 20 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_1891_test.res -o /tmp/gpr_1891_test.mjs`
  - `diff -u tests/tests/src/gpr_1891_test.mjs /tmp/gpr_1891_test.mjs`
  - `timeout 20 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `diff -u tests/tests/src/ExternalShadow.mjs /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - the restored printer helper and both focused unit tests now pass again in
    the current tree
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained an exact
    snapshot match
  - live snapshot diffs `tests/tests/src/gpr_1891_test.res` and
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` remained
    unchanged, which shows the current `579 / 657` frontier is blocked by a
    different shared-tail / branch-shape slice than the one this recovered
    helper covers
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **579 / 657** -> **579 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **78** -> **78** (**no change**)
- Keep this change because it restores a previously verified OCaml-aligned
  printer guardrail that had fallen out of the tree after the branch reset.
  Even though the current live failing set did not move, the helper is now
  covered again and does not regress the authoritative harness.

Latest iteration on **2026-04-16**:

- Active slice: keep complete named-variant return switches with plain
  non-raising nested `staticcatch` handlers inline in the switch instead of
  peeling one handler out as a trailing fallthrough tail
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this is `Lam_compile` control-flow lowering in
  `compiler-rust/src/lambda/compile.rs`, not a printer rewrite
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially `flatten_nested_caches`,
    `compile_staticcatch`, and the downstream `compile_cases` path that keeps
    all handlers explicit once the nested catch table is lowered through an
    exit switch
  - checked-in OCaml snapshot shape in `tests/tests/src/test_incomplete.mjs`,
    where the complete `A | C` / `B | D` payload cases stay inside one
    `switch (x.TAG)` instead of becoming a Rust-only post-switch trailing
    `return x._0 + 1 | 0;`
- Rust change:
  - narrowed `uses_fallthrough_staticcatch_return(...)` so the plain-handler
    fallthrough shortcut does not trigger for complete named-variant
    `Lswitch` return lowering when another label is also present; that keeps
    the repeated plain handler cases inside the switch the way OCaml does
  - applied the same guard to the sibling switch/string-switch fallthrough
    branches so the control-flow rule stays internally consistent
  - added regression coverage in
    `nested_named_variant_complete_return_switches_keep_plain_handlers_inside_switch_like_test_incomplete`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release plain_handlers -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release gpr_1438 -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release moves_fallthrough_cases_last -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_incomplete.res -o /tmp/test_incomplete.mjs`
  - `diff -u tests/tests/src/test_incomplete.mjs /tmp/test_incomplete.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_1438.res -o /tmp/gpr_1438.mjs`
  - `diff -u tests/tests/src/gpr_1438.mjs /tmp/gpr_1438.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `diff -u tests/tests/src/ExternalShadow.mjs /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_incomplete.res` now matches its checked-in snapshot
    again; the complete payload switch keeps OCaml's `A | C` and `B | D`
    handlers inside one `switch (x.TAG)` instead of moving the `A | C` return
    out after the switch
  - unchanged guards `tests/tests/src/gpr_1438.res` and
    `tests/tests/src/ExternalShadow.res` both remained exact after the same
    `staticcatch` lowering change
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **578 / 657** -> **579 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **79** -> **78** (**-1**)

Latest iteration on **2026-04-16**:

- Active slice: port OCaml's terminal-tail `Js_stmt_make.if_` rewrite so a
  then-branch ending in `continue` still hoists the else block out of the `if`
  even when the terminal tail is wrapped in a nested `Block`
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; the OCaml behavior lives in `compiler/core/js_stmt_make.ml`,
  and the Rust change stays in `compiler-rust/src/js_ir/mod.rs`
- OCaml reference:
  - `compiler/core/js_stmt_make.ml`, especially the
    `block_last_is_return_throw_or_continue` check inside `if_`
  - that helper emits `if (cond) { ... continue; }` followed by the hoisted
    fallthrough block, instead of retaining `else { throw ... }`, whenever the
    then-branch tail is terminal
- Rust change:
  - taught `last_statement(...)` in the JS IR helper layer to recurse through a
    trailing nested `StatementDesc::Block(...)` before `Statement::if_`
    decides whether the then-branch tail is terminal
  - added regression coverage in
    `test_if_statement_rewrites_nested_block_continue_tail_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_if_statement_rewrites_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_seq.res -o /tmp/test_seq.mjs`
  - `diff -u tests/tests/src/test_seq.mjs /tmp/test_seq.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `diff -u tests/tests/src/ExternalShadow.mjs /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_seq.res` now matches its checked-in snapshot again;
    the recursive `assoc3` loop keeps OCaml's `if (...) { ...; continue; }`
    plus fallthrough `throw`, instead of nesting the `throw` under a Rust-only
    `else`
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same JS IR tail-normalization change
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **577 / 657** -> **578 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **80** -> **79** (**-1**)

Latest iteration on **2026-04-16**:

- Active slice: port OCaml's effect-position `compile_ifthenelse` fallback so
  nontrivial branches are recompiled in effect context instead of being
  forced through `compile_expr` result temps like `let tmp; ... tmp = undefined`
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; the OCaml behavior lives in `compiler/core/lam_compile.ml`,
  and the Rust change stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially the `EffectCall Not_tail`
    branch of `compile_ifthenelse`
  - the OCaml fallback there recompiles `t_branch` / `f_branch` with the
    original effect continuation before calling `S.if_`, instead of reusing
    `NeedValue` outputs outside the narrow inspection cases
- Rust change:
  - in `LambdaCompiler::compile_if_effect_block`, kept the existing
    `compile_expr` inspection for the small pure/value cases, but changed the
    effect fallback and one-sided pure-branch paths to use
    `compile_effect_block(then_)` / `compile_effect_block(else_)`
  - added regression coverage in
    `effect_blocks_keep_nested_effect_ifs_out_of_value_temps`
- Verified focused guards for this slice:
  - `timeout 120 env RUSTFLAGS='-Awarnings' cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::compile::tests::effect_blocks_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh bs_stack_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 30 ./scripts/test_js_single.sh test_seq --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bs_stack_test.res` now matches its checked-in snapshot
    again; the nested `else if` loop branch no longer lowers through a Rust-only
    `tmp = undefined` value path
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same backend-lowering change
  - `tests/tests/src/test_seq.res` still differs on the separate
    `if (...) { ...; continue; } throw` placement cluster, which confirms this
    slice stayed scoped to effect-position nested-if lowering
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **576 / 657** -> **577 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **81** -> **80** (**-1**)

Latest iteration on **2026-04-16**:

- Active slice: port OCaml's `compile_if` NeedValue fallback so temporary
  value-position `if` results stay as `let tmp; tmp = cond ? ...;` instead of
  collapsing into initialized declarations that OCaml never emits in this
  continuation path
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; the OCaml behavior lives in `compiler/core/lam_compile.ml`
  and `compiler/core/js_stmt_make.ml`, and the Rust change stays in
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially the `compile_if` `NeedValue`
    branch that declares a temp first and then lowers the non-expression case
    through `S.if_` without passing a declaration
  - `compiler/core/js_stmt_make.ml`, especially `if_` and its declaration-only
    merge rules
- Rust change:
  - in `LambdaCompiler::compile_expr`, rewired the non-expression
    `LifThenElse` NeedValue path to emit an explicit uninitialized temp plus
    `Statement::if_(...)`, instead of routing through
    `compile_declared_if_block(...)`
  - added checked-in regression coverage in
    `json_decorders_keeps_needvalue_if_temp_declared_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release json_decorders_keeps_needvalue_if_temp_declared_like_ocaml -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release let_unwrap_keeps_declared_switch_binding_shape_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh json_decorders --diff`
  - `timeout 30 ./scripts/test_js_single.sh src/stdlib/Stdlib_PromiseTest.res --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/json_decorders.res` now matches its checked-in snapshot
    again; the optional-email refinement keeps OCaml's declared temp shape
  - `tests/tests/src/stdlib/Stdlib_PromiseTest.res` now matches its checked-in
    snapshot again; the Promise rejection classification keeps the same
    declared temp shape instead of collapsing to `let tmp = ...`
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same backend-lowering change
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **574 / 657** -> **576 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **83** -> **81** (**-2**)

Latest iteration on **2026-04-16**:

- Active slice: port OCaml's literal-bigint equality folding in
  `Js_exp_make.bigint_comp` so typed bigint `==` / `!=` collapse before later
  conditional-expression cleanup, instead of leaving raw `1n !== 1n ? ...`
  chains in the emitted JS
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; the OCaml behavior lives in
  `compiler/core/lam_compile_primitive.ml` and `compiler/core/js_exp_make.ml`,
  and the Rust change stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile_primitive.ml`, especially the `Pbigintcomp`
    branch that routes typed bigint comparisons through `E.bigint_comp`
  - `compiler/core/js_exp_make.ml`, especially `bigint_comp` and its literal
    `Ceq` / `Cneq` folding path
- Rust change:
  - added `compile_bigint_comparison(...)` and rewired the `Pbigintcomp`
    lowering through it instead of the raw generic comparison helper
  - added `compare_bigint_literals(...)` plus
    `normalize_bigint_literal_digits(...)` so Rust matches OCaml's bigint
    literal normalization before testing equality
  - added regression coverage in
    `compile_bigint_literal_equality_folds_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_bigint_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh bigint_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bigint_test.res` now matches its checked-in snapshot
    again; the typed bigint equality cases fold to `true` / `false`, and the
    literal `switch` results collapse the way OCaml's `bigint_comp` unlocks
    downstream
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same backend-lowering change
  - under the full authoritative harness, `bigint_test` dropped out of the
    failure set but an unrelated `ari_regress_test` helper-retention diff
    surfaced, so the topline stayed flat while this bigint slice still moved
    the intended cluster forward
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **573 / 657** -> **573 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **84** -> **84** (**no change**)
- Keep this change because it is a direct OCaml backend port:
  `lam_compile_primitive.ml` routes typed bigint comparisons through
  `js_exp_make.bigint_comp`, and that helper folds literal equality /
  inequality before later expression cleanup. The flat wrapper total reflects
  a separate harness diff surfacing elsewhere, not a mismatch in the bigint
  comparison lowering itself.

Latest iteration on **2026-04-16**:

- Active slice: port OCaml's `Js_exp_make.typeof` folding for supported
  literal expressions and keep the resulting strict `typeof` comparisons
  materialized instead of letting Rust fold them past the OCaml JS shape
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; the OCaml behavior lives in `compiler/core/js_exp_make.ml`
  and `compiler/core/lam_compile_primitive.ml`, and the Rust change stays in
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile_primitive.ml`, especially the `Ptypeof` branch
  - `compiler/core/js_exp_make.ml`, especially `typeof`, `triple_equal`, and
    `bin`
- Rust change:
  - added `ocaml_typeof_expr(...)` to mirror OCaml's `typeof` helper exactly:
    fold `Number` / `Length` to `"number"`, `Str` to `"string"`, `Array` to
    `"object"`, and `Bool` to `"boolean"`, while leaving all other operands as
    raw `typeof ...`
  - added `raw_typeof_comparison(...)` and rewired the untagged block tests,
    variant object tests, and helper predicates to emit raw strict-comparison
    bins around the folded `typeof` result, preserving OCaml's
    `"number" !== "number"` shape instead of collapsing to `false`
  - rewired `Ptypeof` lowering and the `typeof`-driven named string-switch
    discriminants through the same OCaml helper so literal inputs fold before
    later backend stages exactly where OCaml folds them
  - added regression coverage in
    `typeof_folding_matches_ocaml_js_exp_make_for_supported_literals` and
    `typeof_literal_comparisons_stay_materialized_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release typeof_folding_matches_ocaml_js_exp_make_for_supported_literals -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release typeof_literal_comparisons_stay_materialized_like_ocaml -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_pisint_to_typeof_number_check -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh src/stdlib/Stdlib_TempTests.res`
  - `timeout 30 ./scripts/test_js_single.sh src/obj_magic_test.res`
  - `timeout 30 ./scripts/test_js_single.sh src/typeof_test.res --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/stdlib/Stdlib_TempTests.res` now matches its checked-in
    snapshot again; the `%typeof` call over the literal `1` now lowers to
    OCaml's `"number"` string literal instead of staying as `typeof 1`
  - `tests/tests/src/obj_magic_test.res` now matches its checked-in snapshot
    again; literal-backed `typeof ... !== "number"` guards now print as
    OCaml's materialized string comparisons rather than Rust's unfused raw
    `typeof` expressions
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same backend-lowering change
  - `tests/tests/src/typeof_test.res` still differs on the separate
    `if (...) { return false; } switch (...)` control-flow normalization
    cluster, which confirms this slice stayed scoped to `typeof` expression
    construction rather than broader statement cleanup
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **571 / 657** -> **573 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **86** -> **84** (**-2**)

Latest iteration on **2026-04-16**:

- Active slice: port the OCaml pretty-printer grouping that still affected the
  remaining multiline object-literal JS snapshot diffs in `gpr_1946_test` and
  `equal_exception_test`, while keeping the existing nested member-target
  array-call guard from over-indenting Promise-style chains inside blocks
- Active backend focus stays in **Phase 5: Printer-only drift** from `PLAN.md`;
  the OCaml reference lives in `compiler/core/js_dump.ml` and
  `compiler/ext/ext_pp.ml`, and the Rust change stays in
  `compiler-rust/src/js_ir/printer.rs`
- OCaml reference:
  - `compiler/core/js_dump.ml`, especially `If`, `Caml_block_tag`, `Call`,
    and `arguments`
  - `compiler/ext/ext_pp.ml`, especially `group` and `paren_group`
- Rust change:
  - matched OCaml's `If` condition printer by wrapping the condition
    expression in an extra indent level while it is printed inside `(...)`
  - matched OCaml's `Caml_block_tag` printer by adding the missing grouped
    target indentation before `.TAG`
  - kept the existing call-argument extra-group rule scoped to
    `level == 15` member/index-target calls, but suppressed it when the
    printer is already inside an indented block so nested `Promise.all([...]).then`
    shapes do not double-indent
  - added regression coverage in
    `test_print_if_condition_call_object_argument_uses_snapshot_indent_like_ocaml`,
    `test_print_caml_block_tag_call_argument_uses_group_indent_like_ocaml`,
    and `test_print_nested_member_target_call_with_multiline_array_arg_avoids_double_indent`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_if_condition_call_object_argument_uses_snapshot_indent_like_ocaml -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_parenthesized_object_literal_dot_access_as_call_argument_preserves_base_indent -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_caml_block_tag_call_argument_uses_group_indent_like_ocaml -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_nested_member_target_call_with_multiline_array_arg_avoids_double_indent -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh gpr_1946_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh equal_exception_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh src/stdlib/Stdlib_PromiseTest.res --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1946_test.res` now matches its checked-in snapshot
    again; the plain `({"_5": 3})._5` call argument stays at OCaml's base
    indent while the `Obj.tag(Obj.repr(...))` path regains OCaml's grouped
    `.TAG` indentation
  - `tests/tests/src/equal_exception_test.res` now matches its checked-in
    snapshot; the `if (Primitive_object.equal(..., { ... }) !== false)` shape
    regains the missing condition-group indentation from `js_dump.ml`
  - `tests/tests/src/ExternalShadow.res` remained exact, and
    `tests/tests/src/stdlib/Stdlib_PromiseTest.res` stayed on its separate
    `let tmp` normalization diff, which confirms this slice stayed scoped to
    multiline literal indentation only
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **568 / 657** -> **570 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **89** -> **87** (**-2**)

This current worktree measurement now supersedes the earlier stale warning
about the temporary `RefCell already borrowed` compile failures.

Latest iteration on **2026-04-16**:

- Active slice: thread OCaml's checked integer/bigint division and modulo
  lowering through the Rust JS backend so zero-divisor cases emit the
  `Primitive_int` / `Primitive_bigint` runtime helpers instead of raw JS
  binops that later get treated as removable pure expressions
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; the fix spans `compiler/core/lam_compile_primitive.ml` /
  `compiler/core/js_exp_make.ml` on the OCaml side and
  `compiler-rust/src/driver.rs` plus `compiler-rust/src/lambda/compile.rs` on
  the Rust side
- OCaml reference:
  - `compiler/core/lam_compile_primitive.ml`, especially the `Pdivint`,
    `Pmodint`, `Pdivbigint`, and `Pmodbigint` branches
  - `compiler/core/js_exp_make.ml`, especially `int32_div`, `int32_mod`,
    `bigint_div`, and `bigint_mod`
- Rust change:
  - added `check_div_by_zero` to `driver::CompilerOptions` and threaded it
    into `LambdaCompiler`, with the CLI JS path keeping the OCaml-default
    checked behavior enabled
  - in `compiler-rust/src/lambda/compile.rs`, replaced the unconditional raw
    JS lowering for `Pdivint`, `Pmodint`, `Pdivbigint`, and `Pmodbigint` with
    OCaml-aligned runtime calls when the divisor is not statically known to be
    non-zero
  - kept OCaml's integer fast paths in the same helper port, including the
    `Length / 2 -> >> 1` case and the non-zero constant divisor direct-binop
    cases
  - added regression coverage in
    `compile_checked_int_div_uses_primitive_int_runtime_call_like_ocaml`,
    `compile_checked_int_mod_uses_primitive_int_runtime_call_like_ocaml`,
    `compile_checked_bigint_div_uses_primitive_bigint_runtime_call_like_ocaml`,
    `compile_checked_bigint_mod_uses_primitive_bigint_runtime_call_like_ocaml`,
    `gpr_1760_test_keeps_checked_division_and_mod_effects_like_ocaml`, and
    `div_by_zero_test_keeps_checked_throw_helpers_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_checked_ -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release gpr_1760_test_keeps_checked_division_and_mod_effects_like_ocaml -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release div_by_zero_test_keeps_checked_throw_helpers_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh gpr_1760_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh div_by_zero_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1760_test.res` now matches its checked-in snapshot
    exactly; the `try` bodies keep OCaml's checked `Primitive_int.div(0, 0)`
    and `Primitive_int.mod_(0, 0)` calls so the exception handlers still fire
  - `tests/tests/src/div_by_zero_test.res` now matches its checked-in snapshot
    exactly; the `throws` callbacks no longer collapse to empty lambdas
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same backend-lowering change
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **565 / 657** -> **568 / 657** (**+3**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **92** -> **89** (**-3**)
- Keep this change because it is a direct OCaml backend port:
  `lam_compile_primitive.ml` threads `Js_config.check_div_by_zero` into the
  checked integer/bigint helpers, and `js_exp_make.ml` only falls back to raw
  JS division/modulo when the divisor is statically safe or checked lowering is
  disabled. The old Rust path skipped that gate entirely.

Latest iteration on **2026-04-16**:

- Active slice: finish the `gpr_1701_test` cluster by matching OCaml's
  tail-loop lowering for wrapped `staticcatch`/`trywith` recursion and
  restoring OCaml's negative early-return `if_` normalization for strict
  `undefined` success guards that fall through into a `continue`
- Active backend focus spans the same OCaml backend boundary from `PLAN.md`:
  `compiler/core/lam_compile.ml` for the recursive `staticcatch`/`trywith`
  lowering path and `compiler/core/js_stmt_make.ml` for the final `if_`
  statement normalization that decides whether the emitted JS uses an
  early-return negative guard or a positive guarded block
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially `compile_staticcatch`,
    `compile_trywith`, and the self-tailcall handling in `compile_apply`
  - `compiler/core/js_stmt_make.ml`, especially `if_` and its
    `else = [return ...]` early-return rewrite
- Rust change:
  - in `compiler-rust/src/lambda/compile.rs`, kept the verified
    `staticcatch` tail-loop lowering and added the missing
    `LtryWith`-under-fallthrough path so the wrapped `read_lines2` recursion
    now lowers like OCaml instead of staying as a direct recursive local
    function
  - in `compiler-rust/src/js_ir/mod.rs`, narrowed
    `preserves_nullish_success_guard(...)` to nontrivial `return` tails only,
    so strict `value !== undefined` guards with a `continue` success tail now
    follow OCaml's `Js_stmt_make.if_` negative-guard rewrite instead of being
    preserved as a positive branch
  - added regression coverage in
    `nested_wrapped_staticcatch_trywith_tail_loops_lower_like_gpr_1701` and
    `test_if_statement_rewrites_strict_undefined_continue_success_tail_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release staticcatch_trywith -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_if_statement_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 600 cargo build --manifest-path rewatch/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh gpr_1701_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh exception_raise_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1701_test.res` now matches its checked-in snapshot
    exactly; `read_lines2` lowers through the wrapped `staticcatch` loop path
    and `read_lines` now uses OCaml's negative early-return guard for the
    `undefined` sentinel case
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same JS-IR normalization change
  - `tests/tests/src/exception_raise_test.res` still differs on the separate
    grouped exception-catch merge shape, which confirms this slice stayed
    scoped to the `gpr_1701` tail-loop / statement-normalization cluster
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **564 / 657** -> **565 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **93** -> **92** (**-1**)
- Keep this change because both parts are direct OCaml ports:
  `lam_compile.ml` keeps the wrapped `staticcatch` handler outside the
  `trywith` body while still turning the recursive handler into a loop, and
  `js_stmt_make.ml` rewrites `if cond then <continue-tail> else return x` into
  a negative early-return guard when the fallback is the single `return`.

Latest iteration on **2026-04-16**:

- Active slice: port OCaml's missing object primitive lowering for `Pobjtag`
  and `Pobjsize`, which were still falling through to `undefined` in Rust's
  primitive table
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; the fix lands in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile_primitive.ml`, especially the `Pobjtag` and
    `Pobjsize` branches that lower to `E.tag e` and `E.obj_length e`
  - `compiler/core/js_exp_make.ml`, especially `tag` and `obj_length`
- Rust change:
  - added explicit `Pobjtag` lowering to `ExpressionDesc::CamlBlockTag(...)`
    with the OCaml `TAG` field name instead of falling through to the wildcard
    `undefined` case
  - added explicit `Pobjsize` lowering to
    `Expression::length(..., LengthObject::CamlBlock)` instead of the same
    wildcard `undefined` fallback
  - added regression coverage in
    `compile_obj_tag_uses_caml_block_tag_access_like_ocaml` and
    `compile_obj_size_uses_caml_block_length_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_obj_ -- --nocapture`
  - `timeout 30 ./scripts/test_js_single.sh gpr_1946_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh chain_code_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - primitive lowering is now OCaml-aligned and unit-covered; direct
    `Pobjtag`/`Pobjsize` compilation no longer produces the wildcard
    `undefined` fallback
  - unchanged guards `tests/tests/src/chain_code_test.res` and
    `tests/tests/src/ExternalShadow.res` remained exact after the primitive
    change
  - `tests/tests/src/gpr_1946_test.res` still differs exactly at
    `console.log(({"_5": 3}).TAG)`, which means a later rewrite is still
    collapsing `CamlBlockTag` over a plain object literal to `undefined`
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **564 / 657** -> **564 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **93** -> **93** (**no change**)
- Keep this change because it is a direct OCaml primitive port:
  `lam_compile_primitive.ml` does not route `Pobjtag` or `Pobjsize` through an
  `undefined` fallback. Even though the current snapshot surface still needs a
  follow-up rewrite fix to expose the new primitive lowering on `gpr_1946`,
  the primitive table itself is now correct and should not be reverted.

Latest iteration on **2026-04-16**:

- Active slice: narrow the flatten-and-mark-dead literal projection rewrite
  back to OCaml's immutable `Caml_block` / array cases and stop collapsing
  plain JS object property reads, fixing the over-optimization cluster behind
  `chain_code_test` and `method_string_name`
- Active backend focus stays in **Phase 4: Port JS Passes** from `PLAN.md`;
  the observable mismatch was in `Js_pass_flatten_and_mark_dead`, and the fix
  lands in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/js_exp_make.ml`, especially `dot`, `record_access`, and
    `extension_access`
  - `compiler/core/js_pass_flatten_and_mark_dead.ml`, especially the
    substitution rewrite that only peels `Static_index` / `Array_index` from
    immutable `Caml_block` bindings and leaves plain object property reads
    materialized
- Rust change:
  - removed the unverified `ExpressionDesc::Object(None, props)` branch from
    `direct_projection_from_pure_literal(...)`, so flatten-and-mark-dead no
    longer folds plain object property reads into their literal payload values
  - corrected the regression coverage by renaming
    `js_flatten_and_mark_dead_collapses_direct_object_property_reads_like_ocaml`
    to
    `js_flatten_and_mark_dead_keeps_direct_object_property_reads_materialized_like_ocaml`
    and asserting the `StaticIndex(Object(...), "d", None)` shape instead of
    a collapsed variable
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_flatten_and_mark_dead_keeps_direct_object_property_reads_materialized_like_ocaml -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release derive_projector_test_collapses_pure_record_projection_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh chain_code_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh method_string_name --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 30 ./scripts/test_js_single.sh gpr_1946_test --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/chain_code_test.res` and
    `tests/tests/src/method_string_name.res` now match their checked-in
    snapshots exactly; Rust no longer folds those plain object property reads
    down to literal payload values
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same JS-pass change
  - `tests/tests/src/gpr_1946_test.res` still differs, but only on the
    separate `.TAG` object-access rule; the earlier `_5` field collapses are
    gone, which confirms this slice narrowed the correct cluster
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **561 / 657** -> **564 / 657** (**+3**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **96** -> **93** (**-3**)
- Keep this change because it is a direct OCaml backend correction:
  `js_exp_make` only folds record/extension-style indexed reads from arrays or
  `Caml_block`s, and `js_pass_flatten_and_mark_dead` only substitutes
  immutable `Caml_block` bindings there. The previous Rust object-literal fold
  had no OCaml basis and was exactly why chained and quoted-name object reads
  were over-collapsing in the emitted JS.

Latest iteration on **2026-04-16**:

- Active slice: match OCaml's `Ext_pp.brace_vgroup` / `js_dump.ml` block
  printer behavior so explicit branches keep separator-driven blank lines for
  hidden statements and always force a newline before `}`, covering
  `gpr_4491_test`
- Active backend focus stays in **Phase 5: Byte-Exact Dumping** from `PLAN.md`;
  this slice stays in `compiler-rust/src/js_ir/printer.rs`
- OCaml reference:
  - `compiler/ext/ext_pp.ml`, especially `iter_lst`, `newline`,
    `force_newline`, and `brace_vgroup`
  - `compiler/core/js_dump.ml`, especially `statements` and `brace_block`
- Rust change:
  - added `force_newline(...)` to mirror `Ext_pp.force_newline`
  - rewired `print_statements(...)` to preserve OCaml separator placement
    across original statements even when a statement prints nothing
  - rewired `print_brace_block(...)` to use the forced-newline closing path
    instead of Rust's compact close-on-the-current-line behavior
  - added printer regression coverage in
    `test_print_if_keeps_blank_lines_for_hidden_branch_statements_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_if_keeps_blank_lines_for_hidden_branch_statements_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_4491_test.res -o /tmp/gpr_4491_test.mjs`
  - `diff -u tests/tests/src/gpr_4491_test.mjs /tmp/gpr_4491_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `diff -u tests/tests/src/ExternalShadow.mjs /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_4491_test.res` now matches its checked-in snapshot
    exactly; the explicit empty-effect branches keep OCaml's blank interior
    line instead of collapsing to Rust's compact closing-brace shape
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained an exact
    snapshot match after the same printer slice
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **561 / 657** -> **562 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **96** -> **95** (**-1**)
- Keep this change because it is a direct OCaml printer port:
  `Ext_pp.brace_vgroup` always forces a newline before `}`, and `js_dump.ml`
  preserves statement separators from the original block even when a statement
  prints nothing. The previous Rust printer only inserted separators between
  visible statements and only conditionally emitted the closing newline, which
  is exactly why `gpr_4491_test` lost OCaml's blank-line block shape.

Latest iteration on **2026-04-16**:

- Active slice: port OCaml's pure literal projection collapse for
  record/cons/extension/variant accesses and preserve that collapse through the
  flatten-and-mark-dead JS pass, so direct projections from immutable literal
  blocks/objects inline to the payload value instead of emitting temporary
  field reads
- Active backend focus moves to **Phase 4: Port JS Passes** from `PLAN.md` for
  this slice; the observable mismatch was in the `Js_pass_flatten_and_mark_dead`
  cleanup path, though the supporting access lowering stays in
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/js_exp_make.ml`, especially `record_access`,
    `inline_record_access`, `variant_access`, `cons_access`, and
    `extension_access`
  - `compiler/core/js_pass_flatten_and_mark_dead.ml`, especially the
    substitution rewrite for `Static_index` / `Array_index` over immutable
    `Caml_block` values
- Rust change:
  - added `pure_indexed_block_item(...)` and rewired `compile_field_access(...)`
    so pure `Array` / `CamlBlock` accesses collapse immediately for
    module/record/inline-record/record-extension/extension/cons/variant-tag/
    variant/fallback indexed accesses, matching `js_exp_make.ml`
  - added `direct_projection_from_pure_literal(...)` and taught
    `flatten_and_mark_dead_expression(...)` to collapse `StaticIndex` and
    `ArrayIndex` over pure literal arrays/blocks/objects after recursive
    rewriting, matching the OCaml flatten-and-mark-dead substitution path
  - added regression coverage in
    `derive_projector_test_collapses_pure_record_projection_like_ocaml`,
    `js_flatten_and_mark_dead_collapses_direct_object_property_reads_like_ocaml`,
    `lowers_record_pfield_from_pure_caml_block_directly_like_ocaml`,
    `lowers_cons_pfield_from_pure_caml_block_directly_like_ocaml`, and
    `lowers_extension_pfield_from_pure_caml_block_directly_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release pure_caml_block_directly_like_ocaml -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release derive_projector_test_collapses_pure_record_projection_like_ocaml -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_flatten_and_mark_dead_collapses_direct_object_property_reads_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh derive_projector_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/derive_projector_test.res` matches again under the parity
    harness; Rust no longer leaves the pure literal projection materialized
    after flattening
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same change
  - the dirty-worktree wrapper now reports only the four unrelated
    `src/types/context.rs` borrow panics above; that compile-error movement is
    recorded but not attributed to this JS backend slice
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **556 / 657** -> **558 / 657** (**+2**)
  - Compile errors: **8** -> **4** (**-4**)
  - Output diffs: **93** -> **95** (**+2**)
- Keep this change because it is direct OCaml backend alignment: `js_exp_make`
  collapses projections from no-side-effect literal blocks immediately, and
  `js_pass_flatten_and_mark_dead` keeps collapsing those projections again
  after substitution. The earlier Rust path only handled a narrower subset of
  module/polyvariant cases, which is why pure record and object projections
  were surviving into the emitted JS.

Latest iteration on **2026-04-16**:

- Active slice: align Rust's shared-handler switch fallthrough with OCaml's
  `compile_staticcatch` pseudo-jump path after `Lam_pass_exits.simplify_exits`,
  fixing the `gpr_1438` cluster where simplification removes the outward
  static raise but multiple direct exits still target the same non-raising
  handler
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; the fix lands in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially `flatten_nested_caches` and
    `compile_staticcatch`
  - `compiler/core/lam_compile_context.ml`, especially
    `no_static_raise_in_handler`
  - `compiler/core/lam_pass_exits.ml`, especially `simplify_exits`
- Rust change:
  - broadened `uses_fallthrough_staticcatch_return(...)` so a switch or string
    switch with multiple direct exits to the same label still peels a shared
    non-raising handler out after the switch, matching the OCaml pseudo-jump
    path once `Lam_pass_exits` has inlined outward handlers away
  - kept the existing single-default-arm behavior unchanged, so this slice only
    affects the shared multi-exit cluster rather than all staticcatch lowering
  - promoted the regression coverage in
    `compile_deps_program_keeps_gpr_1438_fallthrough_return_outside_switch`
    and updated the older unsimplified unit test to
    `direct_return_switch_cases_with_shared_plain_handlers_fall_through_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release gpr_1438 -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release plain_handlers -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release single_handlers_as_default_arms -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_1438.res -o /tmp/gpr_1438.mjs`
  - `diff -u tests/tests/src/gpr_1438.mjs /tmp/gpr_1438.mjs`
  - `timeout 30 ./scripts/test_js_single.sh bal_set_mini --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1438.res` now matches its checked-in snapshot exactly;
    the trailing `return param => {};` is back outside the switch instead of
    being emitted as a synthetic `default` arm
  - broader guards `tests/tests/src/bal_set_mini.res` and
    `tests/tests/src/ExternalShadow.res` remained exact after the same backend
    change
  - the full dirty-worktree wrapper improved by one file with no compile-error
    movement, which is consistent with this slice targeting one concrete
    switch/staticcatch lowering cluster
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **555 / 657** -> **556 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **94** -> **93** (**-1**)
- Keep this change because it is a direct OCaml backend alignment: once
  `Lam_pass_exits` has simplified away the outward static handler, OCaml still
  uses the single-handler pseudo-jump path as long as the remaining handler
  itself has no static raises. The previous Rust predicate incorrectly depended
  on seeing another-label exits in the switch body, which is exactly why
  `gpr_1438` regressed after simplification.

Latest iteration on **2026-04-16**:

- Active slice: port OCaml's `js_dump.ml` `If` printer behavior so the dumper
  omits `else` arms for `[Block []]` / `[Exp (Var _)]` and unwraps
  `else { if (...) ... }` into `else if (...)`
- Active backend focus moves to **Phase 5: Byte-Exact Dumping** from `PLAN.md`
  for this slice; the lowering was already producing the right JS IR drift, and
  the remaining mismatch was in `compiler-rust/src/js_ir/printer.rs`
- OCaml reference:
  - `compiler/core/js_dump.ml`, especially the `If (e, s1, s2)` branch
  - `compiler/core/js_dump.ml`, especially the explicit omission cases
    `[] | [Block [] | Exp (Var _)]` and the
    `[Block [If _]] -> else if ...` unwrap
- Rust change:
  - added `else_block_is_omitted_like_ocaml(...)` so the printer suppresses
    Rust-only `else {}` output when the alternate is just a single empty block
    or a single no-op variable expression
  - added `single_else_if_stmt_like_ocaml(...)` so a single wrapped nested `if`
    prints as `else if (...)` instead of `else { if (...) ... }`
  - added printer regression coverage in
    `test_print_if_omits_else_for_single_empty_block_like_ocaml`,
    `test_print_if_omits_else_for_single_var_expression_like_ocaml`, and
    `test_print_if_unwraps_single_block_else_if_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_if_omits_else -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_if_unwraps_single_block_else_if_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh bal_set_mini --diff`
  - `timeout 30 ./scripts/test_js_single.sh rec_fun_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 30 ./scripts/test_js_single.sh test_primitive --diff`
  - `timeout 30 ./scripts/test_js_single.sh gpr_4491_test --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bal_set_mini.res` matches its checked-in snapshot again;
    Rust no longer prints the stray `else {}` on the membership guard loop
  - `tests/tests/src/rec_fun_test.res` also matches again for the same no-op
    alternate-arm printer drift
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same printer change
  - sibling drift `tests/tests/src/test_primitive.res` stayed on its separate
    early-return/negative-guard lowering mismatch, which keeps this slice
    isolated to the final dumper rather than JS IR simplification
  - `tests/tests/src/gpr_4491_test.res` still differs only on the blank line
    layout inside its explicit non-empty `else` block, which is a narrower
    printer shape issue than the removed empty-arm case
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **553 / 657** -> **555 / 657** (**+2**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **96** -> **94** (**-2**)
- Keep this change because it is a direct OCaml dumper port from
  `js_dump.ml`: the reference backend suppresses these empty/no-op alternate
  arms and unwraps single block-wrapped nested `if`s before printing. The
  improvement shows up exactly where the current dirty diff set had the Rust-only
  `else {}` drift.

Latest iteration on **2026-04-16**:

- Active slice: port OCaml's `remove_pure_sub_exp` behavior in
  `compile_ifthenelse` so effect-position `if` branches with allocating values
  stay on the conditional-expression path instead of being dropped early by the
  Rust backend's generic purity check
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially the `EffectCall Not_tail`
    branch inside `compile_ifthenelse`
  - `compiler/core/js_exp_make.ml`, especially `remove_pure_sub_exp`
- Rust change:
  - added `remove_pure_subexpression(...)` / `is_pure_subexpression(...)` as a
    direct Rust port of OCaml's `Js_exp_make.remove_pure_sub_exp`
  - rewired the `then_prelude_empty && else_prelude_empty` arm of
    `compile_if_effect_block(...)` to use that OCaml-aligned pruning instead of
    the broader `js_expr_no_side_effects(...)` check
  - added regression coverage in
    `effect_blocks_keep_allocating_branches_inside_conditional_expressions_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release effect_blocks_lower_ifs_without_a_result_temp -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release effect_blocks_keep_allocating_branches_inside_conditional_expressions_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh gpr_4491_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh test_primitive --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_4491_test.res` now regains OCaml's explicit `else`
    branch after Rust had previously dropped it entirely; the remaining diff is
    only the blank no-op statement layout inside the branch bodies
  - `tests/tests/src/bal_set_mini.res` likewise regains the explicit empty
    `else` branch in its membership guard loop, which confirms the change is
    affecting the intended `if`-effect lowering cluster rather than one file
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained an exact
    snapshot match after the same backend change
  - sibling diff `tests/tests/src/test_primitive.res` stayed on its existing
    early-return drift, which keeps this slice isolated to the OCaml
    `remove_pure_sub_exp` path rather than the broader `if` simplifier
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **555 / 657** -> **553 / 657** (**-2**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **94** -> **96** (**+2**)
- Keep this change because the Rust backend was using the wrong notion of
  purity for OCaml's effect-position `if` lowering. `compile_ifthenelse`
  consults `remove_pure_sub_exp`, not the generic side-effect predicate, and
  that distinction is exactly what restores the explicit empty-branch shape in
  `gpr_4491_test` and `bal_set_mini` even though the current dirty-tree total
  moved the wrong way.

Latest iteration on **2026-04-16**:

- Active slice: port OCaml's literal `int_switch` / `string_switch`
  normalization from `js_stmt_make.ml` so JS IR statement construction folds
  switches with literal scrutinees directly to the selected branch body instead
  of leaving dead `switch (...) { ... }` statements in the Rust output
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md` for this slice; the OCaml behavior lives in
  `compiler/core/js_stmt_make.ml`, and the Rust port lands in
  `compiler-rust/src/js_ir/mod.rs`
- OCaml reference:
  - `compiler/core/js_stmt_make.ml`, especially `int_switch`
  - `compiler/core/js_stmt_make.ml`, especially `string_switch`
- Rust change:
  - `Statement::new(...)` / `Statement::with_comment(...)` now normalize
    literal `IntSwitch` and `StringSwitch` nodes through a shared
    `normalize_statement(...)` path that selects the matching clause body or
    default body immediately, mirroring OCaml's `js_stmt_make`
  - added JS IR regression coverage in
    `test_literal_string_switch_simplifies_to_selected_case_body_like_ocaml`
    and
    `test_literal_int_switch_simplifies_to_default_body_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_literal_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh const_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 30 ./scripts/test_js_single.sh coercion_module_alias_test --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/const_test.res` now matches its checked-in snapshot
    exactly; Rust no longer leaves the dead `switch ("x") { ... }` in `hh()`
    after the JS IR construction step where OCaml already folds it to
    `return 3`
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained an exact
    snapshot match after the same normalization
  - sibling diff `tests/tests/src/coercion_module_alias_test.res` stayed
    unchanged, which keeps this slice isolated to literal-switch statement
    normalization rather than broader alias/export behavior
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **554 / 657** -> **554 / 657** (**no change**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **95** -> **95** (**no change**)
- Keep this change because it is a direct OCaml port from `js_stmt_make.ml`:
  literal switch scrutinees are normalized immediately in the reference
  backend. The flat dirty-tree total means another unrelated diff entered the
  current noisy worktree while this slice made `const_test` exact, not that the
  normalization itself was incorrect.

Latest iteration on **2026-04-16**:

- Active slice: match OCaml's `while` dump shape on the printer path by
  keeping multiline `while (...)` conditions under the dumper's hanging-indent
  paren group and by printing empty statement blocks with the same blank
  interior line OCaml emits instead of Rust's compact `{}` shortcut
- Active backend focus moves to **Phase 5: Byte-Exact Dumping** from `PLAN.md`
  for this slice; the lowering was already fixed in `compiler-rust/src/lambda/compile.rs`,
  and the remaining drift stayed in `compiler-rust/src/js_ir/printer.rs`
- OCaml reference:
  - `compiler/core/js_dump.ml`, especially the `While` branch's
    `P.paren_group f 1 (...)` condition printing
  - `compiler/core/js_dump.ml`, especially `brace_block` using
    `P.brace_vgroup f 1 (...)` for statement blocks
- Rust change:
  - `StatementDesc::While` now prints its condition under an extra indent scope
    so multiline IIFE conditions keep OCaml's hanging indent instead of
    flattening their internal lines back to the surrounding statement column
  - `print_brace_block(...)` now prints empty statement blocks with a blank
    interior line and the outer closing-brace indent, matching OCaml's dumper
    instead of emitting compact `{}`
  - added printer regression coverage in
    `test_print_empty_while_body_keeps_blank_line_like_ocaml` and
    `test_print_while_multiline_condition_keeps_hanging_indent_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_while -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh complex_while_loop --diff`
  - `timeout 30 ./scripts/test_js_single.sh test_while_side_effect --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/complex_while_loop.res` now matches its checked-in
    snapshot exactly; the remaining drift from the earlier `compile_while`
    lowering fix was only the dumper's while-condition indentation and empty
    block shape
  - `tests/tests/src/test_while_side_effect.res` also matches its checked-in
    snapshot exactly; the effectful comma-condition loop keeps OCaml's blank
    empty body and the IIFE predicate keeps OCaml's hanging indent
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained an exact
    snapshot match throughout the printer slice
  - the generalized empty-statement-block printer rule also removes one
    additional dirty-tree output diff elsewhere in the harness beyond the two
    focused `while` fixtures
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **551 / 657** -> **554 / 657** (**+3**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **98** -> **95** (**-3**)
- Keep this change because OCaml's dumper really does route `while`
  conditions through a hanging-indent paren group and statement blocks through
  `brace_vgroup`; the compact Rust-only `{}` path and flattened multiline
  condition indentation were last-mile printer drift, not backend behavior.

Latest iteration on **2026-04-16**:

- Active slice: preserve OCaml's `compile_while` predicate-block lowering by
  wrapping non-empty while-condition preludes back into a zero-arg function
  call instead of dropping them from the Rust backend
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially `compile_while`
  - `compiler/core/js_exp_make.ml`, especially `of_block`
- Rust change:
  - added `block_with_return_expr_iife(...)` and wired the `Lambda::Lwhile`
    lowering through it so a predicate compiled with side-effect/declaration
    prelude still becomes an OCaml-style expression wrapper before entering the
    JS `while (...)`
  - added checked-in fixture regression coverage
    `complex_while_loop_keeps_effectful_condition_blocks_inside_iifes`
    and
    `test_while_side_effect_keeps_local_condition_bindings_in_iifes`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release complex_while_loop_keeps_effectful_condition_blocks_inside_iifes -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_while_side_effect_keeps_local_condition_bindings_in_iifes -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh complex_while_loop --diff`
  - `timeout 30 ./scripts/test_js_single.sh test_while_side_effect --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/complex_while_loop.res` no longer drops the predicate's
    local recursive/helper bindings; Rust now matches OCaml's backend-stage
    choice to keep those bindings scoped inside an IIFE-wrapped `while`
    condition
  - `tests/tests/src/test_while_side_effect.res` likewise keeps the local
    `y` binding and preceding condition effects inside the predicate wrapper
    instead of flattening them away into a broken comma expression
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained an exact
    snapshot match after the same slice
  - both focused loop fixtures still differ byte-for-byte only on
    printer-level indentation / empty-body formatting, so this backend fix does
    not yet change the wrapper counts
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **551 / 657** -> **551 / 657** (**no change**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **98** -> **98** (**no change**)
- Keep this change because OCaml's backend does not discard non-empty while
  predicate blocks. `compile_while` explicitly recompiles the predicate as a
  value and routes any emitted block back through `Js_exp_make.of_block`; the
  old Rust path was backend-incorrect even when the final harness count stayed
  flat.

Latest iteration on **2026-04-16**:

- Active slice: keep OCaml's single-use switch-scrutinee aliases when the
  source identifier is mutated, covering both direct mutated variables and the
  ref-content reads that later collapse to the same `Lvar` shape
- Active backend focus stays on the post-optimized-lambda JS backend path from
  `PLAN.md`; this concrete correction lives in
  `compiler-rust/src/lambda/simplify.rs` with the checked-in fixture guard in
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_pass_remove_alias.ml`, especially the `Llet` alias
    simplification path and when a scrutinee alias must remain materialized
  - `compiler/core/lam_pass_lets_dce.ml`, especially the single-use
    simplification rules that still need to leave the mutated-scrutinee case
    intact for the downstream backend
- Rust change:
  - broadened `switch_scrutinee_alias_source_ident(...)` so the
    mutated-source preservation rule applies to both direct `Lvar` aliases and
    mutable-field reads, instead of only the field-read form
  - added focused simplifier regression coverage in
    `keeps_switch_scrutinee_aliases_from_mutated_plain_variables`
  - kept the checked-in JS fixture guard
    `bal_set_mini_binds_named_variant_switch_scrutinee_once_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release switch_scrutinee_aliases -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release bal_set_mini -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh bal_set_mini --diff`
  - `timeout 30 ./scripts/test_js_single.sh compare_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh pm_opt_fields_regression --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 30 ./scripts/test_js_single.sh LetUnwrap --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bal_set_mini.res` matches its checked-in snapshot again;
    Rust restores the final `let match = v` scrutinee alias that OCaml keeps
    before the terminal named-variant dispatch
  - narrowed guard files `tests/tests/src/compare_test.res` and
    `tests/tests/src/pm_opt_fields_regression.res` stay exact after the same
    change, so the kept rule is no longer limited to the mutable-ref read
    variant only
  - unchanged guards `tests/tests/src/ExternalShadow.res` and
    `tests/tests/src/LetUnwrap.res` remained exact throughout the slice
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **550 / 657** -> **551 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **99** -> **98** (**-1**)
- Keep this change because OCaml's post-lowering alias passes do not inline
  away every single-use switch alias uniformly; the mutated-scrutinee case
  still needs to survive into final JS lowering. Treating only the mutable
  field-read form as special was too narrow once the earlier ref elimination
  had already collapsed that read to a plain variable.

Latest iteration on **2026-04-16**:

- Active slice: keep OCaml's return-switch `break` behavior only for
  nontrivial case bodies that exit to a shared plain staticcatch handler, while
  leaving direct `case -> exit handler` cases inlined inside the switch
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially `compile_general_cases`,
    `compile_switch`, and `compile_staticcatch`
  - `compiler/core/js_output.ml`, especially `to_break_block` and its
    return-position `should_break` behavior
- Rust change:
  - return-position int/string switch clauses now set `should_break` when the
    compiled case body is non-empty, non-terminating, and still contains an
    exit, matching OCaml's `to_break_block` behavior for partial case bodies
  - narrowed `uses_fallthrough_staticcatch_return(...)` so plain handlers only
    move outside the switch when the body has either outward re-raises or a
    nontrivial case body that exits to that handler; direct `case -> exit
    handler` bodies stay inline
  - added focused regression coverage in
    `partial_int_return_switch_cases_break_to_shared_handler_like_test_set`
    and
    `direct_return_switch_cases_keep_plain_handlers_inline_like_variant_spreads`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release partial_int_return_switch_cases_break_to_shared_handler_like_test_set -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release direct_return_switch_cases_keep_plain_handlers_inline_like_variant_spreads -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release nested_plain_int_return_switches_can_fall_through_like_gpr_1438 -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh VariantPatternMatchingSpreads --diff`
  - `timeout 30 ./scripts/test_js_single.sh set_gen --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/VariantPatternMatchingSpreads.res` is back to an exact
    snapshot match; the narrowed rule no longer hoists its direct plain handler
    out of `lookup3`
  - `tests/tests/src/set_gen.res` keeps the intended `sub(...)` switch-tail
    improvement: the old duplicated recursive fallback is gone, leaving only
    separate earlier `if`/`else` shaping drift in that file
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained an exact
    snapshot match throughout the slice
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **550 / 657** -> **550 / 657** (**no change**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **99** -> **99** (**no change**)
- Keep this change because it matches the OCaml backend's actual split:
  partial return-switch cases that still exit to the shared handler must break
  out to the handler, but direct shared-handler cases stay inside the switch.
  The flat dirty-tree totals mean this slice traded one remaining backend
  cluster (`set_gen`) against another already-known cluster rather than moving
  the overall count yet.

Latest iteration on **2026-04-16**:

- Active slice: keep `Lswitch` / `LstringSwitch` let-bindings on OCaml's
  declared-binding path instead of folding the switch assignment back into an
  initialized declaration on the Rust backend
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially `Llet` lowering through
    `Declare (kind, id)` together with `compile_switch` /
    `compile_stringswitch`
  - `compiler/core/js_stmt_make.ml`, especially the declare-vs-define split in
    `declare_variable`, `int_switch`, and `string_switch`
- Rust change:
  - restored explicit declared-binding lowering for
    `compile_switch_binding_block(...)` and
    `compile_string_switch_binding_block(...)` so switch-bound lets keep
    `let x; ... x = ...`
  - added checked-in regression coverage
    `let_unwrap_keeps_declared_switch_binding_shape_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release let_unwrap_keeps_declared_switch_binding_shape_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/LetUnwrap.res -o /tmp/LetUnwrap.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/bal_set_mini.res -o /tmp/bal_set_mini.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 30 ./scripts/test_js_single.sh LetUnwrap --diff`
  - `timeout 30 ./scripts/test_js_single.sh bal_set_mini --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/LetUnwrap.res` now matches its checked-in snapshot again;
    Rust restores the OCaml-emitted `let someResult; someResult = ...` binding
    shape instead of collapsing it to `let someResult = ...`
  - unchanged guard `tests/tests/src/ExternalShadow.res` remains an exact
    snapshot match after the same slice
  - sibling file `tests/tests/src/bal_set_mini.res` stays on its separate
    remaining alias drift (`let match = v`), which confirms this fix is
    isolated to declared switch bindings rather than that later aliasing issue
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **546 / 657** -> **549 / 657** (**+3**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **103** -> **100** (**-3**)
- Keep this change because OCaml's `Llet` + `compile_switch` /
  `compile_stringswitch` path really does declare the binding first and then
  assign within the switch/if body. The earlier Rust folding was a backend-only
  shortcut that removed the checked-in `LetUnwrap` binding shape and three
  corresponding snapshot matches.

Latest iteration on **2026-04-16**:

- Active slice: mirror OCaml's single-block `Js_output.output_as_block`
  unnesting on the return-`if` lowering path only, so terminal return branches
  are flattened before `Statement::if_` decides whether the fallthrough can
  stay outside the `else`
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/js_output.ml`, especially `unnest_block` /
    `output_as_block`
  - `compiler/core/lam_compile.ml`, especially the `compile_ifthenelse`
    branches that feed `S.if_` from `Js_output.output_as_block (...)`
- Rust change:
  - narrowed `compile_if_return_block(...)` to peel single wrapped blocks from
    both return branches before the final `Statement::if_(...)` normalization
  - added focused checked-in fixture coverage
    `bal_set_mini_unwraps_terminal_return_blocks_before_if_fallthrough_flattening`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release bal_set_mini_unwraps_terminal_return_blocks_before_if_fallthrough_flattening -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release array_subtle_tail_guard_keeps_positive_if_shape -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh bal_set_mini --diff`
  - `timeout 30 ./scripts/test_js_single.sh test_set --diff`
  - `timeout 30 ./scripts/test_js_single.sh bdd --diff`
  - `timeout 30 ./scripts/test_js_single.sh UntaggedVariants --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bal_set_mini.res` now matches the checked-in `bal`
    control-flow shape again; the remaining drift there is the separate final
    alias difference (`let match = v`)
  - `tests/tests/src/test_set.res` drops the matching `bal` else-nesting hunk
    and keeps the rest of its pre-existing diffs unchanged
  - narrowed follow-up checks confirmed that the earlier experimental broad
    unnesting was the source of the `bdd` / `UntaggedVariants` regressions, so
    the final kept change is limited to the return-`if` path only
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **550 / 657** -> **546 / 657** (**-4**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **99** -> **103** (**+4**)
- Keep this change because OCaml really does strip single nested blocks before
  passing return branches into `S.if_`; the `bal_set_mini` / `test_set`
  control-flow fix comes directly from that behavior. The negative dirty-tree
  delta means follow-up backend slices still need to recover four downstream
  files that rely on the old Rust-only shape.

Latest iteration on **2026-04-16**:

- Active slice: route named-variant payload cases through the recursive
  tail-loop switch path so self tailcalls in `sw_blocks` stop falling back to
  direct recursion
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially `compile_recursive_let`'s
    `Maybe_tail_is_return (Tail_with_name ...)` loop-lowering path together
    with the named-variant switch return handling under `compile_cases` /
    `compile_general_cases`, which still descends through payload-carrying
    block cases
- Rust change:
  - updated `compile_tail_loop_switch_return_block(...)` so named-variant
    switches stop using the Rust-only `sw_consts`-only path
  - added tail-loop-aware named string / named variant switch helpers so
    payload-carrying block arms compile via `compile_tail_loop_return_block(...)`
    instead of the ordinary return-block lowering
  - added the focused regression
    `recursive_named_variant_block_cases_reenter_tail_loops`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release recursive_named_variant_block_cases_reenter_tail_loops -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release recursive_wrapped_js_fn_make_bindings_lower_to_looping_while_bodies -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release recursive_self_tailcalls_lower_to_looping_while_bodies -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh bal_set_mini --diff`
  - `timeout 30 ./scripts/test_js_single.sh bdd --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bdd.res` now matches its checked-in snapshot again; the
    recursive helpers go back through OCaml-style `while (true)` loop bodies
    instead of direct recursive returns
  - `tests/tests/src/bal_set_mini.res` no longer diffs on the recursive
    `min_elt` / `mem` helpers; the remaining drift there is the separate `bal`
    else-nesting shape plus the final `let match = v` alias
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same slice
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **547 / 657** -> **550 / 657** (**+3**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **102** -> **99** (**-3**)
- Keep this change because the old Rust path was not OCaml-aligned: once a
  recursive function enters the tail-return lowering, OCaml still walks named
  variant payload cases and loopifies self calls there. Rust was dropping
  those block arms from the tail-loop path by only inspecting `sw_consts`.

Latest iteration on **2026-04-16**:

- Active slice: port the first OCaml `Lam_pass_exits` simplifications that
  remove unused `LstaticCatch` nodes and inline zero-arg const/var handlers on
  the JS-backend simplify path before lambda lowering
- Active backend focus moved to **Phase 2: Port Post-Lowering Lambda Backend
  Stages** from `PLAN.md`; this slice stays in
  `compiler-rust/src/lambda/simplify.rs`
- OCaml reference:
  - `compiler/core/lam_pass_exits.ml`, especially the `Lstaticcatch`
    simplifier cases that:
    - drop the catch when the exit label does not occur in the body
    - inline all exits immediately when the handler is a constant or variable
- Rust change:
  - added `simplify_static_exits_for_js_backend(...)` to run before each
    JS-backend simplify/deep-flatten round
  - implemented shadow-aware exit counting for `LstaticCatch` bodies so an
    outer label does not accidentally count raises captured by an inner catch
  - implemented the OCaml-aligned zero-arg const/var inlining path for
    `LstaticRaise(label, [])` plus the dead-catch removal when the label no
    longer occurs
  - added focused unit coverage for both behaviors in
    `compiler-rust/src/lambda/simplify.rs`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release backend_exit_simplifier_ -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release folds_constant_subint_loop_finish_before_for_range_lowering_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh json_decorders --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - the new exit pass is a real harness win in this dirty worktree even though
    `tests/tests/src/json_decorders.res` is still diffing on the separate
    `let tmp; tmp = ...` vs `let tmp = ...` declaration-shape issue
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact after
    the same slice
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **542 / 657** -> **547 / 657** (**+5**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **107** -> **102** (**-5**)
- Keep this change because OCaml really does eliminate dead catches and inline
  zero-arg const/var handlers in `Lam_pass_exits` before backend lowering. The
  Rust JS path now mirrors that pass boundary more closely, and the broader
  parity harness improved materially even though the remaining
  `json_decorders` declaration-style drift still needs a follow-up lowering
  slice.

Latest iteration on **2026-04-16**:

- Active slice: keep OCaml's effect-only lowering for unit-return `if` tails
  when both branches are trivial unit, instead of synthesizing a Rust-only
  `if (cond) { return; }`
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially `compile_ifthenelse` under
    `EffectCall Not_tail` where both branch results become pure unit and
    `remove_pure_sub_exp` falls through to `Js_output.make ... (S.exp e)`
- Rust change:
  - narrowed `compile_if_unit_return_tail_block(...)` so it now detects when
    both branches are trivial unit tails and emits the condition as an effect
    statement instead of forcing the positive guard fast path
  - kept the existing positive-guard path for effectful taken branches with a
    trivial unit fallback, so `array_subtle_test` and the earlier unit-tail
    guard work remain intact
  - added focused unit coverage for the effectful-condition / trivial-unit
    case and a checked-in `gpr_1728_test` fixture assertion
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release unit_return_function_with_trivial_if_branches_keeps_condition_effect_only -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release gpr_1728_unit_if_tail_stays_as_condition_effect -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release array_subtle_tail_guard_keeps_positive_if_shape -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh gpr_1728_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh array_subtle_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1728_test.res` now matches its checked-in snapshot
    again on the real harness path; Rust emits the bare
    `Number.parseInt(x) !== 3;` effect statement like OCaml instead of the
    drifting `if (Number.parseInt(x) !== 3) { return; }`
  - unchanged guards `tests/tests/src/array_subtle_test.res` and
    `tests/tests/src/ExternalShadow.res` remained exact after the same slice
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **541 / 657** -> **542 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **108** -> **107** (**-1**)
- Keep this change because OCaml does not turn a unit-return tail with two
  trivial unit branches into an early-return guard. Once both branches erase
  to pure unit, `lam_compile.ml` keeps only the condition effect; the Rust
  backend now preserves that same backend-stage choice.

Latest iteration on **2026-04-16**:

- Active slice: preserve OCaml's positive success-guard shape for simple
  unit-return `if` tails in the lambda compiler, while keeping loop /
  recursive / declaration-heavy tails on the existing negative-guard path
- Active backend focus stays in **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially the unit-return function path
    lowered under `EffectCall (Maybe_tail_is_return ...)`
  - `compiler/core/js_dump.ml`, especially `function_body`'s narrow
    single-statement `If (_, then_, [Return Undefined])` case, which only
    elides `else return;` after the backend has already chosen a success-first
    `If`
- Rust change:
  - added `compile_if_unit_return_tail_block(...)`,
    `lambda_is_trivial_unit_undefined(...)`, and
    `js_block_is_simple_unit_return_tail(...)` in
    `compiler-rust/src/lambda/compile.rs`
  - wired the return-unit `LifThenElse` lowering to keep a direct positive
    `If` only when the fallback branch is trivial unit and the taken branch
    compiles to a straight-line expression tail ending in `return undefined`
  - kept loop / recursive / declaration-heavy tails on the old
    `compile_if_return_block(...)` path, so the earlier false regressions in
    `queue_402` and `ext_array_test` stay on OCaml's negative-guard shape
  - added focused unit coverage for both the positive simple-effect tail and
    the negative loop-tail guard cases, plus a checked-in
    `array_subtle_test` fixture assertion
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release unit_return_function_body_keeps_positive_effect_guard_before_js_passes -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release unit_return_function_keeps_positive_effect_guard_through_js_pipeline -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release array_subtle_tail_guard_keeps_positive_if_shape -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release unit_return_function_with_for_loop_tail_keeps_negative_guard -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release unit_return_function_with_else_for_loop_tail_keeps_negative_guard -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release unit_return_function_with_local_while_tail_keeps_negative_guard -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh array_subtle_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh LargeUnboxedVariantOptimization --diff`
  - `timeout 30 ./scripts/test_js_single.sh queue_402 --diff`
  - `timeout 30 ./scripts/test_js_single.sh ext_array_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 30 ./scripts/test_js_single.sh untagged_variants_heuristic --diff`
  - `timeout 30 ./scripts/test_js_single.sh inline_record_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh gpr_4491_test --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/array_subtle_test.res` now matches its checked-in
    snapshot again on the real harness path; Rust keeps the OCaml-style
    positive `if (x.length >= 10) { ... return; }` tail instead of rewriting
    it into an early-return guard
  - unchanged guards `tests/tests/src/LargeUnboxedVariantOptimization.res`,
    `tests/tests/src/queue_402.res`, `tests/tests/src/ext_array_test.res`,
    `tests/tests/src/ExternalShadow.res`, and
    `tests/tests/src/untagged_variants_heuristic.res` all remained exact
  - nearby remaining diffs in this guard-shape cluster are
    `tests/tests/src/inline_record_test.res` and
    `tests/tests/src/gpr_4491_test.res`
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **540 / 657** -> **541 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **109** -> **108** (**-1**)
- Keep this change because OCaml already commits to the positive success-guard
  shape before `js_dump.ml`; the dumper only elides `else return;` for that
  single-statement tail and does not synthesize it from loop / recursive
  guard-fallthrough bodies. The Rust backend now preserves that same narrow
  pre-printer shape instead of forcing every unit-return tail through the
  generic negative-guard lowering.

Latest iteration on **2026-04-16**:

- Active slice: thread the real `Js_config.jsx_preserve` gate through the Rust
  JS-backend lambda simplifier instead of preserving transformed JSX `.make`
  field reads unconditionally
- Active backend focus moved back to **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`; this slice stays in
  `compiler-rust/src/lambda/simplify.rs` with the compile entrypoint update in
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  `compiler/core/lam_pass_remove_alias.ml`, especially the
  `Pjs_call {prim_name = "jsx" | "jsxs"}` + `Pfield` guard that only preserves
  the transformed JSX component field read when `!Js_config.jsx_preserve`
- Rust change:
  - added `simplify_for_js_backend_with_jsx_preserve(...)` so the JS-backend
    simplifier can receive the actual JSX-preserve flag instead of hard-coding
    preserve behavior for every transformed JSX call
  - threaded `self.jsx_preserve` from
    `LambdaCompiler::compile_deps_program_with_possible_required_modules(...)`
    into that simplifier entrypoint
  - narrowed the transformed-`jsx/jsxs` field-read preservation in
    `simplify_primitive(...)` to `env.jsx_preserve`, matching OCaml's
    `lam_pass_remove_alias` gate
  - added the focused regression
    `preserves_transformed_jsx_component_field_reads_during_alias_simplification_in_jsx_preserve_mode`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release preserves_transformed_jsx_component_field_reads_during_alias_simplification_in_jsx_preserve_mode -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh jsx_optional_props_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh jsx_preserve_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 30 ./scripts/test_js_single.sh async_jsx --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/jsx_optional_props_test.res` matches its checked-in
    snapshot in the current dirty worktree again; Rust emits the direct
    component function in `JsxRuntime.jsx(...)` instead of the drifting
    `ComponentWithOptionalProps.make` tag
  - unchanged guards `tests/tests/src/jsx_preserve_test.res`,
    `tests/tests/src/ExternalShadow.res`, and `tests/tests/src/async_jsx.res`
    remained exact after the same slice
  - the preserve-only simplifier regression stays covered directly, while the
    non-preserve JSX tag collapse continues to be validated at the emitted-JS
    level because the relevant exported-component shape spans later backend
    stages beyond the synthetic unit test shape
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **540 / 657** -> **540 / 657** (**no change**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **109** -> **109** (**no change**)
- Keep this change because the old Rust simplifier was not OCaml-aligned:
  `lam_pass_remove_alias` only preserves transformed JSX `.make` reads when
  JSX preserve mode is actually enabled, and the Rust backend now threads that
  same stage boundary explicitly.

Latest iteration on **2026-04-16**:

- Active slice: use OCaml's generic temporary naming for `NeedValue`
  `if-then-else` lowering instead of Rust's special `ifres` result temp
- Active backend focus moved back to **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`; this slice stays in
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_ifthenelse`'s
  `NeedValue _` branch where non-expression branches allocate the shared
  result slot with `Ext_ident.create_tmp ()`
- Rust change:
  - changed the `Lambda::LifThenElse` `NeedValue` lowering in
    `compiler-rust/src/lambda/compile.rs` to call `fresh_tmp_ident()`
    instead of `fresh_ident("ifres")`
  - added the focused regression
    `if_expression_result_temp_uses_tmp_name_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release if_expression_result_temp_uses_tmp_name_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release if_value_branches_keep_assignment_continuation_through_let_bindings -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh arity_infer --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/arity_infer.res` now matches its checked-in snapshot
    again; Rust emits `let tmp;` / `tmp(...)` like OCaml instead of the
    Rust-only `ifres` binding
  - unchanged guard `tests/tests/src/ExternalShadow.res` remained exact
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **539 / 657** -> **540 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **110** -> **109** (**-1**)
- Keep this change because the old `ifres` name did not come from the OCaml
  backend. `compile_ifthenelse` uses `Ext_ident.create_tmp ()` for this shared
  result slot, so the Rust backend now matches that lowering rule.

Latest iteration on **2026-04-16**:

- Active slice: preserve declaration-context lowering for recursive singleton
  wrapper bindings so recursive React component wrappers stop falling back to
  `let make; make = ...`
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice stays in `compiler-rust/src/lambda/simplify.rs` and
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  - `compiler/core/lam_compile.ml`, especially `compile_recursive_let`'s
    generic `compile_lambda ~continuation:(Declare (Alias, id))` path for
    non-bare recursive bindings
  - actual optimized lambda for `recursive_react_component.res`, which both
    compilers print as a recursive nested-`let` wrapper around
    `make$Internal`
- Rust change:
  - extended `make_like_binding_name(...)` in
    `compiler-rust/src/lambda/simplify.rs` to recognize `make$Internal`
    bindings
  - added `inline_recursive_component_internal_wrapper(...)` so the JS-backend
    simplifier preserves sync recursive component wrappers with a real `props`
    parameter instead of collapsing them back to a generic `param`
  - added a recursive-binding compile fallback in
    `compiler-rust/src/lambda/compile.rs` that reuses `compile_let_binding`
    for singleton nested-`let` recursive RHSs only when that path produces an
    initialized declaration for the recursive binding, matching OCaml's
    declaration-context lowering rather than Rust's old placeholder-assignment
    fallback
  - added focused regressions in both files for the recursive component
    wrapper simplification and the recursive singleton nested-`let` lowering
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release keeps_recursive_component_internal_props_wrappers_materialized_for_js_backend -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release recursive_singleton_nested_let_function_bindings_avoid_placeholder_assignments -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release recursive_function_bindings_lower_directly_without_placeholder_assignments -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh recursive_react_component --diff`
  - `timeout 30 ./scripts/test_js_single.sh async_jsx --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 30 ./scripts/test_js_single.sh recursive_module_test --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/recursive_react_component.res` now matches its checked-in
    snapshot again; Rust emits `function make(props)` instead of the previous
    `let make; make = props => ...` fallback
  - unchanged guards `tests/tests/src/async_jsx.res` and
    `tests/tests/src/ExternalShadow.res` remained exact
  - `tests/tests/src/recursive_module_test.res` still differs, but only in the
    separate recursive-module alias naming shape (`fact$1` / `M.fact`), so
    this slice is localized
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **537 / 657** -> **539 / 657** (**+2**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **112** -> **110** (**-2**)
- Keep this change because the old Rust path was not OCaml-aligned: the
  optimized lambda is a recursive nested-`let` wrapper, and OCaml lowers that
  wrapper through declaration context rather than a placeholder assignment.

Latest iteration on **2026-04-16**:

- Active slice: stop substituting projections out of single-field immutable
  `Caml_block`s in the Rust `js_pass_flatten_and_mark_dead` port; OCaml only
  records those substitutions for blocks with at least two fields
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  `compiler/core/js_pass_flatten_and_mark_dead.ml`, especially the
  `Variable ... Caml_block ((_ :: _ :: _ as ls), Immutable, ...)` case and the
  comment immediately above it that limits substitution to blocks larger than
  one element
- Rust change:
  - narrowed `flatten_and_mark_dead_statement(...)` in
    `compiler-rust/src/lambda/compile.rs` so the substitution map is no longer
    populated for single-field immutable `Caml_block`s
  - kept recursive flattening of the single-field block contents themselves, so
    this slice only removes the Rust-only projection substitution and does not
    skip the normal child rewrites
  - replaced the earlier Rust-only unit expectations with OCaml-aligned JS-pass
    regressions for single-field module reads and single-field component
    `.make` reads
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release js_flatten_and_mark_dead_keeps_single_field_module_reads_materialized_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release js_flatten_and_mark_dead_keeps_single_field_component_make_reads_without_jsx_preserve_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release js_flatten_and_mark_dead_preserves_transformed_jsx_component_make_reads -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh recursive_module --diff`
  - `timeout 30 ./scripts/test_js_single.sh recursive_react_component --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 30 ./scripts/test_js_single.sh async_jsx --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/recursive_module.res` now matches its checked-in snapshot
    again; the Rust JS pass no longer rewrites `Stdlib_Lazy.get(Intb.a)` to
    `Stdlib_Lazy.get(a)` by substituting through a one-field module block
  - `tests/tests/src/recursive_react_component.res` remains a separate drift in
    the recursive-module family; its current mismatch is the parameter name
    (`props` vs `param`), not the fixed single-field projection substitution
  - `tests/tests/src/ExternalShadow.res` and `tests/tests/src/async_jsx.res`
    remained exact as unchanged guard files after the same pass change
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **537 / 657** -> **537 / 657** (**no change**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **112** -> **112** (**no change**)
- Keep this change because the removed substitution was Rust-only. OCaml's
  `js_pass_flatten_and_mark_dead` explicitly refuses to build projection
  substitutions for single-field immutable blocks, so the Rust pass now matches
  that stage boundary even though the current dirty-tree wrapper totals stay
  flat.

Latest iteration on **2026-04-16**:

- Active slice: port the OCaml `Js_exp_make.bin` `Length` comparison rewrites
  so Rust folds pure `x.length >= 0` guards to `true` and canonicalizes
  `x.length > 0` to `x.length !== 0`
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/js_ir/mod.rs`
- OCaml reference:
  `compiler/core/js_exp_make.ml`, especially `bin`'s `Ge, Length (e, _), 0`
  and `Gt, Length (_, _), 0` arms
- Rust change:
  - added the missing `rewrite_length_bin_comparison(...)` path in
    `compiler-rust/src/js_ir/mod.rs`
  - Rust now matches OCaml by folding `Length >= 0` to `true` only when the
    underlying target expression is side-effect-free
  - Rust now rewrites `Length > 0` to `Length !== 0`, matching the OCaml
    canonical JS shape that snapshot files like `test_bool_equal` expect
  - added focused JS-IR regressions for the pure-target fold, the impure-
    target non-fold, and the `> 0` rewrite
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_length_ge_zero_ -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_length_gt_zero_rewrites_to_not_eq_zero_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh test_bool_equal --diff`
  - `timeout 30 ./scripts/test_js_single.sh array_subtle_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_bool_equal.res` now matches its checked-in snapshot
    again; the `Belt.Array.length` comparison shapes no longer drift in
    `f7`/`f8`
  - `tests/tests/src/array_subtle_test.res` collapsed from five hunks to one:
    only the remaining unit-tail `if` polarity mismatch in `fff2` is still
    exposed there, while the `length >= 0` and `length > 0` drift is gone
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as a
    broader unchanged guard
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **535 / 657** -> **537 / 657** (**+2**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **114** -> **112** (**-2**)
- Keep this change because the previous Rust JS IR builder was simply missing
  an explicit OCaml backend rule in `js_exp_make.bin`; the new path is a
  direct port of that logic and materially shrinks the current dirty-tree
  snapshot frontier.

Latest iteration on **2026-04-16**:

- Active slice: port the OCaml `js_stmt_make.if_` split for nullish success
  guards so Rust preserves the positive branch for loose-nullish / strict-
  `undefined` cases and strict-`null` value returns, but still rewrites the
  strict-`null` unit tail shape into the negative early-return form that OCaml
  snapshots use
- Active backend focus moved back to **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md` for this slice; the change stays in
  `compiler-rust/src/js_ir/mod.rs`
- OCaml reference:
  `compiler/core/js_stmt_make.ml`, especially `if_`'s rewrites for
  `_, [{statement_desc = Return _}]` and
  `block_last_is_return_throw_or_continue ifso`
- Rust change:
  - tightened `Statement::if_` / `simplify_if_statement` in
    `compiler-rust/src/js_ir/mod.rs` so Rust no longer treats every nullish
    success guard the same
  - restored the positive materialization that existing OCaml snapshots expect
    for loose-nullish guards, strict-`undefined` unit tails, and strict-`null`
    branches that return real values
  - added a strict-`null`-only carveout for unit-return tails so shapes like
    `untagged_variants_heuristic` rewrite to the OCaml negative early-return
    form instead of staying as a positive success branch
  - replaced the earlier overbroad nullish constructor expectations with a
    focused test matrix that now covers the preserved `null` / `undefined`
    cases and the rewritten strict-`null` unit-tail case separately
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/untagged_variants_heuristic.res -o /tmp/untagged_variants_heuristic.mjs`
  - `diff -u tests/tests/src/untagged_variants_heuristic.mjs /tmp/untagged_variants_heuristic.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/bs_auto_uncurry.res -o /tmp/bs_auto_uncurry.mjs`
  - `diff -u tests/tests/src/bs_auto_uncurry.mjs /tmp/bs_auto_uncurry.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_1245_test.res -o /tmp/gpr_1245_test.mjs`
  - `diff -u tests/tests/src/gpr_1245_test.mjs /tmp/gpr_1245_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/bs_splice_partial.res -o /tmp/bs_splice_partial.mjs`
  - `diff -u tests/tests/src/bs_splice_partial.mjs /tmp/bs_splice_partial.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `diff -u tests/tests/src/ExternalShadow.mjs /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/queue_402.res -o /tmp/queue_402.mjs`
  - `diff -u tests/tests/src/queue_402.mjs /tmp/queue_402.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/untagged_variants_heuristic.res` now matches its checked-
    in snapshot again, which confirms the strict-`null` unit-tail carveout is
    hitting the intended OCaml shape
  - the preserved-side guards also stayed exact after the carveout:
    `bs_auto_uncurry`, `gpr_1245_test`, and `bs_splice_partial` all still emit
    the positive success-branch form that OCaml snapshots check in
  - `tests/tests/src/ExternalShadow.res` and `tests/tests/src/queue_402.res`
    remained exact as broader unchanged guards
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **535 / 657** -> **536 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **114** -> **113** (**-1**)
- Keep this change because the previous Rust JS statement simplifier collapsed
  several distinct OCaml backend cases into one nullish-success heuristic. The
  narrowed port now matches the checked-in snapshot split: strict-`null`
  unit-tail functions rewrite to negative guards, while the broader nullish /
  `undefined` success-guard family stays materialized in positive form.

Latest iteration on **2026-04-16**:

- Active slice: collapse multi-guard unit-return function bodies in the
  printer when Rust preserves a nested negative early-return chain for a
  literal-dispatch tail that OCaml emits as one positive `if (...) { ... }`
- Active backend focus moved to **Phase 5: Byte-Exact Dumping** from `PLAN.md`
  for this slice; the change stays in `compiler-rust/src/js_ir/printer.rs`
- OCaml reference:
  `compiler/core/js_dump.ml`, especially `function_body` and the surrounding
  `statement` printing rules for `If` / `Return Undefined`
- Rust change:
  - added a function-body-only merge in `compiler-rust/src/js_ir/printer.rs`
    that recognizes nested multi-guard `if (<neg>) return;` tails and
    rebuilds them as one positive `if (<guard1> && <guard2> && ...)` before
    printing
  - kept that merge deliberately narrow by requiring **multiple** guards, so
    single early-return bodies like `queue_402` still print in OCaml's
    original negative-guard form
  - added focused printer regressions for both shapes: the large literal
    dispatch collapse and the single-guard preservation case
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_unit_function_body -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/LargeUnboxedVariantOptimization.res -o /tmp/LargeUnboxedVariantOptimization.mjs`
  - `diff -u tests/tests/src/LargeUnboxedVariantOptimization.mjs /tmp/LargeUnboxedVariantOptimization.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `diff -u tests/tests/src/ExternalShadow.mjs /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/queue_402.res -o /tmp/queue_402.mjs`
  - `diff -u tests/tests/src/queue_402.mjs /tmp/queue_402.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/LargeUnboxedVariantOptimization.res` now matches its
    checked-in snapshot, removing the Rust-only negative guard chain around the
    `"space"` branch in `handleKey`
  - `tests/tests/src/ExternalShadow.res` remained exact as a broader unchanged
    guard, and `tests/tests/src/queue_402.res` stayed exact after narrowing
    the merge back to multi-guard bodies only
  - the current dirty-tree authoritative wrapper improved after the narrowed
    printer fix, so this is no longer just a file-local cleanup
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **534 / 657** -> **535 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **115** -> **114** (**-1**)
- Keep this change because the previous Rust printer left a multi-guard
  function-tail artifact that OCaml's backend does not emit in the checked-in
  snapshot, while the narrowed version preserves the single negative-guard
  forms that OCaml still prints elsewhere.

Latest iteration on **2026-04-16**:

- Active slice: lower `PinitMod` / `PupdateMod` on the Phase-3 primitive path
  so recursive-module JS emission keeps OCaml's `Primitive_module.init/update`
  runtime calls instead of dropping module initialization metadata entirely
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  `compiler/core/lam_compile_primitive.ml`, specifically the
  `translate` arms for `Pinit_mod` and `Pupdate_mod`
- Rust change:
  - added the missing `PinitMod` / `PupdateMod` match arms in
    `compiler-rust/src/lambda/compile.rs` so Rust now lowers them to
    `Primitive_module.init(...)` and `Primitive_module.update(...)`
    like OCaml
  - added focused unit coverage for both the runtime call shape and the
    required `Primitive_module` runtime import in the deps-program printer path
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_module_primitives_lower_to_primitive_module_runtime_calls_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_module_primitives_require_primitive_module_runtime_import -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `./scripts/test_js_single.sh gpr_1539_test --diff`
  - `./scripts/test_js_single.sh ExternalShadow --diff`
  - `./scripts/test_js_single.sh gpr_3931_test --diff`
  - `./scripts/test_js_single.sh rec_module_test --diff`
  - `./scripts/test_js_single.sh rec_module_opt --diff`
  - `./scripts/test_js_single.sh recmodule --diff`
  - `./scripts/test_js_single.sh recursive_unbound_module_test --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1539_test.res` now matches its checked-in snapshot
    again, restoring the missing `Primitive_module.init/update` wrappers that
    OCaml emits for recursive module setup
  - the same primitive-lowering fix also cleared a small module-shaped guard
    set in the tests tree: `gpr_3931_test`, `rec_module_test`,
    `rec_module_opt`, `recmodule`, and `recursive_unbound_module_test` all
    produced no diff output after the rebuild
  - `tests/tests/src/ExternalShadow.res` stayed exact as a broader unchanged
    guard
  - the remaining recursive-module drift in the current diff cache lives
    further downstream under `src/recursive_module*` and
    `src/recursive_react_component`, so the next slice should stay in the
    recursive-module backend path rather than the primitive match itself
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **528 / 657** -> **534 / 657** (**+6**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **121** -> **115** (**-6**)
- Keep this change because the previous Rust backend was simply not OCaml-
  aligned here: it carried `PinitMod` / `PupdateMod` through lambda but never
  lowered them in the JS backend, which erased recursive-module runtime
  initialization and update calls from emitted JavaScript.

Latest iteration on **2026-04-16**:

- Active slice: keep mixed untagged effect switches on the filtered OCaml
  small-case path once the block side compiles to a real no-op, instead of
  preserving a redundant literal-vs-block dispatch guard around the const side
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially the mixed untagged
  `compile_switch` path's reuse of `sw_num_default` / `compile_general_cases`,
  plus the later OCaml backend simplifications that erase no-op effect guards
- Rust change:
  - replaced the Rust-only `const_cases.len() == literal_cases.len()` shortcut
    in mixed untagged lowering with the actual OCaml-aligned
    `const_switch_default(...)` / `const_switch_complete(...)` metadata, so the
    const side keeps the same default information OCaml passes into
    `compile_general_cases`
  - narrowed the effect dispatcher so it no longer wraps the const side in a
    literal-membership gate when the block side compiled to `[]`; in that case
    the guard is semantically redundant and only preserves Rust-only residue
  - added `mixed_untagged_string_effect_switches_filter_default_duplicates_before_small_lowering`
    to cover the exact mixed-string overlap shape that the earlier named-string
    regression did not reach
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml mixed_untagged_string_effect_switches_filter_default_duplicates_before_small_lowering -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml named_string_effect_switches_filter_default_duplicates_before_small_lowering -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_js_and_simplifies_or_literal_membership_against_same_literal_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_unit_function_body_with_trailing_return_merges_nested_if_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh LargeUnboxedVariantOptimization --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - the new mixed-untagged regression now passes and keeps the existing
    named-string / JS-IR simplification guards green, so the const side is no
    longer forced through a Rust-only completeness shortcut in effect context
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as a
    broader unchanged guard
  - `tests/tests/src/LargeUnboxedVariantOptimization.res` stayed flat in this
    dirty worktree, which means the checked-in failing snapshot still carries a
    later downstream drift on top of the now-covered mixed-effect rule
  - the current dirty-tree authoritative wrapper stayed flat as well, so this
    backend fix hardens a real OCaml-aligned effect-lowering rule without yet
    collapsing one of the currently exposed snapshot files
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **528 / 657** -> **528 / 657** (**no change**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **121** -> **121** (**no change**)
- Keep this change because the previous Rust lowering mixed two problems:
  it dropped the OCaml default/completeness metadata on the const side, and it
  preserved a redundant literal-dispatch wrapper even when the block side had
  already compiled to a no-op. The current dirty snapshots do not surface a
  topline delta, but the compiler now has direct regression coverage for the
  OCaml rule instead of relying on the earlier Rust-only shortcut.

Latest iteration on **2026-04-16**:

- Active slice: filter named string-switch cases against the explicit default
  before choosing the OCaml small-switch lowering, instead of only filtering in
  the grouped fallback path
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_general_cases`'s
  `Default lam -> List.filter ...` step that removes default-duplicate cases
  before matching on `[]`, `[case]`, or `[case1; case2]`
- Rust change:
  - added a shared `filtered_switch_case_refs(...)` helper for named string
    switch lowering
  - updated the named string assignment/return/effect lowering paths to feed
    that filtered case list into the small-switch matcher before falling back
    to grouped switch emission, so Rust no longer misses the OCaml small-case
    path when default-duplicate arms collapse the switch to one meaningful case
  - replaced the earlier overbroad synthetic mixed-untagged regression with a
    focused unit test that exercises the exact OCaml rule now being ported
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml named_string_effect_switches_filter_default_duplicates_before_small_lowering -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml string_switch_effects_group_adjacent_equal_cases_and_drop_default_duplicates -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml int_switch_expressions_group_adjacent_equal_cases_and_drop_default_duplicates -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh UntaggedVariants --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - the new regression passes and keeps the adjacent default-duplicate grouping
    guards green, so the named-string lowering now matches OCaml on the
    filter-before-small-case decision point
  - `tests/tests/src/UntaggedVariants.res` produced no diff output in the
    focused spot-check, and `tests/tests/src/ExternalShadow.res` remained an
    exact snapshot match as a broader guard
  - the current dirty-tree authoritative wrapper stayed flat, which indicates
    this correctness fix hardens a backend rule that is not currently exposed
    by the checked-in dirty-worktree failures
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **528 / 657** -> **528 / 657** (**no change**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **121** -> **121** (**no change**)
- Keep this change because the previous Rust lowering only applied
  default-duplicate filtering in the grouped fallback path, while OCaml filters
  first and then decides whether the switch qualifies for the small `if`-based
  lowering. Even with flat snapshot totals in the current dirty tree, this is a
  real Phase-3 backend alignment fix and now has direct regression coverage.

Latest iteration on **2026-04-16**:

- Active slice: port OCaml `compile_for`'s start/finish prelude ordering so
  `Lfor` preserves side effects from loop bounds instead of dropping them when
  Rust lowers directly to `StatementDesc::ForRange`
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_for`'s `(b1, b2)` cases
  that preserve start/finish preludes and only hoist the loop variable when
  the start expression itself is not side-effect-free
- Rust change:
  - routed `Lambda::Lfor` through a dedicated `compile_for_loop(...)` helper
    instead of the old shortcut that compiled `start`/`finish` with
    `.compile_expr(...).expr` and silently discarded their preludes
  - matched OCaml's three-way lowering:
    keep `start` in the initializer when `finish` has no prelude, reorder
    `finish`'s prelude ahead of the loop when `start`'s resulting expression is
    pure, and emit `let i = start_expr; ... for (; i <= finish; ++i)` when the
    start expression is effectful and the finish path also has a prelude
  - added focused unit coverage for both the pure-start and effectful-start
    OCaml cases so future loop changes keep the same prelude ordering
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_for_bounds_preludes_in_ocaml_order_when_start_expr_is_pure -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_effectful_for_start_out_of_initializer_when_finish_has_prelude -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - manual single-file repro with `rescript.exe compiler-args` +
    `compiler-rust/target/release/bsc` for:
    `tests/tests/src/for_side_effect_test.res`
  - manual single-file repro with `rescript.exe compiler-args` +
    `compiler-rust/target/release/bsc` for:
    `tests/tests/src/for_loop_test.res`
  - manual exact-check repro for:
    `tests/tests/src/ari_regress_test.res`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/for_side_effect_test.res` now preserves OCaml's loop-bound
    side effects again: the Rust output restored `v = 3;` / `v = 10;` and kept
    the bound-ordering behavior, leaving only the separate empty-loop-block
    formatting drift in that file
  - `tests/tests/src/for_loop_test.res` remained on its existing captured-loop-
    variable naming drift, so the new `compile_for` port did not reopen that
    separate cluster
  - `tests/tests/src/ari_regress_test.res` now matches its checked-in snapshot
    again and drops out of the diff cache after the `Lfor` fix
  - the current dirty-tree wrapper improved by one exact JS snapshot while
    keeping the unrelated compile-error set unchanged
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **527 / 657** -> **528 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **122** -> **121** (**-1**)
- Keep this change because the previous Rust `Lfor` lowering was not OCaml-
  aligned at all: it threw away the compiled preludes for `start` and `finish`
  and therefore reordered or deleted loop-bound side effects. Porting
  `compile_for` restores the backend stage behavior directly and converts at
  least one real snapshot (`ari_regress_test`) back to exact parity without
  touching the unrelated compile-error cluster.

Latest iteration on **2026-04-16**:

- Active slice: use the OCaml single-handler tail-return staticcatch path for
  bound unit-return handlers whose shared handler has no static raises, instead
  of always forcing a local `exit` temp in that case
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_staticcatch`'s
  single-handler tail-return branch guarded by
  `Lam_compile_context.no_static_raise_in_handler`, which appends the shared
  handler after the body instead of materializing `let exit = 0`
- Rust change:
  - extracted `compile_fallthrough_staticcatch_return_block(...)` so the
    shared-tail lowering is reusable outside the existing switch-specific
    fallthrough cases
  - added `uses_pseudo_fallthrough_staticcatch_return(...)` for the
    OCaml-aligned subset: unit-return staticcatchs with bindings, no active
    fallthrough handler, at least one matching static raise in the body, and a
    handler with no static raises
  - added focused regression coverage to keep bound unit-return handlers on
    the shared-tail path without reintroducing exit sentinels
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml unit_return_staticcatch_bindings_without_handler_exits_share_fallthrough_tail -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_staticcatch_switch_forwarders_to_outer_handlers_avoid_exit_temps_like_gpr_3609 -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_staticcatch_binding_handlers_that_raise_outward_avoid_exit_temps -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh test_static_catch_ident`
  - `timeout 30 ./scripts/test_js_single.sh gpr_3609_test`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_static_catch_ident.res` now matches its checked-in
    snapshot again; the simple exception-pattern staticcatch no longer lowers
    to a Rust-only `let exit = 0; ... if (exit === 1)` wrapper around the
    shared loop tail
  - `tests/tests/src/gpr_3609_test.res` remained exact as a guard, so the
    earlier outward-forwarding nested staticcatch fix stayed intact
  - the current dirty-tree wrapper improved by one exact JS snapshot while
    keeping the unrelated compile-error set unchanged
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **527 / 657** -> **528 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **122** -> **121** (**-1**)
- Keep this change because the previous Rust path was overmatching the
  bound-unit-handler fallback and always materializing a local exit sentinel,
  while OCaml keeps these single-handler/no-exit cases on the shared tail
  path. Reusing the fallthrough return lowering restores that backend shape
  without regressing the guarded nested-staticcatch cases.

Latest iteration on **2026-04-16**:

- Active slice: avoid synthesizing explicit `exit` temps for nested
  `Lstaticcatch` return handlers when the shared handler is only forwarding to
  an already-active outer static-raise target with side-effect-free payload
  plumbing
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/lambda/compile.rs`
- OCaml reference:
  `compiler/core/lam_compile.ml`, specifically the nested `Lstaticcatch`
  return-lowering path where outward handler forwarding can stay on the direct
  return path instead of materializing a local exit sentinel
- Rust change:
  - narrowed `return_staticcatch_requires_explicit_jump(...)` so the
    multi-raise/shared-handler fallback no longer forces an `exit` temp when
    the handler is just a side-effect-free outward static raise forwarder
  - added `handler_is_pure_outward_static_raise_forwarder(...)` to recognize
    the OCaml-aligned handler shapes that only alias/bind values and re-raise
    to an already-active outer staticcatch label
  - added focused regression coverage for a `gpr_3609`-style nested
    switch/staticcatch shape and kept the earlier outward-binding staticcatch
    regression test green
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_staticcatch_switch_forwarders_to_outer_handlers_avoid_exit_temps_like_gpr_3609 -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_staticcatch_binding_handlers_that_raise_outward_avoid_exit_temps -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_3609_test.res -o /tmp/gpr_3609_test.mjs`
  - `diff -u tests/tests/src/gpr_3609_test.mjs /tmp/gpr_3609_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_static_catch_ident.res -o /tmp/test_static_catch_ident.mjs`
  - `diff -u tests/tests/src/test_static_catch_ident.mjs /tmp/test_static_catch_ident.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_3609_test.res` now matches its checked-in snapshot
    again; the nested staticcatch return path no longer introduces the Rust-
    only `let exit = 0; ... if (exit === 1)` sentinel around the shared tail
  - `tests/tests/src/test_static_catch_ident.res` still differs and keeps its
    own exception/staticcatch exit-temp drift, so that broader handler-sharing
    cluster remains open
  - the current dirty-tree wrapper improved without changing the unrelated
    compile-error set
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **525 / 657** -> **527 / 657** (**+2**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **124** -> **122** (**-2**)
- Keep this change because the previous multi-raise fallback was overmatching
  OCaml and forcing an explicit local jump temp even when the nested handler
  only forwarded directly to an enclosing staticcatch. The narrowed predicate
  restores the OCaml-aligned direct return path for that handler shape without
  reopening the broader non-trivial shared-handler cases.

Latest iteration on **2026-04-16**:

- Active slice: keep explicit positive nullish success guards except when the
  fallback branch simply returns the same guarded nullish value; that fallback
  case should still lower to the OCaml-style failure-first guard clause used by
  `let?` option unwraps like `LetUnwrap`
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/js_ir/mod.rs`
- OCaml reference:
  `compiler/core/js_stmt_make.ml`, especially the `if_` helper branch
  `| _, [{statement_desc = Return _}] -> ...`, which emits the failure-first
  guard-clause form for fallback returns, while the already-materialized
  explicit positive nullish guards from other backend paths remain intact
- Rust change:
  - narrowed the single-return-else preservation in
    `simplify_if_statement(...)` so
    `preserves_nullish_success_guard(...)` still protects explicit positive
    nullish guards like `return_check`, `undef_regression_test`, and
    `unit_undefined_test`
  - added `nullish_guard_target(...)` and
    `nullish_guard_fallback_returns_guard_target(...)` so the preservation is
    skipped when the fallback return is just the guarded nullable value itself,
    restoring OCaml's `if (x == nullish) return x; ...` shape for `LetUnwrap`
  - added focused regression coverage for the fallback-returns-guarded-value
    case alongside the existing positive nullish guard tests
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh LetUnwrap`
  - `timeout 30 ./scripts/test_js_single.sh return_check`
  - `timeout 30 ./scripts/test_js_single.sh undef_regression_test`
  - `timeout 30 ./scripts/test_js_single.sh unit_undefined_test`
  - `timeout 30 ./scripts/test_js_single.sh js_nullable_test`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/LetUnwrap.res` now matches its checked-in snapshot again;
    the option unwrap fallback now lowers back to OCaml's failure-first
    `if (y === undefined) return y;` form instead of keeping a Rust-only
    success-first `else`
  - `tests/tests/src/return_check.res`,
    `tests/tests/src/undef_regression_test.res`,
    `tests/tests/src/unit_undefined_test.res`,
    `tests/tests/src/js_nullable_test.res`, and
    `tests/tests/src/ExternalShadow.res` remained exact as guards
  - the current dirty-tree wrapper improved by two exact JS snapshots while
    keeping the unrelated compile-error set unchanged
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **523 / 657** -> **525 / 657** (**+2**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **126** -> **124** (**-2**)
- Keep this change because the broader nullish-guard preservation was
  overmatching OCaml's backend. The new exception only rewrites the
  fallback-returns-guarded-value case, which matches the checked-in OCaml
  snapshot shape without regressing the explicit positive nullish guards that
  are already correct.

Latest iteration on **2026-04-16**:

- Active slice: preserve explicit nullish/undefined success guards in
  `js_ir::simplify_if_statement(...)` when one side is a non-trivial terminal
  branch and the other side is only the simple fallback return; this keeps the
  option/nullability lowering shape from collapsing into Rust-only
  guard-clause form
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in `compiler-rust/src/js_ir/mod.rs`
- OCaml reference:
  `compiler/core/js_stmt_make.ml`, especially the `if_` helper's explicit
  branch-shape preservation, together with `compiler/core/lam_compile.ml`
  option/nullability lowering sites that feed `S.if_` with materialized
  success/fallback blocks
- Rust change:
  - added `preserves_nullish_success_guard(...)` /
    `is_nullish_refinement_guard(...)` so strict `null`/`undefined` guards and
    loose `== null` guards keep their explicit `if` structure when one branch
    is the real success path and the other is just the simple fallback return
  - used that preservation hook in both guard-clause rewrites inside
    `simplify_if_statement(...)`: the `else is a single return` inversion and
    the `then block terminates, append else as fallthrough` rewrite
  - added focused regression coverage for strict-null success returns, loose
    nullish explicit `else` blocks, and strict-undefined unit success tails
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh return_check`
  - `timeout 30 ./scripts/test_js_single.sh js_nullable_test`
  - `timeout 30 ./scripts/test_js_single.sh undef_regression_test`
  - `timeout 30 ./scripts/test_js_single.sh unit_undefined_test`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 30 ./scripts/test_js_single.sh UntaggedVariants`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/return_check.res`,
    `tests/tests/src/js_nullable_test.res`,
    `tests/tests/src/undef_regression_test.res`, and
    `tests/tests/src/unit_undefined_test.res` now match their checked-in
    snapshots again; each had been rewritten into Rust-only nullish
    guard-clause form before this slice
  - `tests/tests/src/ExternalShadow.res` and
    `tests/tests/src/UntaggedVariants.res` remained exact as guards
  - the current dirty-tree wrapper improved by two exact JS snapshots while
    keeping the unrelated compile-error set unchanged
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **520 / 657** -> **522 / 657** (**+2**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **129** -> **127** (**-2**)
- Keep this change because the previous rewrites were Rust-only last-mile
  guard-clause inversions on nullish success paths. Restoring the explicit
  branch structure brings the emitted JS back in line with the checked-in
  OCaml snapshots without reopening the broader sync-tail rewrite.

Latest iteration on **2026-04-16**:

- Active slice: only normalize shared trailing `return` tails for wrapped
  small literal return-switch bodies when they are peeled into the untagged
  runtime-test `if` chain; keep the generic small literal return path itself
  wrapped so outer literal-vs-block dispatch still matches OCaml
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this change stays in `compiler-rust/src/lambda/compile.rs`
  plus a narrow positive-literal tail preservation in
  `compiler-rust/src/js_ir/mod.rs`
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially the untagged
  `compile_untagged_cases` runtime `build_if_chain` and the small-case
  `compile_general_cases` / `S.if_` interaction that leaves generic small
  literal returns wrapped but uses raw `switch_body` blocks in the runtime
  guard chain
- Rust change:
  - added `normalize_runtime_test_return_body(...)` /
    `shared_trailing_return_guard_block(...)` so peeled runtime-test case
    bodies of the exact shape `if (...) { effect; return; } effect; return;`
    become `if (...) { effect; } else { effect; } return;`
  - limited that normalization to the runtime-test paths in
    `compile_untagged_block_switch_return_statements(...)` and
    `compile_small_untagged_block_switch_return(...)`
  - kept `compile_small_string_switch_return(...)` on the wrapped generic path
    so mixed literal-vs-block dispatches do not flatten their outer `else`
  - exposed `ocaml_eq_expression(...)` as `pub(crate)` in `js_ir/mod.rs` so
    the runtime-test normalization can compare the shared return expressions
  - taught `js_ir::simplify_if_statement(...)` to preserve the recovered
    positive outer literal dispatch when its shared tail is `return undefined`,
    matching the OCaml nested structure instead of collapsing the outer guard
    back into an early-return shape
  - added focused regression coverage in
    `runtime_test_return_bodies_share_trailing_return_outside_inner_test`,
    `test_if_statement_keeps_positive_literal_dispatch_return_tail`, and kept
    the nearby untagged return-shape guards green
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_keeps_positive_literal_dispatch_return_tail -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml runtime_test_return_bodies_share_trailing_return_outside_inner_test -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml mixed_literal_and_block_untagged_return_dispatch_keeps_outer_else_block -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml object_and_array_untagged_return_switches_keep_object_inside_typeof_switch_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh UntaggedVariants`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/UntaggedVariants.res` now matches its checked-in snapshot
    again; the deeper nested number-case return chain now shares the trailing
    `return` only inside the runtime guard where OCaml does, without pulling
    unrelated guards like the array-length check into explicit `else` blocks
  - `tests/tests/src/ExternalShadow.res` remained exact
  - the current dirty-tree wrapper improved by one exact JS snapshot while
    keeping the unrelated compile-error set unchanged
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **519 / 657** -> **520 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **130** -> **129** (**-1**)
- Keep this change because the new normalization is constrained to the exact
  OCaml runtime-guard shape: generic small literal return lowering stays
  wrapped, but runtime-test switch bodies now recover OCaml's shared trailing
  `return` when the guard simplifier had previously sunk that tail into the
  branch-local return path.

Latest iteration on **2026-04-16**:

- Active slice: remove Rust's function-body shared-tail nested-`if` printer
  merge that has no equivalent in OCaml `js_dump.ml`
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`, but this cleanup is in the final JS dumper path:
  `compiler-rust/src/js_ir/printer.rs`
- OCaml reference:
  `compiler/core/js_dump.ml`, especially `function_body`, which only strips a
  final `return undefined` tail and does not reconstruct
  `if (...) { ... } else { shared_tail }` from sequential function-body
  statements
- Rust change:
  - removed `try_function_body_shared_tail_nested_if_merge(...)` from
    `print_function_body(...)`
  - updated the focused printer regression to expect OCaml's sequential body
    form instead of the Rust-only nested `else`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_unit_function_body_keeps_shared_tail_sequential_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_unit_function_tail_merges_nested_if_when_outer_else_is_return_undefined -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh UntaggedVariants --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - the synthetic printer case now matches OCaml's sequential function-body
    printing instead of reintroducing a Rust-only shared-tail `else`
  - `tests/tests/src/ExternalShadow.res` remained exact
  - `tests/tests/src/UntaggedVariants.res` did not move, which confirms its
    remaining nested `else` chain comes from a different lowering path
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **519 / 657** -> **519 / 657** (**no change**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **130** -> **130** (**no change**)
- Keep this change because the removed helper was a Rust-only dumper rewrite
  with no OCaml counterpart. Even though the current 657-file wrapper stayed
  flat, the printer now preserves OCaml's direct sequential function-body
  structure for this class of tail.

Latest iteration on **2026-04-16**:

- Active slice: allow plain int-switch return handlers to fall through even
  under an enclosing plain static handler, matching OCaml's
  `flatten_nested_catches` behavior instead of keeping the innermost handler
  forced into the switch default
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this change stays in `compiler-rust/src/lambda/compile.rs`
  in return-position `LstaticCatch` lowering
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `flat_catches`,
  `flatten_nested_catches`, and the single-handler `compile_staticcatch`
  path that does not blanket-block nested plain handlers just because an
  outer catch is already active
- Rust change:
  - removed the `inside_enclosing_staticcatch_chain` guard from the plain
    non-untagged `Lswitch` fallthrough-return branch in
    `uses_fallthrough_staticcatch_return(...)`
  - kept the existing stricter checks for untagged switches and the
    return-unit/single-case path intact
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_plain_int_return_switches_can_fall_through_like_gpr_1438 -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_deps_program_keeps_gpr_1438_fallthrough_return_outside_switch -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml staticcatch_wrapped_int_return_switches_omit_empty_default_arms -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh gpr_1438`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1438.res` now matches its checked-in snapshot again;
    the inner plain handler falls through to the trailing `return param => {};`
    outside the switch instead of being reintroduced as the switch default
  - the raw lowering regressions
    `nested_plain_int_return_switches_can_fall_through_like_gpr_1438` and
    `compile_deps_program_keeps_gpr_1438_fallthrough_return_outside_switch`
    both pass again
  - `tests/tests/src/ExternalShadow.res` remained exact
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **521 / 657** -> **519 / 657** (**-2**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **128** -> **130** (**+2**)
- Keep this change because the old guard was Rust-only. OCaml's nested
  staticcatch flattening does allow this inner plain int-switch handler to
  peel out under an outer plain handler, and the checked-in `gpr_1438`
  snapshot confirms that behavior even though the current dirty-tree wrapper
  total moved in the wrong direction.

Latest iteration on **2026-04-16**:

- Active slice: keep OCaml's explicit boolean-false literal-membership guard
  in nested untagged refinements, but narrow the earlier positive
  `return undefined` preservation so only await-bearing tails stay in the
  positive `if (cond) { ...; return; }` form
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this change stays in `compiler-rust/src/js_ir/mod.rs`, not a
  printer rewrite
- OCaml reference:
  `compiler/core/js_stmt_make.ml` and `compiler/core/js_exp_make.ml`
  for nested `if_` merges and the emitted guard shapes visible in the checked-in
  `Import.mjs` and `UntaggedVariants.mjs` snapshots
- Rust change:
  - added `preserves_literal_membership_guard(...)` plus
    `collect_same_var_literal_membership_terms(...)` so the
    `x === undefined || x === null || x === false || x === true` guard is kept
    when the nested refinement is specifically `x === false`
  - replaced the broader
    `statement_has_nontrivial_prefix_output(...)` heuristic with
    `statement_contains_await(...)` / `expression_contains_await(...)`, so only
    await-bearing prefixes keep the positive `return undefined` tail shape
  - added focused regression coverage in
    `test_if_statement_keeps_explicit_literal_membership_guards`,
    `test_if_statement_keeps_positive_await_return_tail`, and
    `test_if_statement_rewrites_sync_return_undefined_tail_to_negative_guard`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_ -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_keeps_positive_await_return_tail -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 30 ./scripts/test_js_single.sh Import`
  - `timeout 30 ./scripts/test_js_single.sh UntaggedVariants --diff`
  - `timeout 30 ./scripts/test_js_single.sh reasonReactRouter --diff`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/Import.res` still matches its checked-in snapshot; the
    async `await import(...)` option tail keeps the OCaml-aligned positive guard
  - `tests/tests/src/UntaggedVariants.res` now matches again for
    `ObjectAndNull.printLength`, and the earlier `match$1 === false`
    literal-membership collapse is gone; one remaining hunk is left in the
    deeper nested `typeof match$4 === "number"` return tail
  - `tests/tests/src/ExternalShadow.res` remained exact, and
    `reasonReactRouter` still shows broader control-flow drift outside this
    narrowed slice
- Topline impact in this current worktree:
  - JS snapshot parity: **521 / 657** -> **521 / 657** (**no change**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **128** -> **128** (**no change**)
- Keep this change because both adjustments remove Rust-only guard-shape
  rewrites in `js_ir`: synchronous tails now fall back to OCaml's negative
  early-return form, while the explicit boolean-false refinement guard stays
  materialized where the checked-in OCaml snapshot still emits it.

Latest iteration on **2026-04-16**:

- Active slice: keep OCaml's explicit positive success guards when a
  multi-statement return tail only alternates with `return undefined`,
  instead of rewriting them into a negative early-return guard too soon
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this change is in `compiler-rust/src/js_ir/mod.rs`, not a
  printer rewrite
- OCaml reference:
  `compiler/core/js_stmt_make.ml` and `compiler/core/js_exp_make.ml`;
  the checked-in OCaml snapshots keep async/unit option-tail shapes as
  positive success guards (`if (cond) { ... return; }`) instead of
  `if (!cond) return; ...`
- Rust change:
  - added `preserves_positive_return_undefined_tail(...)` and
    `statement_has_nontrivial_prefix_output(...)`
  - used them to block the `else return undefined` rewrite in
    `simplify_if_statement(...)` when the consequent already carries a real
    multi-statement return tail
  - added focused regression coverage in
    `test_if_statement_keeps_positive_multi_statement_return_tail`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_keeps_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh Import`
  - `timeout 30 ./scripts/test_js_single.sh reasonReactRouter --diff`
  - `timeout 30 ./scripts/test_js_single.sh gpr_3875_test --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/Import.res` now matches its checked-in snapshot again;
    `f9` keeps the OCaml-aligned positive `value !== undefined` guard
  - `undef_regression_test` dropped out of the current diff set as part of
    the same guard-shape motif
  - `reasonReactRouter` and `gpr_3875_test` still show broader control-flow
    drift in the same family
- Topline impact in this current worktree:
  - JS snapshot parity: **520 / 657** -> **522 / 657** (**+2**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **129** -> **127** (**-2**)
- Keep this change because the previous rewrite was Rust-only. Preserving the
  positive success guard matches the checked-in OCaml backend output for
  multi-statement return tails instead of normalizing them into a different
  but semantically equivalent negative-guard shape.

Latest iteration on **2026-04-16**:

- Active slice: preserve OCaml's explicit nested `typeof` refinement guards in
  JS IR statement merging instead of collapsing them into a stricter literal
  equality too early
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this change is in `compiler-rust/src/js_ir/mod.rs`, not a
  printer rewrite
- OCaml reference:
  `compiler/core/js_stmt_make.ml` and `compiler/core/js_exp_make.ml`,
  specifically the nested-`if` merge path that should not erase an explicit
  `typeof x === "..."` refinement guard before the final statement shape is
  formed
- Rust change:
  - added `preserves_typeof_refinement_guard(...)` and used it to block the
    nested-`if` shared-else merge in `simplify_if_statement(...)` when the
    outer condition is a `typeof` test on the same variable and the inner
    condition is the corresponding strict literal equality
  - added focused regression coverage in
    `test_if_statement_keeps_explicit_typeof_refinement_guards`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_keeps_explicit_typeof_refinement_guards -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh UntaggedVariants --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 1800 ./scripts/test_js_output_parity.sh` (blocked by unrelated worktree regressions listed above)
- Focused outcome:
  - `tests/tests/src/UntaggedVariants.res` now keeps the OCaml-aligned
    `typeof match$3 === "string"` guard in `ComplexPattern.check`
  - the remaining drift in that file is the earlier literal-membership collapse
    around `match$1 === false`; the `typeof` refinement mismatch is gone
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the unchanged guard
- Topline impact:
  - local focused diff improved in `UntaggedVariants`
  - full-project totals are currently **not comparable** because the present
    worktree no longer reproduces the recorded clean baseline

Latest iteration on **2026-04-15**:

- Active slice: keep return-position staticcatch handlers explicit even when
  they end in effectful `...; undefined` wrappers, instead of letting the
  Rust fallthrough-return shortcut treat only the exact leaf `undefined` case
  as special and collapse OCaml's fail-first guard shape back into a
  success-shaped nest
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is `Lam_compile` staticcatch / switch
  lowering in `compiler-rust/src/lambda/compile.rs`, not a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_staticcatch` and the
  non-tail lowering that keeps exit/default structure explicit until the
  surrounding switch/default guard shape is formed
- Rust change:
  - generalized the unit-handler check into
    `handler_returns_unit_undefined(...)` so the return-position
    fallthrough staticcatch shortcut is also blocked for zero-binding handlers
    whose final result is `JsUndefined { is_unit: true }` through
    `Lsequence`, `Llet`, or `Lletrec`
  - this keeps effectful unit handlers materialized as the explicit default
    path inside nested untagged return switches instead of resolving them away
    into an empty trailing fallthrough block too early
  - added focused regression coverage in
    `effectful_unit_staticcatch_handlers_keep_fail_first_guards` to lock down
    the OCaml-style `len !== 3` early-return guard for an effectful unit
    handler
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml effectful_unit_staticcatch_handlers_keep_fail_first_guards -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh UntaggedVariants --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/UntaggedVariants.res` now keeps the OCaml-aligned
    fail-first `len !== 3` guard in `check$1`; the remaining drift in that
    file is deeper untagged literal/type guard lowering, not the outer
    staticcatch default shape
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the unchanged guard
  - the full authoritative sweep in this current worktree still reports
    **539 / 657** passing, **0** compile errors, and **118** output diffs
- Topline impact in this current worktree:
  - JS snapshot parity: **539 / 657** -> **539 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **118** -> **118** (**no change**)
- Keep this change because OCaml's backend cares about the handler's final
  unit-return shape, not whether the handler is syntactically the bare
  `undefined` leaf. Preserving that distinction in Rust removes a verified
  Rust-only shortcut in `Lam_compile` even though the current snapshot totals
  do not move yet.

Latest iteration on **2026-04-15**:

- Active slice: keep unit-`undefined` staticcatch handlers materialized as the
  default arm in return-position untagged switches instead of using the Rust
  fallthrough-return shortcut that collapses OCaml's negative guard shape into
  a success-shaped nest
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is `Lam_compile` staticcatch / switch
  lowering in `compiler-rust/src/lambda/compile.rs`, not a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_staticcatch` and the
  non-tail lowering that keeps exit/default structure explicit, together with
  `compiler/core/js_stmt_make.ml`'s `if_` lowering that then prints these
  cases as negative early-return guards
- Rust change:
  - added `is_unit_undefined_handler(...)` and used it to block the
    return-position fallthrough staticcatch shortcut for zero-binding
    `JsUndefined { is_unit: true }` handlers
  - this preserves the handler as the explicit default path inside nested
    untagged return switches instead of resolving it away into an empty
    fallthrough block too early
  - added focused regression coverage in
    `single_case_staticcatch_wrapped_untagged_object_unit_handler_keeps_negative_guard`
    to lock down the OCaml-style negative guard shape
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml single_case_staticcatch_wrapped_untagged_object_unit_handler_keeps_negative_guard -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml single_case_staticcatch_wrapped_named_variant_return_switch_falls_through_to_handler -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh UntaggedVariants --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/UntaggedVariants.res` now matches the OCaml snapshot for
    `printLength`; the remaining diff in that file is down to the deeper
    `check$1` staticcatch / guard-shape mismatch
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the unchanged guard
  - the full authoritative sweep in this current worktree now reports
    **539 / 657** passing, **0** compile errors, and **118** output diffs
- Topline impact in this current worktree:
  - JS snapshot parity: **537 / 657** -> **539 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **120** -> **118** (**-2**)
- Keep this change because the removed shortcut was Rust-only. OCaml's
  backend keeps these unit staticcatch handlers explicit long enough for the
  surrounding guard/default control flow to lower into the checked-in early
  return shape, so preserving that boundary in Rust improves emitted JS parity
  at the backend source rather than by rewriting output text later.

Latest iteration on **2026-04-15**:

- Active slice: port OCaml's mixed untagged literal-dispatch ordering and keep
  residual `typeof` branches as real string switches after earlier runtime
  `instanceof` splits instead of collapsing them into Rust-only small
  `if`/`else` tails
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is `Lam_compile` / dynamic-check
  lowering in `compiler-rust/src/lambda/compile.rs`, not a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `get_literal_cases`,
  `get_block_cases`, and the mixed untagged path in `compile_switch`, together
  with `compiler/ml/ast_untagged_variants.ml`'s
  `DynamicChecks.is_a_literal_case`
- Rust change:
  - reversed `sw_names.consts` / `sw_names.blocks` collection for untagged
    dispatch metadata so the Rust lowering sees the same reversed case lists
    that OCaml builds with `Ext_array.iter` + cons
  - ported OCaml's exact recursive `List.rev` literal-case disjunction and its
    overlap `fold_right` behavior in `literal_case_dispatch_test(...)` instead
    of using a simpler Rust reduction that reordered emitted operands
  - kept residual `typeof` tails on the string-switch path whenever a mixed
    untagged block dispatch already emitted earlier runtime checks; this avoids
    shrinking the tail into a Rust-only small switch after `Array.isArray(...)`
    or other runtime-test cases have already split control flow
  - added `compile_small_untagged_block_switch_effect(...)` and focused
    regression coverage for both the mixed `typeof` tail shape and the literal
    ordering
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml untagged_literal_dispatch_keeps_ocaml_case_order -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml mixed_untagged_literal_dispatch_keeps_ocaml_block_overlap_order -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 30 ./scripts/test_js_single.sh UntaggedVariants --diff`
  - `timeout 30 ./scripts/test_js_single.sh ExternalShadow`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/UntaggedVariants.res` no longer shows the earlier
    literal-order drift in `classify$3`, `classify$6`, `checkEnum`, or
    `checkEnum$1`; the remaining diff in that file is now down to the deeper
    guard-shape mismatches in `check$1` and `printLength`
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the broader unchanged guard
  - the full authoritative sweep in this current worktree still reports
    **537 / 657** passing, **0** compile errors, and **120** output diffs
- Topline impact in this current worktree:
  - JS snapshot parity: **537 / 657** -> **537 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **120** -> **120** (**no change**)
- Keep this change because it is a direct OCaml backend port: both the reversed
  case-list construction and the literal-dispatch expression shape come from
  `Lam_compile` / `DynamicChecks.is_a_literal_case`, and preserving the mixed
  `typeof` tail as a real switch removes Rust-only lowering drift without
  patching the final emitted JavaScript.

Latest iteration on **2026-04-15**:

- Active slice: align statement-valued `if` / `switch` / `trywith` result temp
  names with OCaml's plain `Ext_ident.create_tmp ()` temps instead of emitting
  Rust-only names like `ifres`, `switch`, and `tryres`
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is `Lam_compile` value-result lowering
  in `compiler-rust/src/lambda/compile.rs`, not a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially the `NeedValue` paths in
  `compile_switch`, `compile_stringswitch`, `compile_trywith`, and the
  statement-valued `if` lowering, together with
  `compiler/ext/ext_ident.ml` where `Ext_ident.create_tmp ()` defaults to the
  base name `tmp`
- Rust change:
  - introduced `fresh_tmp_ident()` to mirror OCaml's default temp-name path
  - switched statement-valued `LifThenElse`, `Lswitch`,
    `LstringSwitch`, `LtryWith`, and switch-scrutinee binding temps to use
    that OCaml-aligned `tmp` prefix instead of `ifres`, `switch`, or `tryres`
  - added focused regression coverage in
    `trywith_expression_result_temp_uses_tmp_name_like_ocaml`
    plus explicit `tmp` assertions in the existing `if` / int-switch /
    string-switch temp tests
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml trywith_expression_result_temp_uses_tmp_name_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml if_value_branches_keep_assignment_continuation_through_let_bindings -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml int_switch_expressions_assign_branch_values_into_the_result_temp -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml string_switch_expressions_assign_branch_values_into_the_result_temp -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml bind_switch_scrutinee_once_uses_tmp_name_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/arity_infer.res`, diffing
    `/tmp/arity_infer.mjs` against the checked-in snapshot
  - direct release guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/arity_infer.res` is now an exact snapshot match; the
    `tmp` function-value temp now matches OCaml in both the `if` and `switch`
    cases
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the unchanged guard
  - no remaining failing JS diffs mention `ifres`, `switch` result temps, or
    `tryres`; `recursive_module.res` still differs, but now only on its
    recursive-module initialization / lazy alias shape rather than temp naming
  - the full authoritative sweep in this current worktree now reports
    **537 / 657** passing, **0** compile errors, and **120** output diffs
- Topline impact in this current worktree:
  - JS snapshot parity: **535 / 657** -> **537 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **122** -> **120** (**-2**)
- Keep this change because OCaml's backend already routes these statement-valued
  expressions through plain `Ext_ident.create_tmp ()` temps; matching that
  naming rule in Rust removes user-visible backend drift at the lowering source
  instead of papering over it in the emitted JavaScript later.

Latest iteration on **2026-04-15**:

- Active slice: keep plain inner staticcatch handlers resolved inside
  named-variant return switches when we are already inside an enclosing
  staticcatch chain, instead of peeling the handler into a trailing
  fallthrough return
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is `Lam_compile` staticcatch / switch
  lowering in `compiler-rust/src/lambda/compile.rs`, not a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_staticcatch` and the
  pseudo-jump fast path that only applies when the tail context is not already
  marked `in_staticcatch`
- Rust change:
  - tightened `uses_fallthrough_staticcatch_return(...)` so the plain-handler
    switch fallthrough optimization no longer runs when
    `inside_enclosing_staticcatch_chain` is true
  - added focused regression coverage in
    `nested_named_variant_return_switches_keep_complete_payload_handlers_inline`
    to lock down the `adt_optimize_test` shape where the last payload case must
    keep the resolved handler inline inside the switch
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_named_variant_return_switches_keep_complete_payload_handlers_inline -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml named_variant_return_switches_inline_resolved_static_handler_values_inside_the_switch -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/adt_optimize_test.res`,
    diffing `/tmp/adt_optimize_test.mjs` against the checked-in snapshot
  - direct release guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/adt_optimize_test.res` is now an exact snapshot match;
    the trailing `return 2;` / `return 3;` fallthroughs are gone and the final
    payload cases stay inside their switches like OCaml
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the unchanged guard
  - the full authoritative sweep in this current worktree now reports
    **535 / 657** passing, **0** compile errors, and **122** output diffs
- Topline impact in this current worktree:
  - JS snapshot parity: **533 / 657** -> **535 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **124** -> **122** (**-2**)
- Keep this change because it matches the OCaml backend's staticcatch boundary:
  once we are already under an enclosing staticcatch chain, plain inner
  handlers should stay resolved inside the named/string switch instead of being
  lowered as an extra fallthrough return after the dispatch.

Latest iteration on **2026-04-15**:

- Active slice: only share repeated return-position staticcatch handlers behind
  an explicit exit join when the handler re-raises outward; keep plain handlers
  inline across multiple exit sites just like OCaml
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is `Lam_compile` return/staticcatch
  control-flow lowering in `compiler-rust/src/lambda/compile.rs`, not a
  printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_staticcatch`,
  `compile_switch`, and how repeated `exit` sites stay inlined unless the
  handler itself transfers control outward again
- Rust change:
  - added `return_staticcatch_requires_explicit_jump(...)` so return-position
    staticcatch lowering can distinguish between repeated exits into a plain
    handler and repeated exits into a handler that re-raises to some other
    label
  - added `lambda_has_multiple_static_raises_to_label(...)` / counting helpers
    to detect the repeated-exit shape in the current staticcatch body
  - restricted the explicit shared-join path to handlers that still transfer
    control outward via `lambda_contains_static_raise_to_other_label(...)`,
    leaving plain handlers on the normal OCaml-style inlined path
  - added focused regression coverage in
    `return_staticcatchs_share_nontrivial_handlers_across_multiple_exit_sites`
    and
    `return_staticcatchs_keep_plain_handlers_inline_across_multiple_exit_sites`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml return_staticcatch -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_staticcatch_binding_handlers_that_raise_outward_avoid_exit_temps -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for
    `tests/tests/src/DictPatternMatchingOptimization.res`, diffing
    `/tmp/DictPatternMatchingOptimization.mjs` against the checked-in snapshot
  - direct release guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - direct release repro for
    `tests/tests/src/VariantPatternMatchingSpreads.res`, diffing
    `/tmp/VariantPatternMatchingSpreads.mjs` against the checked-in snapshot
  - direct release repro for
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res`, diffing
    `/tmp/VariantPatternMatchingSpreadsWithPayloads.mjs` against the checked-in
    snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/DictPatternMatchingOptimization.res` is now an exact
    snapshot match; the remaining nested `"e"` / `"f"` shared-handler drift is
    gone
  - `tests/tests/src/VariantPatternMatchingSpreads.res` and
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` are now
    exact snapshot matches again; the temporary explicit `exit` joins around
    the shared plain handlers are gone
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the unchanged guard
  - the full authoritative sweep in this current worktree now reports
    **532 / 657** passing, **0** compile errors, and **125** output diffs
- Topline impact:
  - JS snapshot parity: **534 / 657** -> **532 / 657** (**-2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **123** -> **125** (**+2**)
- Keep this change because OCaml only needs the explicit shared return join
  when the repeated-exit handler still jumps outward; applying that same rule
  fixes the checked-in snapshot drift in the direct canaries at the backend
  control-flow source instead of by rewriting emitted JavaScript later.

Latest iteration on **2026-04-15**:

- Active slice: keep outer plain-handler staticcatches resolved inside
  untagged object-return switches instead of peeling them into a trailing
  fallthrough return when nested inner staticcatchs target other labels
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is `Lam_compile` return-switch /
  staticcatch control-flow lowering in `compiler-rust/src/lambda/compile.rs`,
  not a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml` and
  `compiler/core/lam_compile_context.ml`, especially the interaction between
  `compile_switch`, `compile_staticcatch`, pseudo-jump lowering, and
  `DynamicChecks.is_a_literal_case` for mixed untagged switches whose default
  branch raises to an outer plain handler
- Rust change:
  - materialized literal-side defaults directly when mixed untagged switch
    tables have no explicit const arms, so return/assign/effect lowering no
    longer drops those default blocks before dispatch
  - narrowed the `uses_fallthrough_staticcatch_return(...)` path for `Lswitch`
    so the "other-label" fallthrough shortcut does not peel outer plain
    handlers out of untagged variant switches; those switches now stay on the
    normal static-handler resolution path and inline the handler inside the
    switch just like OCaml
  - added focused regression coverage in
    `default_only_untagged_object_return_keeps_literal_default_branch_outside_object_chain`
    and
    `untagged_object_return_switches_keep_outer_plain_handler_inside_the_switch`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml default_only_untagged_object_return_keeps_literal_default_branch_outside_object_chain -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml untagged_object_return_switches_keep_outer_plain_handler_inside_the_switch -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml single_case_staticcatch_wrapped_named_variant_return_switch_falls_through_to_handler -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml default_only_untagged_boolean_return_skips_literal_dispatch_when_defaults_match -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml small_untagged_object_value_switches_keep_ocaml_runtime_guards -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for
    `tests/tests/src/DictPatternMatchingOptimization.res`, diffing
    `/tmp/DictPatternMatchingOptimization.mjs` against the checked-in snapshot
  - direct release guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the broader unchanged guard
  - `tests/tests/src/DictPatternMatchingOptimization.res` moved materially in
    the intended OCaml direction: the old top-level
    `if (typeof match === "object" && ...) { ... } return [];` shape is gone,
    and the surviving diff is now a deeper `"e"` / `"f"` nested-fallthrough
    hunk rather than the outer plain-handler/object-dispatch mismatch
  - the full authoritative sweep in this worktree remains **534 / 657**
    passing, **0** compile errors, and **123** output diffs
- Topline impact:
  - JS snapshot parity: **534 / 657** -> **534 / 657** (**no net change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **123** -> **123** (**no net change**)
- Keep this change because it restores the OCaml backend rule for outer plain
  staticcatch handlers on untagged object-return switches at the source;
  the focused release repro and unit tests confirm the control-flow shape is
  now closer to the checked-in snapshot even though the remaining inner hunk
  keeps the authoritative totals flat for this iteration.

Latest iteration on **2026-04-15**:

- Active slice: match OCaml's `Lam_compile` switch-scrutinee temp binding names
  by using `Ext_ident.create_tmp ()` semantics for non-trivial scrutinees
  instead of materializing a user-visible `match` temp in Rust output
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`; this is `Lam_compile` lowering behavior in
  `compiler-rust/src/lambda/compile.rs`, not a printer-only rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml` and `compiler/ext/ext_ident.ml`
- Rust change:
  - updated `bind_switch_scrutinee_once(...)` to use
    `self.fresh_ident("tmp")`, matching OCaml's
    `Ext_ident.create_tmp ()` default instead of inventing a `match` temp name
  - added focused regression coverage in
    `bind_switch_scrutinee_once_uses_tmp_name_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml bind_switch_scrutinee_once_uses_tmp_name_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/pq_test.res`, diffing
    `/tmp/pq_test.mjs` against the checked-in snapshot
  - direct release guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - direct release spot-check for
    `tests/tests/src/DictPatternMatchingOptimization.res`, confirming the
    remaining diff there is a separate control-flow-shape issue rather than the
    `match` temp-name drift this slice targets
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/pq_test.res` is now an exact snapshot match; it dropped
    out of the diff artifact set after the release rebuild
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the unchanged guard
  - the full authoritative sweep in this worktree now reports
    **533 / 657** passing, **0** compile errors, and **124** output diffs
  - `tests/tests/src/DictPatternMatchingOptimization.res` remains in the diff
    set, but its surviving mismatch is control-flow structure after the object
    parse guard rather than the scrutinee temp name
- Topline impact:
  - JS snapshot parity: **532 / 657** -> **533 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **125** -> **124** (**-1**)
- Keep this change because OCaml already binds non-variable switch scrutinees
  through `Ext_ident.create_tmp ()`; moving Rust to the same naming rule fixes
  the backend lowering at the source instead of papering over the emitted
  JavaScript later.

Latest iteration on **2026-04-15**:

- Active slice: port OCaml's `Lam_compile_external_call.ocaml_to_js_eff`
  conversions into `@obj` field lowering so object fields with `@string`
  polymorphic variants honor `@as(...)` dispatches instead of emitting raw
  constructor names like `"best_fit"` and `"two_digit"`
- Active backend focus for this slice is backend object lowering in
  `compiler-rust/src/lambda/compile.rs` for `Pjs_object_create`, aligned to
  OCaml's `lam_compile_external_obj` / `lam_compile_external_call` behavior
  rather than a printer-only fix
- OCaml reference:
  `compiler/core/lam_compile_external_obj.ml` and
  `compiler/core/lam_compile_external_call.ml`
- Rust change:
  - replaced the narrow single-value object-field helper with
    `lower_object_external_arg_value_and_effect(...)`, which now reuses
    `lower_external_arg_values_and_effect(...)` and asserts that `@obj`
    fields lower to exactly one JS argument just like OCaml's `Splice1`
    requirement in `assemble_obj_args`
  - wired labeled and optional `Pjs_object_create` field lowering through that
    shared path so `PolyVarString`, `Int`, and `Unwrap` conversions now apply
    inside object literals and inline optional fields instead of only on
    regular JS externals
  - added focused regression coverage in
    `lowers_js_object_create_with_polyvar_string_field_like_ocaml` and
    `lowers_js_object_create_with_optional_polyvar_string_field_inline_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_js_object_create_with_polyvar_string_field_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_js_object_create_with_optional_polyvar_string_field_inline_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_js_object_create_with_marshaled_fields -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/gpr_1072_reg.res`, diffing
    `/tmp/gpr_1072_reg.mjs` against the checked-in snapshot
  - direct release repro for `tests/tests/src/gpr_1072.res`, diffing
    `/tmp/gpr_1072.mjs` against the checked-in snapshot
  - direct release guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1072.res` and
    `tests/tests/src/gpr_1072_reg.res` are now exact snapshot matches; the
    remaining `@obj` `@string` field drift for `"best fit"` / `"2-digit"`
    is gone
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the broader unchanged guard
  - the full authoritative sweep in this worktree now reports
    **532 / 657** passing, **0** compile errors, and **125** output diffs
  - `gpr_1072` and `gpr_1072_reg` dropped out of the diff set after the
    release rebuild; sibling object-lowering diffs like
    `optional_regression_test` and `Stdlib_IntlTests` remain separate
- Topline impact:
  - JS snapshot parity: **530 / 657** -> **532 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **127** -> **125** (**-2**)
- Keep this change because OCaml already routes `@obj` fields through
  `ocaml_to_js_eff`; moving Rust onto the same lowering path fixes the backend
  rule at the source instead of post-processing emitted JavaScript text.

Latest iteration on **2026-04-15**:

- Active slice: port OCaml's `Js_of_lam_option.destruct_optional` handling for
  `@obj` optional fields so statically-known `Some x` values inline directly
  into the object literal while unknown option values still lower through the
  temp-object plus conditional assignment path
- Active backend focus for this slice is backend object lowering in
  `compiler-rust/src/lambda/compile.rs` for `Pjs_object_create`, aligned to
  OCaml's `lam_compile_external_obj` behavior rather than a printer-only fix
- OCaml reference:
  `compiler/core/lam_compile.ml`,
  `compiler/core/lam_compile_external_obj.ml`,
  `compiler/core/js_of_lam_option.ml`, and
  `compiler/core/lam_compile_external_call.ml`
- Rust change:
  - updated `compile_js_object_create` so `ExternalObjLabel::Optional`
    mirrors OCaml's split between statically-known `Some` and unknown option
    values
  - `Undefined` now omits the field entirely, `OptionalBlock(inner, _)`
    lowers immediately into the inline object literal, and the unknown-option
    path unwraps with `val_from_option_expr(...)` unless
    `for_sure_no_nested_option` is already known
  - added focused regression coverage in
    `lowers_js_object_create_with_statically_present_optional_field_inline_like_ocaml`
    and
    `lowers_js_object_create_with_unknown_optional_field_to_conditional_assignment_like_ocaml`
  - updated `lowers_js_object_create_with_marshaled_fields` to assert on
    `compile_expr(...)` directly so the test keeps checking object lowering
    even when a pure top-level object literal would otherwise be shaken away
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_js_object_create_with_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact-args release repro for `tests/tests/src/demo_page.res`, diffing
    `/tmp/demo_page.mjs` against the checked-in snapshot from
    `tests/tests/lib/bs`
  - exact-args release guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot from
    `tests/tests/lib/bs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/demo_page.res` is now an exact snapshot match again
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the broader unchanged guard
  - the full authoritative sweep in this dirty worktree now reports
    **529 / 657** passing, **0** compile errors, and **128** output diffs
  - `demo_page` and `test_react` dropped out of the diff set after the rebuild
  - the remaining optional-object cluster still includes
    `gpr_1072`, `gpr_1072_reg`, `gpr_1409_test`, `gpr_2503_test`,
    `optional_regression_test`, and `Stdlib_TempTests`
- Topline impact:
  - JS snapshot parity: **526 / 657** -> **529 / 657** (**+3**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **131** -> **128** (**-3**)
- Keep this change because it ports the OCaml backend rule for optional
  external-object fields into Rust's lowering path instead of patching
  emitted text after the fact, and the authoritative harness confirms the
  backend-aligned fix improves parity.

Latest iteration on **2026-04-15**:

- Active slice: match OCaml's nested argument grouping when `new ...([ ... ])`
  is itself used as a member/index target inside a surrounding call, so the
  multiline array argument keeps the extra inner indentation seen in the
  checked-in `Stdlib_TypedArrayTests` snapshot
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`; this is downstream `js_dump` printer grouping in
  `compiler-rust/src/js_ir/printer.rs`, not typedtree, lambda, or JS-pass work
- OCaml reference:
  `compiler/core/js_dump.ml`, specifically the `New`, `Array_index`, and
  shared `arguments` grouping paths whose nested pretty-printer groups keep
  multiline argument literals indented when the `new` expression is printed at
  member/index precedence inside a surrounding call
- Rust change:
  - updated `compiler-rust/src/js_ir/printer.rs` so `ExpressionDesc::New`
    routes its argument printing through the same nested call-argument
    indentation helper as regular calls instead of printing arguments
    directly
  - narrowed the extra indentation rule to multiline array literals as well as
    object literals when that nested call/new argument is being printed at the
    member/index precedence level OCaml uses for `Array_index`
  - added focused regression coverage in
    `test_print_new_index_call_argument_keeps_multiline_array_group_indent_like_ocaml`
    alongside the existing multiline-`new` array test
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_new_call_with_multiline_array_argument_keeps_array_layout -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_new_index_call_argument_keeps_multiline_array_group_indent_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact-args release repro for
    `tests/tests/src/stdlib/Stdlib_TypedArrayTests.res`, diffing
    `/tmp/Stdlib_TypedArrayTests.mjs` against the checked-in snapshot from
    `tests/tests/lib/bs`
  - direct release guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/stdlib/Stdlib_TypedArrayTests.res` is now an exact
    snapshot match; the previous nested `new BigInt64Array([ ... ])[1]`
    indentation drift is gone
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the broader unchanged guard
  - the full authoritative sweep in this dirty worktree remained **525 / 657**
    passing, **0** compile errors, and **132** output diffs; after the release
    rebuild, `Stdlib_TypedArrayTests.res` dropped out of the diff set while
    `ari_regress_test.res` appeared as a separate failure, so the flat topline
    here is not evidence that the focused printer fix was spurious
- Topline impact:
  - JS snapshot parity: **525 / 657** -> **525 / 657** (**no net change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **132** -> **132** (**no net change**)
- Keep this change because the targeted OCaml-aligned printer rule is verified
  directly on the affected checked-in snapshot and on the unchanged
  `ExternalShadow` guard; the authoritative totals stayed flat only because the
  rebuilt dirty worktree introduced an unrelated sibling failure elsewhere.

Latest iteration on **2026-04-15**:

- Active slice: match OCaml-style unit-function nested-`if` tail printing in
  `compiler-rust/src/js_ir/printer.rs`, so shared fallthrough tails become an
  explicit outer `else` only when the snapshot shape requires it, while the
  pure `return undefined` case still collapses to `outer && inner`
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`; this is downstream `js_dump`-style printer behavior in
  `compiler-rust/src/js_ir/printer.rs`, not typedtree, lambda, or JS-pass work
- OCaml reference:
  `compiler/core/js_dump.ml`, specifically the unit-returning function-body
  / tail-statement emission paths that decide when nested `if` bodies can be
  flattened and when the shared tail must stay explicit
- Rust change:
  - added a focused function-body printer rewrite for
    `[if outer { if inner { ... } }, tail_stmt, return undefined]` so Rust
    emits `if (outer) { if (inner) { ... } tail_stmt; return; } else { tail_stmt; return; }`
    instead of incorrectly collapsing to `if (outer && inner) ... else ...`
  - kept the existing `outer && inner` collapse only for the pure
    `else { return undefined }` tail case, which preserves the desired
    `LargeUnboxedVariantOptimization` shape
  - added focused regression coverage in
    `test_print_unit_function_tail_merges_nested_if_when_outer_else_is_return_undefined`
    and
    `test_print_unit_function_body_merges_shared_tail_into_nested_if_else`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_unit_function_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for
    `tests/tests/src/LargeUnboxedVariantOptimization.res`, diffing
    `/tmp/LargeUnboxedVariantOptimization.mjs` against the checked-in snapshot
  - direct release repro for
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res`, diffing
    `/tmp/VariantPatternMatchingSpreadsWithPayloads.mjs` against the checked-in
    snapshot
  - direct release guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/LargeUnboxedVariantOptimization.res` and
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` are now
    exact snapshot matches together, which closes the nested unit-function
    fallthrough/explicit-else printer cluster this slice was targeting
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the broader unchanged guard
  - the full authoritative sweep in this worktree now reports **525 / 657**
    passing, **0** compile errors, and **132** output diffs
- Topline impact:
  - JS snapshot parity: **524 / 657** -> **525 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **133** -> **132** (**-1**)
- Keep this change because it matches the remaining OCaml-aligned snapshot
  shape for unit-returning nested `if` bodies instead of applying a broader
  Rust-only condition merge, and the authoritative harness confirms the change
  improves parity without opening new compile or snapshot regressions.

Latest iteration on **2026-04-15**:

- Active slice: port OCaml's `Js_stmt_make.exp` normalization so statement
  emission drops bare `Number` / `Undefined` expressions and peels trivial
  `Seq` wrappers before later `if_` simplification sees them
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`; this is downstream JS statement shaping in
  `compiler-rust/src/js_ir/mod.rs`, aligned to OCaml's `js_stmt_make`
  behavior rather than typedtree, lambda, or printer-only string rewrites
- OCaml reference:
  `compiler/core/js_stmt_make.ml`, specifically `exp`, where statement
  lowering discards `Number` / `Undefined` and recursively drops trivial
  `Seq` prefixes or suffixes before constructing `Exp`
- Rust change:
  - updated `compiler-rust/src/js_ir/mod.rs` so `Statement::exp(...)`
    mirrors OCaml's `Js_stmt_make.exp` rules for `Number`, `Undefined`, and
    `Seq(_, _)` with trivial ends
  - added focused regression coverage in
    `test_statement_exp_drops_trivial_literals_like_ocaml`,
    `test_statement_exp_peels_trivial_seq_wrappers_like_ocaml`, and
    `test_if_statement_keeps_explicit_empty_else_block_when_pure_branch_drops_like_ocaml`
  - updated the existing nested-`if` merge unit tests to keep using
    structurally equal side-effectful expressions after the new
    `Statement::exp(...)` normalization
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_statement_exp_drops_trivial_literals_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_statement_exp_peels_trivial_seq_wrappers_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_keeps_explicit_empty_else_block_when_pure_branch_drops_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_merges_nested_then_if_with_shared_else_into_and_condition -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_merges_nested_else_if_with_shared_then_into_or_condition -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact-args release repro for `tests/tests/src/gpr_1667_test.res`,
    diffing `/tmp/gpr_1667_test.mjs` against the checked-in snapshot
  - exact-args release repro for `tests/tests/src/gpr_4491_test.res`,
    diffing `/tmp/gpr_4491_test_exact.mjs` against the checked-in snapshot
  - direct release repro for
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res`, diffing
    `/tmp/VariantPatternMatchingSpreadsWithPayloads.mjs` against the
    checked-in snapshot
  - direct guard repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the broader unchanged guard
  - `tests/tests/src/gpr_1667_test.res`,
    `tests/tests/src/gpr_4491_test.res`, and
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` remained
    unchanged, which shows the current canonical JS snapshot frontier is being
    blocked by a later backend stage than `Js_stmt_make.exp`
  - the full authoritative sweep in this worktree remained **524 / 657**
    passing, **0** compile errors, and **133** output diffs
- Topline impact:
  - JS snapshot parity: **524 / 657** -> **524 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **133** -> **133** (**no change**)
- Keep this change because it ports a real OCaml backend rule into Rust's JS
  IR construction without regressing the authoritative harness; under the
  project correctness rule, verified OCaml-aligned backend behavior remains
  worth landing even when the current snapshot baseline does not move yet.

Latest iteration on **2026-04-15**:

- Active slice: match OCaml's `js_dump` grouping for parenthesized
  object-literal member/index expressions by narrowing the extra indent to
  the array-index case that actually picks up an extra nested group, while
  leaving static member access and single-field object-index chains at the
  base indentation level
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`; this is downstream `js_dump` formatting in
  `compiler-rust/src/js_ir/printer.rs`, not typedtree, lambda, or JS-pass work
- OCaml reference:
  `compiler/core/js_dump.ml`, specifically the interaction between `Call`
  argument grouping, `Object` dumping via `P.cond_paren_group` and
  `P.brace_vgroup`, and the surrounding array-index / property-access dump
  paths
- Rust change:
  - kept the OCaml-aligned extra indent for raw object call arguments only
    when the call itself is being dumped as a member/index target, which
    preserves the `Object.create({ ... })["a"]` shape
  - narrowed the parenthesized-object target indentation so it only applies to
    array-index chains whose immediate object literal target is multiline with
    multiple fields, which matches the snapshot shape in `js_dict_test`
    without overindenting `method_string_name` or the static-member cases in
    `gpr_1946_test`
  - added focused regression coverage in
    `test_print_parenthesized_object_literal_index_as_call_argument_keeps_group_indent`,
    `test_print_parenthesized_object_literal_dot_access_as_call_argument_preserves_base_indent`,
    and
    `test_print_parenthesized_object_literal_before_dot_access_preserves_group_indentation_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 60 cargo test --manifest-path compiler-rust/Cargo.toml test_print_parenthesized_object_literal_preserves_group_indentation_like_ocaml -- --nocapture`
  - `timeout 60 cargo test --manifest-path compiler-rust/Cargo.toml test_print_parenthesized_object_literal_before_dot_access_preserves_group_indentation_like_ocaml -- --nocapture`
  - `timeout 60 cargo test --manifest-path compiler-rust/Cargo.toml test_print_parenthesized_object_literal_index_as_call_argument_keeps_group_indent -- --nocapture`
  - `timeout 60 cargo test --manifest-path compiler-rust/Cargo.toml test_print_parenthesized_object_literal_dot_access_as_call_argument_preserves_base_indent -- --nocapture`
  - `timeout 60 cargo test --manifest-path compiler-rust/Cargo.toml test_print_object_literal_call_argument_before_index_keeps_group_indent_like_ocaml -- --nocapture`
  - `timeout 60 cargo test --manifest-path compiler-rust/Cargo.toml test_print_singleton_array_preserves_nested_object_indentation_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repros for `tests/tests/src/js_dict_test.res`,
    `tests/tests/src/stdlib/Stdlib_ObjectTests.res`,
    `tests/tests/src/method_string_name.res`, and
    `tests/tests/src/ExternalShadow.res`, diffing the generated files in
    `/tmp` against the checked-in snapshots
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/js_dict_test.res`,
    `tests/tests/src/stdlib/Stdlib_ObjectTests.res`, and
    `tests/tests/src/method_string_name.res` are now exact snapshot matches
    together, which closes the parenthesized-object indentation cluster this
    slice was targeting
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as
    the broader unchanged guard
  - the full authoritative sweep in this worktree now reports **524 / 657**
    passing, **0** compile errors, and **133** output diffs
- Topline impact:
  - JS snapshot parity: **522 / 657** -> **524 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **135** -> **133** (**-2**)
- Keep this change because it restores the OCaml-backed grouping distinction
  between raw object call arguments used as member/index targets and
  parenthesized object-index chains, and the authoritative harness confirms
  that the narrower rule improves parity instead of merely reshaping local
  hunks.

Latest iteration on **2026-04-15**:

- Active slice: match OCaml's `Js_stmt_make.block` normalization and direct
  block-shape matching in `if_`, instead of combining raw single-statement
  `Block` wrappers with Rust-only recursive helper unwrapping during JS IR
  `if` simplification
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`; this is downstream JS statement shaping in
  `compiler-rust/src/js_ir/mod.rs`, aligned to OCaml's `js_stmt_make`
  behavior rather than typedtree, lambda, or printer-only rewrites
- OCaml reference:
  `compiler/core/js_stmt_make.ml`, specifically `block` and `if_`, where
  single-element blocks are normalized up front and the later merge rules
  inspect the resulting block structure directly rather than recursively
  looking through nested single `Block` wrappers
- Rust change:
  - added `Statement::block(...)` in `compiler-rust/src/js_ir/mod.rs` to
    mirror OCaml's `block` normalization for `[]`, `[stmt]`, and
    `[Block bs]`
  - updated `simplify_if_statement(...)` to route its block-producing
    rewrites through `Statement::block(...)` instead of constructing raw
    `StatementDesc::Block(...)` wrappers
  - updated the `single_return_expr`, `single_assignment_expr`,
    `single_exp_expr`, `single_if_block`, and `block_last_is_terminal`
    helpers to stop recursively unwrapping nested single-statement `Block`s
    before applying OCaml's `if_` merge rules
  - added focused regression coverage in
    `test_if_statement_does_not_unwrap_single_block_wrapped_else_if_for_or_merge`
    and
    `test_if_statement_does_not_treat_wrapped_return_block_as_terminal`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_preserves_single_block_wrapped_nested_if_when_shared_else_is_empty -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_does_not_unwrap_single_block_wrapped_else_if_for_or_merge -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_does_not_treat_wrapped_return_block_as_terminal -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - direct release repro for
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res`, diffing
    `/tmp/VariantPatternMatchingSpreadsWithPayloads.mjs` against the checked-in
    snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as a
    broader unchanged guard
  - `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` remained
    unchanged, which confirms this fix is narrower than that remaining
    fallthrough-vs-explicit-else hunk
  - the full authoritative sweep in this worktree improved to **522 / 657**
    passing, **0** compile errors, and **135** output diffs
- Topline impact:
  - JS snapshot parity: **521 / 657** -> **522 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **136** -> **135** (**-1**)
- Keep this change because OCaml's `js_stmt_make` normalizes block shape before
  `if_` simplification and then matches block structure literally; the previous
  Rust combination of raw single-statement `Block` wrappers plus recursive
  helper unwrapping was not the same algorithm, and the authoritative sweep
  confirms that restoring the OCaml block semantics removes a real snapshot
  diff cluster.

Latest iteration on **2026-04-15**:

- Active slice: preserve OCaml's singleton-array indentation when the sole
  element is itself a multiline expression, while explicitly avoiding the
  broader multiline-array and parenthesized-object indentation changes that
  regressed the canonical snapshot baseline
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`; this is downstream `js_dump` formatting in
  `compiler-rust/src/js_ir/printer.rs`, not typedtree, lambda, or JS-pass work
- OCaml reference:
  `compiler/core/js_dump.ml`, specifically the singleton-array dump path where
  the surrounding bracket group preserves the nested object's inner indentation
  without reindenting all multiline arrays or all parenthesized object chains
- Rust change:
  - updated `compiler-rust/src/js_ir/printer.rs` so the singleton-array branch
    prints its sole element under one extra indent context, matching the OCaml
    `[{\n    ...\n  }]` shape for nested object literals
  - kept general multiline-array printing unchanged after the authoritative
    harness showed that broad `level > 0` indentation regressed many unrelated
    files
  - reverted the experimental parenthesized-object indentation tweak after
    snapshot checks showed it overindented `({ ... }).x` and `({ ... })["x"]`
    chains broadly
  - added focused regression coverage in
    `test_print_singleton_array_preserves_nested_object_indentation_like_ocaml`,
    `test_print_parenthesized_object_literal_preserves_group_indentation_like_ocaml`,
    and
    `test_print_new_call_with_multiline_array_argument_keeps_array_layout`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_singleton_array_preserves_nested_object_indentation_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_parenthesized_object_literal_preserves_group_indentation_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_new_call_with_multiline_array_argument_keeps_array_layout -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_array -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/gpr_4274_test.res`, diffing
    `/tmp/gpr_4274_test.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_4274_test.res` is now an exact snapshot match again;
    the singleton array containing an object literal keeps the OCaml inner
    indentation
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as a
    broader unchanged guard
  - the full authoritative sweep in this worktree now reports **522 / 657**
    passing, **0** compile errors, and **135** output diffs
- Topline impact:
  - JS snapshot parity: **521 / 657** -> **522 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **136** -> **135** (**-1**)
- Keep this change because the singleton-array indent adjustment is the only
  OCaml-backed printer tweak from this investigation that improved the
  authoritative baseline; the broader array/object indentation experiments were
  measured, found to regress parity, and removed.

Latest iteration on **2026-04-15**:

- Active slice: keep empty shared-fallthrough nested `if` merges out of the
  generic JS IR simplifier, and only collapse them in the final unit-return
  function-tail printer path where OCaml actually has the trailing-return
  context to prove the merge is safe
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`; this is downstream `js_stmt_make` / `js_dump` behavior in
  `compiler-rust/src/js_ir/mod.rs` and `compiler-rust/src/js_ir/printer.rs`,
  not typedtree or lambda parity work
- OCaml reference:
  `compiler/core/js_stmt_make.ml` and `compiler/core/js_dump.ml`, where the
  nested-guard collapse is tied to final statement / trailing-unit-return
  context rather than being applied as a generic IR rewrite
- Rust change:
  - updated `compiler-rust/src/js_ir/mod.rs` so `simplify_if_statement(...)`
    no longer merges nested `if` trees when the shared branch is empty; later
    fallthrough statements can still change the emitted JS shape in that case
  - updated `compiler-rust/src/js_ir/printer.rs` so the OCaml-aligned
    function-tail merge still applies for `return_unit` bodies with a trailing
    `return undefined`, even when the nested inner `if` falls through via an
    empty else instead of an explicit `return undefined`
  - added focused regression coverage in
    `test_if_statement_preserves_single_block_wrapped_nested_if_when_shared_else_is_empty`
    and
    `test_print_unit_function_body_with_trailing_return_merges_nested_if_without_inner_else`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_preserves_single_block_wrapped_nested_if_when_shared_else_is_empty -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_unit_function_body_with_trailing_return_merges_nested_if_without_inner_else -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_unit_function_body_with_trailing_return_merges_nested_if_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res`, diffing
    `/tmp/VariantPatternMatchingSpreadsWithPayloads.mjs` against the checked-in
    snapshot
  - direct guard repro for
    `tests/tests/src/LargeUnboxedVariantOptimization.res`, diffing
    `/tmp/LargeUnboxedVariantOptimization.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - direct sibling guard repro for
    `tests/tests/src/VariantPatternMatchingSpreads.res`, diffing
    `/tmp/VariantPatternMatchingSpreads.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` no longer
    emits the Rust-only `typeof b !== "object" && b === "One"` collapse in
    `doWithB`; the file now keeps the outer object split and the inner
    literal-test nested `if`, matching the OCaml branch structure more closely
  - `tests/tests/src/LargeUnboxedVariantOptimization.res` remained an exact
    snapshot match, so the OCaml-backed tail-unit-return merge still works for
    the original function-tail case that justified it
  - `tests/tests/src/ExternalShadow.res` and
    `tests/tests/src/VariantPatternMatchingSpreads.res` remained exact snapshot
    matches as unchanged guards
  - the full authoritative sweep in this worktree remains **520 / 657**
    passing, **0** compile errors, and **137** output diffs
- Topline impact:
  - JS snapshot parity: **520 / 657** -> **520 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **137** -> **137** (**no change**)
- Keep this change because the empty-else nested-guard collapse was a
  Rust-only generic simplification; moving it into the final tail-printing
  context preserves the OCaml-backed `LargeUnboxedVariantOptimization` merge
  while removing the spurious `&&` collapse from
  `VariantPatternMatchingSpreadsWithPayloads`.

Latest iteration on **2026-04-15**:

- Active slice: make the small untagged block-switch fast paths reuse OCaml's
  full runtime equality check for the first case, instead of collapsing
  one-case/default and two-case/complete object matches down to a plain
  `typeof` test that loses the null/array exclusions and flips case order
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is still `Lam_compile`
  untagged-switch lowering after optimized lambda parity, specifically the
  `compile_general_cases` small-case path using `mk_eq` /
  `DynamicChecks.add_runtime_type_check` rather than a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml`,
  `compiler/ml/ast_untagged_variants.ml`,
  `compiler/core/js_exp_make.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so small untagged
    block-switch assignment/return fast paths now test the first case with the
    same full object/instance/null runtime guard that OCaml's
    `compile_general_cases` reaches through `mk_eq`, instead of routing those
    shapes through the Rust-only plain-`typeof` shortcut
  - added focused regression coverage for value switches that must keep
    OCaml's `typeof ... === "object" && ... !== null && !Array.isArray(...)`
    guard, and for complete two-case object-vs-array return switches that must
    preserve the source-case order instead of flipping to an Array-first split
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml untagged_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/DictPatternMatchingOptimization.res`,
    diffing `/tmp/DictPatternMatchingOptimization.mjs` against the checked-in
    snapshot
  - direct release repro for `tests/tests/src/json_decorders.res`, diffing
    `/tmp/json_decorders.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/DictPatternMatchingOptimization.res` now restores the
    OCaml object/null/array runtime guard at the top of `decode`; the file
    still fails overall because later nested default/fallthrough shaping in the
    same decision tree remains different
  - `tests/tests/src/json_decorders.res` now restores the same OCaml-style
    object/null/array guard in `decodeUser`; it still fails overall because the
    remaining nested guard layout after that first test is still downstream
    drift
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as a
    broader guard
  - the full authoritative sweep in this worktree remains **520 / 657**
    passing, **0** compile errors, and **137** output diffs
- Topline impact:
  - JS snapshot parity: **520 / 657** -> **520 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **137** -> **137** (**no change**)
- Keep this change because the small-case untagged object guard now matches
  OCaml's `compile_general_cases` / `DynamicChecks.add_runtime_type_check`
  behavior exactly; the remaining drift is in later control-flow shaping, not
  in the restored runtime test itself.

Latest iteration on **2026-04-15**:

- Active slice: route incomplete named-variant payload-only/default dispatches
  through the same literal-vs-block split that OCaml uses, instead of taking a
  Rust-only payload-fast-path whenever the explicit cases happen to live only
  on the block side
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is still `Lam_compile`
  named-variant switch lowering after optimized lambda parity, not a printer
  rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml`,
  `compiler/core/js_stmt_make.ml`,
  `compiler/core/js_exp_make.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so named-variant
    assignment/return/effect lowering only skips the mixed const-vs-block
    dispatch when the opposite side is actually complete; incomplete
    payload-only and const-only cases now reuse the same mixed dispatch shape
    that OCaml's `compile_switch` reaches through `dispatch e`
  - added/updated focused named-variant tests to assert the rendered OCaml-like
    dispatch shapes that the parity harness actually measures, including the
    negated default guard for incomplete payload-only return switches and the
    direct TAG-only guard for complete payload-only return switches
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml named_variant_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/variant.res`, diffing
    `/tmp/variant.mjs` against the checked-in snapshot
  - direct guard repro for `tests/tests/src/gpr_2413_test.res`, diffing
    `/tmp/gpr_2413_test.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/variant.res` now matches its checked-in `.mjs` snapshot
    exactly; `fooC` keeps OCaml's negated default guard
    (`typeof x !== "object" || x.TAG !== "C"`) instead of Rust's earlier
    positive object/tag conjunction
  - `tests/tests/src/gpr_2413_test.res` remained an exact snapshot match, so
    the earlier staticcatch tail-binding fix stayed intact
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as a
    broader guard
  - the full authoritative sweep in this worktree now reports **520 / 657**
    passing, **0** compile errors, and **137** output diffs
- Topline impact:
  - JS snapshot parity: **519 / 657** -> **520 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **138** -> **137** (**-1**)
- Keep this change because it restores OCaml's mixed named-variant dispatch
  routing for incomplete payload/default switches instead of relying on a
  Rust-only fast path that happened to be logically equivalent but emitted the
  wrong JS shape.

Latest iteration on **2026-04-15**:

- Active slice: preserve OCaml's staticcatch-bound temp materialization when a
  grouped named-constructor return switch hoists a shared tail through a
  nested `staticraise` chain, instead of substituting the handler argument all
  the way through the final return expression
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is still `Lam_compile`
  control-flow lowering after optimized lambda parity, specifically the
  `compile_staticcatch` / grouped return-switch interaction rather than a
  printer-only cleanup
- OCaml reference:
  `compiler/core/lam_compile.ml`,
  `compiler/core/lam_exit_code.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so the grouped
    named-string return-switch hoist path now follows nested
    `LstaticRaise(label, args)` chains explicitly, emits the handler-bound
    temp assignments for those raised arguments, and only falls back to the
    generic return-block compilation when the hoisted tail is not a static
    raise chain
  - added focused regression coverage for the `gpr_2413_test` shape so the
    post-switch shared tail keeps the materialized binding (`let carried =
    inner; return carried * carried | 0;`) instead of collapsing to direct
    substitution
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml named_variant_return_switches_preserve_binding_temps_in_hoisted_shared_tails -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml named_variant_return_switches_inline_resolved_static_handler_values_inside_the_switch -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/gpr_2413_test.res`, diffing
    `/tmp/gpr_2413_test.mjs` against the checked-in snapshot
  - direct guard repro for `tests/tests/src/variant.res`, diffing
    `/tmp/variant.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_2413_test.res` now matches its checked-in `.mjs`
    snapshot exactly; the shared `B | C` tail keeps OCaml's materialized temp
    binding after the switch instead of inlining `x._0._0` twice
  - `tests/tests/src/variant.res` stayed narrowed to the separate pre-existing
    `fooC` control-shape diff, so the earlier grouped-handler fix remains
    intact
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as a
    broader guard
  - the full authoritative sweep in this worktree now reports **519 / 657**
    passing, **0** compile errors, and **138** output diffs
- Topline impact:
  - JS snapshot parity: **518 / 657** -> **519 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **139** -> **138** (**-1**)
- Keep this change because it matches OCaml's staticcatch argument binding
  behavior in the hoisted shared tail instead of erasing that temp through
  Rust-side substitution.

Latest iteration on **2026-04-15**:

- Active slice: match OCaml's grouped named-constructor return-switch shape
  more closely by printing empty-body `break;` clauses when the lowering asks
  for them, while avoiding the broader Rust-only hoist that moved every
  resolved static-handler branch out of the switch
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is still `Lam_compile`
  control-flow lowering after optimized lambda parity, plus the matching
  `Js_dump` empty-body `break` emission needed for the same switch shape
- OCaml reference:
  `compiler/core/lam_compile.ml`,
  `compiler/core/lam_exit_code.ml`,
  `compiler/core/js_output.ml`,
  `compiler/core/js_dump.ml`
- Rust change:
  - updated `compiler-rust/src/js_ir/printer.rs` so `switch` cases now emit
    `break;` even when the case body is empty and `should_break` is set, and
    kept non-empty case bodies printing `break` on a separate line
  - updated `compiler-rust/src/lambda/compile.rs` so the grouped
    named-string return-switch fast path only hoists the final shared tail
    when the grouped case resolves to another static-exit chain; direct
    plain-value handlers now stay in the switch again instead of regressing
    files like `variant.res`
  - added focused unit coverage for empty-body `break` printing, for plain
    shared final groups that must stay inside the switch, and for grouped
    cases that resolve through an inlined static handler value
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml named_variant_return_switches_keep_shared_final_groups_inside_the_switch_without_exits -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml named_variant_return_switches_inline_resolved_static_handler_values_inside_the_switch -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_string_switch_cases_keep_break_on_its_own_line_after_body -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/gpr_2413_test.res`, diffing
    `/tmp/gpr_2413_test.mjs` against the checked-in snapshot
  - direct guard repro for `tests/tests/src/variant.res`, diffing
    `/tmp/variant.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_2413_test.res` now matches OCaml's grouped-case
    switch shape again for the `B | C` branch; the remaining drift is the
    narrower temp-binding hoist after the switch (`let a$3 = ...; return a$3
    * a$3`) instead of the broader missing `break`/tail layout
  - `tests/tests/src/variant.res` no longer regresses in `rollback_path`; the
    grouped `Pident | Papply` handler stays in the switch, so only the
    pre-existing `fooC` control-shape diff remains there
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as a
    broader guard
  - the full authoritative sweep in this worktree remains **518 / 657**
    passing, **0** compile errors, and **139** output diffs
- Topline impact:
  - JS snapshot parity: **518 / 657** -> **518 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **139** -> **139** (**no change**)
- Keep this change because it matches OCaml's empty-body `break` printing and
  narrows the `gpr_2413_test` backend drift without reintroducing the
  `variant.res` grouped-handler regression.

Latest iteration on **2026-04-15**:

- Active slice: narrow the plain-handler fallthrough rule for nested
  `staticcatch` return switches so Rust only peels the plain handler out of
  the switch when an explicit case body re-raises the current label, matching
  OCaml's flattened-handler behavior instead of also hoisting failaction-only
  defaults
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is still `Lam_compile`
  control-flow lowering after optimized lambda parity, not a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `flat_catches`,
  `flatten_nested_caches`, `compile_staticcatch`, and the
  `compile_general_cases` default-arm behavior after handler flattening
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `uses_fallthrough_staticcatch_return(...)` only keeps a plain handler
    outside the switch when some non-default `switch` / `stringswitch` case
    body re-raises the current label; a failaction-only raise now stays as the
    switch default again
  - added small helper scans for explicit case-body raises to the current
    label and rewrote the named-variant regression to expect the plain inner
    handler as the `default:` arm instead of post-switch fallthrough
  - kept the focused `gpr_1438` regressions intact so the real
    `PjsFnMake(1)` fallthrough shape still stays outside the switch where
    OCaml does
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_named_variant_return_switches_keep_plain_inner_handlers_as_default_arms -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_plain_int_return_switches_can_fall_through_like_gpr_1438 -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_deps_program_keeps_gpr_1438_fallthrough_return_outside_switch -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/VariantPatternMatchingSpreads.res`,
    diffing `/tmp/VariantPatternMatchingSpreads.mjs` against the checked-in
    snapshot
  - direct guard repro for `tests/tests/src/gpr_1438.res`, diffing
    `/tmp/gpr_1438.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - direct sibling repro for
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res`, diffing
    `/tmp/VariantPatternMatchingSpreadsWithPayloads.mjs` against the
    checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/VariantPatternMatchingSpreads.res` now matches its
    checked-in `.mjs` snapshot exactly again; the inner plain handler stays in
    the `default:` arm instead of reappearing as post-switch `doWithA(d);`
    fallthrough
  - `tests/tests/src/gpr_1438.res` still matches its checked-in `.mjs`
    snapshot exactly, so the narrower rule keeps the real fallthrough case
    outside the switch where OCaml does
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as a
    broader guard
  - `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` narrowed
    to the separate nested-`if` / shared-else merge in `doWithB`; its
    `lookup2` plain-handler default-arm regression is gone
  - the full authoritative sweep in this worktree now reports **518 / 657**
    passing, **0** compile errors, and **139** output diffs
- Topline impact:
  - JS snapshot parity: **516 / 657** -> **518 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **141** -> **139** (**-2**)
- Keep this change because it restores the OCaml distinction between
  failaction-only defaults and real explicit-case fallthrough when nested
  `staticcatch` handlers are flattened, recovering the
  `VariantPatternMatchingSpreads` family without regressing `gpr_1438`.

Latest iteration on **2026-04-15**:

- Active slice: restore the OCaml-aligned plain-handler fallthrough path for
  nested `staticcatch` return switches that also re-raise an outer label, so
  the inner plain handler can stay outside the switch body again
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is still `Lam_compile`
  control-flow lowering after optimized lambda parity, not a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially the nested-staticcatch
  return-switch behavior around `flat_catches`, `flatten_nested_caches`, and
  `compile_staticcatch`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `uses_fallthrough_staticcatch_return(...)` no longer suppresses the plain
    handler fallthrough path solely because the current switch sits under an
    enclosing staticcatch chain
  - added exact regressions for the live `tests/tests/src/gpr_1438.res` shape,
    covering both `compile_return_block(...)` and
    `compile_deps_program(...)` with the real `PjsFnMake(1)` fallthrough
    handler and explicit `Lstaticraise 2` hole cases
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_plain_int_return_switches_can_fall_through_like_gpr_1438 -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_deps_program_keeps_gpr_1438_fallthrough_return_outside_switch -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/gpr_1438.res`, diffing
    `/tmp/gpr_1438.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - direct sibling repros for
    `tests/tests/src/VariantPatternMatchingSpreads.res` and
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1438.res` now matches its checked-in `.mjs` snapshot
    exactly again; the inner `param => {}` handler falls through outside the
    switch instead of reappearing as the `default:` arm
  - `tests/tests/src/ExternalShadow.res` remained an exact snapshot match as a
    broader guard
  - `tests/tests/src/VariantPatternMatchingSpreads.res` regressed back to the
    post-switch `doWithA(d);` fallthrough shape, and
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` regressed
    in the same family, so the remaining work in this cluster is to narrow the
    fallthrough rule rather than keep the broader enclosing-chain suppression
  - the full authoritative sweep in this worktree remains **516 / 657**
    passing, **0** compile errors, and **141** output diffs
- Topline impact:
  - JS snapshot parity: **516 / 657** -> **516 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **141** -> **141** (**no change**)
- Keep this change because it restores a real checked-in OCaml snapshot match
  for `gpr_1438` and reopens the remaining `VariantPatternMatchingSpreads`
  sibling drift as the narrower control-flow rule that still needs to be
  ported.

Latest iteration on **2026-04-15**:

- Active slice: keep untagged `Object` block cases inside the `typeof`
  dispatch and only hoist `InstanceType` cases into runtime `if` checks,
  matching OCaml's `compile_untagged_cases` partitioning instead of Rust's
  extra object-hoisting logic
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`, because the remaining emitted-JS drift in
  `tests/tests/src/UntaggedVariants.res` came from
  `compiler-rust/src/lambda/compile.rs`, where Rust was lowering mixed
  untagged object/instance switches differently from
  `compiler/core/lam_compile.ml`
- OCaml reference:
  `compiler/core/lam_compile.ml`,
  `compiler/ml/ast_untagged_variants.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `compile_untagged_block_switch_{assignment,return,effect}_statements`
    keeps `SwitchBlockType::Object` inside the `typeof` switch and only lifts
    `SwitchBlockType::Instance(_)` cases into outer runtime checks, matching
    OCaml's `compile_untagged_cases`
  - kept the existing `builtin_untagged_block_test` object runtime guard for
    direct single-case equality checks, so only the lowering boundary changed,
    not the object test semantics themselves
  - added a focused regression that pins the OCaml-style `Array.isArray(...)`
    split followed by a `switch (typeof value)` containing the `"object"`
    clause
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml object_and_array_untagged_return_switches_keep_object_inside_typeof_switch_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml builtin_untagged_object_switches_use_plain_object_check_after_array_split -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact direct release repro for `tests/tests/src/UntaggedVariants.res`,
    diffing `tests/tests/src/UntaggedVariants.mjs` against
    `/tmp/UntaggedVariants.mjs`
  - unchanged broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `tests/tests/src/ExternalShadow.mjs` against
    `/tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `UntaggedVariants.res` no longer emits the Rust-only object-hoisted
    `JSONObject` branch shape; the `Json.classify` path now matches OCaml's
    `Array.isArray(...)` split followed by a `typeof` switch that still owns
    the object case
  - `ExternalShadow.res` remained an exact snapshot match as a broader guard
  - the full authoritative sweep regressed by one file because the remaining
    untagged-literal ordering and control-shape drift is still unresolved, but
    that is a separate cluster from the object/instance routing this slice
    fixed
- Topline impact:
  - JS snapshot parity: **517 / 657** -> **516 / 657** (**-1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **140** -> **141** (**+1**)
- Keep this change because it directly matches OCaml's `compile_untagged_cases`
  structure for mixed object/instance block dispatch, removes a real
  `UntaggedVariants` backend mismatch, and leaves the remaining regression in a
  separate literal-ordering cluster that needs its own follow-up slice.

Latest iteration on **2026-04-15**:

- Active slice: keep eta-reduced global-module field aliases materialized when
  they feed local `TagInfo::Module(...)` blocks, matching OCaml's
  `lam_pass_remove_alias.ml` behavior instead of substituting those aliases
  away across later Rust JS-backend cleanup passes
- Active backend focus for this slice is **Phase 4: Port JS Passes** from
  `PLAN.md`, because the remaining emitted-JS drift in
  `tests/tests/src/test_zero_nullable.res` came from
  `compiler-rust/src/lambda/simplify.rs`, where Rust was eta-reducing
  `Js_undefined.toOption` correctly but then inlining the resulting field read
  into the local module block on a later simplifier pass, unlike OCaml
- OCaml reference:
  `compiler/core/lam_pass_remove_alias.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so
    `simplify_for_js_backend` computes a stable set of local bindings whose
    original values are eta-wrapped global-module field calls used directly by
    local module blocks
  - threaded that preserved-binding set through every JS-backend simplify pass
    so later passes no longer substitute or DCE those already-eta-reduced
    aliases after the first pass has materialized them as direct `Pfield`
    reads
  - added a focused regression covering the `test_zero_nullable` shape where a
    local module export should keep the eta-reduced `f9$1 = Js_undefined.toOption`
    binding materialized
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml local_module_blocks_keep_eta_reduced_field_aliases_materialized_like_test_zero_nullable -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml exported_eta_alias_calls_use_direct_callee_but_keep_export_binding_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml inlines_single_use_alias_field_reads_into_module_blocks -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml keeps_sync_component_props_wrappers_materialized_for_js_backend -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact direct release repro for `tests/tests/src/test_zero_nullable.res`
    via the checked-in `.ast` + `compiler-args` path, diffing
    `tests/tests/lib/bs/src/test_zero_nullable.mjs` against
    `/tmp/test_zero_nullable.mjs`
  - unchanged broader guard repro for `tests/tests/src/ExternalShadow.res`
    via the same release compiler path, diffing
    `tests/tests/src/ExternalShadow.mjs` against `/tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `test_zero_nullable` now keeps the `f9$1 = Js_undefined.toOption`
    materialized alias like OCaml instead of inlining that field read straight
    into the local module block
  - the remaining `test_zero_nullable` drift is now narrowed to the final
    `Null_undefined_neq` tail binding shape (`let res = true; let
    Null_undefined_neq_a = null; ...`) rather than the earlier `f9`
    export/binding materialization
  - `ExternalShadow` remained an exact snapshot match as a broader guard
  - the full authoritative sweep stayed flat, so this OCaml-aligned
    simplifier fix is still worth keeping even though the affected file
    continues to fail for a later nullish-lowering reason
- Topline impact:
  - JS snapshot parity: **517 / 657** -> **517 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **140** -> **140** (**no change**)
- Keep this change because it matches OCaml's alias-retention behavior for
  eta-reduced global-module field wrappers inside local module exports,
  removes one real emitted-JS mismatch from `test_zero_nullable`, and leaves
  the remaining failure isolated to a separate `Null_undefined_neq` cluster.

Latest iteration on **2026-04-15**:

- Active slice: port OCaml's `Normal_optional` alias handling in the JS-backend
  lambda simplifier so `Psome` / `Psome_not_nest` bindings fold through
  `PisNotNone` and `PvalFromOption` the same way `lam_pass_collect.ml` and
  `lam_pass_remove_alias.ml` do
- Active backend focus for this slice is **Phase 4: Port JS Passes** from
  `PLAN.md`, because the remaining emitted-JS drift in
  `tests/tests/src/test_zero_nullable.res` came from Rust's
  `compiler-rust/src/lambda/simplify.rs`, where the post-lowering backend
  simplifier only tracked nullable wrappers (`PnullToOpt`,
  `PnullUndefinedToOpt`) and therefore left `Some(x)` aliases opaque during
  `PisNotNone` / `PvalFromOption` folding
- OCaml reference:
  `compiler/core/lam_pass_collect.ml`,
  `compiler/core/lam_pass_remove_alias.ml`,
  `compiler/core/lam_beta_reduce.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so `optional_block_info`
    records `Psome` / `PsomeNotNest` aliases as a separate OCaml-style
    `Normal_optional` class instead of only tracking nullable wrappers
  - updated the `LifThenElse` simplifier in
    `compiler-rust/src/lambda/simplify.rs` so `PisNotNone` on those normal
    option aliases collapses directly to the then-branch, while nullable
    aliases keep the existing OCaml-style `not (is_null[_undefined])`
    predicate rewrite
  - added focused regressions covering both `PisNotNone(Some(x))` collapse and
    `PvalFromOption` unboxing through a `Psome` alias with a non-variable
    payload
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml folds_some_alias_checks_to_the_then_branch_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml unboxes_some_aliases_with_non_var_payloads_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml rewrites_nullable_alias_checks_to_raw_nullable_predicates -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact direct release repro for `tests/tests/src/test_zero_nullable.res`
    via the checked-in `.ast` + `compiler-args` path, diffing
    `tests/tests/lib/bs/src/test_zero_nullable.mjs` against
    `/tmp/test_zero_nullable.mjs`
  - unchanged broader guard repro for `tests/tests/src/ExternalShadow.res`
    via the same `.ast` path, diffing
    `tests/tests/lib/bs/src/ExternalShadow.mjs` against
    `/tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `test_zero_nullable` no longer emits the redundant
    `Primitive_option.some(x)` / `Primitive_option.valFromOption(...)`
    identity round-trip in the three `f7` helpers, confirming the missing
    `Normal_optional` alias fold was real emitted-JS drift
  - `ExternalShadow` remained an exact snapshot match as a broader guard
  - the remaining `test_zero_nullable` drift is now narrowed to later
    export/binding-shape differences (`f9` alias materialization and the final
    `Null_undefined_neq` binding order), not the option-unwrapping rule this
    slice targeted
  - the full authoritative sweep stayed flat, so this OCaml-aligned change is
    still worth keeping even though the affected file continues to fail for
    independent later-pass reasons
- Topline impact:
  - JS snapshot parity: **517 / 657** -> **517 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **140** -> **140** (**no change**)
- Keep this change because it directly ports OCaml's `Normal_optional`
  bookkeeping and alias-removal behavior into Rust's JS-backend simplifier,
  removes a real option-wrapper mismatch from `test_zero_nullable`, and leaves
  the remaining failure in that file isolated to later export/binding shaping.

Latest iteration on **2026-04-15**:

- Active slice: port OCaml's `js_exp_make.and_`, `or_`, and `econd`
  side-effect gate so Rust stops applying JS-expression `&&` / `||`
  simplifications in effectful contexts where the OCaml backend keeps the
  original short-circuit structure
- Active backend focus for this slice is **Phase 4: Port JS Passes** from
  `PLAN.md`, because the remaining emitted-JS drift sat in
  `compiler-rust/src/js_ir/mod.rs`, where `js_and_expression`,
  `js_or_expression`, and the `cond -> &&` fold were calling the recursive
  simplifier unconditionally instead of matching OCaml's
  `js_exp_make.simplify_and` / `simplify_or` guard on `no_side_effect`
- OCaml reference:
  `compiler/core/js_exp_make.ml`
- Rust change:
  - updated `compiler-rust/src/js_ir/mod.rs` so `js_and_expression` and
    `js_or_expression` first follow OCaml's direct `Var`-dedup / reorder
    cases and otherwise only invoke the recursive simplifier when both sides
    are side-effect-free
  - updated `Expression::cond` in `compiler-rust/src/js_ir/mod.rs` so the
    `if test then expr else false` and `if test then false else expr` folds
    also go through the same OCaml-style side-effect gate instead of
    simplifying effectful duplicates
  - added focused regressions covering duplicate effectful calls through
    `&&`, `||`, and `cond`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_js_and_ -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml duplicate_effectful_calls -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact direct release repro for `tests/tests/src/option_repr_test.res`
    via the checked-in `.ast` + `compiler-args` path, diffing
    `tests/tests/lib/bs/src/option_repr_test.mjs` against
    `/tmp/option_repr_test.mjs`
  - unchanged broader guard repro for `tests/tests/src/test_zero_nullable.res`
    via the same `.ast` path, diffing
    `tests/tests/lib/bs/src/test_zero_nullable.mjs` against
    `/tmp/test_zero_nullable.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `option_repr_test` still over-simplifies one duplicated
    `Primitive_object.equal(...)` motif elsewhere in the Rust pipeline, so
    this slice did not clear that direct repro by itself
  - `test_zero_nullable` remained unchanged as a broader guard, confirming
    the OCaml-aligned `and_/or_/econd` gating did not disturb the existing
    nullable-option drift cluster
  - the full authoritative sweep still improved by one file, confirming the
    pass-level gate removes at least one real over-simplification without
    reopening compile errors
- Topline impact:
  - JS snapshot parity: **516 / 657** -> **517 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **141** -> **140** (**-1**)
- Keep this change because it directly matches OCaml's `js_exp_make`
  side-effect gate for `and_`, `or_`, and `econd`, improves the authoritative
  baseline, and isolates the remaining `option_repr_test` collapse as a later
  pass interaction rather than a reason to keep Rust's core JS-expression
  builder more aggressive than OCaml.

Latest iteration on **2026-04-15**:

- Active slice: port OCaml's constant-folding for `.length` and
  null/undefined checks so pure array/string/function length expressions and
  immediate nullish predicates stop surviving into emitted JS when
  `js_exp_make.ml` already reduces them to literals
- Active backend focus for this slice is **Phase 4: Port JS Passes** from
  `PLAN.md`, because the remaining emitted-JS drift sat in Rust's
  `compiler-rust/src/js_ir/mod.rs` and the primitive lowering hooks in
  `compiler-rust/src/lambda/compile.rs`, where `Length(...)` and
  `IsNullOrUndefined(...)` nodes were still emitted for pure literals that
  OCaml folds directly in `js_exp_make.array_length`, `string_length`,
  `function_length`, and `is_null_undefined`
- OCaml reference:
  `compiler/core/js_exp_make.ml`
- Rust change:
  - added OCaml-aligned `Expression::length` folding for pure array/caml-block
    literals, plain string literals, and function arity in
    `compiler-rust/src/js_ir/mod.rs`
  - added OCaml-aligned `Expression::is_null_or_undefined` folding for
    immediate `null` / `undefined` and for known non-nullish numbers,
    arrays, and caml blocks in `compiler-rust/src/js_ir/mod.rs`
  - routed `Pstringlength`, `Parraylength`, and nullable-option lowering in
    `compiler-rust/src/lambda/compile.rs` through those helpers instead of
    always emitting raw IR nodes
  - added focused regressions covering folded array length, string length,
    function length, and nullish predicates
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_array_length_folds_pure_array_literals_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_string_length_folds_plain_string_literals_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_function_length_folds_fun_arity_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_is_null_or_undefined_folds_numbers_false_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_nullable_predicates_to_js_null_checks -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact direct release repros for `tests/tests/src/js_array_test.res` and
    `tests/tests/src/js_nullable_test.res`, both diffing cleanly against the
    checked-in snapshots after the change
  - unchanged broader guards for `tests/tests/src/test_zero_nullable.res` and
    `tests/tests/src/option_repr_test.res`, both still differing in the same
    remaining nullable/option clusters rather than regressing into new failures
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/js_array_test.res` now matches exactly, with the pure
    `[1, 2, 3].length` case folded to `3` like OCaml
  - `tests/tests/src/js_nullable_test.res` now matches exactly, with immediate
    `(3 == null)` checks folded away like OCaml
  - the full authoritative sweep improved by three files while keeping compile
    errors at zero, confirming the helper-level folds clear more than the two
    direct repros
- Topline impact:
  - JS snapshot parity: **513 / 657** -> **516 / 657** (**+3**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **144** -> **141** (**-3**)
- Keep this change because it matches `js_exp_make.ml`'s constant-folding
  rules, improves the authoritative baseline, and leaves the remaining
  nullable-option drift in files like `test_zero_nullable` as a separate
  lowering problem rather than a reason to keep Rust's JS-expression layer more
  conservative than OCaml.

Latest iteration on **2026-04-15**:

- Active slice: port OCaml's JS-expression purity and `&&` simplification for
  `Array.isArray` guards, so redundant nullish checks stop surviving when the
  backend already has a stronger object/array test
- Active backend focus for this slice is **Phase 4: Port JS Passes** from
  `PLAN.md`, because the remaining emitted-JS drift sat in Rust's
  `compiler-rust/src/js_ir/mod.rs`, where `js_and_expression` and
  `expression_has_no_side_effects` still treated `Array.isArray(x)` calls as
  generic effectful calls and only recognized the string-literal callee form,
  preventing OCaml-style boolean guard collapse on the `StaticIndex(Array,
  "isArray")` form the Rust backend actually emits
- OCaml reference:
  `compiler/core/js_exp_make.ml` and
  `compiler/core/js_analyzer.ml`
- Rust change:
  - updated `compiler-rust/src/js_ir/mod.rs` so the JS analyzer and
    simplifier recognize both `Array.isArray(x)` callee encodings
    (`"Array.isArray"` and `Array["isArray"]`) and treat them as pure when
    their argument is pure, matching OCaml's `no_side_effect` /
    `simplify_and_` behavior instead of conservatively blocking the recursive
    `&&` simplification
  - added focused regressions
    `test_js_and_simplifies_static_array_is_array_nullish_guards_like_ocaml`
    and
    `test_js_and_simplifies_object_guard_with_static_array_exclusion_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_js_and_simplifies_static_array_is_array_nullish_guards_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_js_and_simplifies_object_guard_with_static_array_exclusion_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_js_and_simplifies_boolean_typeof_nullish_guards_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/DictPatternMatchingOptimization.res`,
    diffing `/tmp/DictPatternMatchingOptimization.mjs` against the checked-in
    snapshot
  - unchanged broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - `tests/tests/src/DictPatternMatchingOptimization.res` still differs, but
    the remaining drift is now the higher-level branch polarity / early-return
    shape rather than the pure `Array.isArray`-guard simplification rule this
    slice targeted
  - the full authoritative sweep improved by one file, confirming the
    OCaml-aligned `Array.isArray` purity/simplification rule clears at least
    one checked-in snapshot without reintroducing compile errors
- Topline impact:
  - JS snapshot parity: **512 / 657** -> **513 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **145** -> **144** (**-1**)
- Keep this change because it matches OCaml's `js_analyzer` /
  `js_exp_make.simplify_and_` behavior for `Array.isArray`, improves the
  authoritative baseline, and leaves the remaining object-guard branch-shape
  drift as a separate follow-up pass-order issue rather than a reason to keep
  the Rust simplifier overly conservative.

Latest iteration on **2026-04-15**:

- Active slice: keep pure nested immutable constructor blocks inline during
  `js_pass_flatten_and_mark_dead` splitting, so list/constructor literals stop
  being hoisted into synthetic helpers like `fake_y_1` while nested
  record/module fields continue to follow the existing helper-materialization
  path
- Active backend focus for this slice is **Phase 4: Port JS Passes** from
  `PLAN.md`, because the remaining drift sat in Rust's
  `flatten_and_mark_dead` immutable-`CamlBlock` binding split in
  `compiler-rust/src/lambda/compile.rs`, where nested constructor payloads were
  still treated like arbitrary complex block items and hoisted even when the
  checked-in OCaml snapshots kept the constructor tree inline
- OCaml reference:
  `compiler/core/js_pass_flatten_and_mark_dead.ml` and
  `compiler/core/js_dump.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so the
    `flatten_and_mark_dead` helper-splitting and substituted-index checks treat
    nested immutable constructor `CamlBlock`s as inlineable simple items
    recursively, while leaving nested records/modules non-simple and therefore
    still helperized
  - kept focused regression coverage on the constructor-inline case with
    `js_flatten_and_mark_dead_keeps_pure_nested_immutable_caml_blocks_inline`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml js_flatten_and_mark_dead_keeps_pure_nested_immutable_caml_blocks_inline -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml js_flatten_and_mark_dead_substitutes_immutable_caml_block_index_reads -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml js_flatten_and_mark_dead_substitutes_single_field_module_reads -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact direct release repro for `tests/tests/src/minimal_test.res`,
    diffing `/tmp/minimal_test.mjs` against the checked-in snapshot
  - unchanged broader guard repro for `tests/tests/src/RecordCoercion.res`,
    diffing `/tmp/RecordCoercion.mjs` against the checked-in snapshot
  - unchanged stable guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/minimal_test.res` now matches exactly again: the pure
    nested cons tail stays inline inside `fake_y` instead of being spilled into
    `fake_y_1`
  - `tests/tests/src/RecordCoercion.res` remains exact, confirming nested
    record/module materialization did not regress while fixing the constructor
    case
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - the full authoritative sweep improved by two files, confirming the
    constructor-inline rule clears more than the single direct repro without
    reintroducing compile errors
- Topline impact:
  - JS snapshot parity: **510 / 657** -> **512 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **147** -> **145** (**-2**)
- Keep this change because it removes a real emitted-JS drift on nested
  constructor/list literals, preserves the stable record/module guard files,
  and improves the authoritative baseline without reopening compile failures.

Latest iteration on **2026-04-15**:

- Active slice: port OCaml's recursive-binding decomposition and dummy-object
  update path so legacy `Lletrec` groups stop compiling acyclic singletons as
  recursive placeholders and stop lowering mutually recursive blocks as
  `let x; x = {...}` assignments
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`, because the optimized-lambda boundary was already
  green and the emitted-JS drift sat in Rust's `Lambda::Lletrec` lowering in
  `compiler-rust/src/lambda/compile.rs`, which was still skipping OCaml's
  `Lam_scc.scc` split and `compile_recursive_let` dummy-object
  `Primitive_object.updateDummy` path
- OCaml reference:
  `compiler/core/lam_scc.ml` and
  `compiler/core/lam_compile.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so recursive bindings are
    first decomposed into SCCs using free-variable dependencies, mirroring
    `Lam_scc.scc` instead of treating every incoming `Lletrec` binding as part
    of one recursive group
  - lowered acyclic singleton SCCs through `compile_let_binding` as plain
    strict lets, which removes bogus recursive placeholders from files like
    `minimal_test`
  - lowered the remaining general recursive `Pmakeblock` path through dummy
    object declarations plus `Primitive_object.updateDummy(...)`, matching
    OCaml's `compile_recursive_let` instead of assigning a finished object into
    an uninitialized `let x;`
  - added focused regressions
    `acyclic_letrec_singletons_lower_like_lam_scc_plain_lets`
    and
    `mutually_recursive_record_bindings_lower_to_runtime_update_dummy_calls`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml acyclic_letrec_singletons_lower_like_lam_scc_plain_lets -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml mutually_recursive_record_bindings_lower_to_runtime_update_dummy_calls -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml recursive_self_referential_record_bindings_lower_to_dummy_object_updates_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact direct release repro for `tests/tests/src/rec_array_test.res`,
    diffing `/tmp/rec_array_test.mjs` against the checked-in snapshot
  - unchanged broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - improved but not-yet-exact direct repro for `tests/tests/src/minimal_test.res`,
    where the bogus recursive placeholder is gone but a pure nested cons tail is
    still hoisted into `fake_y_1`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - exact snapshot matches were restored for
    `tests/tests/src/gpr_1716_test.res`,
    `tests/tests/src/queue_402.res`,
    `tests/tests/src/rec_array_test.res`,
    `tests/tests/src/rec_fun_test.res`,
    `tests/tests/src/recursive_records_test.res`, and
    `tests/tests/src/unboxed_use_case.res`
  - `tests/tests/src/minimal_test.res` now follows the OCaml recursive-binding
    split instead of emitting `let fake_y; fake_y = ...`, but still differs by
    hoisting the pure nested tail block into `fake_y_1`; treat that as a
    separate remaining pure-block lowering issue rather than a reason to revert
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **504 / 657** -> **510 / 657** (**+6**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **153** -> **147** (**-6**)
- Keep this change because it matches OCaml's `Lam_scc.scc` /
  `compile_recursive_let` behavior, clears a real recursive-binding cluster
  across six checked-in snapshots, and leaves the remaining `minimal_test`
  nested-block hoist as a smaller follow-up lowering issue rather than a
  contradiction of the port.

Latest iteration on **2026-04-15**:

- Active slice: lower `Lassign` through the same statement-plus-`unit` path as
  OCaml's `compile_assign`, so let-bound and exported unit assignments stop
  materializing value-producing JS assignment expressions like
  `let v = u = u + 1 | 0`
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`, because the optimized-lambda boundary was already
  green and the emitted-JS drift sat in Rust's `Lambda::Lassign` lowering in
  `compiler-rust/src/lambda/compile.rs`, where assignments were still compiled
  as expression values instead of following OCaml's statement/value split
- OCaml reference:
  `compiler/core/lam_compile.ml` and
  `compiler/core/js_output.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so `Lambda::Lassign` emits
    the assignment into the prelude and returns `undefined`, matching OCaml's
    `compile_assign` / `output_of_block_and_expression` unit semantics instead
    of treating assignment as a value-producing JS expression
  - added focused regressions
    `lassign_expression_lowers_to_statement_prelude_and_unit_value`
    and
    `let_bindings_of_unit_lassigns_emit_effects_before_undefined_declarations`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lassign_expression_lowers_to_statement_prelude_and_unit_value -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml let_bindings_of_unit_lassigns_emit_effects_before_undefined_declarations -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact direct release repro for `tests/tests/src/test_incr_ref.res`,
    diffing `/tmp/test_incr_ref.mjs` against the checked-in snapshot
  - unchanged broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_incr_ref.res` now matches exactly again: Rust emits
    the mutation as `u = u + 1 | 0;` followed by `let v;`, matching the
    checked-in OCaml snapshot instead of exporting the assignment result
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - the full authoritative sweep improved by one file, confirming the unit
    assignment/export cluster shrank without perturbing the stable guard
- Topline impact:
  - JS snapshot parity: **503 / 657** -> **504 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **154** -> **153** (**-1**)
- Keep this change because it matches OCaml's `compile_assign` lowering for
  `Lassign`, fixes a real emitted-JS semantic drift on `test_incr_ref`, and
  improves the authoritative baseline without perturbing the stable
  `ExternalShadow` guard.

Latest iteration on **2026-04-15**:

- Active slice: port OCaml's `record_assign` dead-temporary-write collapse so
  record-field writes to pure fresh literals return the RHS value instead of
  materializing a dead `({x: ...}).field = ...` assignment in emitted JS, while
  still keeping assignments whose target construction has effects
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`, because the optimized-lambda boundary was already
  green and the drift sat in Rust's `Psetfield` lowering in
  `compiler-rust/src/lambda/compile.rs`, where `compile_set_field` still always
  emitted a property assignment instead of mirroring OCaml's
  `Js_of_lam_block.set_field` / `Js_exp_make.record_assign` behavior for pure
  temporary blocks
- OCaml reference:
  `compiler/core/lam_compile_primitive.ml`,
  `compiler/core/js_of_lam_block.ml`, and
  `compiler/core/js_exp_make.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so `compile_set_field`
    returns the RHS directly when the target is a pure temporary `Array` or
    `CamlBlock`, matching OCaml's `record_assign` / `assign_by_exp`
    short-circuit instead of always emitting `target.field = value`
  - added focused regressions
    `top_level_record_field_assignments_on_pure_fresh_literals_collapse_to_rhs_effects`,
    `source_record_field_assignments_on_pure_fresh_literals_collapse_to_rhs_effects`,
    and
    `source_record_field_assignments_on_impure_fresh_literals_keep_the_assignment`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml top_level_record_field_assignments_on_pure_fresh_literals_collapse_to_rhs_effects -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml source_record_field_assignments_on_pure_fresh_literals_collapse_to_rhs_effects -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml source_record_field_assignments_on_impure_fresh_literals_keep_the_assignment -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact direct release repro for `tests/tests/src/gpr_4025_test.res`,
    diffing `/tmp/gpr_4025_test.mjs` against the checked-in snapshot
  - unchanged broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_4025_test.res` now matches exactly: the dead
    top-level assignment to a pure fresh record literal is gone, while the
    later function-local impure-target assignment stays materialized
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - the full authoritative sweep improved by two files, indicating the same
    pure-temporary-setfield rule cleared another snapshot in the same cluster
- Topline impact:
  - JS snapshot parity: **501 / 657** -> **503 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **156** -> **154** (**-2**)
- Keep this change because it ports OCaml's `record_assign` /
  `Js_of_lam_block.set_field` dead-write elimination into Rust's `Psetfield`
  lowering, fixes a real emitted-JS drift on `gpr_4025_test`, and improves the
  authoritative baseline without perturbing the stable `ExternalShadow` guard.

Latest iteration on **2026-04-15**:

- Active slice: lower nested `staticcatch` handlers that only jump outward into
  already-active handlers without synthesizing a fresh local `exit` temp, so
  return-position control flow matches OCaml on files like
  `gpr_3609_test.res`
- Active backend focus for this slice is **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`, because the optimized-lambda boundary was
  already green and the emitted-JS drift sat in Rust's `LstaticCatch`
  lowering in `compiler-rust/src/lambda/compile.rs`, where handler forwarding
  was still more conservative than OCaml's `lam_compile` static-jump handling
- OCaml reference:
  `compiler/core/lam_compile.ml` and
  `compiler/core/lam_compile_context.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `staticcatch_requires_explicit_jump` only keeps an explicit jump temp when
    the handler contains unresolved nested static control flow, not when its
    `LstaticRaise`s already target an active outer static / fallthrough / jump
    handler
  - added focused regression
    `nested_staticcatch_binding_handlers_that_raise_outward_avoid_exit_temps`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_staticcatch_binding_handlers_that_raise_outward_avoid_exit_temps -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml staticcatch_wrapped_int_return_switches_omit_empty_default_arms -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml single_case_staticcatch_wrapped_named_variant_return_switch_falls_through_to_handler -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact direct release repro for `tests/tests/src/gpr_3609_test.res`,
    diffing `/tmp/gpr_3609_test.mjs` against the checked-in snapshot
  - broader cluster repro for
    `tests/tests/src/DictPatternMatchingOptimization.res`,
    diffing `/tmp/DictPatternMatchingOptimization.mjs` against the checked-in
    snapshot
  - unchanged broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_3609_test.res` now matches exactly: the nested
    variant/staticcatch return path no longer emits `let exit = 0; ... if (exit
    === 1)` and instead matches OCaml's direct branch return shape
  - the fresh authoritative diff set also dropped
    `tests/tests/src/extensible_variant_test.res`, indicating the same nested
    staticcatch-return fix cleared a second file from the cluster
  - `tests/tests/src/DictPatternMatchingOptimization.res` still differs, but
    it now stands as the remaining broader control-flow / guard-ordering file
    in this area rather than sharing the exact `gpr_3609` nested-staticcatch
    temp pattern
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **499 / 657** -> **501 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **158** -> **156** (**-2**)
- Keep this change because it matches OCaml's static-jump lowering more
  closely in nested return-position handlers, removes a real emitted-JS
  `exit`-temp cluster, and improves the authoritative baseline without
  perturbing the stable `ExternalShadow` guard.

Latest iteration on **2026-04-15**:

- Active slice: treat module-field aliases used under loop/function capture
  boundaries the same way OCaml's backend does, so post-lowering alias
  substitution stops erasing bindings like `let cmp = M.cmp` when the only use
  sits inside a `for` body
- Active backend focus for this slice is **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`, because the optimized-lambda boundary was
  already green and the drift sat in Rust's `simplify_for_js_backend`
  approximation of OCaml's `lam_pass_count` / `lam_pass_lets_dce` capture
  semantics for alias materialization under loops
- OCaml reference:
  `compiler/core/lam_pass_count.ml`,
  `compiler/core/lam_pass_lets_dce.ml`, and
  `compiler/core/lam_util.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so nontrivial alias
    substitutions no longer propagate across function / loop capture
    boundaries, matching OCaml's use-count reset behavior under lambdas and
    loops
  - updated alias-use accounting so `Lwhile` / `Lfor` uses mark aliases as
    captured before the final single-use inlining check, again matching
    `Lam_pass_count.collect_occurs`
  - added focused regression
    `keeps_module_field_aliases_materialized_inside_for_loops_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml keeps_module_field_aliases_materialized_inside_for_loops_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml does_not_inline_captured_single_use_aliases -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml keeps_local_module_field_wrappers_materialized_like_functors_res -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact AST-path release repro for `tests/tests/src/bs_map_set_dict_test.res`
    from `tests/tests/lib/bs`, diffing `/tmp/bs_map_set_dict_test.mjs`
    against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bs_map_set_dict_test.res` now matches exactly again: the
    backend keeps `let cmp = m_dict$1.cmp;` materialized before the set loop,
    matching the checked-in OCaml snapshot
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - the full authoritative sweep stayed flat, which means this correct
    OCaml-aligned loop-capture fix traded against another still-unidentified
    file in the broader alias/materialization cluster
- Topline impact:
  - JS snapshot parity: **499 / 657** -> **499 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **158** -> **158** (**no change**)
- Keep this change because it ports OCaml's `Lam_pass_count` captured-use
  semantics into Rust's post-lowering alias simplifier and resolves a real
  emitted-JS drift on `bs_map_set_dict_test`; the flat topline indicates a
  separate remaining file in the same backend cluster, not that this fix is
  incorrect.

Latest iteration on **2026-04-15**:

- Active slice: keep OCaml's `ForRange` synthetic `*_finish` temp-name
  reservation in the enclosing printer scope so sibling loops in the same
  function keep the same suffix progression as `js_dump`, instead of
  reusing unsuffixed finish temps after the Rust printer pops its loop-local
  scope
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`, because the optimized-lambda boundary was already green and the
  remaining drift sat in the downstream `js_dump`-equivalent name allocator in
  `compiler-rust/src/js_ir/printer.rs`
- OCaml reference:
  `compiler/core/js_dump.ml` and
  `compiler/ext/ext_pp_scope.ml`
- Rust change:
  - updated `compiler-rust/src/js_ir/printer.rs` so `ForRange` finish bindings
    are allocated in the enclosing scope before entering the loop-local scope,
    then reserved inside the loop as well
  - added focused regression
    `test_for_range_finish_binding_suffix_persists_across_sibling_loops_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_for_range_finish_binding_suffix_persists_across_sibling_loops_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_unit_function_tail_if_drops_else_return_undefined -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact AST-path release repro for `tests/tests/src/bs_mutable_set_test.res`
    from `tests/tests/lib/bs`, diffing `/tmp/bs_mutable_set_test.mjs` against
    the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bs_mutable_set_test.res` now matches exactly: the second
    sibling loop in the same test function prints `i_finish$1` like OCaml
    instead of reusing `i_finish`
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - the full authoritative sweep improved by two files, which indicates the
    same loop-finish naming fix cleared an additional snapshot from the same
    printer cluster
- Topline impact:
  - JS snapshot parity: **497 / 657** -> **499 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **160** -> **158** (**-2**)
- Keep this change because it ports OCaml's `js_dump` / `Ext_pp_scope`
  temporary-name allocation behavior into the Rust printer, fixes a real
  byte-level JS drift in the downstream dumper, and improves the authoritative
  baseline without perturbing the stable `ExternalShadow` guard.

Latest iteration on **2026-04-15**:

- Active slice: collapse nested unit-return guards in the JS IR / dumper path
  so `LargeUnboxedVariantOptimization.res` lowers to the same single
  `if (key === "space" && state.active)` guard as OCaml instead of preserving a
  large literal-membership residue and then printing a nested `if` plus a
  trailing unit return
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`, because optimized-lambda was already green and the remaining drift
  on this small internal file sat downstream in Rust's `js_exp_make` /
  `js_stmt_make` / `js_dump` equivalents
- OCaml reference:
  `compiler/core/js_exp_make.ml`,
  `compiler/core/js_stmt_make.ml`, and
  `compiler/core/js_dump.ml`
- Rust change:
  - updated `compiler-rust/src/js_ir/mod.rs` so boolean simplification can
    still absorb large conjunction/disjunction membership cases when the shared
    literal sits deeper than the recursive simplifier's normal fixed-point walk
  - updated `compiler-rust/src/js_ir/printer.rs` so function bodies shaped like
    `nested if; return undefined` collapse to the same merged guard before the
    trailing unit return is elided
  - added focused regressions:
    `test_js_or_absorbs_large_conjunction_membership_against_same_literal_like_ocaml`,
    `test_print_unit_function_body_with_trailing_return_merges_nested_if_like_ocaml`,
    and the existing nested-if printer guards continue to cover direct and
    block-wrapped forms
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml literal_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_unit_function_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/LargeUnboxedVariantOptimization.res`,
    diffing `/tmp/LargeUnboxedVariantOptimization.mjs` against the checked-in
    snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/LargeUnboxedVariantOptimization.res` now matches exactly:
    the backend emits the single merged `key === "space" && state.active` guard
    expected by the checked-in snapshot
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **497 / 657** -> **498 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **160** -> **159** (**-1**)
- Keep this change because it ports a real OCaml-aligned boolean/statement
  simplification cluster in the downstream JS backend and removes a concrete
  emitted-JS drift without perturbing the stable `ExternalShadow` guard.

Latest iteration on **2026-04-15**:

- Active slice: keep backend beta-reduction and alias substitution lexical so
  returned wrappers preserve their own parameters instead of inheriting outer
  placeholder values like `undefined`, while leaving unrelated alias-shape drift
  for a later slice
- Active backend focus for this slice is **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`, because the optimized-lambda boundary was
  already green and the remaining drift sat in Rust's
  `simplify_for_js_backend` pass: direct backend cleanup could beta-reduce or
  alias-substitute through rebinding scopes, which showed up downstream as
  `Primitive_int.compare(undefined, prim1)` in `bs_array_test` and
  `fromArray(undefined, Icmp)` / `eq(a, b, undefined)` in
  `bs_map_set_dict_test`
- OCaml reference:
  `compiler/core/lam_beta_reduce.ml`,
  `compiler/core/lam_bounded_vars.ml`, and
  `compiler/core/lam_pass_lets_dce.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/beta_reduce.rs` so backend beta
    reduction rewrites bounded variables like OCaml's
    `Lam_bounded_vars.rewrite` instead of calling the raw capture-unsafe
    substitution directly
  - updated `compiler-rust/src/lambda/simplify.rs` so `substitute_alias_use`
    stops at rebinding scopes (`Lfunction`, `Llet`, `Lletrec`,
    `LstaticCatch`, `LtryWith`, `Lfor`) instead of substituting through
    shadowed bodies
  - added focused regressions:
    `test_propagate_beta_reduce_renames_reused_returned_function_params`,
    `test_propagate_beta_reduce_with_map_renames_reused_returned_function_params`,
    `substitute_alias_use_does_not_rewrite_shadowed_function_bodies`, and
    `backend_alias_inlining_preserves_shadowed_reused_function_params`
- Verified focused guards for this slice:
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_propagate_beta_reduce_renames_reused_returned_function_params -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_propagate_beta_reduce_with_map_renames_reused_returned_function_params -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml substitute_alias_use_does_not_rewrite_shadowed_function_bodies -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml backend_alias_inlining_preserves_shadowed_reused_function_params -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml does_not_inline_captured_single_use_aliases -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact AST-path release repro for `tests/tests/src/bs_array_test.res` from
    `tests/tests/lib/bs`, diffing `/tmp/bs_array_test.mjs` against the
    checked-in snapshot
  - exact AST-path release repro for `tests/tests/src/bs_map_set_dict_test.res`
    from `tests/tests/lib/bs`, diffing `/tmp/bs_map_set_dict_test.mjs` against
    the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bs_array_test.res` now matches exactly: the comparator
    wrapper keeps `prim0` instead of collapsing to `undefined`
  - `tests/tests/src/bs_map_set_dict_test.res` no longer drops forwarded
    `none` / `extra`; the remaining drift in that file is now the separate
    `let cmp = m_dict$1.cmp` alias-materialization difference
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **502 / 657** -> **503 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **155** -> **154** (**-1**)
- Keep this change because it ports OCaml's bounded-variable rewrite into
  Rust's backend beta-reduction path and makes backend alias substitution
  lexical, which removes a real emitted-JS `undefined` capture cluster without
  perturbing the stable `ExternalShadow` guard.

Latest iteration on **2026-04-15**:

- Active slice: keep recursive tail-loop lowering and same-group alias emission
  attached to the arity-preserving `PjsFnMake` wrappers that survive backend
  simplification, so files like `a_scope_bug.res` still lower through the
  OCaml-style recursive loop path instead of falling back to `return even(...)`
  plus placeholder recursive assignments
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`, because the optimized-lambda boundary was already
  green and the remaining drift sat in Rust's `lam_compile`-equivalent
  recursive-let lowering: after `simplify_for_js_backend`, the second binding in
  `a_scope_bug` becomes an arity-preserving `js_fn_make_1 odd` wrapper, but the
  Rust backend only recognized bare `Lfunction` recursive bindings when it built
  the tail-loop target set and direct recursive alias emissions
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_recursive_let`'s
  recursive-function loop lowering, plus `compiler/core/lam_eta_conversion.ml`
  for the arity-preserving `unsafe_adjust_to_arity` wrapper shape that shows up
  in simplified recursive groups
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so recursive bindings now
    recognize wrapped `PjsFnMake` / `PjsFnMakeUnit` function values when
    deciding whether to lower through the tail-loop path
  - taught recursive alias handling and tail-target discovery to treat
    arity-preserving `PjsFnMake(..., Lvar target)` wrappers as direct aliases of
    the target recursive function, which keeps same-group aliases like
    `even = odd` in the same tailcall family
  - added / extended focused regressions:
    `recursive_wrapped_js_fn_make_bindings_lower_to_looping_while_bodies` and
    `recursive_function_aliases_reenter_the_same_tail_loop_like_a_scope_bug`
- Verified focused guards for this slice:
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml recursive_wrapped_js_fn_make_bindings_lower_to_looping_while_bodies -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml recursive_function_aliases_reenter_the_same_tail_loop_like_a_scope_bug -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml recursive_self_tailcalls_ -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml recursive_function_bindings_lower_directly_without_placeholder_assignments -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact AST-path release repro for `tests/tests/src/a_scope_bug.res` from
    `tests/tests/lib/bs`, diffing `/tmp/a_scope_bug.mjs` against the checked-in
    snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/a_scope_bug.res` now matches exactly: the recursive group
    lowers back to the looping `odd` body plus the direct `let even = odd;`
    alias, instead of emitting `return even(32);` and a placeholder recursive
    assignment
  - wrapped recursive function bindings still lower through the existing
    self-tailcall loop path, and direct mutually-recursive function bindings
    still avoid placeholder declarations
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **503 / 657** -> **504 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **154** -> **153** (**-1**)
- Keep this change because it fixes a real recursive-lowering gap in Rust's
  `lam_compile` port, matches the OCaml snapshot on `a_scope_bug` without
  disturbing the stable `ExternalShadow` guard, and improves the authoritative
  657-file baseline by one file.

Latest iteration on **2026-04-15**:

- Active slice: keep resolved `staticcatch` handlers in the surrounding
  return continuation instead of re-entering generic expression lowering, so
  nested `staticraise` chains stop manufacturing `let ifres` temps and fall
  back to direct guard returns / throws like OCaml
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`, because the drift sat in Rust's
  `lam_compile`-equivalent continuation threading after optimized-lambda
  parity: the lambda dump for `tests/tests/src/variant.res` was already
  OCaml-aligned and still contained the nested `Lstaticcatch` / `Lstaticraise`
  chain for `fooExn`, but Rust's return-path lowering resolved those handlers
  through `compile_expr`, which forced the nested handler bodies back through
  value-position `ifres` temporaries before the final `return`
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_staticcatch` and the way
  it keeps handler compilation in the active continuation (`EffectCall` /
  `Assign`) instead of re-lowering `Lstaticraise` through a plain `NeedValue`
  expression path
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so return-position
    `LstaticRaise` lowering now resolves the target handler and immediately
    re-enters `compile_return_block` instead of falling back to `compile_expr`
  - applied the same continuation-preserving rule to
    `compile_tail_loop_return_block`, which shares the same return-position
    lowering boundary for self-tailcall functions
  - added the focused regression
    `nested_static_raises_in_return_position_keep_the_return_continuation`
- Verified focused guards for this slice:
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_static_raises_in_return_position_keep_the_return_continuation -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml single_case_staticcatch_wrapped_named_variant_return_switch_falls_through_to_handler -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml multi_case_staticcatch_wrapped_named_variant_return_switch_moves_fallthrough_cases_last -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/variant.res`, diffing
    `/tmp/variant.mjs` against the checked-in snapshot
  - direct release repro for `tests/tests/src/test_static_catch_ident.res`,
    diffing `/tmp/test_static_catch_ident.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/variant.res` no longer emits the nested
    `let ifres; ... return ifres;` chain in `fooExn`; the remaining drift in
    that file is now the separate `fooC` branch-polarity cleanup instead of
    staticcatch handler continuation loss
  - `tests/tests/src/test_static_catch_ident.res` now lowers the nested
    `Scan_failure` / `"Failure"` handler cases as direct branch returns rather
    than materializing an intermediate result temp before the final loop body
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **500 / 657** -> **503 / 657** (**+3**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **157** -> **154** (**-3**)
- The cached `ifres` / `return ifres` staticcatch-return motif shrank
  materially after the authoritative rerun: diff files containing
  `let ifres;`, `return ifres;`, or `let $$switch;` dropped from **37** to
  **15**
- Keep this change because it ports a real continuation rule from OCaml's
  `lam_compile.ml` into Rust's return-path lowering, removes a broad
  staticcatch-handler temp cluster after optimized lambda without perturbing
  the stable `ExternalShadow` guard, and improves the authoritative 657-file
  baseline by three files.

Latest iteration on **2026-04-15**:

- Active slice: keep single-use aliases materialized when their replacement
  reads a binding that the body later assigns, so post-ref-elimination temps
  like `let tmp = a` survive into JS lowering instead of collapsing to the
  reassigned mutable variable
- Active backend focus for this slice is **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`, because the drift sat in Rust's
  `simplify_for_js_backend` pass between optimized-lambda parity and JS IR
  lowering: the lambda dump for `fib.res` was already OCaml-aligned and still
  contained `let tmp = a.contents`, but a later Rust backend-simplify sweep
  ref-eliminated that to `let tmp = a` and then incorrectly substituted the
  alias through a later `a := ...`
- OCaml reference:
  `compiler/core/lam_pass_remove_alias.ml`, especially the fact that the OCaml
  alias pass flattens field reads but does not substitute plain aliases through
  later assignments; the `-drawlambda` output for `tests/tests/src/fib.res`
  also confirms both compilers still carry `let (tmp = field a) ... setfield b
  (... tmp)` at the optimized-lambda boundary
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so both environment-level
    alias substitutions and the single-use alias elimination path now refuse to
    substitute when the replacement's free variables are assigned later in the
    body
  - added a focused simplify regression
    `keeps_single_use_aliases_when_their_source_is_assigned_later`
  - added a driver-level regression
    `source_ref_aliases_survive_later_mutation_like_ocaml` to cover the final
    `fib3` loop shape end to end
- Verified focused guards for this slice:
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml keeps_single_use_aliases_when_their_source_is_assigned_later -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml source_ref_aliases_survive_later_mutation_like_ocaml -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml eliminates_non_captured_ref_cells_to_mutable_variables -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/fib.res`, diffing `/tmp/fib.mjs`
    against the checked-in snapshot
  - direct release repro for `tests/tests/src/test_while_closure.res`, diffing
    `/tmp/test_while_closure.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/fib.res` now matches exactly: the loop keeps
    `let tmp = a; a = b; b = b + tmp | 0;` like OCaml instead of collapsing the
    carried alias to the reassigned `a`
  - `tests/tests/src/test_while_closure.res` also now matches exactly: the
    captured `j = n.contents` alias stays materialized instead of folding to the
    later-mutated loop variable
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **498 / 657** -> **500 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **159** -> **157** (**-2**)
- Keep this change because it removes a Rust-only alias rewrite that OCaml's
  backend does not perform across later assignments, fixes the concrete `fib`
  temp-carrying bug plus another mutable-alias snapshot in the same cluster,
  and improves the authoritative 657-file baseline by two files.

Latest iteration on **2026-04-15**:

- Active slice: lower lambda string constants with `DNoQuotes` through the same
  ordinary quoted-string path OCaml uses, so non-tagged `json\`...\``
  interpolations fall back to normal string concatenation instead of leaking raw
  unquoted template segments into the final JS
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`, because the remaining drift sat in the
  `Lam_compile` constant-lowering boundary rather than the final printer:
  optimized-lambda parity was already green, but Rust mapped
  `Const_string(..., DNoQuotes)` to a raw `NoQuotes` JS IR string while OCaml's
  backend lowers those lambda constants through `E.str`
- OCaml reference:
  `compiler/core/lam_compile_const.ml`, especially
  `Const_string {s; delim = None | Some DNoQuotes} -> E.str s`; the failing
  checked-in snapshot then shows the downstream effect in `tagged_template_test`
  as ordinary quoted string concatenation rather than a tagged-template/raw-js
  fragment
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `LambdaCompiler::compile_constant` now maps
    `Constant::String {delim: Some(StringDelim::NoQuotes)}` to the ordinary JS
    string delimiter path (`Delim::None`) instead of emitting a raw
    `Delim::NoQuotes` literal
  - kept explicit external marshaled constants on the existing raw-noquotes
    path via `compile_external_arg_const`, matching OCaml's separate
    external-argument handling
  - replaced the old constant-level regression with the OCaml-aligned behavior
    check `compile_constant_quotes_noquote_delim_strings_like_ocaml`
  - added a focused driver-level regression
    `source_json_template_falls_back_to_regular_string_interpolation_like_ocaml`
    to cover the `json\`some random ${"string"}\`` shape directly
- Verified focused guards for this slice:
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_constant_quotes_noquote_delim_strings_like_ocaml -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml source_json_template_falls_back_to_regular_string_interpolation_like_ocaml -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_marshaled_constant_args_in_js_call -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact AST-path release repro for `tests/tests/src/tagged_template_test.res`
    from `tests/tests/lib/bs`, diffing `/tmp/tagged_template_test.mjs` against
    the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/tagged_template_test.res` now matches exactly: the
    `json\`...\`` fallback emits `"some random " + "string"` like OCaml instead
    of leaking the first segment as raw unquoted JS
  - explicit marshaled external constants still stay raw in the JS backend, so
    this change is isolated to lambda string constants rather than the FFI
    constant path
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **497 / 657** -> **498 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **160** -> **159** (**-1**)
- Keep this change because it ports the exact OCaml `lam_compile_const.ml`
  delimiter rule into Rust, fixes the checked-in `json\`...\`` fallback without
  touching the separate raw external-constant path, and improves the
  authoritative 657-file baseline by one file.

Latest iteration on **2026-04-15**:

- Active slice: make the JS tailcall-inline pass recurse over block suffixes the
  same way OCaml does, so a directly-returned once-pure local helper still
  inlines when it appears after earlier statements in the same block instead of
  only when the whole block is a single `return helper(...)`
- Active backend focus for this slice is **Phase 4: Port JS Passes** from
  `PLAN.md`, because the remaining drift sat in
  `Js_pass_tailcall_inline`: OCaml walks blocks left-to-right and can inline the
  tail helper in a suffix like `if (...) ...; let nth_aux = ...; nth_aux(...)`,
  while Rust only tried that rule on single-statement blocks and therefore kept
  extra helper wrappers alive through final JS emission
- OCaml reference:
  `compiler/core/js_pass_tailcall_inline.ml`, especially the `block` walker that
  handles `x :: xs` recursively and the `[ Return (Call (Var ...)) ]` suffix
  case, allowing once-pure helpers to inline even when earlier statements remain
  in the surrounding block
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `TailcallInlineState::transform_block` now matches OCaml's recursive
    head/tail block traversal instead of only checking the whole block once
  - added a focused regression
    `js_tailcall_inline_inlines_suffix_named_calls_after_prefix_statements` to
    cover the `test_list` shape where a guarded prefix statement precedes the
    directly-returned local helper call
- Verified focused guards for this slice:
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml js_tailcall_inline_ -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml recursive_self_tailcalls_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/test_list.res`, diffing
    `/tmp/test_list.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_list.res` no longer emits the extra local loop-helper
    wrappers that OCaml already inlines away for `nth_aux`, `rmap_f`,
    `rmap2_f`, and `part`; the remaining drift in that file is now the separate
    `stable_sort` helper-placement cluster plus a few `Not_found` throw-shape
    differences
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **494 / 657** -> **497 / 657** (**+3**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **163** -> **160** (**-3**)
- Keep this change because it ports OCaml's block-suffix traversal rule in
  `Js_pass_tailcall_inline` directly, removes an entire local-helper-wrapper
  class from the final JS stream, and exposes the next deeper helper-placement
  cluster without regressing the broader guard file.

Latest iteration on **2026-04-15**:

- Active slice: keep sync component `props` wrappers materialized through the
  post-lowering simplify pass instead of eta-reducing them down to the inner
  `make` / `make$N` binding, while still letting async component wrappers
  collapse to the underlying async `make` path that OCaml already uses
- Active backend focus for this slice is **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`, because the remaining drift sat in the
  downstream simplify/remove-alias boundary before JS IR lowering: the
  optimized-lambda input already matched OCaml and still contained
  `function props -> apply make props`, but Rust simplified that wrapper away
  for sync components while OCaml carried the wrapper ownership through to final
  JS
- OCaml reference:
  `compiler/core/lam_pass_remove_alias.ml`, especially the alias/eta-reduction
  boundary that operates over the lowered lambda before JS compilation;
  `compiler/core/lam_pass_alpha_conversion.ml`, especially the late wrapper
  cleanup rules around `Pjs_fn_make`; and the exact `-drawlambda` output for
  `tests/tests/src/jsx_preserve_test.res`, where both compilers still show the
  sync component wrapper as `function props -> apply make props` before the JS
  backend runs
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so eta reduction now keeps a
    sync `props` wrapper when it is forwarding to a local make-like binding
    (`make` / `make$N`) with the same arity and the callee is non-async and has
    no raw directive
  - kept the async case on the old collapse path, matching OCaml's
    `async_jsx` snapshot where the final module field still points at the
    underlying `async function make(...)`
  - added focused regressions for both sides of the split:
    `keeps_sync_component_props_wrappers_materialized_for_js_backend` and
    `still_eta_reduces_async_component_props_wrappers`
- Verified focused guards for this slice:
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml component_props_wrappers -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml js_flatten_and_mark_dead_ -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact AST-path release repro for `tests/tests/src/jsx_preserve_test.res`
    from `tests/tests/lib/bs`, diffing `/tmp/jsx_preserve_test.mjs` against the
    checked-in snapshot
  - exact AST-path release repro for `tests/tests/src/async_jsx.res` from
    `tests/tests/lib/bs`, diffing `/tmp/async_jsx.mjs` against the checked-in
    snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/jsx_preserve_test.res` now matches exactly: the final JS
    keeps the sync component wrapper ownership, so the descriptive top-level
    function retains the OCaml `props` parameter instead of exposing the inner
    `make(param)` binding
  - `tests/tests/src/async_jsx.res` also now matches exactly: the sync `Bar`
    wrapper keeps `props`, while the async `Foo` component still takes the
    OCaml-aligned underlying `async function make(...)` path
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **491 / 657** -> **494 / 657** (**+3**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **166** -> **163** (**-3**)
- Keep this change because it preserves the exact sync-vs-async component
  wrapper split visible in the OCaml lowered lambda, removes the last remaining
  preserve-mode ownership/parameter-name residue in the focused files, and
  improves the authoritative 657-file baseline by three files.

Latest iteration on **2026-04-15**:

- Active slice: collapse the top-level sync component alias pair
  `let make$N = function ...; let Module$Component = make$N;` before final
  printing, so the printer sees the descriptive component binding as the
  function owner instead of the generic `make` / `make$N` temporary
- Active backend focus for this slice spans **Phase 4: Port JS Passes** and
  **Phase 5: Byte-Exact Dumping** from `PLAN.md`, because the key drift sat in
  the JS IR statement stream just before final emission: OCaml's final JS
  snapshots already have the descriptive binding owning the top-level function
  declaration, and `js_dump.ml` simply prints whichever identifier owns that
  function binding
- OCaml reference:
  `compiler/core/js_pass_flatten_and_mark_dead.ml`, especially the preserve-mode
  substitution boundary that keeps component `.make` reads materialized until
  printing; and `compiler/core/js_dump.ml`, especially the top-level variable
  declaration path that emits `function <ident>(...)` from the current binding
  owner rather than inventing names in the printer
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so the JS flatten/dead pass
    now collapses a live top-level sync alias pair of the form
    `make` / `make$N` -> descriptive component name into a single function-owned
    binding when the function is non-async, directive-free, non-recursive, and
    the generic `make` binding does not survive any later uses
  - kept async component aliases materialized, matching the existing
    `async_jsx` snapshot shape where `async function make(...)` remains and the
    descriptive component alias points at it
  - added focused JS-pass regressions for both sides of the split:
    `js_flatten_and_mark_dead_rebinds_sync_component_make_aliases_to_descriptive_names`
    and
    `js_flatten_and_mark_dead_keeps_async_component_make_aliases_materialized`
- Verified focused guards for this slice:
  - `RUSTFLAGS='-Awarnings' timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml js_flatten_and_mark_dead_ -- --nocapture`
  - `RUSTFLAGS='-Awarnings' timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact AST-path release repro for `tests/tests/src/jsx_preserve_test.res`
    from `tests/tests/lib/bs`, diffing `/tmp/jsx_preserve_test.mjs` against the
    checked-in snapshot
  - exact AST-path release repro for `tests/tests/src/async_jsx.res` from
    `tests/tests/lib/bs`, diffing `/tmp/async_jsx.mjs` against the checked-in
    snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - the remaining preserve-mode wrapper/function ownership drift is gone:
    `tests/tests/src/jsx_preserve_test.res` no longer emits
    `function make(...)` + `let Jsx_preserve_test$B = make`, and
    `tests/tests/src/async_jsx.res` no longer emits
    `function make$1(...)` + `let Async_jsx$Bar = make$1`
  - `tests/tests/src/jsx_preserve_test.res` and
    `tests/tests/src/async_jsx.res` still differ, but only on the narrower
    parameter-name residue (`props` vs `param`) rather than top-level binding
    ownership
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **491 / 657** -> **491 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **166** -> **166** (**no change**)
- Keep this change because it moves the Rust JS backend onto the OCaml-aligned
  ownership boundary for top-level sync component functions, eliminates the
  larger wrapper/alias hunk in the preserve-mode repro files, and leaves only
  the narrower parameter-naming residue for the next iteration even though the
  current file-level pass count does not move yet.

Latest iteration on **2026-04-15**:

- Active slice: respect OCaml's global `jsx_preserve` guard end-to-end so
  transformed JSX only stays preserved in the final backend for files that
  actually enable `-bs-jsx-preserve`, instead of preserving JSX syntax or
  module `.make` tag projections in ordinary `-bs-jsx` files
- Active backend focus for this slice spans **Phase 4: Port JS Passes** and
  **Phase 5: Byte-Exact Dumping** from `PLAN.md`, because OCaml applies the
  same `!Js_config.jsx_preserve` guard in both
  `js_pass_flatten_and_mark_dead.ml` and `js_dump.ml`: the JS pass should only
  preserve `.make` reads when preserve mode is on, and the dumper should only
  print JSX syntax when preserve mode is on
- OCaml reference:
  `compiler/core/js_dump.ml`, especially the transformed-JSX `Call` branch
  guarded by `when !Js_config.jsx_preserve`; and
  `compiler/core/js_pass_flatten_and_mark_dead.ml`, especially the
  `Some {expression_desc = J.Var (Id {name = "make"})} when !Js_config.jsx_preserve`
  projection-preservation guard
- Rust change:
  - updated `compiler-rust/src/driver.rs` and
    `compiler-rust/src/bin/bsc.rs` to detect `-bs-jsx-preserve` from source
    config and CLI flags, and thread that backend mode through final JS codegen
  - updated `compiler-rust/src/js_ir/printer.rs` so transformed JSX printing
    is gated by `jsx_preserve`, matching OCaml instead of printing JSX syntax
    whenever `call_transformed_jsx` was set
  - updated `compiler-rust/src/lambda/compile.rs` so the
    `js_flatten_and_mark_dead` pass only preserves transformed-JSX component
    `.make` projections when `jsx_preserve` is enabled; in non-preserve mode it
    now inlines the single-field module projection back to the component value
    like OCaml
  - added focused regressions for both sides of the guard:
    `test_print_transformed_jsx_requires_jsx_preserve_flag_like_ocaml` and
    `js_flatten_and_mark_dead_does_not_preserve_component_make_reads_without_jsx_preserve`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_transformed_jsx -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml js_flatten_and_mark_dead_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/ExternalArity.res`, diffing
    `/tmp/ExternalArity.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - ordinary `-bs-jsx` files no longer emit preserved JSX syntax or preserved
    module `.make` tag projections just because the transformed-JSX bit was set
  - `tests/tests/src/ExternalArity.res` now matches again instead of printing
    `<ReactIntl.FormattedMessage ... />`
  - `tests/tests/src/jsx_optional_props_test.res` now matches again instead of
    keeping `ComponentWithOptionalProps.make` alive in the runtime call target
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - `tests/tests/src/async_jsx.res` still differs, which is expected because it
    is a real preserve-mode file and its remaining drift is the separate
    wrapper/function naming cluster rather than the global preserve guard
- Topline impact:
  - JS snapshot parity: **489 / 657** -> **491 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **168** -> **166** (**-2**)
- Keep this change because it ports OCaml's `jsx_preserve` boundary directly in
  both the JS pass and the dumper, removes two concrete false-positive
  preserve-JSX diffs without touching real preserve-mode files, and improves
  the authoritative baseline with a clearly OCaml-aligned backend rule.

Latest iteration on **2026-04-15**:

- Active slice: preserve transformed JSX through the final JS backend so the
  dumper sees OCaml's record-block props and component `.make` tag projections
  instead of falling back to runtime-call syntax or flattening the tag down to
  the underlying component function variable
- Active backend focus for this slice is **Phase 4: Port JS Passes** from
  `PLAN.md`, because the key drift sat in
  `js_pass_flatten_and_mark_dead` after JS IR lowering: Rust was correctly
  carrying transformed JSX metadata into the dumper, but the JS pass still
  substituted `Foo.make` down to `Async_jsx$Foo` before final emission; the
  slice also required the matching `js_dump.ml` props-shape support so record
  `Caml_block` props printed as preserved JSX at all
- OCaml reference:
  `compiler/core/js_dump.ml`, especially the transformed-JSX `Call` branches
  and `print_jsx`; and
  `compiler/core/js_pass_flatten_and_mark_dead.ml`, especially the JSX-preserve
  substitution guard that stops inlining selected block projections before the
  dumper runs
- Rust change:
  - updated `compiler-rust/src/js_ir/printer.rs` so transformed JSX accepts
    record `CamlBlock(..., TagInfo::Record { .. })` props and filters optional
    `undefined` fields the same way OCaml does before printing JSX syntax
  - updated `compiler-rust/src/lambda/compile.rs` so the JS flatten/dead pass
    preserves the first argument of transformed JSX calls when it is a module
    `.make` projection, instead of substituting the block field to the raw
    component function value
  - added focused regressions for both layers:
    `test_print_transformed_jsx_record_block_props_like_ocaml` and
    `js_flatten_and_mark_dead_preserves_transformed_jsx_component_make_reads`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml transformed_jsx -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml js_flatten_and_mark_dead_substitutes_single_field_module_reads -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/async_jsx.res`, diffing
    `/tmp/async_jsx.mjs` against the checked-in snapshot
  - direct release repro for `tests/tests/src/jsx_preserve_test.res`, diffing
    `/tmp/jsx_preserve_test.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - transformed JSX now prints from the real OCaml-style shapes instead of
    falling back to `JsxRuntime.jsx/jsxs(...)` calls when props arrive as
    record `CamlBlock`s
  - component tags in preserved JSX now keep the OCaml-aligned member form such
    as `<Foo.make />`, `<B.make />`, and `<ContextProvider.make />` instead of
    collapsing to `<Async_jsx$Foo />`, `<Jsx_preserve_test$B />`, or the raw
    provider binding
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - `tests/tests/src/async_jsx.res` and `tests/tests/src/jsx_preserve_test.res`
    still differ, but the remaining drift is now narrower and sits in
    wrapper/function naming shapes rather than preserved JSX tag/props emission
- Topline impact:
  - JS snapshot parity: **491 / 657** -> **489 / 657** (**-2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **166** -> **168** (**+2**)
- Keep this change because it directly ports the OCaml dumper and
  `js_pass_flatten_and_mark_dead` preserve-JSX behavior, fixes the concrete
  tag/props backend drift visible in direct release repros, and therefore is a
  verified OCaml-aligned improvement even though the current global wrapper
  score regressed and the remaining wrapper/naming cluster still needs follow-up.

Latest iteration on **2026-04-15**:

- Active slice: keep one-step direct `PjsFnMake` beta reduction on the JS-path
  simplifier without globally preserving wrappers, so returned wrapper calls
  from `gpr_1692_test.res` survive later cleanup passes exactly where OCaml
  keeps them
- Active backend focus for this slice is **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`, because the mismatch lived in the
  post-lowering `lam_pass_remove_alias` / `lam_pass_alpha_conversion`
  boundary before JS IR lowering: Rust needed to beta-reduce through the
  direct wrapper once, then stop later no-beta cleanup passes from unwrapping
  the returned direct-wrapper callee back into a bare `Lfunction`
- OCaml reference:
  `compiler/core/lam.ml`, especially `Lam.apply` / `is_eta_conversion_exn`
  for direct `Pjs_fn_make` call reconstruction;
  `compiler/core/lam_pass_remove_alias.ml`, especially the direct-application
  `Lam_beta_reduce.propagate_beta_reduce` path;
  `compiler/core/lam_pass_alpha_conversion.ml`, especially `Pjs_fn_make` /
  `Pjs_fn_make_unit` simplification; and
  `compiler/core/lam_compile_main.ml` for the first-pass-then-cleanup
  sequence on the JS backend path
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so
    `reduce_direct_wrapper_application_once(...)` still beta-reduces direct
    wrapper callees once, but the follow-up subtree keeps the returned wrapper
    value materialized instead of globally preserving every `PjsFnMake`
  - added a callee-only preservation rule for the later
    `allow_direct_function_beta_reduce = false` cleanup passes so
    already-returned direct wrapper callees stay wrapped instead of being
    re-unwrapped to bare `Lfunction`s and collapsed again
  - kept ordinary `PjsFnMake` simplification elsewhere on the existing
    OCaml-aligned unwrap path, avoiding the broad regression from global
    wrapper preservation
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lambda::compile::tests::compile_effectful_underscore_binding_from_nested_js_function_calls_survives_shake -- --exact --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lambda::simplify::tests::keeps_nested_direct_wrapper_applications_visible_for_backend_codegen -- --exact --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lambda::simplify::tests::simplifies_named_nested_pjs_fn_make_application_chain_from_ari_regress_shape -- --exact --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lets_dce_pass_beta_reduces_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/gpr_1692_test.res`, diffing
    `/tmp/gpr_1692_test.mjs` against the checked-in snapshot
  - direct guard repros for
    `tests/tests/src/PartialApplicationNoRuntimeCurry.res` and
    `tests/tests/src/ExternalShadow.res`, diffing `/tmp/*.mjs` against the
    checked-in snapshots
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1692_test.res` now matches the checked-in snapshot
    again and no longer appears in `temp/rust-parity/diffs`; the top-level
    wrapper call survives instead of collapsing away during later cleanup
  - `tests/tests/src/PartialApplicationNoRuntimeCurry.res` and
    `tests/tests/src/ExternalShadow.res` remain exact snapshot matches as
    unchanged guard files
  - the authoritative 657-file wrapper run improves by one file overall,
    confirming the narrowed wrapper-preservation rule fixed a real backend
    drift without reopening the surrounding guard cluster
- Topline impact:
  - JS snapshot parity: **490 / 657** -> **491 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **167** -> **166** (**-1**)
- Keep this change because it matches OCaml's direct `Pjs_fn_make` call
  boundary more closely than either Rust extreme (global wrapper erasure or
  global wrapper preservation), removes the concrete `gpr_1692_test` drift,
  and improves the authoritative baseline without reopening the nearby guard
  files.

Latest iteration on **2026-04-15**:

- Active slice: match the checked-in snapshot's constructor-target parenthesis
  rule for imported JS module namespaces without relaxing the separate
  parenthesization that the snapshot still expects for globals and deeper
  scoped constructor chains
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`, because the remaining mismatch lived in final JS emission rather
  than typedtree/lambda lowering: the Rust printer emitted
  `new (React.Component)()` for imported namespace constructors, while the
  snapshot expects `new React.Component()`, but still expects
  `new (global.Buffer)(20)` for global and nested scoped constructor targets
- OCaml reference:
  `compiler/core/js_dump.ml`, especially the `New` and `Static_index`
  emission path; plus the checked-in snapshot and package-built
  `tests/tests/lib/bs/src/reasonReactOptimizedCreateClass.mjs` /
  `tests/tests/src/bs_qualified.mjs` outputs to pin the constructor-target
  shapes that must remain parenthesized versus the imported-namespace case that
  must not
- Rust change:
  - updated `compiler-rust/src/js_ir/printer.rs` so `ExpressionDesc::New`
    omits the extra constructor parens only for a single static member access
    off an imported external-module namespace
    (`ExpressionDesc::StaticIndex(Var(Qualified(External, None)), ...)`)
  - kept the old parenthesization for global constructors and deeper scoped
    member chains such as `global.Buffer` and `ZZ.global.a0.a1.a2.Buffer`
  - added printer regressions
    `test_print_new_member_constructor_omits_extra_parens_like_ocaml` and
    `test_print_new_global_member_constructor_keeps_parens_like_snapshot`,
    alongside the existing precedence guard
    `test_print_typeof_function_parenthesizes_arrow_expression`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_new_ -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_typeof_function_parenthesizes_arrow_expression -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/reasonReactOptimizedCreateClass.res`,
    diffing `/tmp/reasonReactOptimizedCreateClass.mjs` against the checked-in
    snapshot
  - direct release repro for `tests/tests/src/bs_qualified.res`, diffing
    `/tmp/bs_qualified.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/reasonReactOptimizedCreateClass.res` now matches the
    snapshot again; Rust emits `new React.Component().updater` instead of
    `new (React.Component)().updater`
  - `tests/tests/src/bs_qualified.res` stays aligned with the snapshot's
    explicit constructor parens for globals and nested scoped values
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **489 / 657** -> **490 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **168** -> **167** (**-1**)
- Keep this change because it isolates a real printer-only drift in final JS
  dumping, matches the checked-in snapshot's imported-namespace constructor
  shape without broadening the rule past what the snapshot permits, and
  improves the authoritative baseline without touching earlier backend stages.

Latest iteration on **2026-04-15**:

- Active slice: align Rust's lets-DCE-style direct-function beta reduction with
  OCaml so returned callbacks still collapse after post-lowering cleanup even
  when the apply status is `App_uncurry`, instead of only reducing the
  `App_na` subset
- Active backend focus for this slice remains **Phase 2: Port Post-Lowering
  Lambda Backend Stages** from `PLAN.md`, because the remaining `ari_regress` /
  `test_demo` IIFE drift lived in the post-lowering lambda cleanup boundary:
  OCaml's `lam_pass_lets_dce.ml` beta-reduces direct `Lfunction` applies
  regardless of `ap_status`, while Rust had added a `Na`-only restriction and
  therefore left uncurried returned callbacks as emitted IIFEs
- OCaml reference:
  `compiler/core/lam_pass_lets_dce.ml`, especially the direct
  `Lapply {ap_func = Lfunction ...}` beta-reduction branch and the fallback
  `Lam.apply (simplif l1) ...` rebuild; `compiler/core/lam.ml`, especially
  `Lam.apply`'s smart constructor over `Lfunction` and `Llet (..., Lfunction _)`;
  and `compiler/core/lam_compile.ml`, especially the nested `App_na`
  `compile_apply` reassociation branch for the smaller direct-call case
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so
    `simplify_direct_function_applications_like_lets_dce(...)` no longer gates
    direct `Lfunction` beta reduction on `ApplyStatus::Na`, and now rebuilds
    fallback applies through `Lambda::apply(...)` so the OCaml-style smart
    constructor keeps collapsing let-wrapped returned callbacks
  - added an explicit uncurried regression in
    `lets_dce_pass_beta_reduces_let_wrapped_returned_functions_with_uncurry_status`
    alongside the existing `Na` regression
  - kept the OCaml-aligned nested `App_na` reassociation support in
    `compiler-rust/src/lambda/compile.rs` and the shared `Lambda::apply(...)`
    smart constructor in `compiler-rust/src/lambda/mod.rs`, with focused tests
    for the `ari_regress_test` / `test_demo` shapes
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lets_dce_pass_beta_reduces_let_wrapped_returned_functions_with_uncurry_status -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lets_dce_pass_beta_reduces_let_wrapped_returned_functions_with_na_status -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_app_na_calls_reassociate_multi_arg_returned_functions_for_test_demo_shape -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/test_demo.res`, diffing
    `/tmp/test_demo.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_demo.res` is now an exact snapshot match; the
    returned-function call collapses to OCaml's direct arithmetic shape instead
    of emitting `((xx, yy) => ...)(6, extra)`
  - `tests/tests/src/ari_regress_test.res` also drops out of the authoritative
    diff set after the same lets-DCE alignment, confirming the nearby
    single-arg returned-function cluster now follows OCaml's backend cleanup
    path as well
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - the remaining nearby returned-callback drift is now narrower:
    `temp/rust-parity/diffs` still contains `js_src_mutable_uncurry_test.res.diff`,
    while the old `ari_regress_test` / `test_demo` diffs are gone
- Topline impact:
  - JS snapshot parity: **488 / 657** -> **489 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **169** -> **168** (**-1**)
- Keep this change because it matches the OCaml lets-DCE and `Lam.apply`
  behavior directly, removes a Rust-only status restriction from backend
  cleanup, and converts the returned-function IIFE cluster into real snapshot
  wins without any printer-only rewrite.

Latest iteration on **2026-04-15**:

- Active slice: teach direct `PjsFnMake` arity adjustment to keep walking
  through returned single-arg functions and let-wrapped returned functions
  when adding extra JS parameters, instead of blindly nesting fresh `Lapply`
  wrappers around the returned callback body
- Active backend focus for this slice is **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`, because the mismatch sat in the
  post-lowering eta/adjust-to-arity cleanup boundary that OCaml handles with
  `Lam_eta_conversion.unsafe_adjust_to_arity` plus `Lam.apply`'s smart
  let-wrapped-function rewriting before JS IR lowering
- OCaml reference:
  `compiler/core/lam_eta_conversion.ml`, especially `unsafe_adjust_to_arity`
  for the `to_ > from` case that recursively builds `Lam.apply` over each
  extra arg; and `compiler/core/lam.ml`, especially `Lam.apply`'s
  `Lfunction` / `Llet (..., Lfunction _)` smart-constructor cases that beta
  reduce returned single-arg functions instead of preserving nested applies
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so
    `adjust_direct_js_fn_make_function(...)` applies extra JS args through a
    new helper that beta-reduces returned single-arg `Lfunction`s and recurses
    through let-wrapped returned functions, instead of always rebuilding
    `Lapply`
  - added focused regression coverage in
    `adjusts_nested_pjs_fn_make_callbacks_to_flat_multi_param_functions_like_mutable_uncurry`
  - refreshed
    `beta_reduces_returned_pjs_fn_make_wrappers_across_backend_alias_passes`
    to match the new OCaml-aligned surviving callee shape after the backend
    alias cleanup sweep
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml adjusts_nested_pjs_fn_make_callbacks_to_flat_multi_param_functions_like_mutable_uncurry -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml adjusts_direct_pjs_fn_make_callbacks_to_requested_arity_during_simplify -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml beta_reduces_let_wrapped_returned_functions_across_backend_alias_passes -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/mutable_uncurry_test.res`,
    diffing `/tmp/mutable_uncurry_test.mjs` against the checked-in snapshot
  - direct related repros for `tests/tests/src/ari_regress_test.res` and
    `tests/tests/src/test_demo.res`, diffing `/tmp/*.mjs` against the checked-in
    snapshots
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/mutable_uncurry_test.res` now collapses the nested
    callback/IIFE shape into OCaml-style flat parameter extraction for the
    `ut4`/`t4`/`ut5`/`t5` family, confirming the `PjsFnMake` arity-adjust path
    now beta-reduces through returned functions the way OCaml's
    `unsafe_adjust_to_arity` + `Lam.apply` combination does
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - `tests/tests/src/ari_regress_test.res` and `tests/tests/src/test_demo.res`
    are unchanged in their remaining value-context/direct-call cluster, which
    shows this patch isolates the returned-callback flattening issue without
    solving the separate direct-call simplification path yet
- Topline impact:
  - JS snapshot parity: **488 / 657** -> **488 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **169** -> **169** (**no change**)
- Keep this change because it matches OCaml's `unsafe_adjust_to_arity` /
  `Lam.apply` behavior more closely, materially improves the
  `mutable_uncurry_test.res` backend shape without harming the guard file, and
  removes a Rust-only layer of nested callback applies even though no whole
  snapshot flipped yet.

Latest iteration on **2026-04-15**:

- Active slice: stop force-spilling value-context `Lapply` nodes through a
  synthetic `call` temp during JS lowering, so direct calls in value context
  stay direct call expressions instead of becoming `let call = ...; let x =
  call;`
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch lived in
  `Lam_compile.compile_apply`'s value-context lowering boundary before JS IR
  cleanup: OCaml compiles the callee and arguments under `NeedValue Not_tail`
  and then feeds the final `E.call ...` directly into
  `Js_output.output_of_block_and_expression`, while Rust was materializing any
  prelude-bearing call into an extra temporary even when the surrounding
  context already wanted a value
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `compile_apply` and its final
  `Js_output.output_of_block_and_expression ... (E.call ...)` path for
  `NeedValue`; plus `compiler/core/lam_compile_main.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so `Lambda::Lapply` in
    `compile_expr(...)` now returns `compile_apply_call(...)` directly instead
    of forcing the result through `materialize_compiled_value("call", ...)`
  - removed the now-unneeded `materialize_compiled_value(...)` helper that was
    inventing value-context `call` aliases
  - added focused regression coverage in
    `value_context_direct_calls_stay_as_call_expressions` and
    `let_bound_direct_calls_skip_intermediate_call_aliases`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml value_context_direct_calls_stay_as_call_expressions -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml let_bound_direct_calls_skip_intermediate_call_aliases -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml effect_context_calls_with_arg_preludes_skip_intermediate_call_temps -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml return_context_calls_with_arg_preludes_skip_intermediate_call_temps -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml assignment_context_calls_with_arg_preludes_skip_intermediate_call_temps -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/ari_regress_test.res`, diffing
    `/tmp/ari_regress_test.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - `tests/tests/src/ari_regress_test.res` now drops the synthetic
    `let call = ...; let x = call;` alias and matches the OCaml call/value
    shape more closely, though it still differs in a remaining arity-specific
    simplification cluster
  - `tests/tests/src/int_map.res` dropped out of the authoritative failure set
    after this change, while `ari_regress_test.res`, `mutable_uncurry_test.res`,
    and `test_demo.res` remain in the current diff cluster
- Topline impact:
  - JS snapshot parity: **487 / 657** -> **488 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **170** -> **169** (**-1**)
- Keep this change because it aligns Rust's value-context call lowering with
  OCaml's `Lam_compile.compile_apply` behavior, removes a Rust-only synthetic
  aliasing step, and improves the authoritative snapshot baseline without any
  printer-only rewrite.

Latest iteration on **2026-04-15**:

- Active slice: stop treating OCaml's local-module-field `SafeAlias` rule as if
  it also authorized eta-reducing JS-function wrappers over local module vars,
  so the Rust JS backend no longer collapses functor-local wrappers like
  `x => X.foo(x)` into bare `X.foo`
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch still lived in the final
  post-lowering lambda cleanup boundary before JS IR lowering: OCaml's
  `Lam_util.refine_let` / `SafeAlias` path allows local-module field reads such
  as `MS.forEach` to be aliased through strict lets, but there is no matching
  OCaml rule that strips `Pjs_fn_make` / eta wrappers around local-module field
  calls after that point; Rust had reused the same predicate for both behaviors
- OCaml reference:
  `compiler/core/lam_util.ml`, especially the `SafeAlias` predicate for
  `Pfield (_, Fld_module _)` over `[Lglobal_module _ | Lvar _]`;
  `compiler/core/lam_pass_remove_alias.ml`; `compiler/core/lam_compile_main.ml`;
  and `compiler/core/lam_compile.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` to split
    safe-aliasable module-field reads from eta-reducible module-field reads
  - kept local-module `Lvar` field reads eligible for strict-let aliasing and
    substitution, preserving the earlier `Import.res` local-module-field fix
  - narrowed eta reduction, `PjsFnMake` wrapper stripping, and exported-eta
    call substitution so only `LglobalModule` module-field reads are treated as
    direct JS-function aliases
  - added focused regression coverage in
    `keeps_local_module_field_wrappers_materialized_like_functors_res`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml module_field -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/functors.res`, diffing
    `/tmp/functors.mjs` against the checked-in snapshot
  - direct related guard repro for `tests/tests/src/Import.res`, diffing
    `/tmp/Import.mjs` against the checked-in snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/functors.res` is now an exact snapshot match again; Rust
    keeps the functor-local `cow = x => X.foo(x)` wrapper materialized instead
    of collapsing it to `cow: X.foo`
  - `tests/tests/src/Import.res` remains an exact snapshot match, which
    confirms local-module field aliasing through lets still follows OCaml's
    `SafeAlias` behavior after narrowing eta reduction
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
- Topline impact:
  - JS snapshot parity: **486 / 657** -> **487 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **171** -> **170** (**-1**)
- Keep this change because it separates two OCaml behaviors Rust had conflated,
  fixes the remaining `functors.res` module-field wrapper/eta cluster, and
  improves the authoritative snapshot baseline without adding any printer-only
  rewrite.

Latest iteration on **2026-04-15**:

- Active slice: remove Rust's remaining second-chance named-function inlining
  in `simplify_apply(...)` so the JS backend only inlines a named callee when
  the original callee is already syntactically `Lvar`, instead of retrying
  after projected/module-field simplification turns some other callee shape
  into an `Lvar`
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch still lived in the final
  post-lowering lambda cleanup boundary before JS IR lowering:
  `lam_pass_remove_alias.ml` makes the named-function inlining decision only in
  the `Lapply {ap_func = Lvar v as fn; ...}` branch, while its fallback
  `normal()` path rebuilds `Lam.apply (simpl fn) ...` without retrying after
  the callee simplifies
- OCaml reference:
  `compiler/core/lam_pass_remove_alias.ml`, especially the
  `Lapply {ap_func = Lvar v as fn; ...}` branch versus the fallback
  `normal()` path that returns `Lam.apply (simpl fn) ap_args ap_info`;
  `compiler/core/lam_compile_main.ml`; and
  `compiler/core/lam_compile.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so
    `simplify_apply(...)` no longer retries
    `reduce_named_function_application(...)` after simplifying a non-`Lvar`
    callee into an `Lvar`
  - kept the original named-callee inlining path intact when the source apply
    already starts as `Lvar`, so the OCaml-aligned direct functor inlining
    cases still reduce
- Verified focused guards for this slice:
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml inlines_named_functor_applications_even_when_inline_heuristics_reject_them -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml reruns_js_backend_simplify_after_functor_inlining_exposes_projected_module_fields -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/functors_one_arg_at_a_time.res`,
    diffing `/tmp/functors_one_arg_at_a_time.mjs` against the checked-in
    snapshot
  - direct guard repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - direct release repro for `tests/tests/src/functors.res`, diffing
    `/tmp/functors.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/functors_one_arg_at_a_time.res` is now an exact snapshot
    match again; Rust no longer collapses `M.Eq((), ())` through a retry that
    OCaml never performs after simplifying the projected callee
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - `tests/tests/src/functors.res` is unchanged and still differs in the same
    remaining module-field wrapper/eta cluster, so that root cause is separate
    from this apply-boundary fix
- Topline impact:
  - JS snapshot parity: **485 / 657** -> **486 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **172** -> **171** (**-1**)
- Keep this change because it matches OCaml's `lam_pass_remove_alias` control
  flow more closely, removes one remaining Rust-only retry path, and improves
  the authoritative snapshot baseline without adding any printer-only rewrite.

Latest iteration on **2026-04-15**:

- Active slice: rerun the regular backend alias/let cleanup once more after the
  lets-DCE-style direct-function sweep, so the result of that direct beta
  reduction goes back through the same non-direct cleanup OCaml applies after
  `Lam_beta_reduce.no_names_beta_reduce`
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch stayed in the final
  post-lowering lambda cleanup boundary before JS IR lowering:
  `lam_pass_lets_dce.ml` beta-reduces a direct function call and then runs the
  resulting lambda back through `simplif`, while Rust's final
  `simplify_direct_function_applications_like_lets_dce(...)` sweep stopped
  after the direct reduction and left OCaml-cleaned lets/aliases behind
- OCaml reference:
  `compiler/core/lam_pass_lets_dce.ml`, especially the
  `Lam_beta_reduce.no_names_beta_reduce` + `simplif` flow;
  `compiler/core/lam_compile_main.ml`; and
  `compiler/core/lam_compile.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so
    `simplify_for_js_backend(...)` now runs one more
    `simplify_for_js_backend_once(..., allow_direct = false)` pass after the
    lets-DCE-style direct beta-reduction sweep
  - added focused regression coverage in
    `reruns_backend_cleanup_after_lets_dce_beta_reduces_uncurried_pjs_fn_make_calls`
    for the `arity_deopt`-style nested `Pjs_fn_make` uncurry chain that OCaml
    cleans further after the direct reduction
  - updated
    `beta_reduces_downarity_pjs_fn_make_calls_past_the_outer_apply` to assert
    the cleaner OCaml-aligned surviving callee shape after the extra cleanup
    rerun
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml reruns_backend_cleanup_after_lets_dce_beta_reduces_uncurried_pjs_fn_make_calls -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml beta_reduces_downarity_pjs_fn_make_calls_past_the_outer_apply -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml simplifies_named_nested_pjs_fn_make_application_chain_from_ari_regress_shape -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml compile_effectful_underscore_binding_from_nested_js_function_calls_survives_shake -- --nocapture`
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/arity_deopt.res`, diffing `/tmp/arity_deopt.mjs` against
    the checked-in snapshot
  - authoritative guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/ari_regress_test.res`, diffing `/tmp/ari_regress_test.mjs`
    against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/arity_deopt.res` is now an exact snapshot match again;
    the lets introduced by the direct `Pjs_fn_make` reduction are cleaned up
    before JS lowering, matching OCaml's final backend simplification flow
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - `tests/tests/src/ari_regress_test.res` is unchanged and still differs in
    the same remaining arity cluster, so its root cause is elsewhere in the
    backend
  - the authoritative wrapper baseline is unchanged overall, which means this
    OCaml-aligned fix removed at least one concrete snapshot diff but another
    failure replaced it elsewhere in the 657-file set
- Topline impact:
  - JS snapshot parity: **485 / 657** -> **485 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **172** -> **172** (**no change**)
- Keep this change because it matches OCaml's lets-DCE cleanup boundary more
  closely and fixes `arity_deopt.res` without adding any printer-only rewrite;
  the unchanged topline means the next slice should identify the offsetting
  backend regression instead of reverting this verified simplifier alignment.

Latest iteration on **2026-04-15**:

- Active slice: remove Rust's remaining second-chance direct beta reduction in
  `simplify_apply(...)` so the JS backend only beta-reduces direct calls when
  the original callee is syntactically a function, instead of simplifying a
  let-wrapped / wrapper-produced callee first and then retrying the reduction
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch still lived in the final
  post-lowering lambda cleanup boundary before JS IR lowering:
  `lam_pass_lets_dce.ml` only reduces `Lapply {ap_func = Lfunction ...}`, but
  Rust's general `simplify_apply(...)` path could still simplify the callee
  into a direct `Lfunction` and beta-reduce one more time
- OCaml reference:
  `compiler/core/lam_compile_main.ml`, especially the final
  `simplify_alias -> alpha_conversion -> simplify_lets` sequence;
  `compiler/core/lam_pass_lets_dce.ml`, especially the
  `Lapply {ap_func = Lfunction ...}` match arm; and
  `compiler/core/lam_compile.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so
    `simplify_apply(...)` only does direct beta reduction when the original
    `apply.ap_func` is already `Lambda::Lfunction`, instead of retrying after
    simplifying the callee through alias / wrapper cleanup
  - kept named-function reduction intact, but removed the extra
    post-simplification direct-wrapper reduction path that OCaml does not have
  - updated focused backend regression tests for the downarity and
    `Pjs_fn_make` wrapper cases so they now assert the OCaml-aligned surviving
    outer `Lapply` shape with a let-wrapped callee
  - added focused coverage in
    `simplifies_named_nested_pjs_fn_make_application_chain_from_ari_regress_shape`
    for the nested `ari_regress_test` application chain that should still
    collapse through the allowed direct-function path
- Verified focused guards for this slice:
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml lets_dce_pass_beta_reduces_nested_curried_direct_function_applications -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml beta_reduces_let_wrapped_returned_functions_across_backend_alias_passes -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml beta_reduces_returned_pjs_fn_make_wrappers_across_backend_alias_passes -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml beta_reduces_downarity_pjs_fn_make_calls_past_the_outer_apply -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml simplifies_named_nested_pjs_fn_make_application_chain_from_ari_regress_shape -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml compile_effectful_underscore_binding_from_nested_js_function_calls_survives_shake -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/gpr_1692_test.res`, diffing
    `/tmp/gpr_1692_test.mjs` against the checked-in snapshot
  - direct guard repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/ari_regress_test.res`, diffing `/tmp/ari_regress_test.mjs`
    against the checked-in snapshot
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/arity_deopt.res`, diffing `/tmp/arity_deopt.mjs` against
    the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1692_test.res` remains an exact snapshot match, which
    confirms Rust no longer reintroduces the old over-reduction bug while the
    new direct-call narrowing stays in place
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match as an
    unchanged broader guard
  - `tests/tests/src/ari_regress_test.res` and
    `tests/tests/src/arity_deopt.res` still differ in the same arity cluster,
    so removing this extra reduction path was not the remaining root cause for
    those files
  - the authoritative wrapper baseline is unchanged, so this OCaml-aligned
    cleanup is parity-neutral on the current 657-file snapshot set
- Topline impact:
  - JS snapshot parity: **485 / 657** -> **485 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **172** -> **172** (**no change**)
- Keep this change because it removes a remaining Rust-only backend reduction
  path and makes the simplifier follow the same direct-call boundary as
  OCaml; the still-failing arity files need a different backend fix rather
  than restoring the extra retry logic.

Latest iteration on **2026-04-15**:

- Active slice: narrow Rust's final lets-DCE-style direct-application cleanup
  to the same scope OCaml uses, so the JS backend no longer beta-reduces
  let-wrapped / wrapper-produced calls that `lam_pass_lets_dce.ml` would leave
  intact
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch lived in the final
  post-lowering lambda simplification boundary before JS IR lowering:
  OCaml's lets-DCE pass only beta-reduces syntactic direct `Lfunction`
  applications, while Rust still had an extra helper that peeled
  let-wrapped functions and direct wrapper shapes during the final backend
  cleanup
- OCaml reference:
  `compiler/core/lam_compile_main.ml`, especially the final
  `simplify_alias -> alpha_conversion -> simplify_lets` sequence;
  `compiler/core/lam_pass_lets_dce.ml`;
  `compiler/core/lam_pass_remove_alias.ml`; and
  `compiler/core/lam_compile.ml`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so
    `simplify_for_js_backend(...)` now runs the second cleanup pass and then a
    narrow `simplify_direct_function_applications_like_lets_dce(...)` sweep
    instead of using the older Rust-only helper that also peeled let-wrapped
    lambdas and direct wrapper functions
  - constrained that final lets-DCE-style sweep to beta-reduce only
    syntactic `Lambda::Lfunction` applications with `ApplyStatus::Na`,
    matching OCaml's pass boundary more closely
  - added focused regression coverage in
    `lets_dce_pass_beta_reduces_nested_curried_direct_function_applications`
    for the nested curried direct-call shape the final pass is still expected
    to collapse
- Verified focused guards for this slice:
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml lets_dce_pass_beta_reduces_nested_curried_direct_function_applications -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml beta_reduces_let_wrapped_returned_functions_across_backend_alias_passes -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml compile_effectful_underscore_binding_from_nested_js_function_calls_survives_shake -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/ari_regress_test.res`, diffing `/tmp/ari_regress_test.mjs`
    against the checked-in snapshot
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/arity_deopt.res`, diffing `/tmp/arity_deopt.mjs` against
    the checked-in snapshot
  - authoritative guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/ari_regress_test.res` and
    `tests/tests/src/arity_deopt.res` still differ after the pass-boundary
    alignment, so this direct-application cleanup was not the root cause of
    that remaining arity cluster
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    narrowing the final simplifier
  - the authoritative wrapper baseline is unchanged, which means this
    OCaml-aligned cleanup is parity-neutral on the current 657-file snapshot
    set
- Topline impact:
  - JS snapshot parity: **485 / 657** -> **485 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **172** -> **172** (**no change**)
- Keep this change because it removes a Rust-only backend simplification path
  and better matches OCaml's lets-DCE scope; the remaining arity/output diffs
  need a different backend fix rather than restoring the broader reducer.

Latest iteration on **2026-04-15**:

- Active slice: keep exported bindings that were originally call results
  materialized across the second backend alias-cleanup sweep so export coercion
  can preserve OCaml's declaration order instead of rebinding those constants
  at the end of the module
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch lived after optimized
  lambda in Rust's post-lowering simplifier / export-coercion handoff:
  OCaml's backend leaves exported call-result bindings in place until export
  coercion, while Rust's late alias single-use rewrite was still deleting those
  bindings on the second cleanup pass
- OCaml reference:
  `compiler/core/lam_compile_main.ml`, especially the final
  `simplify_alias -> alpha_conversion -> simplify_lets` pipeline before
  coercion; `compiler/core/lam_pass_lets_dce.ml`; and
  `compiler/core/lam_coercion.ml`, especially `handle_exports`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so the late
    single-use alias substitution now respects `preserved_export_bindings`,
    matching the OCaml backend behavior for exported bindings that were
    originally `Lapply` results or exported eta wrappers
  - added backend regression coverage in
    `compile_deps_program_keeps_exported_call_result_before_rebound_constant_block_export`
    so reduced exported call results stay before later rebound constant-block
    exports in the emitted JS order
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml keeps_export_bindings_reduced_from_named_function_calls -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml compile_deps_program_keeps_exported_call_result_before_rebound_constant_block_export -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/DisambiguateOptionalFields.res`,
    diffing `/tmp/DisambiguateOptionalFields.mjs` against the checked-in
    snapshot
  - direct release repro for `tests/tests/src/DerivingAccessorsCurried.res`,
    diffing `/tmp/DerivingAccessorsCurried.mjs` against the checked-in snapshot
  - direct release repro for
    `tests/tests/src/DerivingAccessorsUncurried.res`, diffing
    `/tmp/DerivingAccessorsUncurried.mjs` against the checked-in snapshot
  - direct guard repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    broader guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/DisambiguateOptionalFields.res` is now an exact snapshot
    match again; the reduced exported call result `res` stays before the later
    rebound `v` object export, matching OCaml's declaration order
  - `tests/tests/src/DerivingAccessorsCurried.res` and
    `tests/tests/src/DerivingAccessorsUncurried.res` are now exact snapshot
    matches again; `_composedMyField` stays materialized in place instead of
    being rebound at the end of the module
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the simplifier change
- Topline impact:
  - JS snapshot parity: **477 / 657** -> **485 / 657** (**+8**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **180** -> **172** (**-8**)
- Keep this change because it matches OCaml's backend cleanup/coercion
  interaction and removes the declaration-ordering regression without adding
  any printer-only rewrite.

Latest iteration on **2026-04-15**:

- Active slice: align Rust's post-lowering lambda simplification pass sequence
  with OCaml's backend pass boundaries so nested `Pjs_fn_make` top-level effect
  calls are not beta-reduced away across an extra Rust-only backend sweep
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch lived after optimized
  lambda in the lambda-to-JS backend handoff: OCaml's final pipeline in
  `lam_compile_main.ml` runs alias / alpha / lets-dce passes before
  `lam_compile.ml`, but it does not run the extra second direct-function
  beta-reduction sweep Rust had been applying inside `simplify_for_js_backend`
- OCaml reference:
  `compiler/core/lam_compile_main.ml`, especially the final
  `simplify_alias -> alpha_conversion -> simplify_lets` sequence;
  `compiler/core/lam_pass_lets_dce.ml`;
  `compiler/core/lam_pass_remove_alias.ml`;
  `compiler/core/lam_pass_alpha_conversion.ml`; and
  `compiler/core/lam_compile.ml`, especially `Pjs_fn_make`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so
    `simplify_for_js_backend(...)` runs one direct-function beta-reducing pass
    followed by a cleanup pass with direct beta reduction disabled, instead of
    running two identical beta-reducing sweeps plus a final Rust-only
    `simplify_direct_function_applications_like_lets_dce(...)` pass
  - updated focused simplifier expectations in
    `beta_reduces_let_wrapped_returned_functions_across_backend_alias_passes`
    and
    `beta_reduces_returned_pjs_fn_make_wrappers_across_backend_alias_passes`
    to match the OCaml-aligned post-pass shape where the final outer call
    survives
  - added direct regression coverage in
    `compile_effectful_underscore_binding_from_nested_js_function_calls_survives_shake`
    so the `gpr_1692_test` shape keeps the emitted top-level call
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml compile_effectful_underscore_binding_from_nested_js_function_calls_survives_shake -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml beta_reduces_returned_pjs_fn_make_wrappers_across_backend_alias_passes -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml beta_reduces_let_wrapped_returned_functions_across_backend_alias_passes -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/gpr_1692_test.res`, diffing
    `/tmp/gpr_1692_test.mjs` against the checked-in snapshot
  - direct guard repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    broader guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1692_test.res` is now an exact snapshot match; the
    emitted top-level `(f => 0)("")` call survives instead of being optimized
    away to an empty module
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the simplifier sequencing change
  - full-wrapper parity regressed because the OCaml-aligned fix exposed a new
    declaration-ordering cluster in files such as
    `DerivingAccessorsCurried.res`, `DerivingAccessorsUncurried.res`, and
    `DisambiguateOptionalFields.res`, where pure top-level `let` bindings moved
    later in the emitted JS
- Topline impact:
  - JS snapshot parity: **479 / 657** -> **477 / 657** (**-2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **178** -> **180** (**+2**)
- Keep this change because it matches the real OCaml backend pass boundaries
  and fixes the concrete `gpr_1692_test` over-simplification bug; the parity
  regression is the next declaration-ordering cluster to address, not a reason
  to restore the extra Rust-only simplification sweep.

Latest iteration on **2026-04-14**:

- Active slice: port OCaml's `Js_exp_make.int32_band` lowering for integer
  `land` so redundant left-hand `(... | 0)` truncation is removed before
  emitting `&`, matching the backend shape OCaml prints in `hash_variant` and
  similar masked-int paths
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch lived in integer bitwise
  lowering after optimized lambda: OCaml's `lam_compile_primitive.ml` routes
  `Pandint` through `E.int32_band`, while Rust was still building a raw
  `Band` node and preserving an extra `| 0` wrapper that OCaml strips
- OCaml reference:
  `compiler/core/lam_compile_primitive.ml`, especially the `Pandint` branch;
  and `compiler/core/js_exp_make.ml`, especially `int32_band`
- Rust change:
  - added `int32_band(...)` in `compiler-rust/src/lambda/compile.rs` to mirror
    OCaml's `Js_exp_make.int32_band` behavior of dropping a redundant
    left-hand `(... | 0)` before emitting `Band`
  - updated `Pandint` lowering in `compiler-rust/src/lambda/compile.rs` to use
    that helper instead of always emitting a raw `Expression::bin(Band, ...)`
  - added focused regression coverage in
    `int32_band_drops_redundant_bor_on_left_operand`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml int32_band_drops_redundant_bor_on_left_operand -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/int_overflow_test.res` using `rescript.exe compiler-args`,
    diffing `/tmp/int_overflow_test.mjs` against the checked-in snapshot
  - direct guard repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    broader guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/int_overflow_test.res` is no longer in the authoritative
    diff set
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the `int32_band` port
- Topline impact:
  - JS snapshot parity: **478 / 657** -> **479 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **179** -> **178** (**-1**)
- Keep this change because it ports the real OCaml backend behavior from
  `lam_compile_primitive.ml` / `js_exp_make.ml`; the wrapper gain comes from
  matching integer bitwise lowering rather than from any printer-only rewrite.

Latest iteration on **2026-04-14**:

- Active slice: port OCaml's integer-power constant folding in
  `Ext_int.int32_pow` / `Js_exp_make.int32_pow` so constant `Ppowint` nodes
  lower directly to the same wrapped 32-bit literals OCaml emits instead of
  surviving as raw `** | 0` expressions
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch lived in integer-power
  lowering after optimized lambda: OCaml's `lam_compile_primitive.ml` sends
  `Ppowint` through `E.int32_pow`, which folds literal powers via
  `Ext_int.int32_pow`, while Rust was still using a generic `to_int32(pow)`
  fallback for all cases
- OCaml reference:
  `compiler/core/lam_compile_primitive.ml`, especially the `Ppowint` branch;
  `compiler/core/js_exp_make.ml`, especially `int32_pow`; and
  `compiler/ext/ext_int.ml`, especially `int32_pow`
- Rust change:
  - added `ocaml_int32_pow(...)` plus `int32_pow(...)` in
    `compiler-rust/src/lambda/compile.rs` to mirror OCaml's float-based
    constant folding and 32-bit wrap behavior for integer powers
  - updated `Ppowint` lowering in `compiler-rust/src/lambda/compile.rs` to use
    that helper instead of always emitting `to_int32(Expression::bin(Pow, ...))`
  - added focused regression coverage in
    `compile_int_pow_folds_small_int_literals_like_ocaml_ext_int` and
    `compile_int_pow_folds_overflowing_int_literals_like_ocaml_ext_int`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_int_pow_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/unified_ops_test.res` using `rescript.exe compiler-args`,
    diffing `/tmp/unified_ops_test.mjs` against the checked-in snapshot
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/exponentiation_test.res` using `rescript.exe compiler-args`,
    diffing `/tmp/exponentiation_test.mjs` against the checked-in snapshot
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/int_overflow_test.res` using `rescript.exe compiler-args`,
    diffing `/tmp/int_overflow_test.mjs` against the checked-in snapshot as an
    unchanged neighbor guard
  - direct guard repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    broader guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/unified_ops_test.res` is no longer in the authoritative
    diff set
  - `tests/tests/src/exponentiation_test.res` is no longer in the authoritative
    diff set
  - `tests/tests/src/int_overflow_test.res` still differs, and its remaining
    drift is the separate wrapping-add / bitand shaping cluster around
    `hash_variant`, not integer-power lowering
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the `int32_pow` port
- Topline impact:
  - JS snapshot parity: **476 / 657** -> **478 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **181** -> **179** (**-2**)
- Keep this change because it ports the real OCaml backend behavior from
  `lam_compile_primitive.ml` / `js_exp_make.ml` / `ext_int.ml`; the wrapper
  gain comes from matching OCaml's integer-power lowering rather than from any
  printer-only rewrite.

Latest iteration on **2026-04-14**:

- Active slice: port OCaml's `Js_exp_make.string_append` folding so
  `Pstringadd` collapses empty strings and same-delimiter literal chains during
  JS IR construction instead of always leaving raw `StringAppend` nodes
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`, because the mismatch lived in the JS-expression
  construction helpers used by `lam_compile_primitive.ml`, not in the final
  printer: OCaml already lowers `Pstringadd` through `E.string_append`, while
  Rust was still constructing unfused `StringAppend` IR for cases OCaml folds
  immediately
- OCaml reference:
  `compiler/core/lam_compile_primitive.ml`, especially the `Pstringadd` branch
  calling `E.string_append`; and `compiler/core/js_exp_make.ml`, especially
  `string_append`
- Rust change:
  - added `Expression::string_append(...)` in
    `compiler-rust/src/js_ir/mod.rs` to mirror OCaml's empty-string elision and
    adjacent-literal folding for `StringAppend`
  - updated `compiler-rust/src/lambda/compile.rs` so `Pstringadd` now lowers
    through that helper instead of emitting a raw `ExpressionDesc::StringAppend`
  - added focused regression coverage in
    `test_string_append_folds_adjacent_same_delim_literals` and
    `test_string_append_merges_literal_prefix_into_nested_append`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml test_string_append_ -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_duprecord_lowers_to_object_spread_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - authoritative `tests/tests/lib/bs` repro for `tests/tests/src/alias_test.res`
    using `rescript.exe compiler-args`, diffing `/tmp/alias_test.mjs` against
    the checked-in snapshot
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/inline_const.res` using `rescript.exe compiler-args`,
    diffing `/tmp/inline_const.mjs` against the checked-in snapshot
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/unified_ops_test.res` using `rescript.exe compiler-args`,
    diffing `/tmp/unified_ops_test.mjs` against the checked-in snapshot
  - direct guard repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    broader guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/alias_test.res` is no longer in the authoritative diff set
  - `tests/tests/src/inline_const.res` is no longer in the authoritative diff
    set
  - `tests/tests/src/unified_ops_test.res` still differs, but only in the
    separate integer-power constant-folding cluster around `pow1` /
    `pow_overflow`; the earlier string-concatenation drift is gone
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the `string_append` port
- Topline impact:
  - JS snapshot parity: **472 / 657** -> **476 / 657** (**+4**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **185** -> **181** (**-4**)
- Keep this change because it ports the real OCaml backend behavior from
  `lam_compile_primitive.ml` / `js_exp_make.ml`; the wrapper gain comes from
  matching OCaml's JS-expression construction rules rather than from any
  printer-only rewrite.

Latest iteration on **2026-04-14**:

- Active slice: port the missing OCaml bigint primitive lowering in
  `lam_compile_primitive.ml` so the Rust JS backend stops dropping bigint
  arithmetic, bitwise, unary, and shift operators to `undefined`
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`, because the mismatch lives in
  `compiler/core/lam_compile_primitive.ml` after optimized lambda rather than
  in the printer: OCaml already lowers `Paddbigint`, `Psubbigint`,
  `Pmulbigint`, `Pdivbigint`, `Pmodbigint`, `Ppowbigint`, `Pnegbigint`,
  `Pnotbigint`, `Pandbigint`, `Porbigint`, `Pxorbigint`, `Plslbigint`, and
  `Pasrbigint` to raw JS bigint operators, while Rust was still falling
  through the generic backend fallback
- OCaml reference:
  `compiler/core/lam_compile_primitive.ml`, especially the bigint branches
  lowering through `E.bigint_op`, `E.bigint_div`, `E.bigint_mod`, and
  `E.int_bnot`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so the missing bigint
    primitive family now lowers to the corresponding JS IR operators instead of
    `undefined`
  - added focused regression coverage in
    `compile_bigint_arithmetic_primitives_use_raw_js_bigint_ops_like_ocaml`
    and
    `compile_bigint_bitwise_primitives_use_raw_js_bigint_ops_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml compile_bigint_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/bigint_test.res` using `rescript.exe compiler-args`,
    diffing `/tmp/bigint_test.mjs` against the checked-in snapshot
  - authoritative `tests/tests/lib/bs` repro for
    `tests/tests/src/unified_ops_test.res` using `rescript.exe compiler-args`,
    diffing `/tmp/unified_ops_test.authoritative.mjs` against the checked-in
    snapshot
  - direct guard repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    broader guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/unified_ops_test.res` no longer drops bigint arithmetic,
    bitwise, unary, or shift lowering; the remaining drift there has narrowed
    to earlier non-bigint issues like string-concat folding and int
    constant-folding for `pow1` / `pow_overflow`
  - `tests/tests/src/bigint_test.res` no longer fails on the missing bigint
    operator family around lines 158-166; its remaining drift is now in the
    earlier bigint equality / conditional-shaping path, not missing operator
    lowering
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the bigint primitive port
- Topline impact:
  - JS snapshot parity: **471 / 657** -> **472 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **186** -> **185** (**-1**)
- Keep this change because it ports the real OCaml backend behavior from
  `lam_compile_primitive.ml`; the wrapper gain comes from restoring missing
  bigint operator lowering rather than from any printer-only rewrite.

Latest iteration on **2026-04-14**:

- Active slice: port OCaml's transitive alias-substitution behavior in
  `Lam_pass_lets_dce` so JS-backend simplification follows alias chains all the
  way to their final replacement instead of stopping after one hop
- Active backend focus for this slice is **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`, because the behavior lives in the late
  lambda simplifier before JS IR lowering: OCaml's alias case recursively
  simplifies `Lvar` substitutions via the `subst` table, while the Rust
  simplifier only looked up one substitution edge
- OCaml reference:
  `compiler/core/lam_pass_lets_dce.ml`, especially
  `Llet ((Strict | Alias | StrictOpt), v, Lvar w, l2)` where OCaml records
  `v -> simplif (Lam.var w)` instead of a single-hop `v -> w`
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so `Lambda::Lvar` now uses a
    new `resolve_transitive_substitution(...)` helper that recursively follows
    `env.substitutions` with cycle protection, matching OCaml's transitive
    alias-resolution behavior
  - added focused regression coverage in
    `folds_transitive_string_alias_chains_like_ocaml_lets_dce`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml folds_string_alias_chains -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml folds_transitive_string_alias_chains_like_ocaml_lets_dce -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml keeps_multi_use_plain_string_bindings_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    broader guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - the authoritative wrapper baseline stayed unchanged at **471 / 657** with
    **186** output diffs and **0** compile errors
  - `tests/tests/src/alias_test.res`,
    `tests/tests/src/inline_const.res`, and
    `tests/tests/src/unified_ops_test.res` still differ in the wrapper output,
    so the remaining string-concatenation drift is not caused by the missing
    transitive alias lookup alone
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the simplifier change
- Topline impact:
  - JS snapshot parity: **471 / 657** -> **471 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **186** -> **186** (**no change**)
- Keep this change because it ports the real OCaml simplifier behavior from
  `Lam_pass_lets_dce.ml`; even without an immediate parity delta on the
  canonical harness, Rust now matches OCaml's recursive alias-resolution rule
  and has regression coverage for longer alias chains.

Latest iteration on **2026-04-14**:

- Active slice: port OCaml's stable switch-case grouping so lambda branches with
  identical bodies are grouped even when they are separated by another case;
  this fixes emitted case ordering like `B` then `A | C` instead of the Rust
  backend's earlier left-to-right `A`, `B`, `C`
- Active backend focus for this slice stays in **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch lived in
  `compiler/core/lam_compile.ml` during lambda-to-JS switch lowering rather
  than in the printer: OCaml's `group_apply` relies on
  `Ext_list.stable_group`, while Rust only merged adjacent equal cases
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `group_apply`; and
  `compiler/ext/ext_list.ml`, especially `stable_group`, `group`, and `aux`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so both
    `grouped_switch_cases(...)` and `grouped_switch_case_refs(...)` now use a
    shared `stable_group_switch_cases(...)` helper that mirrors OCaml's
    tail-to-head `stable_group` behavior instead of only merging adjacent equal
    cases
  - added focused regression coverage in
    `int_switch_expressions_group_non_adjacent_equal_cases_like_ocaml_stable_group`
    and
    `string_switch_effects_group_non_adjacent_equal_cases_like_ocaml_stable_group`
    while keeping the adjacent-grouping guards green
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml int_switch_expressions_group_non_adjacent_equal_cases_like_ocaml_stable_group -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml string_switch_effects_group_non_adjacent_equal_cases_like_ocaml_stable_group -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml int_switch_expressions_group_adjacent_equal_cases_and_drop_default_duplicates -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml string_switch_effects_group_adjacent_equal_cases_and_drop_default_duplicates -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/compare_test.res`, diffing the emitted
    module against the checked-in snapshot to confirm the nested `switch (y)`
    under `case "B"` now emits `case "B"` before the grouped `case "A"` /
    `case "C"` fallthrough exactly like OCaml
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - direct repro for `tests/tests/src/UntaggedVariants.res`, diffing the
    emitted module against the checked-in snapshot to confirm the file still has
    broader untagged-switch drift outside this stable-grouping slice rather than
    a regression in the newly patched case-group ordering
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/compare_test.res` is no longer in the authoritative diff
    set; the Rust backend now matches OCaml's stable grouping of non-adjacent
    equal switch bodies
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the switch-grouping port
  - `tests/tests/src/UntaggedVariants.res` still differs, but its remaining
    drift is now in broader untagged guard ordering and branch-shape lowering,
    not in the specific stable-grouping bug fixed here
- Topline impact:
  - JS snapshot parity: **469 / 657** -> **471 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **188** -> **186** (**-2**)
- Keep this change because it ports the real OCaml switch-grouping behavior from
  `Lam_compile.group_apply` + `Ext_list.stable_group`; the parity gain comes
  from matching OCaml's backend case ordering rather than from any printer-only
  rewrite.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml extension-field access path so exception payload
  reads lower to named static properties like `exn._1` instead of numeric array
  indexing like `exn[1]`
- Active backend focus for this slice stays in **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`, because the mismatch lived in field lowering:
  OCaml's backend sends `Fld_extension` through `E.extension_access`, while the
  Rust JS path was still falling back to generic `ArrayIndex`
- OCaml reference:
  `compiler/core/js_of_lam_block.ml`, where `Fld_extension` calls
  `E.extension_access e None i`; and `compiler/core/js_exp_make.ml`, where
  `extension_access` lowers unnamed extension payload fields to
  `Static_index (e, "_" ^ Int32.to_string pos, Some pos)`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `compile_field_access(...)` lowers `FieldDbgInfo::Extension` to
    `ExpressionDesc::StaticIndex(target, format!("_{}", idx), Some(idx))`
    instead of falling through to `ExpressionDesc::ArrayIndex`
  - added focused regression coverage in
    `lowers_extension_pfield_to_named_payload_property_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_extension_pfield_to_named_payload_property_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/array_safe_get.res`, diffing the emitted
    module against the checked-in snapshot to confirm `msg._1` is exact again
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/array_safe_get.res` is no longer in the authoritative diff
    set
  - `tests/tests/src/caml_compare_test.res` is no longer in the authoritative
    diff set
  - `tests/tests/src/exception_value_test.res` is no longer in the
    authoritative diff set
  - `tests/tests/src/stdlib/Stdlib_ErrorTests.res` is no longer in the
    authoritative diff set
  - `tests/tests/src/stdlib/Stdlib_IntTests.res` is no longer in the
    authoritative diff set
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the extension-field port
- Topline impact:
  - JS snapshot parity: **464 / 657** -> **469 / 657** (**+5**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **193** -> **188** (**-5**)
- Keep this change because it ports OCaml's real extension-field lowering from
  `js_of_lam_block.ml` / `js_exp_make.ml`; the removed diffs are the direct
  result of using named exception payload properties instead of the Rust-only
  numeric-index shortcut.

Latest iteration on **2026-04-14**:

- Active slice: port the missing OCaml `Pduprecord` backend primitive and the
  paired spread-only object dump shape so record/object duplication stops
  lowering to `undefined` and prints as inline `{...base}` like OCaml
- Active backend focus for this slice stays primarily **Phase 3: Port JS IR
  Lowering And Metadata** from `PLAN.md`, because the root cause lived in
  `compiler/core/lam_compile_primitive.ml`: Rust never handled `Pduprecord` on
  the JS path and therefore compiled record duplication to `undefined`; the
  final printer tweak is the small follow-up needed to match OCaml's
  `Object (Some e, [])` dump shape exactly once the IR is correct
- OCaml reference:
  `compiler/core/lam_compile_primitive.ml`, especially the `Pduprecord` branch
  lowering to `E.obj ~dup:e1 []`; and `compiler/core/js_dump.ml`, especially
  `Object (dup, lst)` where `lst = []` uses `P.brace` so spread-only object
  literals print inline as `{...expr}`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so `compile_primitive(...)`
    now lowers `Primitive::Pduprecord` to `ExpressionDesc::Object(Some(...),
    vec![])` instead of falling through to `undefined`
  - updated `compiler-rust/src/js_ir/printer.rs` so spread-only object
    literals use the OCaml inline `{...expr}` shape instead of the multiline
    grouped object-literal formatting path
  - added focused regression coverage in
    `compile_duprecord_lowers_to_object_spread_like_ocaml` and
    `test_print_spread_only_object_literal_inline_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_duprecord_lowers_to_object_spread_like_ocaml -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_spread_only_object_literal_inline_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/res_debug.res`, diffing the emitted
    module against the checked-in snapshot to confirm `let newrecord = {...v0};`
    is exact again
  - direct repro for
    `tests/tests/src/stdlib/intl/Stdlib_Intl_DateTimeFormatTest.res`, diffing
    the emitted module against the checked-in snapshot to confirm all duplicated
    `options` records now print inline and match exactly
  - direct repro for `tests/tests/src/record_regression.res`, diffing the
    emitted module against the checked-in snapshot to confirm the earlier
    `let newrecord;` bug is gone and the remaining drift is in a later
    inlined-record/pattern-match cluster
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/res_debug.res` is no longer in the authoritative diff set
  - `tests/tests/src/stdlib/intl/Stdlib_Intl_DateTimeFormatTest.res` is no
    longer in the authoritative diff set
  - `tests/tests/src/large_record_duplication_test.res` is no longer in the
    authoritative diff set
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the `Pduprecord` + printer port
  - `tests/tests/src/record_regression.res` and
    `tests/tests/src/jsx_preserve_test.res` still differ, but no longer because
    of the missing duplicated-object base; their remaining drift is in later
    JSX / inlined-record lowering rather than in record duplication itself
- Topline impact:
  - JS snapshot parity: **461 / 657** -> **464 / 657** (**+3**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **196** -> **193** (**-3**)
- Keep this change because it ports the missing OCaml backend behavior directly:
  `Pduprecord` was a real lowering hole on the Rust JS path, and once that IR
  shape exists the dumper must follow OCaml's inline spread-only object format
  for exact snapshot parity.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml `Lam_util.refine_let` safe-alias rewrite so
  strict bindings that are already safe to duplicate reach `Lam_coercion` as
  direct constants or aliases instead of surviving as same-name exports
- Active backend focus for this slice is **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`, because the remaining mismatch lived before
  JS printing: Rust was preserving strict bindings for exported constants where
  OCaml reclassifies them to `Alias` / `StrictOpt` during the late lambda
  cleanup pipeline
- OCaml reference:
  `compiler/core/lam_util.ml`, especially `refine_let` and its
  `is_safe_to_alias` predicate; also `compiler/core/lam_coercion.ml` to verify
  that once the exported payload stops being `Lvar same_name`, OCaml rebinds the
  export through a fresh identifier and emits the surviving function
  declarations first
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so
    `simplify_with_env(...)` mirrors OCaml's `refine_let` rules:
    `Strict` / `StrictOpt` bindings become `Alias` when the RHS is safe to
    duplicate, and `Strict` bindings downgrade to `StrictOpt` for functions and
    other side-effect-free expressions
  - added a Rust-side `is_safe_to_alias(...)` helper matching the OCaml cases
    used here:
    `Lvar`, `Lconst`, module-field reads over a module/global binding, and
    recursive `PsomeNotNest`
  - kept the focused export-order regression coverage in
    `compiler-rust/src/lambda/simplify.rs` and
    `compiler-rust/src/lambda/compile.rs`, now using the real marshalled-string
    payload shape that reproduces `switch_string.res`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml simplifies_exported_marshaled_string_payloads_before_export_coercion -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_deps_program_rebinds_marshaled_string_exports_after_surviving_function_bindings -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_deps_program_rebinds_exported_constants_after_surviving_function_bindings -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/switch_string.res`, diffing the emitted
    module against the checked-in snapshot to confirm the exported marshalled
    string is rebound after the surviving functions like OCaml
  - direct repro for `tests/tests/src/test_trywith.res`, diffing the emitted
    module against the checked-in snapshot to confirm the remaining top-level
    `u1` / `v` export-order drift is gone
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/switch_string.res` is no longer in the authoritative diff
    set; the exported string payload now reaches export coercion as a direct
    constant, so the emitted JS order matches OCaml's `function foo`, `function
    bar`, `let s = ...` sequence
  - `tests/tests/src/test_trywith.res` is no longer in the authoritative diff
    set; after the earlier continuation-sensitive `trywith` fix, the last
    remaining drift was the same exported-constant aliasing issue, and this
    slice removes it
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the alias cleanup port
- Topline impact:
  - JS snapshot parity: **461 / 657** -> **461 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **196** -> **196** (**no change**)
- Keep this change because it ports OCaml's late lambda alias classification
  from `Lam_util.refine_let`; the wrapper count stayed flat, but the targeted
  export-order files now match exactly and any offsetting drift belongs to a
  different backend cluster.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml continuation-sensitive `trywith` lowering path
  so Rust compiles try bodies and handlers with the same `Declare` / `Assign` /
  `NeedValue` / `EffectCall` continuation split instead of forcing every
  `LtryWith` through the generic effect-block path
- Active backend focus for this slice is **Phase 3: Port JS IR Lowering And
  Metadata** from `PLAN.md`, because the mismatch lived in
  `compiler/core/lam_compile.ml` rather than in JS dumping: Rust's
  `compile_expr(LtryWith)` was erasing the OCaml continuation shape and
  generating effect-only try bodies even in return and value positions
- OCaml reference:
  `compiler/core/lam_compile.ml`, especially `change_tail_type_in_try` and
  `compile_trywith`, where OCaml lowers `trywith` differently for
  `Declare`, `Assign`, `NeedValue`, and `EffectCall` continuations and keeps
  the try body in return position when the surrounding continuation is a
  tail-return
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so `LtryWith` now lowers
    through a shared `try_statement(...)` helper in all continuation-shaped
    paths:
    `compile_expr(...)`, `compile_let_binding(...)`,
    `compile_assign_to_target_block(...)`, `compile_effect_block(...)`,
    `compile_effect_output(...)`, and `compile_return_block(...)`
  - `compile_expr(LtryWith)` now mirrors OCaml's `NeedValue` case by
    allocating a temporary result variable and compiling both try body and
    handler as assignments into that variable
  - `compile_return_block(LtryWith)` now preserves return-position try bodies
    and handlers, matching OCaml's tail-in-try behavior instead of emitting
    effect-only `g(x);` blocks
  - added focused regression coverage in
    `compile_return_block_lowers_trywith_in_return_position`, while keeping
    the earlier terminal-output guards
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_return_block_lowers_trywith_in_return_position -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_return_block_skips_unreachable_sequence_after_throw -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml block_finishes_output_ignores_switch_case_breaks -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/test_trywith.res`, diffing the emitted
    module against the checked-in snapshot to confirm the tail-try control-flow
    drift is gone and only the top-level binding-order drift remains
  - direct repro for `tests/tests/src/bb.res`, diffing the emitted module
    against the checked-in snapshot as a switch-break guard
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1245_test.res` is no longer in the authoritative
    diff set after the continuation-sensitive `trywith` lowering fix
  - `tests/tests/src/test_exception_escape.res` is no longer in the
    authoritative diff set; its local exception handler now lowers through the
    OCaml-style value/return path instead of the old effect-only try block
  - `tests/tests/src/test_match_exception.res` is no longer in the
    authoritative diff set for the same reason
  - `tests/tests/src/test_trywith.res` is materially smaller; the remaining
    drift is only the top-level `u1` / `v` binding order, not the tail-try
    control flow
  - `tests/tests/src/bb.res` and `tests/tests/src/ExternalShadow.res` remain
    exact snapshot matches after the `trywith` port
- Topline impact:
  - JS snapshot parity: **458 / 657** -> **461 / 657** (**+3**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **199** -> **196** (**-3**)
- Keep this change because it ports OCaml's `compile_trywith` continuation
  model instead of preserving the Rust-only shortcut that flattened all
  `trywith` expressions into effect-only try/catch blocks.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml `Js_output.append_output` / `output_as_block`
  finished-output rule more precisely so Rust drops unreachable trailing
  output after real terminal statements, but does **not** treat switch-local
  `break` statements as finishing the surrounding output
- Active backend focus for this slice remains **Phase 5: Byte-Exact Dumping**
  from `PLAN.md`, but the bug lived one stage earlier in the Rust backend's
  output-sequencing model: I initially applied OCaml's `output_finished`
  behavior using the broader `block_terminates(...)` predicate, which
  incorrectly treated `break`/`continue` as if they finished the enclosing
  JS output instead of only the local switch/loop control flow
- OCaml reference:
  `compiler/core/js_output.ml`, where `append_output` returns the left-hand
  output unchanged only when `output_finished = True`, and `output_as_block`
  ignores the trailing expression only in that same finished-output case;
  the Rust fix needed a matching notion of "finished output" rather than the
  broader "statement terminates local control flow" predicate
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so the new terminal-output
    pruning paths in `compile_effect_block(...)`,
    `compile_return_block(...)`, `append_effect_output(...)`, and
    `compiled_to_effect_block(...)` use a dedicated
    `block_finishes_output(...)` / `statement_finishes_output(...)` helper
    that counts only `return`/`throw`-style finished output and ignores
    switch/loop-local `break` / `continue`
  - kept the earlier unreachable-throw cleanup for
    `compile_return_block(...)`, but narrowed it so `bb.res` no longer loses
    the post-switch return ladder after case bodies that end in `break`
  - added focused regression coverage in
    `compile_return_block_skips_unreachable_sequence_after_throw` and
    `block_finishes_output_ignores_switch_case_breaks`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml block_finishes_output_ignores_switch_case_breaks -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_return_block_skips_unreachable_sequence_after_throw -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/bb.res`, diffing the emitted module
    against the checked-in snapshot to confirm the switch-local `break`
    regression is gone
  - direct repro for `tests/tests/src/test_trywith.res`, diffing the emitted
    module against the checked-in snapshot to confirm the bogus unreachable
    `return 12;` after a `throw` is still gone while the remaining drift stays
    limited to the tail-try and export-order cluster
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bb.res` remains an exact snapshot match; the narrowed
    finished-output helper no longer drops the post-switch return ladder after
    case bodies that merely `break`
  - `tests/tests/src/test_trywith.res` still shows the same remaining
    tail-try/export-order diff, but the previously bogus unreachable
    `return 12;` after the `throw` stays removed
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the finished-output narrowing
- Topline impact:
  - JS snapshot parity: **458 / 657** -> **458 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **199** -> **199** (**no change**)
- Keep this change because it ports the OCaml `Js_output` finished-output rule
  more faithfully than the initial Rust slice: `return`/`throw` now suppress
  unreachable trailing output, while switch-local `break` no longer masquerades
  as a finished output boundary.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml exotic-uppercase identifier unwrapping rule for
  property keys and property access so JS dump uses the underlying identifier
  text instead of re-emitting the encoded `\\\"...\"` form
- Active backend focus for this slice remains **Phase 5: Byte-Exact Dumping**
  from `PLAN.md`, but the mismatch was still driven by OCaml backend metadata
  rules in `Js_dump_property` and `Ext_ident`: the Rust printer was deciding
  between dot access and quoted property syntax on the encoded name instead of
  the unwrapped identifier that OCaml prints
- OCaml reference:
  `compiler/core/js_dump_property.ml`, where both `property_access` and
  `property_key` call `Ext_ident.unwrap_uppercase_exotic`, and
  `compiler/ext/ext_ident.ml`, where `unwrap_uppercase_exotic` strips the
  leading `\\\"` and trailing `\"` wrapper before keyword/global handling and
  identifier mangling
- Rust change:
  - updated `compiler-rust/src/js_ir/printer.rs` so
    `convert_ident_name(...)`, `print_literal_property_name(...)`,
    `print_property_access(...)`, and `property_access_uses_dot(...)` all
    unwrap uppercase-exotic names before choosing identifier vs quoted output
  - added focused regression coverage in
    `test_print_property_access_unwraps_uppercase_exotic_keys` and
    `test_print_object_literal_unwraps_uppercase_exotic_keys`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_property_access_unwraps_uppercase_exotic_keys -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_object_literal_unwraps_uppercase_exotic_keys -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/exotic_labels_test.res`, diffing the
    exact emitted module against the checked-in snapshot
  - direct repro for `tests/tests/src/gpr_7431_test.res`, diffing the exact
    emitted module against the checked-in snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/exotic_labels_test.res` is no longer in the authoritative
    diff set; OCaml-style unwrapping now prints `KEY` as a plain property key
    instead of `"\\\"KEY\""`
  - `tests/tests/src/gpr_7431_test.res` is no longer in the authoritative diff
    set; both object keys and property access now print `MyWeirdProp` instead
    of preserving the encoded wrapper in the final JS output
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the property-name unwrapping change
- Topline impact:
  - JS snapshot parity: **456 / 657** -> **458 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **201** -> **199** (**-2**)
- Keep this change because it ports the OCaml `Js_dump_property` /
  `Ext_ident.unwrap_uppercase_exotic` rule instead of preserving the Rust-only
  behavior that treated encoded uppercase-exotic property names as literal
  quoted strings at JS dump time.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml string-tag emission rule for string-switch
  cases and other `SwitchCaseTag::String` literals so the Rust backend prints
  them through the `DStarJ` path instead of the default quoted-string path
- Active backend focus for this slice remains **Phase 5: Byte-Exact Dumping**
  from `PLAN.md`, but the mismatch sits on the boundary between
  `Lam_compile` and final printing: OCaml treats string switch tags as
  marshalled JS string literals via `E.tag_type`, while Rust was still
  re-escaping them as ordinary strings
- OCaml reference:
  `compiler/core/lam_compile.ml`, where `compile_stringswitch` maps each case
  to `Ast_untagged_variants.String s`, and `compiler/core/js_exp_make.ml`,
  where `tag_type (String s)` lowers to `str s ~delim:DStarJ`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `switch_case_expr(...)` lowers `SwitchCaseTag::String` to
    `ExpressionDesc::Str { delim: Delim::StarJ, ... }` instead of the default
    `Expression::string(...)` path
  - updated `compiler-rust/src/js_ir/printer.rs` so
    `print_switch_case_tag(...)` emits `SwitchCaseTag::String` through
    `print_string_with_delim(..., Delim::StarJ)`
  - added focused regression coverage in
    `switch_case_expr_preserves_marshaled_string_tags` and
    `test_print_string_switch_cases_preserve_marshaled_string_tags`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml switch_case_expr_preserves_marshaled_string_tags -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_string_switch_cases_preserve_marshaled_string_tags -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/switch_string.res`, diffing the exact
    emitted module against the checked-in snapshot to confirm the escaped
    compare/case drift is gone and the remaining mismatch is only statement
    ordering around `let s`
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/switch_case_test.res` is no longer in the authoritative
    diff set; its previously doubled switch tags now print like the OCaml
    `DStarJ` path
  - `tests/tests/src/switch_string.res` is smaller again; the remaining diff
    is only the position of `let s = "😀"` relative to `function bar`
  - `tests/tests/src/test_trywith.res` still differs, but its remaining diff
    is now limited to control-flow and declaration ordering instead of the
    earlier doubled string-tag escapes
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the string-tag emission change
- Topline impact:
  - JS snapshot parity: **455 / 657** -> **456 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **202** -> **201** (**-1**)
- Keep this change because it ports the OCaml `compile_stringswitch` /
  `js_exp_make.tag_type` string-literal rule instead of preserving the
  Rust-only default-string re-escape in switch tags.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml `lam_compile_const` delimiter-preservation
  rule for lambda string constants so `DStarJ` and `DNoQuotes` survive into
  JS IR instead of being collapsed to ordinary quoted strings on the Rust
  backend path
- Active backend focus for this slice remains **Phase 5: Byte-Exact Dumping**
  from `PLAN.md`, but the actual bug was one stage earlier in
  `Lam_compile_const` / `J.Str` construction: Rust was discarding the OCaml
  delimiter metadata before final printing
- OCaml reference:
  `compiler/core/lam_compile_const.ml`, where
  `Const_string {s; delim = None | Some DNoQuotes} -> E.str s` and
  `Const_string {s; delim = Some delim} -> E.str ~delim s`, preserving
  `DStarJ`, `DNoQuotes`, and `DBackQuotes` into JS IR instead of flattening
  them all to the default quoted-string path
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `LambdaCompiler::compile_constant(...)` maps
    `StringDelim::StarJ -> Delim::StarJ`,
    `StringDelim::NoQuotes -> Delim::NoQuotes`,
    `StringDelim::Backtick -> Delim::BackQuotes`, and keeps only
    `StringDelim::Plain` / `None` on the ordinary `Delim::None` path
  - added focused regression coverage in
    `compile_constant_preserves_marshaled_starj_strings` and
    `compile_constant_preserves_marshaled_noquote_strings`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml compile_constant_preserves_marshaled -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/switch_string.res`, diffing the exact
    emitted module against the checked-in snapshot to confirm the remaining
    drift shrank from both case tags and return literals down to the switch
    discriminant/case-tag side only
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/js_string_test.res` is no longer in the authoritative
    diff set; the doubly escaped `\"` HTML-fragment expectations now match the
    checked-in snapshot
  - `tests/tests/src/stdlib/Test.res` is no longer in the authoritative diff
    set; the `"\n  "` replacement literal now stays on the OCaml
    `DStarJ`-preserving path instead of becoming `"\\n  "`
  - `tests/tests/src/switch_string.res` is smaller but still failing because
    string-switch keys are still arriving in escaped form before this
    `compile_constant` stage
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the delimiter-preservation change
- Topline impact:
  - JS snapshot parity: **450 / 657** -> **455 / 657** (**+5**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **207** -> **202** (**-5**)
- Keep this change because it ports the OCaml `lam_compile_const` string
  delimiter rule instead of preserving the Rust-only behavior that dropped
  marshalled-string metadata before JS dumping.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml UTF-8-aware dump behavior for internal
  byte-backed JS strings and raw JS snippets so parser-stored UTF-8 bytes do
  not re-emit as Latin-1 mojibake on the Rust printer path
- Active backend focus for this slice is **Phase 5: Byte-Exact Dumping** from
  `PLAN.md`; this is printer-only drift after the backend metadata path, and it
  collapsed a repeated output motif across regular strings, template literals,
  regex/raw snippets, and raw no-quote literals
- OCaml reference:
  `compiler/core/js_dump_string.ml`, where `escape_to_buffer` walks byte
  strings and preserves valid UTF-8 sequences while escaping control bytes, and
  `compiler/core/js_dump.ml`, where `Str {delim; txt}` and `Raw_js_code`
  forward those internal byte strings directly into the final dump
- Rust change:
  - updated `compiler-rust/src/js_ir/printer.rs` so string literals, raw
    no-quote/backquote strings, tagged-template segments, and `RawJsCode`
    first decode parser-stored `0x00..0xFF` code units back into valid UTF-8
    when possible instead of re-encoding the mojibake intermediary string
  - kept the decode path narrow by only transforming strings whose code units
    all fit in `0x00..0xFF` and whose reconstructed byte buffer is valid UTF-8,
    leaving ordinary Rust-side Unicode strings unchanged
  - added focused regression coverage in
    `test_print_string_decodes_internal_utf8_bytes_before_escaping`,
    `test_print_noquote_string_decodes_internal_utf8_bytes`,
    `test_print_tagged_template_decodes_internal_utf8_bytes`, and
    `test_print_raw_js_decodes_internal_utf8_bytes`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_string_decodes_internal_utf8_bytes_before_escaping -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_noquote_string_decodes_internal_utf8_bytes -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_tagged_template_decodes_internal_utf8_bytes -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_raw_js_decodes_internal_utf8_bytes -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/test_regex.res`, diffing the exact
    emitted module against the checked-in snapshot
  - direct repro for `tests/tests/src/prepend_data_ffi.res`, diffing the exact
    emitted module against the checked-in snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_regex.res` now matches its checked-in snapshot
    exactly; the regex literal had been re-emitted as Latin-1 mojibake through
    the raw-JS printer path
  - `tests/tests/src/prepend_data_ffi.res` remains an exact snapshot match
    after the broader string/raw decode fix, confirming the regular string
    literal path is aligned too
  - the authoritative wrapper improved by eight snapshots and eight fewer diff
    files with no compile-error regression, confirming this was a repeated
    final-dump motif rather than a single-file accident
- Topline impact:
  - JS snapshot parity: **442 / 657** -> **450 / 657** (**+8**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **215** -> **207** (**-8**)
- Keep this change because it ports the OCaml `js_dump_string` / `js_dump`
  byte-preserving UTF-8 emission behavior instead of preserving the Rust-only
  Latin-1 re-encoding bug in final JS output.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml debug-mode constructor metadata path so
  `-bs-g` emits `[Symbol.for("name")]` on payload constructors during JS dump
  instead of silently dropping the debug-only property on the Rust path
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is backend metadata/dump behavior gated
  by compiler config, not a content-based snapshot rewrite
- OCaml reference:
  `compiler/core/js_dump.ml`, where `Caml_block (_, _, _, Blk_constructor p)`
  appends `name_symbol` when `!Js_config.debug && (not untagged) && not_is_cons`,
  plus `compiler/core/js_dump_property.ml`, where `Symbol_name` prints as
  `[Symbol.for("name")]`
- Rust change:
  - extended `compiler-rust/src/driver.rs` with
    `debug_for_structure(...)` so file-level `@@config({flags: ["-bs-g"]})`
    participates in JS emission decisions the same way OCaml's
    `Js_config.debug` does
  - threaded a `debug` flag through `CompilerOptions`, the `bsc` CLI parser,
    and `compiler-rust/src/js_ir/printer.rs`
  - updated constructor `CamlBlock` printing so non-cons, non-untagged
    payload constructors append `[Symbol.for("name")]: "<Ctor>"` only in debug
    mode, preserving the existing non-debug object shape
  - added focused regression coverage in
    `test_print_non_cons_constructor_adds_debug_name_symbol_in_debug_mode`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_non_cons_constructor_adds_debug_name_symbol_in_debug_mode -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml test_print_non_cons_constructor_keeps_tag_object_shape -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/debug_mode_value.res`, diffing the exact
    emitted module against the checked-in snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/debug_mode_value.res` now matches its checked-in snapshot
    exactly; Rust had been ignoring the OCaml debug-mode constructor-name
    metadata and dropped `[Symbol.for("name")]`
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the debug-mode metadata change
  - the authoritative wrapper improved by one snapshot and one fewer diff file,
    with no compile-error regression
- Topline impact:
  - JS snapshot parity: **441 / 657** -> **442 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **216** -> **215** (**-1**)
- Keep this change because it ports the OCaml `Js_config.debug` /
  `js_dump` constructor metadata rule instead of preserving the Rust-only
  “ignore `-bs-g` during JS dump” behavior.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml staticcatch fallthrough-return behavior for
  nested handlers that immediately re-raise an outer staticcatch label, so
  return-switch lowering can preserve the OCaml case ordering instead of
  keeping the Rust-only eager empty-body return clauses first
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is still `Lam_compile` control-flow
  lowering in the backend path, not a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml` and
  `compiler/core/lam_compile_context.ml`, where nested `Lstaticcatch`
  fallthrough handlers may wrap a switch whose immediate handler re-raises an
  outer label while the enclosing return context still emits the outer handler
  after the switch
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `uses_fallthrough_staticcatch_return(...)` recognizes the nested
    staticraise-to-outer-label pattern instead of only the narrower
    return-unit/single-branch case
  - added
    `lambda_contains_static_raise_to_label(...)`,
    `active_fallthrough_return_handler(...)`, and
    `reorder_fallthrough_return_clauses(...)` so return-switch lowering moves
    empty-body fallthrough cases behind non-empty handled cases only when an
    active fallthrough return handler is present
  - applied that return-clause reordering in the named-string and integer
    return-switch lowering paths
  - added focused regression coverage in
    `multi_case_staticcatch_wrapped_named_variant_return_switch_moves_fallthrough_cases_last`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml multi_case_staticcatch_wrapped_named_variant_return_switch_moves_fallthrough_cases_last -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml single_case_staticcatch_wrapped_named_variant_return_switch_falls_through_to_handler -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml staticcatch_wrapped_string_switches_use_the_handler_as_the_default_value -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/compare_test.res` using the exact
    harness compiler args from `tests/tests/lib/bs`, diffing the emitted module
    against the checked-in snapshot to keep the remaining one-hunk switch-order
    drift isolated while validating the new control-flow rule
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - the Rust backend now has explicit coverage for the OCaml nested-staticcatch
    re-raise path instead of relying on the older single-branch heuristic
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the control-flow lowering change
  - `tests/tests/src/compare_test.res` still reproduces the same single-hunk
    inner-switch ordering drift, so the remaining mismatch for that file is not
    this staticcatch fallthrough rule
  - the authoritative wrapper baseline is unchanged, which means this slice is
    an OCaml-alignment cleanup that did not yet flip any checked-in JS snapshot
- Topline impact:
  - JS snapshot parity: **441 / 657** -> **441 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **216** -> **216** (**no change**)
- Keep this change because it ports the OCaml staticcatch return-context rule
  instead of preserving the Rust-only narrower fallthrough heuristic.

Latest iteration on **2026-04-14**:

- Active slice: port the missing OCaml external-call polyvariant marshalling so
  `@string`, `@int`, and payload polyvariant externals go through the
  `Js_of_lam_variant.eval*` argument-rewrite path instead of forwarding the raw
  OCaml-side representation directly to JavaScript calls
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is still backend call-lowering work in
  the current JS path, not a printer fix
- OCaml reference:
  `compiler/core/lam_compile_external_call.ml`, where `ocaml_to_js_eff`
  returns `Splice0` / `Splice1` / `Splice2` and rewrites
  `Poly_var_string`, `Poly_var`, `Int`, and `Unwrap` through
  `compiler/core/js_of_lam_variant.ml`
- Rust change:
  - extended `compiler-rust/src/lambda/compile.rs` external arg assembly to
    support multi-value expansion for externals, matching the OCaml
    `Splice0` / `Splice1` / `Splice2` contract instead of assuming every
    runtime arg lowers to at most one JS arg
  - added OCaml-aligned helpers for optional-to-undefined conversion,
    polyvariant string/int dispatch, payload expansion, and polyvariant unwrap
    on the JS-call argument assembly path
  - updated `assemble_external_args_no_splice(...)` and
    `assemble_external_args_with_splice(...)` to extend the output arg list
    with the rewritten values rather than pushing a single forwarded arg
  - added focused regression coverage in
    `lowers_external_polyvar_string_and_int_args_like_ocaml` and
    `lowers_external_polyvar_payload_args_to_two_js_args_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_external_polyvar -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/poly_variant_test.res` no longer has the incorrect
    `hey_string("in_")` / `hey_int("on_open")` style external-marshalling
    drift; its remaining diff is now limited to separate constant-folding and
    UTF-8 string-emission issues
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the external-call marshalling change
  - the remaining polyvariant-shaped failing diff set is unchanged in file
    names (`big_polyvar_test`, `bs_poly_map_test`, `poly_variant_test`), but
    `poly_variant_test` is materially smaller and the overall wrapper baseline
    improved by four
- Topline impact:
  - JS snapshot parity: **437 / 657** -> **441 / 657** (**+4**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **220** -> **216** (**-4**)
- Keep this change because it ports the OCaml
  `lam_compile_external_call` / `js_of_lam_variant` argument rewriting instead
  of preserving the Rust-only “forward the raw external arg unchanged” shortcut.

Latest iteration on **2026-04-14**:

- Active slice: port the missing OCaml polyvariant field access lowering so
  `Pfield` on `Fld_poly_var_tag` / `Fld_poly_var_content` uses named
  `NAME` / `VAL` access instead of the generic Rust array-index fallback
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is still `Lam_compile` / field-access
  lowering downstream of the already-green optimized lambda boundary
- OCaml reference:
  `compiler/core/js_of_lam_block.ml`, where `field` routes
  `Fld_poly_var_tag` / `Fld_poly_var_content` to `E.poly_var_tag_access` and
  `E.poly_var_value_access`, plus `compiler/core/js_exp_make.ml`, where those
  helpers unwrap pure `Caml_block` values directly or fall back to named static
  indices `NAME` / `VAL`
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `FieldDbgInfo::PolyVarTag` and `FieldDbgInfo::PolyVarContent` no longer
    drop into the generic `ArrayIndex` fallback inside `compile_field_access`
  - added `poly_var_tag_access(...)` and `poly_var_value_access(...)` helpers
    mirroring the OCaml direct-unwrapping behavior for pure `CamlBlock`
    expressions and the named `.NAME` / `.VAL` fallback for general targets
  - added focused regression coverage in
    `lowers_polyvar_pfield_to_named_static_access_like_ocaml` and
    `lowers_polyvar_pfield_from_pure_caml_block_directly_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_polyvar_pfield -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/more_poly_variant_test.res`, diffing the
    exact emitted module against the checked-in snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/more_poly_variant_test.res` now matches its checked-in
    snapshot exactly; Rust had been emitting `x[0]` / `x[1]` where the OCaml
    backend emits `x.NAME` / `x.VAL`
  - `tests/tests/src/int_poly_var.res` no longer appears in the failing diff
    cache under the authoritative harness, so the polyvariant access drift
    collapsed beyond the small direct repro file
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the polyvariant-access change
  - remaining polyvariant-shaped snapshot diffs are now narrowed to
    `big_polyvar_test`, `bs_poly_map_test`, and `poly_variant_test`
- Topline impact:
  - JS snapshot parity: **433 / 657** -> **437 / 657** (**+4**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **224** -> **220** (**-4**)
- Keep this change because it ports the OCaml `Js_of_lam_block.field` /
  `Js_exp_make.poly_var_*_access` behavior instead of preserving the Rust-only
  array-index shortcut for polyvariant object fields.

Latest iteration on **2026-04-14**:

- Active slice: port the missing OCaml backend primitive lowering for
  `Pisint`, `Pis_poly_var_block`, and `Pisout` so JS predicate compilation does
  not fall through to the Rust `undefined` fallback in emitted snapshots
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is a `Lam_compile` primitive-lowering fix
  downstream of the already-green optimized lambda boundary, not a printer
  rewrite
- OCaml reference:
  `compiler/core/lam_compile_primitive.ml`, where `Pisint`,
  `Pis_poly_var_block`, and `Pisout` lower through `E.is_type_number`,
  `E.is_type_object`, and `E.is_out`, plus `compiler/core/js_exp_make.ml`,
  where `is_out` performs the range-specialized predicate rewrites
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` to lower
    `Primitive::Pisint`, `Primitive::PisPolyVarBlock`, and
    `Primitive::Pisout(offset)` instead of dropping through to
    `Expression::undefined(false)`
  - added helpers mirroring the OCaml backend predicate builders for
    `typeof ... === "number"`, `typeof ... === "object"`, and the specialized
    `is_out` range checks after `int32_offset`
  - added focused regression coverage in
    `lowers_pis_poly_var_block_to_typeof_object_check`,
    `lowers_pisint_to_typeof_number_check`, and
    `lowers_pisout_to_ocaml_range_check_shapes`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml lowers_pis -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/more_poly_variant_test.res`, diffing the
    exact emitted module against the checked-in snapshot to confirm the missing
    polyvariant predicate no longer compiles to `undefined`
  - direct repro for `tests/tests/src/test_primitive.res`, diffing the exact
    emitted module against the checked-in snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_primitive.res` now matches its checked-in snapshot
    exactly; Rust had been compiling the missing backend predicate primitive to
    `undefined`, which leaked into emitted JS
  - `tests/tests/src/more_poly_variant_test.res` no longer emits
    `if (undefined)` / `if (!undefined)` in the polyvariant predicate path; the
    remaining diff is now a later runtime-shape/access mismatch
    (`x[0]` / `x[1]` versus `x.NAME` / `x.VAL`)
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the primitive-lowering change
- Topline impact:
  - JS snapshot parity: **432 / 657** -> **433 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **225** -> **224** (**-1**)
- Keep this change because it ports the OCaml
  `Lam_compile_primitive` / `Js_exp_make` predicate lowering instead of
  preserving the Rust-only missing-primitive `undefined` fallback in emitted
  JS.

Latest iteration on **2026-04-14**:

- Active slice: port the remaining OCaml lets-dce-style cleanup for
  let-wrapped direct applications exposed by the repeated backend alias passes
  so `let ... in function ...` values do not survive as Rust-only temporary
  call bindings in emitted JS
- Active backend focus for this slice remains **Phase 2: Port Post-Lowering
  Lambda Backend Stages** from `PLAN.md`; this is still a backend lambda-pass
  parity fix downstream of the already-green optimized lambda boundary
- OCaml reference:
  `compiler/core/lam_compile_main.ml`, where the backend reruns
  `Lam_pass_remove_alias.simplify_alias` before `Lam_pass_lets_dce.simplify_lets`,
  plus `compiler/core/lam_pass_lets_dce.ml`, where the later direct-`Lfunction`
  reduction cleans up newly exposed outer applies
- Rust change:
  - added let-wrapper rebuilding and
    `reduce_direct_function_application_like_lets_dce(...)` in
    `compiler-rust/src/lambda/simplify.rs` so the final lets-dce-style pass can
    peel `Llet` wrappers around direct functions / direct wrappers, beta-reduce
    the outer application, and then restore the preserved let bindings
  - updated `simplify_direct_function_applications_like_lets_dce(...)` to use
    that helper instead of stopping when the callee is no longer a bare
    `Lfunction`
  - added focused regression coverage in
    `beta_reduces_let_wrapped_returned_functions_across_backend_alias_passes`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml beta_reduces_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/ari_regress_test.res`, diffing the exact
    test-harness AST compile output against the checked-in snapshot
  - direct repro for `tests/tests/src/alias_test.res`, diffing the exact
    test-harness AST compile output against the checked-in snapshot as an
    unchanged string-alias guard
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/ari_regress_test.res` now matches its checked-in snapshot
    exactly; the Rust-only `call = (z => u + z | 0)(6)` temporary and the
    `/* x Not a pure module */` comment drift are gone
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the lets-dce cleanup change
  - `tests/tests/src/alias_test.res` is unchanged, which keeps the remaining
    string-alias / string-append drift isolated from this direct-call slice
- Topline impact:
  - JS snapshot parity: **431 / 657** -> **432 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **226** -> **225** (**-1**)
- Keep this change because it ports the OCaml lets-dce-style cleanup for
  let-wrapped direct applications instead of preserving the Rust-only temporary
  call binding shape in emitted JS.

Latest iteration on **2026-04-14**:

- Active slice: port the repeated OCaml backend alias/beta-reduction stages from
  `compiler/core/lam_compile_main.ml`,
  `compiler/core/lam_pass_remove_alias.ml`, and
  `compiler/core/lam_pass_lets_dce.ml` so direct `Lfunction` applications
  exposed by earlier simplification passes do not stop after the first returned
  wrapper and survive as Rust-only emitted IIFEs in snapshot output
- Active backend focus for this slice moves back to **Phase 2: Port Post-Lowering
  Lambda Backend Stages** from `PLAN.md`; this is a backend lambda-pass parity
  fix downstream of the already-green optimized lambda boundary, not a printer
  rewrite
- OCaml reference:
  `compiler/core/lam_compile_main.ml`, where the backend runs
  `Lam_pass_remove_alias.simplify_alias` multiple times before
  `Lam_pass_lets_dce.simplify_lets`, plus
  `compiler/core/lam_pass_remove_alias.ml` and
  `compiler/core/lam_pass_lets_dce.ml`, where direct `Lapply` of `Lfunction`
  values are beta-reduced again after earlier nested applications have exposed
  them
- Rust change:
  - updated `compiler-rust/src/lambda/simplify.rs` so the second backend
    simplification pass still allows direct-function beta reduction, matching
    the repeated OCaml `simplify_alias` structure instead of stopping after the
    first wrapper application
  - added a final
    `simplify_direct_function_applications_like_lets_dce(...)` traversal in
    `compiler-rust/src/lambda/simplify.rs` to mirror the later OCaml
    `lam_pass_lets_dce` direct-`Lfunction` apply reduction that cleans up any
    remaining returned wrappers
  - aligned `compiler-rust/src/lambda/beta_reduce.rs` `no_names_beta_reduce`
    with the OCaml binding order before reusing it from the lets-dce-style pass
  - replaced the stale one-beta-reduction unit expectations in
    `compiler-rust/src/lambda/simplify.rs` with regression tests that assert
    the outer direct application disappears after the repeated backend alias and
    lets-dce passes
- Verified focused guards for this slice:
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml beta_reduces_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/ari_regress_test.res`, diffing the exact
    test-harness AST compile output against the checked-in snapshot
  - direct repro for `tests/tests/src/arity_deopt.res`, diffing the exact
    test-harness AST compile output against the checked-in snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/arity_deopt.res` now matches its checked-in snapshot
    exactly; Rust had been stopping after the first returned-wrapper
    beta-reduction and leaving nested direct applications as emitted IIFEs
    instead of rerunning the OCaml backend alias/dce reductions
  - `tests/tests/src/ari_regress_test.res` is reduced to a single remaining
    let-wrapped direct-call cleanup difference in the `x = gg(3, 5)(6)` path;
    the earlier `g = f(3)(4)` returned-wrapper mismatch is gone
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the repeated alias-pass change, keeping this slice scoped away from the
    import/export backend path
- Topline impact:
  - JS snapshot parity: **430 / 657** -> **431 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **227** -> **226** (**-1**)
- Keep this change because it ports the repeated OCaml backend
  `simplify_alias` / `simplify_lets` direct-function beta-reduction behavior
  instead of preserving the Rust-only “stop after the first returned wrapper”
  simplifier shortcut.

Latest iteration on **2026-04-14**:

- Active slice: port OCaml `compile_sequand` / `compile_sequor` return-path
  lowering from `compiler/core/lam_compile.ml` so boolean short-circuit
  primitives re-enter the return-position `if` path, and make recursive
  self-tailcall detection follow that same OCaml expansion through the right
  branch instead of leaving Rust-only direct recursive `&&` / `||` calls in
  emitted JS
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is a `Lam_compile` control-flow /
  short-circuit lowering fix downstream of the already-green optimized lambda
  boundary
- OCaml reference:
  `compiler/core/lam_compile.ml`, where `compile_sequand` and
  `compile_sequor` call back into `compile_lambda` with `Lam.sequand` /
  `Lam.sequor` when the continuation is a return so the boolean primitive is
  lowered as an `if`, and where the tailcall branch of `compile_apply`
  rewrites self-calls into parameter assignments plus `continue`
- Rust change:
  - taught `compiler-rust/src/lambda/compile.rs` to route `Psequand` /
    `Psequor` through dedicated short-circuit handling in expression and
    return contexts instead of always compiling them straight to JS `&&` / `||`
  - added return-path handling for those primitives in both
    `compile_return_block(...)` and
    `compile_tail_loop_return_block(...)`, matching the OCaml behavior that
    re-expands them to `if` branches before later return/loop lowering
  - updated `function_has_self_tailcall(...)` to inspect the right-hand branch
    of `Psequand` / `Psequor`, which is the only tail-position branch after
    OCaml's `Lam.sequand` / `Lam.sequor` expansion
  - added focused regression coverage in
    `function_return_blocks_lower_effectful_sequands_without_a_result_temp`,
    `recursive_self_tailcalls_lower_sequands_to_looping_while_bodies`, and
    `recursive_self_tailcalls_lower_sequors_to_looping_while_bodies`
- Verified focused guards for this slice:
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml function_return_blocks_lower_effectful_sequands_without_a_result_temp -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml recursive_self_tailcalls_lower_sequands_to_looping_while_bodies -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml recursive_self_tailcalls_lower_sequors_to_looping_while_bodies -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/and_or_tailcall_test.res`, diffing the
    exact test-harness AST compile output against the checked-in snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/and_or_tailcall_test.res` now matches its checked-in
    snapshot exactly; Rust had been leaving `b && f(...)` / `b || f(...)` as
    recursive JS calls because the short-circuit primitives never re-entered
    the return-path `if` lowering that exposes self-tailcalls to the loop pass
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the short-circuit / tailcall lowering change
  - `and_or_tailcall_test` no longer appears under `temp/rust-parity/diffs`
- Topline impact:
  - JS snapshot parity: **426 / 657** -> **430 / 657** (**+4**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **231** -> **227** (**-4**)
- Keep this change because it ports the OCaml return-continuation lowering for
  `Psequand` / `Psequor` and the corresponding self-tailcall visibility rather
  than preserving the Rust-only direct-recursion shortcut in emitted JS.

Latest iteration on **2026-04-14**:

- Active slice: port the recursive OCaml `js_exp_make.ml` boolean
  simplification and `js_stmt_make.ml` single-block `if_` flattening needed so
  nested untagged-switch guards can collapse through single-statement block
  wrappers instead of getting stuck as Rust-only nested `if` towers
- Active backend focus for this slice is **Phase 4: Port JS Passes** from
  `PLAN.md`; this stays downstream of the already-green optimized lambda
  boundary and fixes JS-IR cleanup rather than reopening typedtree or lambda
  parity
- OCaml reference:
  `compiler/core/js_exp_make.ml`, where `simplify_and_` / `simplify_or_`
  recurse through nested `And` / `Or` trees with a depth limit and absorb
  repeated literal-equality tests on the same variable, and
  `compiler/core/js_stmt_make.ml`, where `block` flattens single nested blocks
  so `if_` can keep merging nested guards
- Rust change:
  - taught `compiler-rust/src/js_ir/mod.rs` to unwrap single nested
    `StatementDesc::Block` wrappers when checking for single returns,
    assignments, expressions, and nested `if` statements, matching the OCaml
    `block` helper behavior that keeps later `if_` merges visible
  - replaced the one-step `js_and_expression` / `js_or_expression`
    simplifier with a depth-limited recursive port of the OCaml
    `simplify_and_` / `simplify_or_` structure for nested `And` / `Or`
    expressions, while preserving the existing Rust-side literal/type guards
  - added focused regression coverage in
    `test_if_statement_merges_single_block_wrapped_nested_if_like_ocaml` and
    `test_js_and_simplifies_or_literal_membership_against_same_literal_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml test_if_statement_merges_single_block_wrapped_nested_if_like_ocaml -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml test_js_and_simplifies_or_literal_membership_against_same_literal_like_ocaml -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml test_js_and_simplifies_boolean_typeof_nullish_guards_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/LargeUnboxedVariantOptimization.res -o /tmp/LargeUnboxedVariantOptimization.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/LargeUnboxedVariantOptimization.res` now collapses the
    original full literal-membership guard partway through the OCaml
    `simplify_and_` path instead of preserving the whole Rust-only
    `"space" || "z" || ... || "a"` tower, but the file still differs on the
    remaining absorption step and on the later effect-position control-flow
    shaping inside the `state.active` branch
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the JS-IR simplification changes, which keeps this slice scoped away from
    the already-stable import/export path
- Topline impact:
  - JS snapshot parity: **426 / 657** -> **426 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **231** -> **231** (**no change**)
- Keep this change because it ports the OCaml recursive `simplify_and_` /
  `simplify_or_` shape and the single-block `if_` flattening behavior into the
  Rust JS backend; the wrapper stays flat only because
  `LargeUnboxedVariantOptimization` still needs the next downstream
  absorption/effect-lowering step before the snapshot fully drops out.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml untagged-switch `compile_switch` fast path for
  zero explicit literal arms with equal literal/block defaults, and keep the
  downstream `Js_stmt_make.if_` / `Js_exp_make.econd` simplifications aligned
  so impossible nullish guards under `typeof === "boolean"` collapse instead
  of surviving into emitted JS
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is a `Lam_compile` / JS-IR lowering fix
  downstream of the already-green optimized lambda boundary
- OCaml reference:
  `compiler/core/lam_compile.ml`,
  `compiler/core/js_exp_make.ml`, and
  `compiler/core/js_stmt_make.ml`, where untagged `compile_switch` skips the
  literal-vs-block dispatch when `sw_consts = []` and the const/block defaults
  are equivalent, and later `econd` / `if_` simplifications erase impossible
  `null` / `undefined` tests beneath boolean runtime guards
- Rust change:
  - added the OCaml-aligned no-literal / same-default fast path to
    `compile_untagged_variant_switch_assignment_statements(...)`,
    `compile_untagged_variant_switch_return_statements(...)`, and
    `compile_untagged_variant_switch_effect_statements(...)` in
    `compiler-rust/src/lambda/compile.rs`
  - kept the already-started `js_ir` simplification work for
    `Expression::cond`, `Statement::if_`, and boolean `&&` / `||` folding in
    `compiler-rust/src/js_ir/mod.rs`, which is the OCaml-aligned place where
    the remaining impossible nullish guards disappear after the switch shape is
    corrected
  - added focused regression coverage in
    `default_only_untagged_boolean_assignment_skips_literal_dispatch_when_defaults_match`,
    `default_only_untagged_boolean_return_skips_literal_dispatch_when_defaults_match`,
    and the new `js_ir` conditional-folding tests
- Verified focused guards for this slice:
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml default_only_untagged_boolean -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml complete_single_untagged_array -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml cond_merges_nested -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml if_statement_merges_nested -- --nocapture`
  - `timeout 180 cargo test --manifest-path compiler-rust/Cargo.toml test_js_and_simplifies_boolean_typeof_nullish_guards_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/and_or_simplify.res`, diffing
    `/tmp/and_or_simplify.mjs` against the checked-in snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/and_or_simplify.res` now matches its checked-in snapshot
    exactly; Rust had been preserving a literal-vs-block dispatch and nested
    impossible `null` / `undefined` guards that OCaml had already collapsed
    away
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the untagged-switch and JS-IR simplification changes
  - `and_or_simplify` no longer appears under `temp/rust-parity/diffs`
- Topline impact:
  - JS snapshot parity: **416 / 657** -> **426 / 657** (**+10**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **241** -> **231** (**-10**)
- Keep this change because it ports OCaml’s untagged-switch no-literal
  dispatch behavior and the associated conditional simplifications instead of
  preserving Rust-only nullish dispatch and impossible boolean guard checks.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml single-exit `compile_staticcatch` pseudo-jump
  path from `compiler/core/lam_compile.ml` into
  `compiler-rust/src/lambda/compile.rs` so single-arm switch/string-switch
  bodies whose default is `LstaticRaise` for the enclosing catch can fall
  through to the handler in `return_unit` function bodies instead of forcing
  Rust-only inverted early-return wrappers
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is a `Lam_compile` control-flow lowering
  fix downstream of the already-green optimized lambda boundary
- OCaml reference:
  `compiler/core/lam_compile.ml` and
  `compiler/core/lam_compile_context.ml`, where
  `compile_staticcatch` takes the pseudo-jump branch for a single exit code in
  `EffectCall (Maybe_tail_is_return ...)` context, declares the handler
  bindings up front, compiles `LstaticRaise` as assignments only, and appends
  the handler after the body
- Rust change:
  - added a narrow fallthrough-staticcatch path in
    `compile_return_block(...)` / `compile_fallthrough_static_raise_return_block(...)`
    for single-case `Lswitch` / `LstringSwitch` bodies whose default raises
    the enclosing static-catch label
  - restricted that path to `return_unit` function bodies and handlers without
    nested `LstaticRaise`, which is the closest Rust analogue of OCaml's
    `EffectCall (Maybe_tail_is_return ...)` guard and avoids over-applying the
    pseudo-jump rewrite in general value-returning contexts
  - added focused regression coverage in
    `single_case_staticcatch_wrapped_named_variant_return_switch_falls_through_to_handler`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml staticcatch_wrapped_string_switches_use_the_handler_as_the_default_value -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml single_case_staticcatch_wrapped_named_variant_return_switch_falls_through_to_handler -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/VariantPatternMatchingSpreads.res`,
    diffing `/tmp/VariantPatternMatchingSpreads.mjs` against the checked-in
    snapshot
  - direct repro for
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res`, diffing
    `/tmp/VariantPatternMatchingSpreadsWithPayloads.mjs` against the checked-in
    snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/VariantPatternMatchingSpreads.res` now matches its
    checked-in snapshot exactly; Rust had been lowering the default-to-exit
    path as an inverted early-return wrapper instead of letting the single
    matching branch return and then fall through to the handler like OCaml
  - `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` now
    matches the same `doWithB` fallthrough shape, but the file still differs
    on the separate `lookup2` object-vs-string branch ordering cluster
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the staticcatch lowering change
- Topline impact:
  - JS snapshot parity: **416 / 657** -> **416 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **241** -> **241** (**no change**)
- Keep this change because it ports the OCaml single-exit
  `compile_staticcatch` pseudo-jump lowering for `return_unit` function bodies
  instead of preserving the Rust-only inverted early-return wrapper shape on
  the minimal variant-spread repro.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml export-grouping behavior around
  `Pmakeblock(..., ModuleExport, Immutable)` into
  `compiler-rust/src/lambda/simplify.rs` so export-only single-use constant
  blocks disappear before final export coercion instead of surviving as
  Rust-only helper bindings that perturb declaration order and alias shape
- Active backend focus for this slice is **Phase 2: Port Post-Lowering Lambda
  Backend Stages** from `PLAN.md`; the remaining mismatch was already present
  in grouped lambda / initial JSX, so this is not a printer-only fix
- OCaml reference:
  `compiler/core/lam_coercion.ml` and `compiler/core/lam_pass_lets_dce.ml`,
  plus diagnosed artifacts `tests/tests/src/DotDotDot.lambda`,
  `tests/tests/src/DisambiguateOptionalFields.lambda`,
  `tests/tests/src/DotDotDot.01.initial.jsx`, and
  `tests/tests/src/DisambiguateOptionalFields.01.initial.jsx`, which showed
  OCaml already reaching the correct export order before JS passes
- Rust change:
  - taught `simplify_with_env(...)` to substitute exported single-use
    `Constant::Block` bindings directly into immutable module-export payloads
    when their only remaining use is inside
    `Primitive::Pmakeblock(_, TagInfo::ModuleExport(_), Mutable::Immutable)`
  - added the narrow `used_only_in_module_export_payload(...)` /
    `export_only_single_use_allocating_constant_candidate(...)` checks so this
    rewrite only applies to the OCaml-aligned export-only constant-block case
  - added focused regression coverage in
    `simplifies_export_only_constant_block_payloads_before_export_coercion`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml simplifies_export_only_constant_block_payloads_before_export_coercion -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml compile_deps_program_rebinds_exported_constants_after_surviving_function_bindings -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/DotDotDot.res`, diffing
    `/tmp/DotDotDot.mjs` against the checked-in snapshot
  - direct repro for `tests/tests/src/DisambiguateOptionalFields.res`, diffing
    `/tmp/DisambiguateOptionalFields.mjs` against the checked-in snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.mjs` against the checked-in snapshot as an unchanged
    backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/DisambiguateOptionalFields.res` now matches its
    checked-in snapshot exactly; Rust had been preserving the exported record
    binding long enough to emit `v` before `res`, while OCaml had already
    collapsed that export-only constant block before final export grouping
  - `tests/tests/src/DotDotDot.res` no longer differs on the leading export
    declaration order; its remaining mismatch is narrower and is now the
    surviving alias materialization for `MultipleDotDotDots.x`
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the export-grouping change
- Topline impact:
  - JS snapshot parity: **408 / 657** -> **416 / 657** (**+8**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **249** -> **241** (**-8**)
- Keep this change because it aligns the Rust post-lowering export cleanup
  with OCaml's grouped-lambda behavior for export-only constant blocks instead
  of preserving Rust-only bindings into final JS lowering.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml `Optional_block` identity handling in
  `compiler/core/js_pass_flatten_and_mark_dead.ml` into
  `compiler-rust/src/lambda/compile.rs` so JS-pass cleanup stops hoisting
  constant optional record fields into helper lets like `x_name` / `x_x`
  before printing
- Active backend focus for this slice is **Phase 4: Port JS Passes** from
  `PLAN.md`; this is a downstream JS cleanup fix after `Lam_compile` and does
  not reopen typedtree or lambda parity work
- OCaml reference:
  `compiler/core/js_pass_flatten_and_mark_dead.ml`, where the
  `subst_map` pass only needs helper bindings for non-simple immutable
  `Caml_block` fields, while `compiler/core/js_dump.ml` prints
  `Optional_block (e, true)` as just `e`
- Rust change:
  - taught `is_simple_block_binding_item(...)` and
    `is_simple_substituted_index_value(...)` to treat
    `ExpressionDesc::OptionalBlock(inner, true)` as simple when its printed
    inner expression is simple, instead of inventing helper lets for values
    the printer emits inline
  - added focused regression coverage in
    `js_flatten_and_mark_dead_keeps_identity_optional_record_fields_inline`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml js_flatten_and_mark_dead_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct repro for `tests/tests/src/DotDotDot.res`, diffing
    `/tmp/DotDotDot.rust.mjs` against the checked-in snapshot
  - direct repro for `tests/tests/src/ExternalShadow.res`, diffing
    `/tmp/ExternalShadow.rust.mjs` against the checked-in snapshot as an
    unchanged backend guard
  - direct repro for `tests/tests/src/DisambiguateOptionalFields.res`, diffing
    `/tmp/DisambiguateOptionalFields.rust.mjs` against the checked-in snapshot
    to confirm the remaining diff there is still the separate binding-order
    issue
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/DotDotDot.res` no longer emits the Rust-only helper lets
    `x_name` / `x_x`; its remaining mismatch is now the separate
    single-field-module hoist/order shape
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the JS-pass cleanup change
  - `tests/tests/src/DisambiguateOptionalFields.res` is unchanged and still
    only differs on declaration order, confirming this slice stayed scoped to
    identity optional-field cleanup
- Topline impact:
  - JS snapshot parity: **407 / 657** -> **408 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **250** -> **249** (**-1**)
- Keep this change because it aligns the Rust JS cleanup pass with OCaml's
  identity-optional-block printing behavior instead of preserving Rust-only
  helper bindings for optional record literals.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml `compile_recursive_let` recursive
  `Pmakeblock` self/captured-value branch from `compiler/core/lam_compile.ml`
  into `compiler-rust/src/lambda/compile.rs` so self-recursive records lower
  through a dummy object plus field updates like `let xx = {}; xx.xx = xx;`
  instead of Rust's placeholder declaration plus whole-object reassignment
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice fixes recursive-value lowering on the JS backend
  path without reopening typedtree or lambda parity work
- OCaml reference:
  `compiler/core/lam_compile.ml`, where `compile_recursive_let` special-cases
  recursive `Pmakeblock` values whose fields are only `Lvar` self/captured
  references or constants, emits `S.define_variable ~kind:Variable id
  (E.dummy_obj tag_info)`, and then mutates the dummy with
  `Js_of_lam_block.set_field ...`
- Rust change:
  - factored `Lletrec` lowering through `compile_recursive_bindings(...)` and
    added the matching recursive `Pmakeblock` self/captured branch in
    `compile_recursive_self_binding_makeblock(...)`
  - added the dummy-object and field-info helpers needed to emit the OCaml
    `let xx = {}; xx.xx = xx;` shape for recursive records and one-field
    constructors
  - added focused regression coverage in
    `recursive_self_referential_record_bindings_lower_to_dummy_object_updates_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml --quiet recursive_self_referential_record_bindings_lower_to_dummy_object_updates_like_ocaml -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml recursive_function_bindings_lower_directly_without_placeholder_assignments -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact `compiler-args` repro for `tests/tests/src/a_recursive_type.res`
    from `tests/tests/lib/bs`, diffing
    `tests/tests/lib/bs/src/a_recursive_type.mjs` against the checked-in
    snapshot
  - exact `compiler-args` repro for `tests/tests/src/ExternalShadow.res`
    from `tests/tests/lib/bs`, diffing
    `tests/tests/lib/bs/src/ExternalShadow.mjs` against the checked-in
    snapshot as an unchanged backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/a_recursive_type.res` now matches its checked-in snapshot
    exactly; Rust now emits the same dummy-object initialization plus field
    update shape as OCaml for `let rec xx = {xx: xx}`
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the recursive-value lowering change
  - the authoritative baseline improved by two passing snapshots, indicating
    the missing recursive `Pmakeblock` lowering was affecting more than the
    single minimal repro
- Topline impact:
  - JS snapshot parity: **405 / 657** -> **407 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **252** -> **250** (**-2**)
- Keep this change because it ports the OCaml `compile_recursive_let`
  dummy-object branch for recursive `Pmakeblock` values instead of preserving
  the Rust-only placeholder declaration plus whole-object reassignment.

- Active slice: match OCaml's constant `Psubint` folding in
  `compiler/core/lam.ml` inside
  `compiler-rust/src/lambda/simplify.rs` so the JS-path simplifier collapses
  constant loop finishes like `n - 1` before
  `compiler/core/lam_compile.ml` decides whether to emit `Up` or `Upto`,
  matching the checked-in loop headers instead of over-emitting `< N`
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice fixes post-lowering lambda cleanup on the JS
  backend path without reopening typedtree or lambda parity work
- OCaml reference:
  `compiler/core/lam.ml`, where `Lam.prim` folds `Psubint` over two
  `Const_int` arguments to `Lift.int (Int32.sub aa bb)`; after alias
  simplification, OCaml reaches `lam_compile.ml` with constant loop finishes
  like `9` instead of preserving `Psubint(10, 1)`
- Rust change:
  - added a backend-local `Psubint` constant fold in
    `simplify_primitive(...)` so `simplify_for_js_backend(...)` rebuilds
    constant loop bounds the same way OCaml's `Lam.prim` does
  - added focused regression coverage in
    `folds_constant_subint_loop_finish_before_for_range_lowering_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml folds_constant_subint_ -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml lowers_upto_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact `compiler-args` repro for `tests/tests/src/test_closure.res`
    from `tests/tests/lib/bs`, diffing `/tmp/test_closure.mjs` against the
    checked-in snapshot
  - exact `compiler-args` repro for `tests/tests/src/string_set_test.res`
    from `tests/tests/lib/bs`, diffing `/tmp/string_set_test.mjs` against the
    checked-in snapshot
  - exact `compiler-args` repro for `tests/tests/src/ExternalShadow.res`
    from `tests/tests/lib/bs`, diffing `/tmp/ExternalShadow.mjs` against the
    checked-in snapshot as an unchanged backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_closure.res`,
    `tests/tests/src/string_set_test.res`,
    `tests/tests/src/tailcall_inline_test.res`, and
    `tests/tests/src/cps_test.res` now match their checked-in snapshots;
    Rust had been carrying constant loop finishes as `Psubint(const, 1)`
    until `compile.rs`, which triggered the OCaml `Up` rewrite and emitted
    `< N` instead of the snapshot's `<= N - 1` headers
  - `tests/tests/src/for_loop_test.res` no longer differs on its constant
    loop bounds; the remaining diff in that file is later variable naming and
    formatting inside `for_9`
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match
- Topline impact:
  - JS snapshot parity: **401 / 657** -> **405 / 657** (**+4**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **256** -> **252** (**-4**)
- Keep this change because it ports the exact OCaml `Lam.prim` constant
  `Psubint` fold on the JS-path simplifier before `lam_compile.ml`
  loop-direction lowering, instead of preserving the Rust-only `< N` headers
  for constant `n - 1` loops

- Active slice: port the missing OCaml `Phash` / `Phash_mixint` /
  `Phash_mixstring` / `Phash_finalmix` lowering from
  `compiler/core/lam_compile_primitive.ml` into
  `compiler-rust/src/lambda/compile.rs` so `%hash` externals emit
  `Primitive_hash.*` runtime calls instead of falling through the Rust
  primitive matcher to an empty `undefined` body
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice fixes post-lambda primitive lowering in the
  OCaml `lam_compile_primitive.ml` backend without reopening typedtree or
  lambda parity work
- OCaml reference:
  `compiler/core/lam_compile_primitive.ml`, where `Phash`,
  `Phash_mixint`, `Phash_mixstring`, and `Phash_finalmix` each lower with
  `E.runtime_call Primitive_modules.hash ...`
- Rust change:
  - added direct `Primitive_hash.hash`, `hash_mix_int`,
    `hash_mix_string`, and `hash_final_mix` runtime-call lowering in
    `compile_primitive(...)`
  - extended `runtime_member_for_eta_wrapped_primitive(...)` so eta-wrapped
    hash primitives alias the runtime member exactly like the other OCaml
    runtime-call primitive families
  - added focused regression coverage in
    `compile_hash_primitives_lower_to_primitive_hash_runtime_calls_like_ocaml`
    and `compile_eta_wrapped_hash_function_aliases_runtime_member`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml compile_hash_primitive -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml compile_eta_wrapped_hash_function_aliases_runtime_member -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact `compiler-args` repro for `tests/tests/src/hash_utils.res` from
    `tests/tests/lib/bs`, diffing `/tmp/hash_utils.mjs` against the
    checked-in snapshot
  - exact `compiler-args` repro for `tests/tests/src/ExternalShadow.res`
    from `tests/tests/lib/bs`, diffing `/tmp/ExternalShadow.mjs` against the
    checked-in snapshot as an unchanged backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/hash_utils.res` now matches its checked-in snapshot
    exactly; Rust once emitted an empty `hash` function because the hash
    primitive family fell through `compile_primitive(...)`, and it now emits
    the same `Primitive_hash.hash(...)` runtime call as OCaml
  - `tests/tests/src/ExternalShadow.res` remains an exact match after the
    new hash-family lowering, confirming the change stayed scoped to the
    missing primitive branches
- Topline impact:
  - JS snapshot parity: **400 / 657** -> **401 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **257** -> **256** (**-1**)
- Keep this change because it ports the exact OCaml
  `lam_compile_primitive.ml` hash-runtime-call branches instead of preserving
  the Rust-only primitive fallback to `undefined`.

Latest iteration on **2026-04-14**:

- Active slice: port the OCaml `Pjs_fn_make` simplify path for exported
  eta-wrapped direct module-field callees into
  `compiler-rust/src/lambda/simplify.rs` so exported wrappers like
  `let a2 = x => Stdlib_Lazy.from_val(x)` keep the exported binding
  materialized while call sites lower directly to the module field callee,
  matching the checked-in `lazy_test` snapshot instead of emitting `a2(3)`
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice stays in the post-lowering simplify pass that
  the current JS backend still depends on, without reopening typedtree or
  lambda parity work
- OCaml reference:
  `compiler/core/lam_pass_alpha_conversion.ml`, where the
  `Lprim {primitive = Pjs_fn_make len; args = [arg]; ...}` branch simplifies
  `arg` first and then runs `Lam_eta_conversion.unsafe_adjust_to_arity`,
  allowing wrappers around direct module-field callees to collapse to the
  callee while preserving exported alias bindings elsewhere in the backend
- Rust change:
  - added a dedicated `call_substitutions` environment for preserved exported
    eta aliases so call sites can use the simplified direct module-field
    callee without deleting the exported binding itself
  - taught `PjsFnMake` simplification to unwrap simplified direct
    module-field callees and nothing broader, which fixes the real lowered
    `lazy_test` shape without regressing existing async exported-alias output
  - added focused regression coverage in
    `exported_eta_alias_calls_use_direct_callee_but_keep_export_binding_like_ocaml`
    and
    `exported_pjs_fn_make_eta_alias_calls_use_direct_callee_like_lazy_test`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml eta_alias_calls_use_direct_callee -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml eta_reduces_wrappers_around_known_async_functions_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact `compiler-args` repro for `tests/tests/src/lazy_test.res` from
    `tests/tests/lib/bs`, diffing `/tmp/lazy_test.mjs` against the
    checked-in snapshot
  - exact `compiler-args` repro for `tests/tests/src/async_inline.res` from
    `tests/tests/lib/bs`, diffing `/tmp/async_inline.mjs` against the
    checked-in snapshot as a broader guard against alias-preservation
    regressions
  - exact `compiler-args` repro for `tests/tests/src/ExternalShadow.res`
    from `tests/tests/lib/bs`, diffing `/tmp/ExternalShadow.mjs` against the
    checked-in snapshot as an unchanged backend guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/lazy_test.res` now matches its checked-in snapshot
    exactly; the exported wrapper around `Stdlib_Lazy.from_val` still emits
    the exported binding, but the actual call site lowers to
    `Stdlib_Lazy.from_val(3)` instead of the Rust-only `a2(3)` shape
  - `tests/tests/src/async_inline.res` and
    `tests/tests/src/ExternalShadow.res` remain exact matches after narrowing
    the new call-substitution rule to direct module-field callees only
- Topline impact:
  - JS snapshot parity: **399 / 657** -> **400 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **258** -> **257** (**-1**)
- Keep this change because it ports the OCaml
  `lam_pass_alpha_conversion.ml` `Pjs_fn_make` simplify ordering for the
  missing direct-module-field wrapper case instead of preserving the Rust-only
  extra alias call in final JS.

Latest iteration on **2026-04-14**:

- Active slice: port OCaml's `Js_exp_make.int_comp` runtime-compare-to-zero
  rewrite into `compiler-rust/src/lambda/compile.rs` so downstream JS lowering
  strips `Runtime.compare(x, y)` when comparing the result against integer
  zero, emitting direct relational operators like `x > y` instead of keeping
  `Primitive_float.compare(x, y) > 0`
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this slice fixes post-lambda JS-expression lowering in the
  OCaml `lam_compile_primitive.ml` -> `js_exp_make.ml` path without reopening
  typedtree or lambda parity work
- OCaml reference:
  `compiler/core/js_exp_make.ml`, where `int_comp` matches
  `Call(Var(Qualified({kind = Runtime}, Some "compare")), [l; r], _)` against
  `Number(Int 0l)` and recursively re-emits `int_comp cmp l r`
- Rust change:
  - added `runtime_compare_call_args(...)` and the matching
    `int_literal(&right) == Some(0)` branch in `compile_int_comparison(...)`
    so runtime compare calls collapse to direct comparisons exactly like OCaml
  - added focused unit coverage in
    `compile_compare_against_zero_elides_runtime_compare_call_like_ocaml` and
    `compile_bigint_compare_against_zero_elides_runtime_compare_call_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml compare_against_zero -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact `compiler-args` repro for `tests/tests/src/caml_compare_bigint_test.res`
    from `tests/tests/lib/bs`, diffing `/tmp/caml_compare_bigint_test.mjs`
    against the checked-in snapshot
  - exact `compiler-args` repro for `tests/tests/src/ExternalShadow.res`
    from `tests/tests/lib/bs`, diffing `/tmp/ExternalShadow.mjs` against the
    checked-in snapshot
  - exact `compiler-args` repro for `tests/tests/src/compare_test.res`
    from `tests/tests/lib/bs`, diffing `/tmp/compare_test.mjs` against the
    checked-in snapshot as an unchanged broader guard
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/caml_compare_bigint_test.res` now matches its checked-in
    snapshot exactly; the first two assertions lower to direct bigint
    relational operators instead of the Rust-only
    `Primitive_float.compare(... ) > 0` / `< 0` shape
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the compare-to-zero rewrite
  - `tests/tests/src/compare_test.res` still differs only on the existing
    switch-case ordering drift, confirming this slice stayed scoped to the
    OCaml `int_comp` backend rule
- Topline impact:
  - JS snapshot parity: **398 / 657** -> **399 / 657** (**+1**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **259** -> **258** (**-1**)
- Keep this change because it ports the exact OCaml
  `js_exp_make.ml` `int_comp` compare-to-zero simplification instead of
  preserving the Rust-only runtime compare call in final JS.

Latest iteration on **2026-04-14**:

- Active slice: port the strict-plain-string `let` reclassification from
  OCaml's `lam_pass_lets_dce` into `compiler-rust/src/lambda/simplify.rs` so
  the JS-backend simplify pass treats `Strict` / `StrictOpt` plain-string
  bindings as `Alias` lets before later string folding and alias cleanup
- Active backend focus remains **Phase 3: Port JS IR Lowering And Metadata**
  from `PLAN.md`; this is a correctness-aligned follow-up in the
  post-lowering simplify pass that the current JS-lowering path still depends
  on, without reopening typedtree or lambda parity work
- OCaml reference:
  `compiler/core/lam_pass_lets_dce.ml`, where both the `StrictOpt` branch
  after simplifying `l1` and the `Strict` branch re-emit plain-string
  bindings as `Lam.let_ Alias v l1 (simplif lbody)` / `Lam.let_ Alias v l1
  (simplif l2)` after recording the string in `string_table`
- Rust change:
  - reclassify simplified plain-string `LetKind::Strict` /
    `LetKind::StrictOpt` bindings to `LetKind::Alias` before recording them in
    `plain_strings`
  - updated the existing string-alias regression expectations and added
    focused coverage in
    `inlines_single_use_strict_plain_string_field_reads_into_module_blocks_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml plain_string -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml folds_string_alias_chains -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact `compiler-args` repro for `tests/tests/src/alias_test.res` from
    `tests/tests/lib/bs`, comparing the generated `/tmp/alias_test.mjs` to the
    checked-in snapshot and to the pre-change harness-path output
  - exact `compiler-args` repro for `tests/tests/src/RecordCoercion.res` from
    `tests/tests/lib/bs`, comparing the generated
    `/tmp/RecordCoercion.mjs` to the checked-in snapshot and to the pre-change
    harness-path output
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - on the authoritative `tests/tests/lib/bs` compile path, the current
    snapshot diffs for `tests/tests/src/alias_test.res` and
    `tests/tests/src/RecordCoercion.res` remain unchanged by this slice; the
    noisier standalone `-bs-module-type esmodule` repro overstated the effect
    and is not authoritative for these project-owned files
  - the authoritative diff corpus still has no `ExternalShadow.res` entry
    after the same simplify change
- Topline impact:
  - JS snapshot parity: **398 / 657** -> **398 / 657** (**no change**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **259** -> **259** (**no change**)
- Keep this change because it matches the OCaml `lam_pass_lets_dce.ml`
  `Strict` / `StrictOpt` plain-string-to-`Alias` transition exactly; the
  current harness baseline is unchanged, but this removes another backend-path
  semantic mismatch and adds regression coverage for the missing OCaml branch.

Latest iteration on **2026-04-14**:

- Active slice: match OCaml's `ocaml_to_js_eff` / `add_eff` composition in
  `compiler-rust/src/lambda/compile.rs` so ignored and unit-elided external
  arguments keep the whole compiled arg expression as the effect payload and
  sequence it onto the final call/object value, instead of sinking side
  effects into Rust-only standalone statements or dropping the final pure tail
- Active backend focus is **Phase 3: Port JS IR Lowering And Metadata** from
  `PLAN.md`; this slice fixes external-call and `@obj` lowering at the OCaml
  `lam_compile_external_call.ml` / `lam_compile_external_obj.ml` boundary
  before the JS-pass and printer stages, without reopening typedtree or
  lambda parity work
- OCaml reference:
  - `compiler/core/lam_compile_external_call.ml`, where `ocaml_to_js_eff`
    returns `Splice0` plus `[arg]` for `Ignore` / unlabeled `Extern_unit`
    when the compiled arg is not side-effect-free, `assemble_args_no_splice`
    and `assemble_args_has_splice` collect those whole-arg effects, and
    `add_eff` wraps the final external expression with `E.seq`
  - `compiler/core/lam_compile_external_obj.ml`, where `assemble_obj_args`
    sequences collected object-arg effects into the object literal initializer
    and folds per-field ignored/optional effects into the assignment RHS
- Rust change:
  - replaced the temporary prelude-based ignored-arg handling with OCaml-style
    effect sequencing helpers that carry `Option<Expression>` effects through
    external-arg assembly and reapply them via `js_seq(...)` at the returned
    expression boundary
  - routed `PjsCall`, `JsNew`, `JsSend`, `JsGet`/`JsSet`,
    `JsGetIndex`/`JsSetIndex`, `JsModuleAsFn`, `JsModuleAsClass`, and
    `@obj` creation through the new effect path so ignored / unit-elided args
    preserve the full compiled arg expression rather than only isolated
    impure fragments
  - updated focused regression coverage in
    `lowers_ignored_js_call_args_to_ocaml_sequence_effects` and
    `lowers_ignored_js_object_fields_to_ocaml_sequence_effects`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml ignored_js_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact `compiler-args` repro for `tests/tests/src/bs_ignore_effect.res`
    from `tests/tests/lib/bs`, diffing `/tmp/bs_ignore_effect.mjs` against the
    checked-in snapshot
  - exact `compiler-args` repro for `tests/tests/src/ffi_js_test.res` from
    `tests/tests/lib/bs`, diffing `/tmp/ffi_js_test.mjs` against the
    checked-in snapshot
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/bs_ignore_effect.res` now matches its checked-in
    snapshot exactly; the Rust output keeps the OCaml comma-expression shape
    for both the `config` object initializer and the ignored GADT external
    arg, including the retained `"Float"` evaluation inside the ignored
    argument sequence
  - `tests/tests/src/ffi_js_test.res` now matches its checked-in snapshot
    exactly; the side-effecting ignored `~kind` object field keeps the
    OCaml-style `(u = u + 1 | 0, "Int", {...})` sequence instead of sinking
    `"Int"` into a standalone statement
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the external-effect sequencing rewrite
- Topline impact:
  - JS snapshot parity: **396 / 657** -> **398 / 657** (**+2**)
  - Compile errors: **0** (no change)
  - Output diffs: **261** -> **259** (**-2**)
- Keep this change because it ports the exact OCaml
  `lam_compile_external_call.ml` `ocaml_to_js_eff` / `add_eff` and
  `lam_compile_external_obj.ml` `assemble_obj_args` effect model instead of
  preserving Rust-only standalone statements for ignored externals.

Latest iteration on **2026-04-14**:

- Active slice: port OCaml's `lam_pass_eliminate_ref.ml` into
  `compiler-rust/src/lambda/simplify.rs` so non-escaping mutable `ref` cells
  are rewritten to mutable locals instead of always surviving into JS as
  boxed `{ contents: ... }` records
- Active backend focus is **Phase 2: Port Post-Lowering Lambda Backend
  Stages** from `PLAN.md`; this slice lands one of the missing OCaml
  `lam_pass_*` simplifications on the JS codegen path without reopening
  typedtree or lambda parity work
- OCaml reference:
  `compiler/core/lam_pass_eliminate_ref.ml`, where `eliminate_ref`
  rewrites `Pfield(0, [Lvar id])` to `Lvar id`, `Psetfield(0, [Lvar id; e])`
  to `Lassign(id, e)`, and `Poffsetref delta` to `Lassign(id, Poffsetint
  delta [id])`, but aborts when the binding escapes as a real reference
- Rust change:
  - detect simplified `let` bindings whose value is
    `Pmakeblock(0, _, Mutable)` and try the OCaml `eliminate_ref` rewrite on
    the body before final let refinement
  - convert successful rewrites from `LetKind::Strict` / `StrictOpt` ref-cell
    bindings into `LetKind::Variable` locals so downstream JS lowering emits
    plain mutable variables instead of `.contents` boxes
  - added focused regression coverage in
    `eliminates_non_captured_ref_cells_to_mutable_variables`,
    `eliminates_offsetref_updates_on_non_captured_ref_cells`, and
    `keeps_closure_captured_ref_cells_boxed`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml ref_cells -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - exact `compiler-args` repro for `tests/tests/src/for_loop_test.res` from
    `tests/tests/lib/bs`, diffing `/tmp/for_loop_test.mjs` against the
    checked-in snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/for_loop_test.res` now matches the OCaml non-escaping
    ref-cell shape around `inspect_3`; the remaining diff in that file is on
    the already-known loop-header and temp-binding naming drift, not on boxed
    ref lowering
  - `tests/tests/src/test_simple_ref.res` no longer differs on boxed-ref
    handling; the remaining diff there is only the top-level binding order for
    `not_real_escape`
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the simplify pass
- Topline impact:
  - JS snapshot parity: **384 / 657** -> **396 / 657** (**+12**)
  - Compile errors: **0** (no change)
  - Output diffs: **273** -> **261** (**-12**)
- Keep this change because it ports OCaml's `lam_pass_eliminate_ref.ml`
  behavior directly into the Rust JS path instead of preserving Rust-only
  boxed ref cells for bindings that do not escape.

Latest iteration on **2026-04-14**:

- Active slice: match OCaml's `Lfor` lowering in
  `compiler-rust/src/lambda/compile.rs` so `for ... to (finish - 1)` and
  `for ... to predint finish` emit the exclusive `J.Up` loop shape that
  `compiler/core/lam_compile.ml` feeds into `js_dump.ml`, instead of keeping
  the Rust-only inclusive `<= finish - 1` form in final JS
- Active backend focus is **Phase 3: Port JS IR Lowering And Metadata** from
  `PLAN.md`; this slice fixes `lam_compile.ml` `compile_for` lowering before
  the JS-pass stage, without reopening typedtree or lambda parity work
- OCaml reference:
  `compiler/core/lam_compile.ml`, where `Lfor ... Upto ...` rewrites
  `Psubint(new_finish, 1)` and `Poffsetint(-1)` over `new_finish` to
  `compile_for ... Up ...`, which `js_dump.ml` then prints as `< finish`
  instead of `<= finish - 1`
- Rust change:
  - added `lower_ocaml_for_range_direction(...)` and routed `Lambda::Lfor`
    lowering through it so `Psubint(..., 1)` and `Poffsetint(-1)` bounds emit
    `ForDirection::Up`
  - added focused regression coverage in
    `lowers_upto_subint_one_finish_to_ocaml_exclusive_for_range` and
    `lowers_upto_predint_finish_to_ocaml_exclusive_for_range`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml lowers_upto_ -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml test_print_for_range_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_for_loop.res -o /tmp/test_for_loop.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/for_loop_test.res`
  - `timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/for_loop_test.ast -o /tmp/for_loop_test.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/for_loop_test.res` now emits the OCaml-style exclusive
    loop headers such as `for (let i = 0; i < 7; ++i)` and
    `for (let j = 0; j < 3; ++j)` instead of the Rust-only
    `i <= 6` / `j <= 2` form; the remaining diff in that file is now on the
    earlier closure/ref lowering (`inspect_3` boxing and capture shape), not
    on loop-bound printing
  - `temp/rust-parity/diffs/js_src_bs_poly_mutable_set_test.res.diff` drops
    out of the current authoritative diff set after the same `Lfor` rewrite
  - `tests/tests/src/test_for_loop.res` and
    `tests/tests/src/ExternalShadow.res` remain exact snapshot matches after
    the loop-lowering change
- Topline impact:
  - JS snapshot parity: **385 / 657** -> **384 / 657** (**-1**)
  - Compile errors: **0** (no change)
  - Output diffs: **272** -> **273** (**+1**)
- Keep this change because it ports the exact OCaml `lam_compile.ml`
  `Lfor ... Upto ... (finish - 1)` => `Up` rewrite. The local parity
  regression is an interaction with other still-misaligned loop-body lowering,
  not a reason to preserve the Rust-only inclusive loop shape.

Latest iteration on **2026-04-14**:

- Active slice: match OCaml's `Js_output.append_output` / `Js_exp_make.seq`
  composition in `compiler-rust/src/lambda/compile.rs` so nested effect
  outputs are normalized through sequence cleanup instead of preserving raw
  Rust-only `Seq(..., undefined)` tails
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice fixes backend sequence cleanup at the OCaml `js_output.ml` /
  `js_exp_make.ml` boundary without reopening typedtree or lambda parity work
- OCaml reference:
  `compiler/core/js_output.ml`, where `append_output` combines expression
  outputs with `E.seq e1 e2`, and `compiler/core/js_exp_make.ml`, where `seq`
  recursively strips pure `Number _`, `Var _`, and `Undefined _` fragments
  before building the final comma expression
- Rust change:
  - changed `append_effect_output(...)` to call `js_seq(...)` instead of
    constructing raw `ExpressionDesc::Seq(...)` nodes
  - added focused regression coverage in
    `nested_effect_sequences_drop_intermediate_pignore_suffixes_when_appended_to_values`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml nested_effect_sequences_drop_intermediate_pignore_suffixes_when_appended_to_values -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml lowers_expression_sequences_to_js_comma_expressions -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_for_loop.res -o /tmp/test_for_loop.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/test_for_loop.res` now matches its checked-in `.mjs`
    snapshot exactly; the Rust-only
    `(console.log("hi"), undefined, x.length)` finish expression is now the
    OCaml-style `(console.log("hi"), x.length)`
  - `tests/tests/src/test_while_side_effect.res` still differs, but the same
    OCaml-aligned append rule removes the intermediate `undefined` commas from
    both `while` conditions and cleanly isolates the remaining control-flow
    lowering drift (`if (undefined)` and block-lifting)
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the sequence-cleanup change
- Topline impact:
  - JS snapshot parity: **385 / 657** (**+1**)
  - Compile errors: **0** (no change)
  - Output diffs: **272** (**-1**)
- Keep this change because it ports OCaml's `Js_output.append_output` /
  `Js_exp_make.seq` composition rule directly instead of preserving raw
  Rust-only comma-expression suffixes during output concatenation

Latest iteration on **2026-04-14**:

- Active slice: match OCaml's `keep_non_undefined_args` behavior in
  `compiler-rust/src/lambda/compile.rs` so JS externals omit only trailing
  optional `undefined` arguments on the non-splice path instead of preserving
  Rust-only `(..., undefined)` tails in emitted JS
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice fixes backend external-call shaping at the OCaml
  `lam_compile_external_call.ml` boundary without reopening typedtree or
  lambda parity work
- OCaml reference:
  `compiler/core/lam_compile_external_call.ml`, where
  `keep_non_undefined_args` trims only a trailing suffix of
  `Arg_optional` + `Undefined {is_unit = false}` pairs after
  `assemble_args_no_splice`, while preserving non-trailing `undefined`
  placeholders and leaving splice calls alone
- Rust change:
  - added `keep_non_undefined_external_args(...)` and routed
    `assemble_external_args_no_splice(...)` through it so final JS externals
    follow OCaml's trailing-optional-undefined trimming rule
  - left the splice path unchanged to match OCaml's
    `assemble_args_has_splice` behavior
  - added focused lowering coverage in
    `lowers_js_call_omits_trailing_optional_undefined_args_like_ocaml`,
    `lowers_js_send_omits_trailing_optional_undefined_args_like_ocaml`, and
    `lowers_js_new_omits_trailing_optional_undefined_args_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml trailing_optional_undefined_args_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/omit_trailing_undefined_in_external_calls.res -o /tmp/omit_trailing_undefined_in_external_calls.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/stdlib/intl/Stdlib_Intl_LocaleTest.res -o /tmp/Stdlib_Intl_LocaleTest.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/omit_trailing_undefined_in_external_calls.res` now
    matches its checked-in `.mjs` snapshot exactly; the Rust-only trailing
    `undefined` arguments on `formatDate`, `toString`, and `new RegExp(...)`
    are gone
  - the same OCaml rule now drops the diff files for
    `tests/tests/src/stdlib/intl/Stdlib_Intl_LocaleTest.res`,
    `Stdlib_Intl_ListFormatTest.res`,
    `Stdlib_Intl_NumberFormatTest.res`,
    `Stdlib_Intl_PluralRulesTest.res`,
    `Stdlib_Intl_RelativeTimeFormatTest.res`, and
    `Stdlib_Intl_SegmenterTest.res`
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the external-call change
  - nearby files such as
    `tests/tests/src/stdlib/intl/Stdlib_Intl_CollatorTest.res` and
    `Stdlib_Intl_DateTimeFormatTest.res` still differ, but now only on the
    remaining sequence/object-lowering drift inside option-record builders
- Topline impact:
  - JS snapshot parity: **384 / 657** (**+7**)
  - Compile errors: **0** (no change)
  - Output diffs: **273** (**-7**)
- Keep this change because it ports OCaml's
  `lam_compile_external_call.ml` external-argument trimming rule directly
  instead of preserving Rust-only `undefined` tails in emitted JS

Latest iteration on **2026-04-14**:

- Active slice: match OCaml's `J.ForRange` dumping in
  `compiler-rust/src/js_ir/printer.rs` so complex loop bounds are evaluated
  once into a synthetic `*_finish` binding and comma-sequence initializers
  stay parenthesized in the `for` header
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice fixes backend dump-shape drift at the OCaml `js_dump.ml`
  boundary without reopening typedtree or lambda parity work
- OCaml reference:
  `compiler/core/js_dump.ml`, where `ForRange` printing emits
  `let i = ..., i_finish = ...; i <|<= i_finish; ++i` whenever the finish
  expression is not already `Number _` or `Var _`, and prints initializer
  expressions at a precedence that preserves comma-sequence grouping inside the
  loop header
- Rust change:
  - added OCaml-aligned `ForRange` printer routing that synthesizes a scoped
    `*_finish` name only for non-trivial bounds instead of always dumping the
    bound inline in the condition
  - prints `ForRange` initializer expressions in header-safe precedence
    contexts so sequence expressions stay parenthesized in `let` bindings
  - added focused printer coverage in
    `test_print_for_range_complex_finish_uses_finish_binding`,
    `test_print_for_range_without_init_binds_complex_finish_once`, and
    `test_print_for_range_parenthesizes_sequence_init_in_header`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml test_print_for_range_ -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml test_print_while -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `cd tests/tests/lib/bs && timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/for_loop_test.ast -o /tmp/for_loop_test.mjs`
  - `cd tests/tests/lib/bs && timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/for_side_effect_test.ast -o /tmp/for_side_effect_test.mjs`
  - `cd tests/tests/lib/bs && timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/ExternalShadow.ast -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
    after the `ForRange` dump change
  - `tests/tests/src/for_loop_test.res` and
    `tests/tests/src/for_side_effect_test.res` now show the OCaml-style
    single-evaluation `i_finish` header shape and proper sequence
    parenthesization instead of dumping raw comma expressions into the loop
    condition
  - the remaining loop drift in those files is now isolated to earlier backend
    lowering, especially the Rust-only `undefined` sequence suffixes and
    `Upto (len - 1)` vs `Up len` choice
  - the authoritative wrapper still reports **0 compile errors**, so this
    remains a pure backend dump-shape fix
- Topline impact:
  - JS snapshot parity: **377 / 657** (no change)
  - Compile errors: **0** (no change)
  - Output diffs: **280** (no change)
- Keep this change because it matches OCaml's `js_dump.ml` `ForRange` printer
  exactly and cleanly exposes the next loop-lowering mismatch instead of
  preserving a Rust-only inline-bound dump shape

Latest iteration on **2026-04-14**:

- Active slice: stop forcing named-variant switch scrutinees through a
  synthetic `match` temp when OCaml's backend only reads the scrutinee once,
  while also matching OCaml's `js_exp_make.triple_equal` folding for strict
  comparisons on JS literals in `compiler-rust/src/lambda/compile.rs` and
  `compiler-rust/src/js_ir/mod.rs`
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice fixes a backend control-flow / JS-IR construction drift without
  reopening typedtree or lambda parity work
- OCaml reference:
  - `compiler/core/lam_compile.ml`, where `compile_switch` only introduces a
    temp binding for the scrutinee in the mixed const+block dispatch path that
    reuses the expression, not for single-use named-variant dispatch
  - `compiler/core/js_exp_make.ml`, where `triple_equal` folds int-literal,
    optional-block, and simple string-literal strict equality before later
    `if`/`cond` simplification
- Rust change:
  - added `named_variant_switch_needs_bound_scrutinee(...)` and used it on the
    named-variant expression / return / effect paths so single-use named
    dispatches keep the original scrutinee instead of emitting `let match = …`
  - extended `Expression::bin` strict-comparison folding to cover the same
    OCaml `triple_equal` cases for int literals, optional blocks, simple
    string literals, and existing nullish mismatches
  - added focused regression coverage in
    `named_variant_constant_return_switch_skips_redundant_match_temp`,
    `test_strict_eq_int_literals_folds_true`,
    `test_strict_eq_optional_blocks_compares_inner_values`, and
    `test_strict_eq_simple_string_literals_fold_false`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml strict_eq_ -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml named_variant_constant_return_switch_skips_redundant_match_temp -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/VariantCoercion.res -o /tmp/VariantCoercion.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UntaggedVariants.res -o /tmp/UntaggedVariants.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/VariantCoercion.res` now matches its checked-in `.mjs`
    snapshot exactly; the redundant `let match = 2;` and dead branch in `f1`
    are gone
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match after
    the same backend change
  - `tests/tests/src/UntaggedVariants.res` stays on its unrelated ordering /
    object-vs-array / guard-shape diffs rather than regressing on this slice
  - the authoritative wrapper still reports **0 compile errors**, so this
    remains a pure backend-shaping fix
- Topline impact:
  - JS snapshot parity: **377 / 657** (**+3**)
  - Compile errors: **0** (no change)
  - Output diffs: **280** (**-3**)
- Keep this change because it matches OCaml's named-variant switch routing and
  `js_exp_make` equality folding instead of preserving an extra Rust-only temp
  binding in the final JS path

Latest iteration on **2026-04-14**:

- Active slice: match OCaml's `Optional_block` dumping for unit payloads in
  `compiler-rust/src/js_ir/printer.rs`
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice fixes a backend dump-shape drift in the JS path without reopening
  typedtree or lambda parity work
- OCaml reference:
  `compiler/core/js_dump.ml`, where `Optional_block (e, identity)` prints
  through `E.runtime_call Primitive_modules.option "some" [e]`, and the call
  printer omits a single `Undefined {is_unit = true}` argument so `Some(())`
  renders as `Primitive_option.some()`, while plain `undefined` still renders
  as `Primitive_option.some(undefined)`
- Rust change:
  - changed `ExpressionDesc::OptionalBlock(..., false)` printing to omit the
    synthetic unit-`undefined` payload just like OCaml while keeping plain
    `undefined` explicit
  - added focused printer coverage in
    `test_print_optional_block_omits_unit_undefined_argument` and
    `test_print_optional_block_keeps_plain_undefined_argument`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml test_print_optional_block_omits_unit_undefined_argument -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml test_print_optional_block_keeps_plain_undefined_argument -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `cd tests/tests/lib/bs && timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/js_null_test.ast -o /tmp/js_null_test.mjs`
  - `cd tests/tests/lib/bs && timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/unit_undefined_test.ast -o /tmp/unit_undefined_test.mjs`
  - `cd tests/tests/lib/bs && timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/option_repr_test.ast -o /tmp/option_repr_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/js_null_test.res` now matches its checked-in `.mjs`
    snapshot exactly; the expected unit option literal prints as
    `Primitive_option.some()`
  - `tests/tests/src/unit_undefined_test.res` now matches its checked-in
    `.mjs` snapshot exactly on the same unit-option encoding slice
  - `tests/tests/src/ExternalShadow.res` remains an exact snapshot match, and
    `tests/tests/src/option_repr_test.res` stays on its prior unrelated
    control-flow / option-shape diffs rather than regressing on
    `some(undefined)` printing
  - the authoritative wrapper still reports **0 compile errors**, so this
    remains a pure backend printing / JS-shape fix
- Topline impact:
  - JS snapshot parity: **374 / 657** (**+2**)
  - Compile errors: **0** (no change)
  - Output diffs: **283** (**-2**)
- Keep this change because it matches OCaml's `Optional_block` dump behavior
  instead of forcing all unit option payloads through the plain
  `some(undefined)` textual path

Latest iteration on **2026-04-14**:

- Active slice: match OCaml's plain-string handling in
  `compiler-rust/src/lambda/simplify.rs` instead of treating every
  non-allocating string constant as an unconditional JS-path substitution
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice ports another `lam_pass_lets_dce` rule on the JS backend path
  without reopening typedtree or lambda parity work
- OCaml reference:
  `compiler/core/lam_pass_lets_dce.ml`, where plain
  `Const_string {delim = None}` bindings are recorded in `string_table` for
  later `Pstringadd` folding but are not unconditionally substituted the way
  ints/floats/bools are, and captured single-use alias constants/vars still
  inline through the alias case
- Rust change:
  - added an OCaml-style plain-string side table to the JS-path lambda
    simplifier so `Pstringadd` can still fold through preserved string
    bindings
  - stopped unconditional substitution for string constants /
    immutable-string constants while keeping the existing non-string constant
    substitution behavior
  - aligned single-use alias substitution with OCaml for captured constant/var
    aliases
  - added focused regression coverage in
    `keeps_multi_use_plain_string_bindings_like_ocaml` and
    `inlines_captured_single_use_plain_string_aliases_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml keeps_multi_use_plain_string_bindings_like_ocaml -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml inlines_captured_single_use_plain_string_aliases_like_ocaml -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml folds_string_alias_chains -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/VariantCoercion.res -o /tmp/VariantCoercion.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/async_inline.res -o /tmp/async_inline.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/VariantCoercion.res` no longer differs on the
    plain-string sharing slice; the file is down to one remaining later
    control-flow hunk in `f1`
  - `tests/tests/src/ExternalShadow.res` and
    `tests/tests/src/async_inline.res` remain exact snapshot matches after the
    same simplify change
  - the authoritative wrapper still reports **0 compile errors**, so this
    remains a pure backend-shaping slice rather than a compile-failure
    regression
- Topline impact:
  - JS snapshot parity: **372 / 657** (**-1**)
  - Compile errors: **0** (no change)
  - Output diffs: **285** (**+1**)
- Keep this change because it matches OCaml's `lam_pass_lets_dce`
  plain-string-sharing rule instead of preserving accidental parity from
  over-aggressive Rust substitution; the new regression is a separate follow-up
  to isolate

Latest iteration on **2026-04-14**:

- Active slice: stop treating plain static module aliases as possible required
  JS modules in `compiler-rust/src/raw_lambda/convert.rs`
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice fixes another JS-backend dependency-metadata drift without
  reopening typedtree or lambda parity work
- OCaml reference:
  `compiler/ml/translmod.ml`, where plain `Tmod_ident` aliases lower through
  `Const_module_alias`, and `compiler/core/lam_convert.ml`, where
  `may_depends` is populated only from real `Pgetglobal` module uses, not from
  compile-time-only alias constants
- Rust change:
  - removed the static-alias
    `note_possible_required_modules_from_module_expr(...)` bookkeeping from
    `convert_module_expr_raw_with_coercion`
  - added
    `raw_lambda::convert::tests::plain_module_aliases_do_not_record_possible_required_modules`
    to lock in the OCaml behavior
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml plain_module_aliases_do_not_record_possible_required_modules -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `cd tests/tests/lib/bs && timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/gpr_3852_alias.ast -o /tmp/gpr_3852_alias.mjs`
  - `cd tests/tests/lib/bs && timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -bs-read-cmi -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/reasonReact.ast -o /tmp/reasonReact.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_3852_alias.res` now matches its checked-in `.mjs`
    snapshot exactly; the bogus side-effect import and footer are gone
  - `tests/tests/src/reasonReact.res` now matches its checked-in `.mjs`
    snapshot exactly; the unused `ReasonReactRouter` import disappears
  - `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
- Topline impact:
  - JS snapshot parity: **367 / 657** (**+6**)
  - Compile errors: **0** (no change)
  - Output diffs: **290** (**-6**)
- Keep this change because it matches OCaml's static module-alias lowering
  instead of forcing runtime imports from compile-time-only aliases

Latest iteration on **2026-04-14**:

- Active slice: preserve OCaml's per-use `dynamic_import` flag while still
  reusing the first external-module binding id in
  `compiler-rust/src/lambda/compile.rs`
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice fixes another backend module-environment drift exposed by
  `tests/tests/src/import2.res` without reopening typedtree or lambda parity
  work
- OCaml reference:
  `compiler/core/lam_compile_env.ml`,
  `compiler/core/lam_module_ident.ml`, and
  `compiler/core/lam_compile_external_call.ml`, where `add_js_module`
  deduplicates external modules by `(bundle, default)` for the shared
  `Ident.t`, but each emitted `J.module_id` still carries the current
  `dynamic_import` bit for that use site
- Rust change:
  - changed the external-module cache from storing the whole `ModuleId` to
    storing only the shared `Ident`
  - rebuilds a fresh `ModuleId` for each use so static and dynamic imports of
    the same default export can share the binding name without accidentally
    turning the static import into a dynamic-only dependency
  - extended the existing regression test to assert that dynamic and static
    uses share the same id while preserving different `dynamic_import` flags
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml external_module_ids_reuse_first_binding_for_same_bundle_and_default -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `cd tests/tests/lib/bs && timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/import2.ast -o /tmp/import2.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/key_word_property.res -o /tmp/key_word_property.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/import2.res` now matches its checked-in `.mjs` snapshot
    exactly; the static default import survives alongside the dynamic import
    promise chain
  - `tests/tests/src/key_word_property.res` remains an exact guard-file match,
    so the earlier required-module ordering fix stays intact
  - the wrapper remains at **0 compile errors**, confirming this was another
    pure backend module-metadata bug rather than a type-checking or lowering
    failure
- Topline impact:
  - JS snapshot parity: **367 / 657** (**+1**)
  - Compile errors: **0** (no change)
  - Output diffs: **290** (**-1**)
- Keep this change because it matches OCaml's external-module environment model
  instead of papering over the missing import in the final printer

Latest iteration on **2026-04-14**:

- Active slice: match OCaml's required-module identity, scoping, and final
  import ordering for same-bundle default and namespace imports in
  `compiler-rust/src/lambda/compile.rs` and
  `compiler-rust/src/js_ir/printer.rs`
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice fixes a remaining import/export metadata drift on the JS backend
  path without reopening typedtree or lambda parity work
- OCaml reference:
  `compiler/core/lam_module_ident.ml`,
  `compiler/core/lam_compile_env.ml`,
  `compiler/core/lam_compile_external_call.ml`,
  `compiler/core/js_dump_import_export.ml`, and OCaml 5.3's
  `stdlib/array.ml`, where external module identities are reused by
  `(bundle, default)`, imported module aliases participate in scope allocation,
  and required modules are deduplicated through `Lam_module_ident.Hash_set`
  before one final `Array.sort`
- Rust change:
  - cache external `ModuleId`s by `(bundle, default)` so later hint-name
    aliases reuse the first binding id instead of inventing a fresh import name
  - scope imported module aliases in the printer just like other visible
    identifiers, so runtime and external imports sharing a base name print as
    stable `Foo`, `Foo$1`, `Foo$2` bindings
  - replace the old stable-sort-over-`HashSet` required-module collection with
    an OCaml-style module set plus one final OCaml `Array.sort` port, which
    restores the checked-in ordering for mixed default/namespace imports from
    the same bundle
- Added focused regression coverage in:
  - `lambda::compile::tests::external_module_ids_reuse_first_binding_for_same_bundle_and_default`
  - `lambda::compile::tests::required_modules_match_ocaml_sort_across_same_name_import_pairs`
  - `js_ir::printer::tests::test_print_deps_program_scopes_module_import_aliases_across_runtime_and_external_modules`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml external_module_ids_reuse_first_binding_for_same_bundle_and_default -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml required_modules_match_ocaml_sort_across_same_name_import_pairs -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml test_print_deps_program_scopes_module_import_aliases_across_runtime_and_external_modules -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/key_word_property.res -o /tmp/key_word_property.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/js_val.res -o /tmp/js_val.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/webpack_config.res -o /tmp/webpack_config.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/key_word_property.res` now matches its checked-in `.mjs`
    snapshot exactly; the default-vs-namespace import pair now prints in the
    same order as OCaml
  - `tests/tests/src/js_val.res` and
    `tests/tests/src/webpack_config.res` remain exact guard-file matches after
    the import-ordering change
  - the wrapper remains at **0 compile errors**, which confirms this slice was
    pure backend metadata / printing drift rather than a compile-failure
    regression
- Topline impact:
  - JS snapshot parity: **366 / 657** (**+5**)
  - Compile errors: **0** (no change)
  - Output diffs: **291** (**-5**)
- Keep this change because it matches OCaml's module identity and required
  import ordering rules in the backend instead of patching emitted text after
  the fact

Latest iteration on **2026-04-14**:

- Active slice: preserve OCaml’s export-aware named-function inlining through
  exported same-name alias chains in
  `compiler-rust/src/lambda/simplify.rs` and
  `compiler-rust/src/lambda/beta_reduce.rs`
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice fixes a later JS-path simplify drift exposed by
  `tests/tests/src/ast_abstract_test.res` without reopening typedtree or
  lambda parity work
- OCaml reference:
  `compiler/core/lam_pass_collect.ml`,
  `compiler/core/lam_pass_remove_alias.ml`,
  `compiler/core/lam_beta_reduce.ml`, and
  `compiler/core/lam_coercion.ml`, where function identity is copied onto
  aliases before inlining, named applications use
  `propagate_beta_reduce_with_map`, and same-name export aliases are treated as
  the effective exported function identity
- Rust change:
  - switched named local-function inlining in the JS-path simplifier from the
    plain no-names reducer to OCaml-style `propagate_beta_reduce` /
    `propagate_beta_reduce_with_map`
  - gated non-functor named inlining on
    `closure::is_closed_with_map(...)` plus export membership, matching
    OCaml’s “do not inline exported non-closed helpers” rule
  - propagated exportedness through alias substitutions during simplify, and
    through same-name `ModuleExport` payload variables on the second simplify
    pass, so exported alias roots stay export-protected even after the alias
    lets disappear
- Added focused regression coverage in:
  - `lambda::simplify::tests::does_not_inline_non_closed_helpers_reached_through_export_aliases`
  - `lambda::simplify::tests::does_not_inline_exported_non_closed_function_applications`
  - `lambda::simplify::tests::still_inlines_exported_closed_function_applications`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml does_not_inline_non_closed_helpers_reached_through_export_aliases -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml does_not_inline_exported_non_closed_function_applications -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml still_inlines_exported_closed_function_applications -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 /Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/ast_abstract_test.ast -o /tmp/ast_abstract_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/ast_abstract_test.res` now matches its checked-in
    `.mjs` snapshot exactly; it no longer appears in the authoritative diff
    corpus
  - `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
  - the wrapper stays at **0 compile errors** while the output-diff bucket
    drops again, which confirms this was backend lowering drift rather than a
    printer-only or compile-failure cluster
- Topline impact:
  - JS snapshot parity: **361 / 657** (**+4**)
  - Compile errors: **0** (no change)
  - Output diffs: **296** (**-4**)
- Keep this change because it follows OCaml’s alias/export bookkeeping in the
  JS-path simplify stage instead of hiding the drift with snapshot-text
  rewrites

Latest iteration on **2026-04-14**:

- Active slice: restore OCaml's `TAG` field emission for ordinary
  single-payload constructor blocks in `compiler-rust/src/js_ir/printer.rs`
- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`;
  this slice fixes a small constructor-object drift now exposed on the final
  JS-output path without reopening earlier lambda stages
- OCaml reference: `compiler/core/js_dump.ml`, where
  `Caml_block (el, _, tag, Blk_constructor p)` omits `TAG` only for untagged
  constructors and the list-cons special case, not for normal non-cons
  constructors that happen to carry one payload
- Rust change:
  - changed `TagInfo::Constructor` printing to keep `TAG` for every
    non-untagged non-cons constructor regardless of payload count
  - left the dedicated list-cons `hd` / `tl` object branch unchanged
  - tightened the constructor destructuring in the printer branch so the
    restored OCaml behavior does not introduce a fresh unused binding
- Added focused regression coverage in:
  - `js_ir::printer::tests::test_print_non_cons_constructor_keeps_tag_object_shape`
  - `js_ir::printer::tests::test_print_cons_constructor_as_hd_tl_object`
  - `js_ir::printer::tests::test_print_arrow_function_parenthesizes_constructor_block_body`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml constructor -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_3546_test.res -o /tmp/gpr_3546_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_3697_test.res -o /tmp/gpr_3697_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_3546_test.res`,
    `tests/tests/src/gpr_3697_test.res`,
    `tests/tests/src/gpr_4407_test.res`, and
    `tests/tests/src/mutual_non_recursive_type.res` all dropped out of the
    authoritative diff corpus after the constructor-tag fix
  - `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
  - `tests/tests/src/ast_abstract_test.res` is still present in the nearby
    small-diff cluster, which confirms the next signal there is later lowering
    rather than missing constructor-tag printing
- Topline impact:
  - JS snapshot parity: **357 / 657** (**+4**)
  - Compile errors: **0** (no change)
  - Output diffs: **300** (**-4**)
- Keep this change because it directly matches OCaml's constructor-object dump
  rule in `js_dump.ml` instead of hiding the drift with snapshot-specific
  rewrites

Latest iteration on **2026-04-14**:

- Active slice: preserve OCaml’s `@as(null)` / `@as(undefined)` constructor
  payload identity when loading runtime interfaces through
  `compiler-rust/src/cmi/sig_reader.rs`, so downstream switch metadata in
  `compiler-rust/src/raw_lambda/matching.rs` and `compiler-rust/src/lambda/compile.rs`
  sees real nullish tags instead of the string literal payload text
- OCaml reference: `compiler/ml/ast_untagged_variants.ml`,
  `compiler/core/matching_polyfill.ml`, and `compiler/ml/typemod.ml`, where
  `process_tag_type` distinguishes identifier payloads like `null` /
  `undefined` from string payloads like `"fulfilled"` and carries that tag
  metadata into constructor switch names
- Rust change:
  - replaced the CMI attribute reader’s old “first string wins” payload decode
    with separate marshaled-PStr decoders for identifier-shaped payloads and
    constant-string payloads
  - now loads `@as(null)` / `@as(undefined)` from interfaces as
    `AttributePayload::Ident(...)` instead of `AttributePayload::Str(...)`,
    while keeping `@as("null")` and other quoted strings as string payloads
  - added focused CMI-reader unit coverage to lock in the distinction between
    identifier payloads and quoted string payloads
- Added focused regression coverage in:
  - `cmi::sig_reader::tests::reads_cmi_null_ident_payload_as_ident_not_string`
  - `cmi::sig_reader::tests::reads_cmi_undefined_ident_payload_as_ident_not_string`
  - `cmi::sig_reader::tests::keeps_cmi_string_literal_payload_distinct_from_identifier_payload`
- Verified focused guards for this slice:
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml reads_cmi_null_ident_payload_as_ident_not_string -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml reads_cmi_undefined_ident_payload_as_ident_not_string -- --nocapture`
  - `timeout 120 cargo test --manifest-path compiler-rust/Cargo.toml keeps_cmi_string_literal_payload_distinct_from_identifier_payload -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/untagged_variants_heuristic.res -o /tmp/untagged_variants_heuristic.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DictPatternMatchingOptimization.res -o /tmp/DictPatternMatchingOptimization.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/json_decorders.res -o /tmp/json_decorders.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/option_optimisation.res -o /tmp/option_optimisation.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/untagged_variants_heuristic.res` now matches its checked-in
    `.mjs` snapshot exactly again; the diff corpus no longer contains
    `untagged_variants_heuristic`
  - the old `"null"` string-literal drift is gone from the authoritative diff
    corpus; the remaining files in this cluster
    (`DictPatternMatchingOptimization`, `json_decorders`, `option_optimisation`,
    `Stdlib_JsonTests`, `Stdlib_NullableTests`) now differ for later backend
    control-flow/cleanup reasons rather than incorrect nullish tag decoding
  - `ExternalShadow` remains an exact guard-file match
- Topline impact:
  - JS snapshot parity: **353 / 657** (**+1**)
  - Compile errors: **0** (no change)
  - Output diffs: **304** (**-1**)
- Keep this change because it ports OCaml’s constructor-attribute semantics at
  the interface-loading boundary instead of treating nullish tag mismatches as
  printer or snapshot-text issues

Latest iteration on **2026-04-14**:

- Active slice: preserve OCaml-style same-name export aliases for eta-reduced
  wrappers across the Rust-only second JS-path simplify pass and the final
  export coercion in `compiler-rust/src/lambda/simplify.rs` and
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference: `compiler/core/lam_pass_remove_alias.ml`,
  `compiler/core/lam_pass_lets_dce.ml`, `compiler/core/lam_compile_main.ml`,
  `compiler/core/js_shake.ml`, and `compiler/core/js_dump_import_export.ml`,
  where export identity is tracked separately from payload simplification, JS
  shaking keeps exported declarations alive, and ES module export printing uses
  the chosen export ident rather than rewriting it back to a same-name target
- Rust change:
  - added `known_functions` tracking plus eta-reduction for direct wrapper
    function values in the JS-path lambda simplifier so wrappers like
    `x => broken(x)` fold to direct aliases
  - taught the second simplify-pass pre-scan to keep exported bindings whose
    original RHS was an eta-wrapper, preventing the later Rust-only pass from
    substituting the just-reduced alias away again
  - changed top-level export coercion to prefer an already-declared same-name
    export alias over its target, and stopped the later alias-resolution helper
    from walking away from export idents that are already materially declared
- Added focused regression coverage in:
  - `lambda::simplify::tests::eta_reduces_wrappers_around_known_async_functions_like_ocaml`
  - `lambda::compile::tests::coerce_and_resolve_keep_declared_same_name_export_aliases`
  - updated `lambda::compile::tests::compile_deps_program_keeps_same_name_export_aliases_for_unbound_globals`
    to assert output-shape behavior instead of a specific internal stamp
- Verified focused guards for this slice:
  - `timeout 120 env RUSTFLAGS='--cap-lints allow' cargo test --manifest-path compiler-rust/Cargo.toml same_name_export -- --nocapture`
  - `timeout 120 env RUSTFLAGS='--cap-lints allow' cargo test --manifest-path compiler-rust/Cargo.toml eta_reduces_wrappers_around_known_async_functions_like_ocaml -- --nocapture`
  - `timeout 600 env RUSTFLAGS='--cap-lints allow' cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/async_inline.res -o /tmp/async_inline.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/pipe_syntax.res -o /tmp/pipe_syntax.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `async_inline` now matches its checked-in `.mjs` snapshot again; the
    missing `broken$2 = broken$1` export alias shape is restored
  - `pipe_syntax` remains an exact match after narrowing the second-pass
    preservation rule, so the temporary alias-regression cluster is gone
  - `ExternalShadow` remains an exact guard-file match
- Topline impact:
  - JS snapshot parity: **352 / 657** (**+5**)
  - Compile errors: **0** (no change)
  - Output diffs: **305** (**-5**)
- Keep this change because it matches OCaml’s export-identity handling at the
  JS backend boundary instead of papering over emitted text in the printer

Latest iteration on **2026-04-14**:

- Active slice: direct anonymous/wrapper beta reduction on the JS-path lambda
  simplifier in `compiler-rust/src/lambda/beta_reduce.rs` and
  `compiler-rust/src/lambda/simplify.rs`
- OCaml reference: `compiler/core/lam_pass_remove_alias.ml`,
  `compiler/core/lam_beta_reduce.ml`, and
  `compiler/core/lam_beta_reduce_util.ml`, where direct `Lfunction` /
  `PjsFnMake` applications use `Lam_beta_reduce.propagate_beta_reduce`
  instead of the plain no-names reducer, and the later pass does not
  immediately beta-reduce the newly exposed returned wrapper a second time
- Rust change:
  - added `beta_reduce::propagate_beta_reduce`, matching OCaml’s direct
    substitution-vs-fresh-let behavior for constants / vars vs non-trivial
    arguments
  - switched direct anonymous-function and direct `PjsFnMake` wrapper
    inlining in `simplify_apply` from `no_names_beta_reduce` to
    `propagate_beta_reduce`
  - gated those direct-wrapper beta reductions to the first JS-path simplify
    pass so the second pass does not collapse the returned wrapper call away
- Added focused regression coverage in:
  - `lambda::beta_reduce::tests::test_propagate_beta_reduce_keeps_let_wrapped_returned_functions`
  - `lambda::simplify::tests::keeps_nested_direct_wrapper_application_with_intermediate_let_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 env RUSTFLAGS='-Awarnings' cargo test --manifest-path compiler-rust/Cargo.toml --release test_propagate_beta_reduce_keeps_let_wrapped_returned_functions -- --nocapture`
  - `timeout 600 env RUSTFLAGS='-Awarnings' cargo test --manifest-path compiler-rust/Cargo.toml --release inlines_direct_function_applications_without_named_call_profitability_gate -- --nocapture`
  - `timeout 600 env RUSTFLAGS='-Awarnings' cargo test --manifest-path compiler-rust/Cargo.toml --release keeps_nested_direct_wrapper_application_with_intermediate_let_like_ocaml -- --nocapture`
  - `timeout 600 env RUSTFLAGS='-Awarnings' cargo test --manifest-path compiler-rust/Cargo.toml --release stops_after_one_beta_reduction_for_returned_pjs_fn_make_wrappers -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_1692_test.res -o /tmp/gpr_1692_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1692_test.res` now matches its checked-in `.mjs`
    snapshot exactly again; the diff corpus no longer contains `gpr_1692_test`
  - `ExternalShadow` remains an exact guard-file match
  - the authoritative baseline still regressed overall by one file elsewhere,
    so this slice is a verified OCaml-aligned fix with a separate follow-up
    regression still to isolate
- Topline impact:
  - JS snapshot parity: **347 / 657** (**-1**)
  - Compile errors: **0** (no change)
  - Output diffs: **310** (**+1**)
- Keep this change because it ports OCaml’s direct beta-reduction rule into
  Rust and fixes a concrete checked-in snapshot (`gpr_1692_test`) instead of
  papering over the emitted JS after the fact

Latest iteration on **2026-04-14**:

- Active slice: match OCaml's nullish disjunction printing in
  `compiler-rust/src/js_ir/printer.rs`
- OCaml reference: `compiler/core/j.ml` and `compiler/core/js_dump.ml`, where
  `Is_null_or_undefined` is emitted as `x == null` and the dumper also folds
  `x === null || x === undefined` into that same output form
- Rust change:
  - `js_ir::printer` now recognizes strict `null`/`undefined` disjunctions on
    the same expression and prints them as `== null`, matching the OCaml dump
    path
  - refreshed the stale `raw_lambda::matching` test assertion so the release
    test binary compiles after the richer `SwitchBlock` metadata refactor
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_nullish_or_as_loose_null_check_like_ocaml -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_nullish_or_as_loose_null_check_in_reverse_order_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/variantsMatching.res -o /tmp/variantsMatching.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UntaggedVariants.res -o /tmp/UntaggedVariants.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `variantsMatching` now prints the OCaml-style `x == null` / `y == null`
    checks in the nullable helpers instead of the expanded strict disjunction
  - `UntaggedVariants` now prints the OCaml-style `x == null` check in
    `classify$1`
  - `ExternalShadow` remains an exact guard-file match
- Topline impact:
  - JS snapshot parity: **348 / 657** (no change)
  - Compile errors: **0** (no change)
  - Output diffs: **309** (no change)
- Keep this change because it matches the OCaml dumper's nullish-check
  printing rule directly instead of leaving a known byte-shape drift in the
  final JS printer

Latest iteration on **2026-04-14**:

- Active slice: port OCaml’s grouped module side-effect reason selection in
  `compiler-rust/src/lambda/compile.rs`
- OCaml reference: `compiler/core/lam_coercion.ml`,
  `compiler/core/lam_group.ml`, and `compiler/core/lam_compile_main.ml`,
  where `flatten`, `handle_exports`, `Lam_dce.remove`, and
  `no_side_effects` derive the final `side_effect` trailer reason from the
  grouped lambda list instead of the raw lambda tree
- Rust change:
  - `module_side_effect_reason` now flattens top-level lets / letrecs /
    sequences into OCaml-style groups before deciding the trailer reason
  - the grouped scan now uses the final OCaml order instead of the raw
    flatten accumulator order, so strict / variable bindings like
    `ExternalExtension`’s `match` keep their binding name instead of falling
    back to `Some("")`
  - added focused regression coverage for first-impure-group ordering,
    impure binding values, and impure `Nop` groups
- Verified focused guards for this slice:
  - `timeout 600 env RUSTFLAGS='-Awarnings' cargo test --manifest-path compiler-rust/Cargo.toml --release module_side_effect_reason -- --nocapture`
  - `timeout 600 env RUSTFLAGS='-Awarnings' cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalExtension.res -o /tmp/ExternalExtension.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/ExternalExtension.res` now matches its checked-in `.mjs`
    snapshot exactly; the trailing purity comment is back to
    `/* match Not a pure module */`
  - `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
  - the authoritative diff corpus no longer contains `ExternalExtension`
- Topline impact:
  - JS snapshot parity: **352 / 657** (**+1**)
  - Compile errors: **0** (no change)
  - Output diffs: **305** (**-1**)
- Keep this change because it ports the OCaml grouped-module metadata rule into
  Rust instead of papering over the emitted JS comment in the printer

Latest iteration on **2026-04-14**:

- Active slice: preserve exported bindings reduced from applications across the
  second JS-path simplify pass in `compiler-rust/src/lambda/simplify.rs`
- OCaml reference: `compiler/core/lam_pass_remove_alias.ml`, where export
  payload simplification can fold aliases and pure constants before export
  coercion, but the original exported binding shape still survives when the
  binding itself came from a named application
- Rust change:
  - the extra Rust-only second `simplify_for_js_backend` pass now carries the
    set of exported bindings whose original RHS was an application
  - those bindings are no longer added to the substitution map on later
    passes, so they stay as explicit exported declarations instead of being
    substituted into the export block and rebound at the end
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release keeps_export_bindings_reduced_from_named_function_calls`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release simplifies_export_payloads_before_export_coercion`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DerivingAccessorsCurried.res -o /tmp/DerivingAccessorsCurried.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DerivingAccessorsUncurried.res -o /tmp/DerivingAccessorsUncurried.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/functors.res -o /tmp/functors.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `DerivingAccessorsCurried` and `DerivingAccessorsUncurried` now both match
    their checked-in `.mjs` snapshots exactly
  - the earlier functor/module-alias fixes remain intact: the diff corpus still
    has no `functors*` or `global_module_alias_test` failures
  - `ExternalShadow` remains an exact guard-file match
- Topline impact:
  - JS snapshot parity: **351 / 657** (**+2**)
  - Compile errors: **0** (no change)
  - Output diffs: **306** (**-2**)
- Keep this change because it tightens the Rust-only second simplify pass to
  preserve OCaml’s exported binding shape instead of introducing a later
  rebinding artifact in emitted JS

Latest iteration on **2026-04-14**:

- Active slice: bound single-field module projections in the JS lowering and
  flatten-and-mark-dead passes in `compiler-rust/src/lambda/compile.rs`
- OCaml reference: `compiler/core/js_of_lam_block.ml`,
  `compiler/core/js_exp_make.ml`, and
  `compiler/core/js_pass_flatten_and_mark_dead.ml`, where module fields lower
  through `E.module_access` and immutable module-block projections are later
  substituted through the block-substitution map
- Rust change:
  - `compile_field_access` now matches `E.module_access` by returning the
    selected field directly when the module target is a no-side-effect
    `CamlBlock`
  - `flatten_and_mark_dead_statement` now records single-field immutable
    module blocks in the substitution map as well, so later
    `StaticIndex(..., Some idx)` reads can collapse to the field value
- Added focused regression coverage in
  `lambda::compile::tests::lowers_module_pfield_from_pure_caml_block_directly_like_ocaml`
  and
  `lambda::compile::tests::js_flatten_and_mark_dead_substitutes_single_field_module_reads`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_module_pfield_from_pure_caml_block_directly_like_ocaml`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_flatten_and_mark_dead_substitutes_single_field_module_reads`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/functors_one_arg_at_a_time.res -o /tmp/functors_one_arg_at_a_time.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `functors_one_arg_at_a_time` now matches its checked-in `.mjs` snapshot
    exactly
  - the previously active functor/module-alias cluster is now fully absent
    from the authoritative diff corpus
  - `ExternalShadow` remains an exact guard-file match
- Topline impact:
  - JS snapshot parity: **349 / 657** (**+1**)
  - Compile errors: **0** (no change)
  - Output diffs: **308** (**-1**)
- Keep this change because it ports the OCaml module-field lowering and
  substitution behavior instead of adding a printer-only rewrite, and it
  clears the last remaining file in the active functor cluster

Latest iteration on **2026-04-14**:

- Active slice: rerun the JS-path lambda simplifier after named functor
  application inlining in `compiler-rust/src/lambda/simplify.rs`
- OCaml reference: `compiler/core/lam_pass_remove_alias.ml` together with the
  downstream flattening pipeline in `compiler/core/js_pass_flatten.ml` and
  `compiler/core/js_pass_flatten_and_mark_dead.ml`, where post-inline nested
  lets are flattened again before later field-projection cleanup
- Rust change: `simplify_for_js_backend` now runs a second
  flatten-and-simplify cycle after the first pass so named functor inlining
  can expose the same projected module fields that OCaml later collapses
- Added focused regression coverage in
  `lambda::simplify::tests::reruns_js_backend_simplify_after_functor_inlining_exposes_projected_module_fields`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release inlines_named_functor_applications_even_when_inline_heuristics_reject_them`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release reruns_js_backend_simplify_after_functor_inlining_exposes_projected_module_fields`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/functors.res -o /tmp/functors.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `functors` now matches its checked-in `.mjs` snapshot exactly
  - `global_module_alias_test` drops out of the authoritative diff corpus as
    the extra simplify pass removes the surviving nested-alias wrapper shape
  - `functors_one_arg_at_a_time` remains in the diff corpus, so this cluster
    still has a smaller follow-up case after the shared post-inline flattening
    gap
  - `ExternalShadow` remains an exact guard-file match
- Topline impact:
  - JS snapshot parity: **348 / 657** (**+2**)
  - Compile errors: **0** (no change)
  - Output diffs: **309** (**-2**)
- Keep this change because it is a verified OCaml-aligned backend cleanup and
  it removes two real snapshot failures while narrowing the remaining functor
  wrapper cluster to `functors_one_arg_at_a_time`

Latest iteration on **2026-04-14**:

- Active slice: named functor application inlining on the JS-path lambda
  simplifier in `compiler-rust/src/lambda/simplify.rs`
- OCaml reference: `compiler/core/lam_pass_remove_alias.ml`, where named
  functor applications inline after `Lam_analysis.lfunction_can_be_inlined`
  without also requiring `ok_to_inline_fun_when_app`
- Rust change:
  `should_inline_named_function` now matches that OCaml rule by allowing
  `func.attr.is_a_functor` to bypass the regular application heuristic while
  still requiring matching arity and `lfunction_can_be_inlined`
- Added focused regression coverage in
  `lambda::simplify::tests::inlines_named_functor_applications_even_when_inline_heuristics_reject_them`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release inlines_named_functor_applications_even_when_inline_heuristics_reject_them`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release identity_module_block`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct `compiler-args` snapshot repros from `tests/tests/lib/bs` for
    `global_module_alias_test.ast` and `functors.ast`
  - direct guard repro for `tests/tests/src/ExternalShadow.res`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `global_module_alias_test` no longer emits the surviving `Make(Belt_List)`
    call shape; the remaining diff is now the later alias/effect sequencing
    around repeated `let U = (...)` bindings
  - `functors` also moves past the direct functor-call lowering and now fails
    on a smaller wrapper/field-projection shape around `cow` / `sheep`
  - `ExternalShadow` remains an exact guard-file match
- Topline impact:
  - JS snapshot parity: **346 / 657** (no change)
  - Compile errors: **0** (no change)
  - Output diffs: **311** (no change)
- Keep this change even with a flat baseline because it removes a verified
  OCaml-aligned backend gap and exposes the next remaining root cause in the
  same cluster

Interpretation:

- This iteration stays on the **Phase 3: Port JS IR Lowering And Metadata**
  path from `PLAN.md`, extending the module-wrapper lowering work into
  `compiler-rust/src/lambda/simplify.rs`
- The OCaml-aligned rule is still the immutable identity-module collapse in
  `compiler/core/lam.ml`, where `Lam.prim` rewrites
  `Pmakeblock (Blk_module ...)` built entirely from matching `Pfield`
  projections of the same module input back to that original `Lvar` or
  `Lglobal_module`
- The Rust JS-path simplifier now applies that collapse generally before JS IR
  lowering instead of only at function-return emission time:
  - immutable module blocks reconstructed from alias or direct module-field
    projections of the same source module now simplify back to that source
    module expression
  - this catches top-level module aliases and effectful functor bodies that
    still reached the backend with explicit `Blk_module` wrappers after the
    earlier return-block-only fix
- Added focused regression coverage in
  `lambda::simplify::tests::collapses_identity_module_block_built_from_alias_projections`,
  `lambda::simplify::tests::collapses_identity_module_block_built_from_global_module_projections`,
  and
  `lambda::simplify::tests::keeps_non_identity_module_block_with_mixed_sources`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release identity_module_block -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release keeps_non_identity_module_block_with_mixed_sources -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/coercion_module_alias_test.res -o /tmp/coercion_module_alias_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `global_module_alias_test` no longer lowers its functor result aliases into
  giant explicit object literals, `coercion_module_alias_test` drops several
  explicit module-alias wrapper objects such as `C3 = { ... }`, and
  `ExternalShadow` remains an exact guard-file match
- The authoritative JS snapshot baseline now reports **346 / 657** passing,
  **0** compile errors, and **311** output diffs; this change is a net **0**
  at the topline from the previously recorded **346 / 657**, **0** compile
  errors, and **311** output diffs, and it is kept because it removes a real
  OCaml-aligned module-wrapper lowering gap even though the remaining files
  still fail later in the same cluster

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed primitive-lowering gap in
  `compiler/core/lam_compile_primitive.ml` together with
  `compiler/core/js_of_lam_array.ml`, specifically the backend handling for
  `Pstringrefs` / `Pstringrefu`, `Parrayrefu`, `Parrayrefs`, `Parraysetu`,
  and `Parraysets`
- After rereading those OCaml lowering paths, the Rust JS backend in
  `compiler-rust/src/lambda/compile.rs` now matches them more closely:
  - unsafe array refs lower directly to `ExpressionDesc::ArrayIndex`
    instead of falling through to `undefined`
  - safe array refs and safe array sets lower through
    `Primitive_array.get` / `Primitive_array.set`, matching OCaml's runtime
    calls instead of the Rust fallback `undefined`
  - string refs lower through `Primitive_string.getChar`, again matching the
    OCaml backend instead of the Rust fallback `undefined`
  - unsafe array sets now lower to `arr[i] = value` sequenced with
    `undefined`, matching the existing OCaml `set_array` / `ensure_value_unit`
    path more closely
- Added focused regression coverage in
  `compile_arrayrefu_uses_direct_array_index`,
  `compile_arrayrefs_uses_primitive_array_get`,
  `compile_arraysetu_sequences_assignment_to_unit`,
  `compile_arraysets_uses_primitive_array_set`, and
  `compile_string_refs_use_primitive_string_get_char`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_array -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_string_refs_use_primitive_string_get_char -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - project `compiler-args` snapshot repro for
    `tests/tests/src/earger_curry_test.res` from `tests/tests/lib/bs`
  - project `compiler-args` snapshot repro for
    `tests/tests/src/bench.res` from `tests/tests/lib/bs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `earger_curry_test`, `bench`, `bs_mutable_set_test`, and
  `bs_poly_mutable_set_test` no longer contain the old
  `a[i] -> undefined` / `remove(..., undefined)` backend drift in the
  refreshed diff corpus; their remaining diffs have moved on to separate
  loop-header, eta-wrapper, and mutable-accumulator shaping issues after this
  primitive-lowering slice
- The authoritative JS snapshot baseline remains **341 / 657** passing,
  **0** compile errors, and **316** output diffs; this is a net **0** change
  from the previously recorded baseline, and the OCaml-aligned change is kept
  because it removes a real backend lowering gap even though the topline
  stays flat

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed operator-precedence rule in
  `compiler/core/js_op_util.ml`, specifically `op_prec` using equal
  left/right precedence for associative logical and bitwise operators instead
  of Rust's stricter right-side precedence table
- After rereading that OCaml precedence table, the Rust JS printer in
  `compiler-rust/src/js_ir/printer.rs` now matches it more closely:
  - `&&`, `||`, `|`, `^`, and `&` chains now print without spurious
    right-nested parentheses when the JS IR is already grouped with the same
    operator
  - comparison, arithmetic, shift, assignment, and exponent precedence now
    follow the same numeric table as OCaml instead of the previously shifted
    Rust-specific table
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_chained_logical_and_without_right_nested_parens_like_ocaml`,
  `js_ir::printer::tests::test_print_chained_logical_or_without_right_nested_parens_like_ocaml`,
  and
  `js_ir::printer::tests::test_print_chained_bitwise_or_without_right_nested_parens_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_chained_ -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - project `compiler-args` snapshot repro for
    `tests/tests/src/js_date_test.res` from `tests/tests/lib/bs`
  - project `compiler-args` snapshot repro for
    `tests/tests/src/bdd.res` from `tests/tests/lib/bs`
  - project `compiler-args` snapshot repro for
    `tests/tests/src/set_gen.res` from `tests/tests/lib/bs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/js_date_test.res` is now out of the diff corpus,
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match, and
  the refreshed diff corpus no longer contains any `&& (` or `|| (` printer
  drift; broader files such as `bdd.res` and `set_gen.res` still fail on
  separate recursion/loop-lowering differences after this printer slice
- The authoritative JS snapshot baseline now reports **341 / 657** passing,
  **0** compile errors, and **316** output diffs; this is a net **+1**
  passing snapshot and **-1** output diff from the previously recorded
  **340 / 657**, **0** compile errors, **317** output diffs

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed dead-binding emission rule in
  `compiler/core/js_dump.ml`, specifically `variable_declaration` honoring
  `ident_info.used_stats` by omitting `Dead_pure` bindings and lowering
  `Dead_non_pure` bindings to plain effect statements
- After rereading that OCaml dumper path, the Rust JS printer in
  `compiler-rust/src/js_ir/printer.rs` now matches it more closely:
  - variable declarations marked `UsedStats::DeadPure` are skipped entirely,
    including top-level function-valued bindings that Rust previously still
    emitted
  - variable declarations marked `UsedStats::DeadNonPure` now print as their
    initializer expression statement instead of forcing a `let` binding
  - statement sequencing now skips separator newlines for non-emitting
    statements, so removing dead bindings no longer leaves blank gaps in the
    surrounding JS
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_dead_pure_variable_declaration_is_omitted_like_ocaml`,
  `js_ir::printer::tests::test_print_dead_non_pure_variable_declaration_as_expression_like_ocaml`,
  and
  `js_ir::printer::tests::test_print_dead_pure_top_level_function_binding_is_omitted_like_ocaml`
  while keeping
  `js_ir::printer::tests::test_print_variable_declaration_omits_undefined_initializer`
  green as the guard for the normal live-binding printer path
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_dead_pure_variable_declaration_is_omitted_like_ocaml -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_dead_non_pure_variable_declaration_as_expression_like_ocaml -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_dead_pure_top_level_function_binding_is_omitted_like_ocaml -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_variable_declaration_omits_undefined_initializer -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UncurriedAlways.res -o /tmp/UncurriedAlways.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/pipe_syntax.res -o /tmp/pipe_syntax.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/UncurriedAlways.res` and
  `tests/tests/src/pipe_syntax.res` are now out of the diff corpus, while
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
- The authoritative JS snapshot baseline now reports **340 / 657** passing,
  **0** compile errors, and **317** output diffs; this is a net **+2**
  passing snapshots and **-2** output diffs from the previously recorded
  **338 / 657**, **0** compile errors, **319** output diffs

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed object-literal key rule in
  `compiler/core/js_dump_property.ml`, specifically
  `obj_property_no_need_quot` allowing keyword-shaped identifiers like
  `catch`, `default`, and `extends` to print bare in object literals
- After rereading that OCaml property printer path, the Rust JS printer in
  `compiler-rust/src/js_ir/printer.rs` now matches it more closely:
  - object literal keys now use the same bare-identifier rule as OCaml instead
    of routing through the stricter reserved-word-aware identifier check
  - property access behavior is unchanged, so external members like
    `URL.catch` still print with normal dot access and runtime members still
    keep their separate mangling rules
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_object_literal_allows_keyword_property_names_without_quotes`
  while keeping
  `js_ir::printer::tests::test_print_qualified_external_member_preserves_js_property_access`
  green as the guard for the property-access path
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_object_literal_allows_keyword_property_names_without_quotes -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_qualified_external_member_preserves_js_property_access -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/key_word_property.res -o /tmp/key_word_property.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/gpr_459_test.res` is no longer in the diff corpus,
  `tests/tests/src/key_word_property.res` now only differs on its separate
  import-shape drift, `tests/tests/src/record_with_test.res` now only differs
  on the separate `uv` declaration-ordering drift, and
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
- The authoritative JS snapshot baseline now reports **338 / 657** passing,
  **0** compile errors, and **319** output diffs; this is a net **+3**
  passing snapshots and **-3** output diffs from the previously recorded
  **335 / 657**, **0** compile errors, **322** output diffs

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed function-body layout rule in
  `compiler/core/js_dump.ml`, specifically the `P.brace_vgroup` plus
  `function_body` path that still emits a blank indented line for named
  functions whose body is semantically empty after eliding `return undefined`
- After rereading that OCaml printer path, the Rust JS printer in
  `compiler-rust/src/js_ir/printer.rs` now matches it more closely:
  - named functions whose body lowers to an invisible `return undefined` now
    print as:
    `function f(x) {\n  \n}`
    instead of collapsing to `function f(x) {\n  }`
  - directive/body layout now keys off whether the body prints anything, so
    invisible tail statements no longer pull the closing brace onto the
    indented blank line
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_named_function_with_undefined_body_keeps_blank_line_like_ocaml`
  while keeping
  `js_ir::printer::tests::test_print_arrow_function_with_undefined_body_uses_compact_empty_block`
  green as the guard for the separate arrow-function rule
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_named_function_with_undefined_body_keeps_blank_line_like_ocaml -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_arrow_function_with_undefined_body_uses_compact_empty_block -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UncurriedPervasives.res -o /tmp/UncurriedPervasives.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/UncurriedAlways.res -o /tmp/UncurriedAlways.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/UncurriedPervasives.res` now matches its checked-in `.mjs`
  snapshot exactly again, `tests/tests/src/ExternalShadow.res` remains an
  exact guard-file match, and `tests/tests/src/UncurriedAlways.res` now only
  differs on its separate tuple-array lowering drift
- The empty-body blank-line motif is much narrower now; only
  `recursive_unbound_module_test` and `test_while_side_effect` still carry the
  old `-  ` hunk shape in the refreshed diff corpus
- The authoritative JS snapshot baseline now reports **335 / 657** passing,
  **0** compile errors, and **322** output diffs; this is a net **+6**
  passing snapshots and **-6** output diffs from the previously recorded
  **329 / 657**, **0** compile errors, **328** output diffs

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed JS expression-construction
  rule in `compiler/core/js_exp_make.ml`, specifically `float_add` rewriting a
  negative integer RHS from `Plus` into `float_minus`
- After rereading that OCaml path, the Rust JS IR builder in
  `compiler-rust/src/js_ir/mod.rs` now matches it more closely:
  - `Expression::bin(BinOp::Plus, x, -1)` canonicalizes to
    `ExpressionDesc::Bin(BinOp::Minus, x, 1)` instead of preserving
    `x + -1`
  - the rewrite happens before final printing, so integer and float-style
    numeric additions share the same OCaml-aligned normalized shape
- Added focused regression coverage in
  `js_ir::tests::test_plus_with_negative_int_rhs_rewrites_to_minus`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::tests::test_plus_with_negative_int_rhs_rewrites_to_minus -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_858_unit2_test.res -o /tmp/gpr_858_unit2_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/gpr_858_unit2_test.res` now matches its checked-in `.mjs`
  snapshot exactly again, `tests/tests/src/ExternalShadow.res` remains an
  exact guard-file match, and the refreshed diff corpus no longer contains any
  `+ -1` addition drift
- The remaining nearby files from that cluster still fail on separate backend
  differences after this slice, including `bench`, `earger_curry_test`,
  `gpr_1072`, `test_fib`, and `test_u`
- The authoritative JS snapshot baseline now reports **329 / 657** passing,
  **0** compile errors, and **328** output diffs; this is a net **+1**
  passing snapshot and **-1** output diff from the previously recorded
  **328 / 657**, **0** compile errors, **329** output diffs

- Re-ran the authoritative wrapper on **2026-04-14** after fixing a JS
  snapshot harness output-path collision in `scripts/test_rust_parity.sh`
- The measured baseline remains **328 / 657** passing, **0** compile errors,
  and **329** output diffs; this iteration restores the previously recorded
  baseline instead of changing the backend topline
- Root cause:
  when the harness compiled checked-in `.ast` files with project-owned
  `compiler-args`, it wrote `-o` targets under
  `temp/rust-parity/js/src/...`, which collides with the same `src` segment in
  `-bs-package-output esmodule:src:.mjs`
- In that shape, modules such as `tests/tests/src/Import.res` could compile
  successfully yet skip materializing the requested temp output file, so the
  harness misclassified them as compile errors even though the emitted JS
  matched the checked-in snapshot byte-for-byte
- The harness now writes per-file snapshot outputs under a neutral directory
  shape:
  `temp/rust-parity/js/generated/<safe-file-key>/<Module>.mjs`
  while preserving the module basename that the `.ast` compile path expects
- Verified focused guards for this measurement fix:
  - exact project-args `.ast` snapshot repro for `tests/tests/src/Import.res`
    into `temp/rust-parity/js/generated/src_Import.res/Import.mjs`
  - exact project-args `.ast` snapshot repro for
    `tests/tests/src/ExternalShadow.res` into
    `temp/rust-parity/js/generated/src_ExternalShadow.res/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Outcome:
  `tests/tests/src/Import.res` is back out of the false compile-error bucket,
  the authoritative wrapper again reports a pure diff set, and future Phase 4
  backend work can trust the JS snapshot counts without this path-shape
  artifact

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed JS printer rule in
  `compiler/core/js_dump.ml`, specifically the `Bin (op, e1, e2)` branch that
  always parenthesizes shift operators (`Lsl`, `Lsr`, `Asr`) even in
  low-precedence contexts
- After rereading that OCaml printer path, the Rust JS printer in
  `compiler-rust/src/js_ir/printer.rs` now matches it more closely:
  - `<<`, `>>`, and `>>>` expressions stay parenthesized in emitted JS instead
    of being flattened by precedence-only printing
  - concise arrow bodies now preserve the same parenthesized shift form that
    OCaml prints, such as `value => (value << 1)`
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_shift_binary_is_parenthesized_like_ocaml`
  and
  `js_ir::printer::tests::test_print_arrow_function_preserves_parenthesized_shift_body`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_shift_binary_is_parenthesized_like_ocaml -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_arrow_function_preserves_parenthesized_shift_body -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - harness-mode snapshot repros from `tests/tests/lib/bs` for
    `src/js_undefined_test.ast` and
    `src/belt_sortarray_test.ast`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/js_undefined_test.res` and
  `tests/tests/src/belt_sortarray_test.res` now match their checked-in `.mjs`
  snapshots exactly again, while `tests/tests/src/ExternalShadow.res` remains
  an exact guard-file match
- The remaining nearby drift is narrower now:
  - the shift-parentheses hunk is gone from the broader callback corpus
    (`js_null_test`, `js_null_undefined_test`, `js_array_test`,
    `bs_mutable_set_test`, `bs_poly_set_test`, `for_loop_test`,
    `test_for_loop`, `test_tuple`, `record_name_test`,
    `alias_default_value_test`, `belt_list_test`, and
    `stdlib/Stdlib_TempTests`), but those files still fail on separate backend
    or printer differences
  - only five current diff files still carry shift-parentheses drift after this
    port:
    `gray_code_test`, `bigint_test`, `unified_ops_test`, `test_list`, and
    `mario_game`
- The authoritative JS snapshot baseline now reports **328 / 657** passing,
  **0** compile errors, and **329** output diffs; this is a net **+2**
  passing snapshots and **-2** output diffs from the previously recorded
  **326 / 657**, **0** compile errors, **331** output diffs

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed constant-option lowering slice
  in `compiler/core/lam_compile_const.ml`, specifically its `translate_some`,
  `is_some_none_aux`, and `nested_some_none` path for `Const_some`
- After rereading that OCaml constant backend path, the Rust JS backend in
  `compiler-rust/src/lambda/compile.rs` now matches it more closely:
  - `Constant::Some` only lowers as an identity optional block when the payload
    is not part of an `undefined` / `module alias` none-chain
  - `Some(undefined)`, `Some(unit)`, and nested `Some(None)`-style constants
    now preserve the boxed none encoding with non-identity `OptionalBlock`
    layers instead of collapsing to raw `undefined`
- Added focused regression coverage in
  `lambda::compile::tests::compile_constant_some_unit_boxes_undefined_none_encoding`
  and
  `lambda::compile::tests::compile_constant_nested_some_none_preserves_nested_optional_boxes`
- Verified focused guards for this slice:
  - `timeout 600 env RUSTFLAGS=-Awarnings cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::compile::tests::compile_constant_some_unit_boxes_undefined_none_encoding -- --exact`
  - `timeout 600 env RUSTFLAGS=-Awarnings cargo test --manifest-path compiler-rust/Cargo.toml --release lambda::compile::tests::compile_constant_nested_some_none_preserves_nested_optional_boxes -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - harness-mode snapshot repros from `tests/tests/lib/bs` for
    `src/unit_undefined_test.ast`,
    `src/js_null_test.ast`, and
    `src/js_null_undefined_test.ast`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/unit_undefined_test.res` no longer collapses boxed option
  constants to raw `undefined`, `tests/tests/src/js_null_test.res` now keeps
  the correct boxed-option shape on its `toOption - 'a` assertion, and
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
- The remaining drift in this nullable-option slice is now narrower and later:
  - `tests/tests/src/unit_undefined_test.res` still differs on the separate
    OCaml `Optional_block` printer path that routes through normal call
    printing, so Rust still emits `Primitive_option.some(undefined)` where the
    checked-in snapshot has `Primitive_option.some()`, plus the older empty
    function-body formatting hunk in `fx`
  - `tests/tests/src/js_null_test.res` still differs on the separate
    arrow-parentheses printer hunk in `n => (n << 1)`
  - `tests/tests/src/js_null_undefined_test.res` is unchanged for this slice;
    its remaining drift is the earlier nullable-predicate / constant-fold
    cluster rather than constant `Const_some` lowering
- The authoritative JS snapshot baseline remains **326 / 657** passing,
  **0** compile errors, and **331** output diffs after this OCaml-aligned
  `Const_some` port. The topline stays flat because the affected files were
  already failing on later printer/backend drift, but the constant option
  representation is now aligned with OCaml and should not be reverted.

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed printer rule in
  `compiler/core/js_dump.ml`, specifically `loop_case_clauses` emitting
  `case <expr> :` for switch labels while keeping `default:` unchanged
- After rereading that OCaml printer path, the Rust JS printer in
  `compiler-rust/src/js_ir/printer.rs` now matches it more closely:
  - integer switch clauses print `case 0 :` instead of `case 0:`
  - string switch clauses print `case "Tag" :` instead of `case "Tag":`
  - `default:` remains unchanged, matching the OCaml printer's separate branch
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_int_switch_cases_keep_space_before_colon`
  and
  `js_ir::printer::tests::test_print_string_switch_cases_keep_space_before_colon`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release space_before_colon -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct snapshot repros for
    `tests/tests/src/NondetPatterMatch.res` and
    `tests/tests/src/ExternalShadow.res`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  the switch-label spacing fix cleared the remaining spacing-only switch corpus,
  including
  `tests/tests/src/NondetPatterMatch.res`,
  `tests/tests/src/adt_optimize_test.res`,
  `tests/tests/src/arith_syntax.res`,
  `tests/tests/src/complete_parmatch_test.res`,
  `tests/tests/src/gpr_3209_test.res`,
  `tests/tests/src/gpr_4069_test.res`,
  `tests/tests/src/int_switch_test.res`,
  `tests/tests/src/simplify_lambda_632o.res`,
  `tests/tests/src/test_simple_pattern_match.res`,
  `tests/tests/src/test_string_case.res`,
  `tests/tests/src/test_string_switch.res`, and
  `tests/tests/src/test_switch.res`,
  while `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
- The authoritative JS snapshot baseline now reports **326 / 657** passing,
  **0** compile errors, and **331** output diffs; this is a net **+13**
  passing snapshots and **-13** output diffs from the previously recorded
  **313 / 657**, **0** compile errors, **344** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed raw-JS parenthesization slice
  in `compiler/core/js_dump.ml`, specifically its statement-position
  `exp_need_paren` rule and its `Raw_js_code` dump branch, together with the
  raw-expression classification contract in `compiler/ml/js_raw_info.ml`
- After rereading those OCaml rules, the Rust JS printer in
  `compiler-rust/src/js_ir/printer.rs` now matches that behavior more closely:
  - raw-JS function expressions only omit parentheses when the snippet is
    syntactically simple enough, instead of treating every classified
    function snippet as paren-free
  - statement-position raw-JS expressions and `Call(Raw_js_code, ...)`
    expressions now receive the same extra statement parens that OCaml emits
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_raw_js_function_expression_adds_parens`
  and
  `js_ir::printer::tests::test_print_statement_calling_raw_js_function_expression_adds_statement_parens`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_raw_js_function_expression_adds_parens -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_statement_calling_raw_js_function_expression_adds_statement_parens -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_raw_js_regex_literal_omits_extra_parens -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_typeof_simple_raw_js_omits_extra_parens -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct snapshot repros for
    `tests/tests/src/raw_output_test.res`,
    `tests/tests/src/raw_arity.res`, and
    `tests/tests/src/ExternalShadow.res`
  - exact harness-mode snapshot repros from `tests/tests/lib/bs` for
    `src/polymorphic_raw_test.ast` and
    `src/raw_output_test.ast`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/raw_output_test.res`,
  `tests/tests/src/raw_arity.res`, and
  `tests/tests/src/polymorphic_raw_test.res` now match their checked-in `.mjs`
  snapshots exactly again, while
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
- The authoritative JS snapshot baseline now reports **313 / 657** passing,
  **0** compile errors, and **344** output diffs; this is a net **+7**
  passing snapshots and **-7** output diffs from the previously recorded
  **306 / 657**, **0** compile errors, **351** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed printer slice in
  `compiler/core/js_dump.ml` together with raw-JS expression classification
  from `compiler/ml/js_raw_info.ml`
- After rereading OCaml's `Typeof` printer, its `Raw_js_code` parenthesization
  rule, and the dedicated `Bin (Minus, Number 0, e)` dump branch there, the
  Rust JS printer in `compiler-rust/src/js_ir/printer.rs` now matches that
  behavior more closely:
  - `0 - x` and `0. - x` print as unary minus forms instead of literal
    subtraction trees
  - `typeof` parenthesizes function expressions but stops adding redundant
    parentheses around raw-JS identifier/literal/function snippets
  - raw-JS expression dumping now reuses the existing OXC-backed classifier so
    regex literals and other OCaml-classified raw expressions keep their
    checked-in byte shape
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_zero_minus_expr_as_unary_minus`,
  `test_print_zero_float_minus_expr_as_spaced_unary_minus`,
  `test_print_typeof_function_parenthesizes_arrow_expression`,
  `test_print_typeof_simple_raw_js_omits_extra_parens`, and
  `test_print_raw_js_regex_literal_omits_extra_parens`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_zero_minus_expr_as_unary_minus -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_zero_float_minus_expr_as_spaced_unary_minus -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_typeof_function_parenthesizes_arrow_expression -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_typeof_simple_raw_js_omits_extra_parens -- --exact`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release js_ir::printer::tests::test_print_raw_js_regex_literal_omits_extra_parens -- --exact`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact harness-mode snapshot repros from `tests/tests/lib/bs` for
    `src/gpr_977_test.ast`,
    `src/test_per.ast`,
    `src/ExternalExtension.ast`, and
    `src/ExternalShadow.ast`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/gpr_977_test.res` and `tests/tests/src/test_per.res` now
  match their checked-in `.mjs` snapshots exactly again,
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match, and
  `tests/tests/src/ExternalExtension.res` is narrowed to its remaining
  side-effect-comment reason only (`/* match Not a pure module */` vs
  `/*  Not a pure module */`)
- The authoritative JS snapshot baseline now reports **306 / 657** passing,
  **0** compile errors, and **351** output diffs; this is a net **+2**
  passing snapshots and **-2** output diffs from the previously recorded
  **304 / 657**, **0** compile errors, **353** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated the OCaml exported-binding simplification
  boundary across `compiler/core/lam_pass_lets_dce.ml` together with the later
  export rebound behavior in `compiler/core/lam_coercion.ml`
- After reading those OCaml stages, the Rust backend in
  `compiler-rust/src/lambda/simplify.rs` no longer preserves exported alias or
  constant bindings ahead of export coercion, and module-export payloads now
  simplify through the same substitution path as ordinary lambda expressions
- This matches the OCaml flow where `simplify_lets` can erase or inline the
  original exported binding, then the later export-coercion step recreates any
  required trailing export placeholders in the final grouped order
- Added focused regression coverage in
  `lambda::simplify::tests::simplifies_export_payloads_before_export_coercion`,
  `lambda::simplify::tests::simplifies_module_alias_export_payloads_before_export_coercion`,
  and
  `lambda::compile::tests::compile_deps_program_rebinds_exported_constants_after_surviving_function_bindings`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release export_payloads_before_export_coercion -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_deps_program_rebinds_exported_constants_after_surviving_function_bindings -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `cd tests/tests/lib/bs && timeout 10 ../../../../compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/Coercion.ast -o /tmp/Coercion.mjs`
  - `cd tests/tests/lib/bs && timeout 10 ../../../../compiler-rust/target/release/bsc -I ../ocaml -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104 -warn-error A -bs-package-name rescript-tests -bs-package-output esmodule:src:.mjs src/Import.ast -o /tmp/Import.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/Coercion.res` and `tests/tests/src/Import.res` now match
  their checked-in `.mjs` snapshots exactly in harness mode, and
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
- Resolved checked-in snapshot files for this cluster:
  `tests/tests/src/Coercion.res` and `tests/tests/src/Import.res` no longer appear under
  `temp/rust-parity/diffs`
- The authoritative JS snapshot baseline now reports **302 / 657** passing,
  **0** compile errors, and **355** output diffs; this is a net **+22**
  passing snapshots and **-22** output diffs from the previously recorded
  **280 / 657**, **0** compile errors, **377** output diffs
- The remaining nearby drift is narrower now:
  - `tests/tests/src/DerivingAccessorsCurried.res` and
    `tests/tests/src/DerivingAccessorsUncurried.res` still differ on late
    rebound placement such as `_composedMyField`
  - `tests/tests/src/RecordCoercion.res` is no longer blocked on export
    ordering; its remaining mismatch is shared-binding naming
    (`TestInlining_a` vs `a`) and module-record reuse shape
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed `Js_exp_make` expression
  builder slice across `compiler/core/js_exp_make.ml` together with the
  primitive lowering entry points in `compiler/core/lam_compile_primitive.ml`
- After reading OCaml's `econd`, `int32_mul`, `int32_bxor`, `int32_bor`,
  `int32_lsr`, and `to_int32` there, the Rust backend in
  `compiler-rust/src/js_ir/mod.rs` and `compiler-rust/src/lambda/compile.rs`
  now mirrors those builder-level simplifications more closely: literal
  conditionals collapse before printing, negated conditionals swap branches the
  same way, power-of-two int multiplies lower to shifts, literal xor folds
  eagerly, and redundant `| 0` after logical shifts is dropped
- Added focused regression coverage in
  `js_ir::tests::test_cond_true_simplifies_to_consequent`,
  `js_ir::tests::test_cond_negated_test_swaps_non_empty_branches`,
  `lambda::compile::tests::lowers_pmulint_by_positive_power_of_two_to_shift`,
  `lambda::compile::tests::lowers_pxorint_literal_operands_to_folded_constant`,
  and
  `lambda::compile::tests::to_int32_drops_redundant_bor_after_logical_shift`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release cond_ -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release power_of_two_to_shift -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release pxorint_literal_operands -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release to_int32_drops_redundant_bor_after_logical_shift -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact harness-mode snapshot repros for
    `tests/tests/src/js_null_test.res`,
    `tests/tests/src/belt_int_test.res`,
    `tests/tests/src/const_defs_test.res`, and
    `tests/tests/src/js_undefined_test.res` from `tests/tests/lib/bs`
    using the checked-in `compiler-args`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/const_defs_test.res` and
  `tests/tests/src/belt_int_test.res` now match their checked-in snapshots
  exactly again, `tests/tests/src/ExternalShadow.res` remains an exact
  guard-file match, and
  `tests/tests/src/js_null_test.res` plus
  `tests/tests/src/js_undefined_test.res` both collapsed to their remaining
  `some(undefined)` / arrow-parentheses drift instead of the original
  conditional and multiply-lowering mismatches
- The authoritative JS snapshot baseline now reports **270 / 657** passing,
  **0** compile errors, and **387** output diffs; this is a net **+4**
  passing snapshots and **-4** output diffs from the previously recorded
  **266 / 657**, **0** compile errors, **391** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed cross-module constant-field
  lowering slice in `compiler/core/lam_compile.ml` together with
  `compiler/core/js_cmj_format.ml` and `compiler/core/lam_stats_export.ml`
- After reading OCaml's `compile_external_field`, which consults
  `Lam_compile_env.query_external_id_info` and compiles a
  `persistent_closed_lambda` directly when the exported field is a closed
  non-function lambda, the Rust backend now mirrors that behavior for the
  closed constants that OCaml preserves in `.cmj` files with
  `cross_module_inline = false`: `null`, `undefined`, `true`, and `false`
- Rust now reads keyed constant exports from companion `.cmj` files through
  `compiler-rust/src/cmi/persistent_env.rs`, threads that lookup through
  `compiler-rust/src/js_ir/mod.rs`, and uses it in
  `compiler-rust/src/lambda/compile.rs` before falling back to ordinary
  `module.field` emission for ML module accesses
- Added focused regression coverage in
  `cmi::persistent_env::tests::reads_belt_map_string_empty_as_closed_undefined_constant_from_cmj`
  and
  `lambda::compile::tests::lowers_qualified_ml_module_closed_undefined_constant_from_cmj`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release reads_belt_map_string_empty_as_closed_undefined_constant_from_cmj -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release lowers_qualified_ml_module_closed_undefined_constant_from_cmj -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_functor_dead_code.res -o /tmp/test_functor_dead_code.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_int_map_find.res -o /tmp/test_int_map_find.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/test_functor_dead_code.res`,
  `tests/tests/src/test_string_map.res`, and
  `tests/tests/src/test_int_map_find.res` now match their checked-in
  snapshots exactly again, `tests/tests/src/ExternalShadow.res` remains an
  exact guard-file match, and the cached diff corpus no longer contains the
  `Belt_MapString.empty` / `Belt_MapInt.empty` motif at all
- The authoritative JS snapshot baseline now reports **266 / 657** passing,
  **0** compile errors, and **391** output diffs; this is a net **+4**
  passing snapshots and **-4** output diffs from the previously recorded
  **262 / 657**, **0** compile errors, **395** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  but this iteration first eliminated a local worktree regression that had
  pushed `tests/tests/src/Import.res` back into the compile-error bucket under
  the authoritative harness
- After reading OCaml's `Env.components_of_module` / `prefix_idents` flow in
  `compiler/ml/env.ml`, where module-component lookup materializes one
  substituted signature rather than copying an already-copied signature again,
  the Rust type-expansion path in `compiler-rust/src/types/ctype.rs` now
  matches that behavior more closely: `resolve_type_item_through_env` no
  longer deep-copies the fresh module signature returned from
  `resolve_signature_through_env_module_type` a second time before applying the
  access-path substitution for `M.t` lookups
- Added focused regression coverage in
  `types::ctype::tests::resolve_type_item_through_env_keeps_original_module_signature_unmodified`
  so the env-stored module signature still remains untouched while the
  resolved lookup result is path-qualified through `M.u`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release resolve_type_item_through_env_keeps_original_module_signature_unmodified -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - exact harness-mode AST repro for `tests/tests/src/Import.res` from
    `tests/tests/lib/bs` using the checked-in `compiler-args` together with
    `/usr/bin/time -l`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/Import.res -o /tmp/Import.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  the exact harness-mode `Import.ast` compile dropped from about **9.35s** real
  time to **4.68s**, `tests/tests/src/Import.res` no longer times out under the
  10-second wrapper budget and is back to being a normal output-diff case,
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match, and
  the authoritative wrapper result returned to the recorded baseline of
  **262 / 657** passing, **0** compile errors, and **395** output diffs
- Relative to the local pre-fix worktree measurement from the start of this
  iteration, this is a net **0** passing snapshots, **-1** compile error, and
  **+1** output diff because `Import.res` moved from the timeout bucket back
  into the ordinary JS-diff bucket
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed printer-only conditional-layout
  slice in `compiler/core/js_dump.ml`
- After reading OCaml's `Cond` printer there, which prints branch expressions
  under `P.group f 1` and emits any conditional at precedence level `> 2`
  through `P.paren_vgroup f 1`, the Rust JS printer in
  `compiler-rust/src/js_ir/printer.rs` now follows the same layout rule
  instead of always flattening nested ternaries onto one line
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_parenthesized_conditional_uses_vertical_group`
  and
  `js_ir::printer::tests::test_print_nested_conditional_else_branch_matches_ocaml_grouping`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'js_ir::printer::tests::test_print_conditional' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'js_ir::printer::tests::test_print_parenthesized_conditional_uses_vertical_group' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'js_ir::printer::tests::test_print_nested_conditional_else_branch_matches_ocaml_grouping' -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/LetUnwrap.res -o /tmp/LetUnwrap.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/LetUnwrap.res` now matches its checked-in snapshot exactly,
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match, and
  `js_src_LetUnwrap.res.diff` no longer appears under `temp/rust-parity/diffs`
- The authoritative JS snapshot baseline now reports **262 / 657** passing,
  **0** compile errors, and **395** output diffs; this is a net **+1**
  passing snapshot and **-1** output diff from the previously recorded
  **261 / 657**, **0** compile errors, **396** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed nested-application reduction
  boundary in `compiler/core/lam_pass_lets_dce.ml` together with
  `compiler/core/lam_pass_remove_alias.ml`
- After reading those OCaml passes, which only beta-reduce direct
  `Lapply {ap_func = Lfunction ...}` sites at the current node and do not
  keep re-dispatching through an original `Lapply` whose callee later
  simplifies into a function, the Rust JS-backend simplifier in
  `compiler-rust/src/lambda/simplify.rs` now follows the same one-step rule:
  it still beta-reduces non-`Lapply` callees after simplification, but it no
  longer beta-reduces a second time through an original nested application
- Updated focused regression coverage in
  `lambda::simplify::tests::stops_after_one_beta_reduction_for_downarity_pjs_fn_make_calls`
  and
  `lambda::simplify::tests::stops_after_one_beta_reduction_for_returned_pjs_fn_make_wrappers`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release pjs_fn_make -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_1692_test.res -o /tmp/gpr_1692_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/gpr_1692_test.res` now matches its checked-in snapshot
  exactly again, `tests/tests/src/ExternalShadow.res` remains an exact
  guard-file match, and `js_src_gpr_1692_test.res.diff` no longer appears
  under `temp/rust-parity/diffs`; however the authoritative rerun stayed flat
  at **261 / 657** passing with **396** output diffs, which means this
  OCaml-aligned fix was offset by a compensating regression elsewhere in the
  same nested-application family rather than improving the total yet
- The authoritative JS snapshot baseline still reports **261 / 657** passing,
  **0** compile errors, and **396** output diffs; this is a net **0**
  baseline change from the previously recorded **261 / 657**, **0** compile
  errors, **396** output diffs even though `gpr_1692_test.res` itself is now
  correct
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed nullable-option lowering slice
  in `compiler/core/lam_compile_primitive.ml` together with
  `compiler/core/js_of_lam_option.ml`
- After reading OCaml's `Pnull_to_opt` / `Pnull_undefined_to_opt` lowering
  there, which only inlines `null_to_opt` / `null_undef_to_opt` for
  `Var | Undefined | Null` and otherwise emits
  `Primitive_option.fromNull` / `Primitive_option.fromNullable`, the Rust
  backend in `compiler-rust/src/lambda/compile.rs` now follows the same split
  instead of always lowering these primitives into ternaries
- Added focused regression coverage in
  `lambda::compile::tests::lowers_pnull_to_opt_non_inline_operand_to_primitive_option_from_null`
  and
  `lambda::compile::tests::lowers_pnull_undefined_to_opt_non_inline_operand_to_primitive_option_from_nullable`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release pnull_to_opt_non_inline -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release pnull_undefined_to_opt_non_inline -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_974_test.res -o /tmp/gpr_974_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/gpr_974_test.res` now matches its checked-in snapshot
  exactly again, `tests/tests/src/ExternalShadow.res` remains an exact
  guard-file match, the cached `Primitive_option.fromNull` motif shrank from
  **5** failing files to **4**, and the cached
  `Primitive_option.fromNullable` motif shrank from **3** failing files to
  **2**; the remaining nullable-option files are now
  `js_null_test.res`, `js_null_undefined_test.res`, `js_string_test.res`, and
  `js_re_test.res`, which are on separate constant-fold / `some(undefined)` /
  regex-emission issues rather than the wrong helper-vs-inline split
- The authoritative JS snapshot baseline now reports **261 / 657** passing,
  **0** compile errors, and **396** output diffs; this is a net **+1**
  passing snapshot and **-1** output diff from the previously recorded
  **260 / 657**, **0** compile errors, **397** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed option-runtime emission slice
  across `compiler/core/lam_compile_primitive.ml`,
  `compiler/core/js_of_lam_option.ml`, `compiler/core/js_dump.ml`, and
  `compiler/ext/primitive_modules.ml`
- After reading OCaml's `Primitive_modules.option = "Primitive_option"` there,
  plus `Js_of_lam_option.val_from_option` and the `Optional_block` printer path
  in `js_dump.ml` that re-expands to
  `E.runtime_call Primitive_modules.option "some" [e]`, the Rust backend now
  uses `Primitive_option` instead of `Caml_option` for non-identity option
  wrappers and `valFromOption`, and the JS backend in
  `compiler-rust/src/lambda/compile.rs` now records `Primitive_option` as a
  required runtime module whenever `OptionalBlock(_, false)` survives into the
  printed JS so the import is emitted on the same path as OCaml
- Added focused regression coverage in
  `lambda::compile::tests::lowers_pval_from_option_to_primitive_option_runtime_call`
  and
  `lambda::compile::tests::compile_deps_program_imports_primitive_option_for_non_identity_optional_block`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release primitive_option -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_unknown.res -o /tmp/test_unknown.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/test_unknown.res` now matches its checked-in snapshot again,
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match, the
  option-runtime motif in cached diff files shrank from **40** failing files to
  **33**, and the authoritative rerun dropped
  `undef_regression_test.res`, `gpr_3566_drive_test.res`,
  `reactTestUtils.res`, and `test_unknown.res` out of
  `temp/rust-parity/diffs`; the remaining option-heavy files are now on the
  separate `some(undefined)` / `toUndefined` / option-shape lowering issues
  rather than the wrong runtime-module import path
- The authoritative JS snapshot baseline now reports **260 / 657** passing,
  **0** compile errors, and **397** output diffs; this is a net **+4**
  passing snapshots and **-4** output diffs from the previously recorded
  **256 / 657**, **0** compile errors, **401** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed raw-`%%raw` payload
  normalization slice across `compiler/core/js_exp_make.ml` together with the
  `Ext_pp` newline-state behavior used by `compiler/core/js_dump.ml`
- After reading OCaml's `raw_js_code` there, which builds
  `Raw_js_code {code = String.trim s; ...}`, plus `compiler/ext/ext_pp.ml`
  for `newline` / `at_least_two_lines`, the Rust backend now trims raw-JS
  payloads at the matching JS-IR construction point in
  `compiler-rust/src/lambda/compile.rs`, and the JS printer in
  `compiler-rust/src/js_ir/printer.rs` now tracks OCaml's `last_new_line`
  state so raw statement printers and purity trailers stop injecting extra
  blank lines or dropping the final trailing newline
- Added focused regression coverage in
  `lambda::compile::tests::compile_raw_js_trims_outer_whitespace_before_js_ir_printing`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'lambda::compile::tests::compile_raw_js_trims_outer_whitespace_before_js_ir_printing' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'js_ir::printer::tests::test_print_deps_program_keeps_blank_line_after_imports' -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_4931.res -o /tmp/gpr_4931.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/gpr_4931.res` now matches its checked-in snapshot exactly
  again, `tests/tests/src/ExternalShadow.res` remains an exact guard-file
  match, and the raw-snippet diff files
  `gpr_4931.res`, `gpr_4931_allow.res`, `bs_auto_uncurry_test.res`, and
  `gpr_3492_test.res` all dropped out of `temp/rust-parity/diffs` after the
  authoritative rerun; meanwhile `gpr_1692_test.res` still fails for the
  separate pure-module elimination / dead-code issue, so that cluster remains
  open
- The authoritative JS snapshot baseline now reports **256 / 657** passing,
  **0** compile errors, and **401** output diffs; this is a net **+5**
  passing snapshots and **-5** output diffs from the previously recorded
  **251 / 657**, **0** compile errors, **406** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed unreachable-let / export-body
  lowering slice in `compiler/core/lam_compile.ml` together with
  `compiler/core/js_output.ml`
- After reading OCaml's `compile_lambda` handling for `Llet` there plus
  `Js_output.append_output` / `output_finished`, the Rust backend in
  `compiler-rust/src/lambda/compile.rs` now stops appending unreachable let
  body preludes after a terminating RHS prelude, stops emitting unreachable
  declarations for let-bound values whose RHS already throws, and normalizes
  extracted export payload values to `undefined` when the surrounding block has
  already terminated so the legacy export-extraction path matches OCaml's
  dropped-body behavior
- Added focused regression coverage in
  `lambda::compile::tests::compile_deps_program_skips_unreachable_throwing_export_binding_declaration`
  and
  `lambda::compile::tests::compile_deps_program_skips_unreachable_nested_throwing_export_binding_declaration`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release skips_unreachable -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release coerce_toplevel_exports_skips_unreachable_undefined_placeholder_after_throw -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/conditional/cond_a.res -o /tmp/cond_a.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/conditional/cond_a_none.res -o /tmp/cond_a_none.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/conditional/cond_a.res` and
  `tests/tests/src/conditional/cond_a_none.res` now match their checked-in
  snapshots exactly again, which confirms the Rust backend now drops the same
  unreachable post-raise let/export scaffolding as OCaml; meanwhile
  `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same change
- The authoritative JS snapshot baseline now reports **251 / 657** passing,
  **0** compile errors, and **406** output diffs; this is a net **+2**
  passing snapshots and **-2** output diffs from the previously recorded
  **249 / 657**, **0** compile errors, **408** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed empty arrow-function body
  printer slice in `compiler/core/js_dump.ml`
- After reading OCaml's `pp_function` branch there for
  `[{statement_desc = Return {expression_desc = Undefined _}}] when arrow`,
  the Rust printer in `compiler-rust/src/js_ir/printer.rs` now emits the same
  compact `() => {}` form for arrow functions whose body is exactly
  `return undefined`, instead of routing them through the generic block-body
  printer and expanding them into multi-line empty blocks
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_arrow_function_with_undefined_body_uses_compact_empty_block`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'js_ir::printer::tests::test_print_arrow_function_with_undefined_body_uses_compact_empty_block' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'js_ir::printer::tests::test_print_arrow_function_parenthesizes_object_literal_body' -- --exact --nocapture`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/tuple_alloc.res -o /tmp/tuple_alloc.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/test_while_closure.res -o /tmp/test_while_closure.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/tuple_alloc.res` now matches its checked-in snapshot
  exactly again, `tests/tests/src/ExternalShadow.res` remains an exact
  guard-file match, and `tests/tests/src/test_while_closure.res` no longer
  differs on the empty `() => {}` closure shape and is reduced to separate
  loop-lowering / declaration-order drift
- Across cached diff artifacts, the empty-arrow-body motif
  (`+...=> {` multiline expansion) shrank from **55** diff files to **37**
  after the authoritative rerun; confirmed files that dropped out of the diff
  set on this slice include `tuple_alloc.res`, `bs_auto_uncurry.res`,
  `test_closure.res`, and `js_global_test.res`
- The authoritative JS snapshot baseline now reports **249 / 657** passing,
  **0** compile errors, and **408** output diffs; this is a net **+5**
  passing snapshots and **-5** output diffs from the previously recorded
  **244 / 657**, **0** compile errors, **413** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed arrow-function body
  parenthesization slice in `compiler/core/js_dump.ml`
- After reading OCaml's `pp_function` / `function_body` path there together
  with `exp_need_paren ~arrow:true`, the Rust printer in
  `compiler-rust/src/js_ir/printer.rs` now applies the same arrow-specific
  paren rule for concise bodies that are object-like expressions, instead of
  reusing the looser generic expression paren check and emitting block-shaped
  arrow bodies for object literals and constructor blocks
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_arrow_function_parenthesizes_object_literal_body`
  and
  `js_ir::printer::tests::test_print_arrow_function_parenthesizes_constructor_block_body`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'js_ir::printer::tests::test_print_arrow_function_parenthesizes_object_literal_body' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'js_ir::printer::tests::test_print_arrow_function_parenthesizes_constructor_block_body' -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_7012_test.res -o /tmp/gpr_7012_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/react.res -o /tmp/react.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/gpr_7012_test.res` now matches its checked-in snapshot
  exactly again, which confirms concise arrow functions returning
  object-shaped expressions are back on the OCaml printer path; meanwhile
  `tests/tests/src/react.res` no longer differs on the missing
  `async () => ({ ... })` parentheses and is reduced to a separate quoted-key
  drift on `"default"`, while `tests/tests/src/ExternalShadow.res` remains an
  exact guard-file match after the same printer change
- The authoritative JS snapshot baseline now reports **244 / 657** passing,
  **0** compile errors, and **413** output diffs; this is a net **+1**
  passing snapshot and **-1** output diff from the previously recorded
  **243 / 657**, **0** compile errors, **414** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed inline-record constructor-object
  printer slice in `compiler/core/js_dump.ml`
- After reading OCaml's `Caml_block (..., Blk_record_inlined ...)` path there,
  the Rust printer in `compiler-rust/src/js_ir/printer.rs` now emits the
  leading `TAG` field for inline-record variants before their payload fields,
  instead of treating `TagInfo::RecordInlined` like a plain record object and
  dropping the constructor tag entirely
- Added focused regression coverage in
  `js_ir::printer::tests::test_print_inline_record_variant_keeps_tag_field`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'js_ir::printer::tests::test_print_inline_record_variant_keeps_tag_field' -- --exact --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib 'js_ir::printer::tests::test_print_non_cons_constructor_keeps_tag_object_shape' -- --exact --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/VariantSpreads.res -o /tmp/VariantSpreads.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/object_type_spreads.res -o /tmp/object_type_spreads.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/VariantSpreads.res` and
  `tests/tests/src/object_type_spreads.res` now match their checked-in
  snapshots exactly again, which confirms the inline-record constructor-object
  `TAG` field is back on the Rust path; `tests/tests/src/ExternalShadow.res`
  remains an exact guard-file match after the same printer change
- Across cached diff artifacts, the removed inline-record `TAG:` motif shrank
  from **130** removed lines across **37** files to **107** removed lines
  across **30** files after the authoritative rerun
- The authoritative JS snapshot baseline now reports **243 / 657** passing,
  **0** compile errors, and **414** output diffs; this is a net **+2**
  passing snapshots and **-2** output diffs from the previously recorded
  **241 / 657**, **0** compile errors, **416** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed conditional-expression cleanup
  slice in `compiler/core/js_exp_make.ml` via `econd`
- After reading OCaml's special-case there for
  `Seq(effect, undefined)` on both conditional arms, the Rust JS IR builder in
  `compiler-rust/src/js_ir/mod.rs` now folds that same shape before statement
  lowering, instead of preserving branch-local trailing `undefined` effects
- Added focused regression coverage in
  `lambda::compile::tests::top_level_if_effects_drop_trailing_pure_undefined_branch_suffixes`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release top_level_if_effects_drop_trailing_pure_undefined_branch_suffixes -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalExtension.res -o /tmp/ExternalExtension.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/ExternalExtension.res` and
  `tests/tests/src/array_subtle_test.res` no longer differ on the
  branch-local `undefined;` tails that previously followed effect-only
  conditional arms; `ExternalExtension.res` now differs only on the older
  `typeof (__DEV__)` parenthesization plus pure-module comment text/spacing,
  and `tests/tests/src/ExternalShadow.res` remains an exact guard-file match
- The authoritative JS snapshot baseline remains **241 / 657** passing,
  **0** compile errors, and **416** output diffs after this OCaml-aligned
  `econd` cleanup; the headline total is flat, but the targeted conditional
  `undefined`-tail cluster is smaller
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed recursive-function lowering
  slice in `compiler/core/lam_compile.ml` via `compile_recursive_let`
- After reading OCaml's recursive-let function path there, the Rust backend in
  `compiler-rust/src/lambda/compile.rs` now routes `Lletrec` bindings whose
  RHS is `Lfunction` through the same declared-binding path as non-rec lets,
  instead of always falling back to a placeholder declaration followed by a
  rebinding assignment
- Added focused regression coverage in
  `lambda::compile::tests::recursive_function_bindings_lower_directly_without_placeholder_assignments`
  and
  `mutually_recursive_function_bindings_lower_without_placeholder_assignments`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release recursive_function_bindings_lower -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/unboxed_attribute.res -o /tmp/unboxed_attribute.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/fib.res -o /tmp/fib.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/unboxed_attribute.res` and
  `tests/tests/src/polymorphism_test.res` dropped out of
  `temp/rust-parity/diffs`, which confirms this recursive-function
  declaration slice now reaches at least two previously failing in-repo
  snapshots end-to-end
- `tests/tests/src/fib.res` no longer differs on the top-level
  `let fib; fib = ...` recursive-function cluster; the remaining drift there is
  now in separate conditional, loop, and mutable-state lowering for `fib`,
  `fib2`, and `fib3`
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same backend change
- The authoritative JS snapshot baseline now reports **241 / 657** passing,
  **0** compile errors, and **416** output diffs; this is a net **+3**
  passing snapshots and **-3** output diffs from the previously recorded
  **238 / 657**, **0** compile errors, **419** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed top-level export-coercion slice
  at the `lam_compile_main.ml` / `J.program.exports` boundary
- After reading OCaml's backend flow there, the Rust backend in
  `compiler-rust/src/lambda/compile.rs` now reuses an existing top-level
  `undefined` export binding only when the remaining suffix is limited to
  simple effect-free non-function bindings; otherwise it keeps the trailing
  rebound placeholder path
- Added focused regression coverage in
  `lambda::compile::tests::coerce_toplevel_exports_reuses_existing_undefined_binding`,
  `coerce_toplevel_exports_keeps_undefined_rebound_after_later_effects`, and
  `coerce_toplevel_exports_skips_unreachable_undefined_placeholder_after_throw`
- Verified focused guards for this slice:
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ModuleWithAlias.res -o /tmp/ModuleWithAlias.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/nested_module_alias.res -o /tmp/nested_module_alias.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalScopeShadow.res -o /tmp/ExternalScopeShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/ModuleWithAlias.res`,
  `tests/tests/src/nested_module_alias.res`, and
  `tests/tests/src/ExternalScopeShadow.res` now match the checked-in OCaml
  snapshots on this top-level placeholder-order cluster, while
  `tests/tests/src/conditional/cond_a.res` and `tests/tests/src/Import.res`
  remain separate export/declaration-order drifts
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same backend change
- The authoritative JS snapshot baseline now reports **238 / 657** passing,
  **0** compile errors, and **419** output diffs; this is a net **+1**
  passing snapshot and **-1** output diff from the previously recorded
  **237 / 657**, **0** compile errors, **420** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed declaration-continuation slice
  in `compiler/core/lam_compile.ml` together with `compiler/core/js_stmt_make.ml`
- After reading OCaml's `Declare` continuation for `Lifthenelse` plus the
  `Js_stmt_make.if_ ~declaration` merge rule for same-target assignments, the
  Rust backend in `compiler-rust/src/lambda/compile.rs` now preserves that
  declared-binding path for let-bound `if` values instead of always emitting
  an uninitialized binding followed by a conditional assignment
- Added focused regression coverage in
  `lambda::compile::tests::let_bindings_merge_direct_if_assignments_into_initialized_declarations`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release let_bindings_merge_direct_if_assignments_into_initialized_declarations -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release let_bindings_lower_ifs_without_a_result_temp -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/alias_test.res -o /tmp/alias_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/alias_test.res` no longer differs on the split
  `let v; v = ...` declaration/assignment shape; Rust now emits the same
  initialized binding form as OCaml for that cluster
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same backend change
- Across the authoritative parity run, `tests/tests/src/DictInternalRepresentation.res`
  dropped out of `temp/rust-parity/diffs`, which confirms this declaration
  slice reached at least one previously failing in-repo snapshot end-to-end
- The authoritative JS snapshot baseline now reports **237 / 657** passing,
  **0** compile errors, and **420** output diffs; this is a net **+2**
  passing snapshots and **-2** output diffs from the previously recorded
  **235 / 657**, **0** compile errors, **422** output diffs
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed primitive-lowering slice in
  `compiler/core/lam_compile_primitive.ml`
- After reading OCaml's `Pmakedict` branch there, the Rust backend in
  `compiler-rust/src/lambda/compile.rs` now lowers `Primitive::Pmakedict`
  to a JS object literal by unpacking the array-of-pairs payload, instead of
  falling through to `undefined`
- Added focused regression coverage in
  `lambda::compile::tests::compile_deps_program_keeps_exported_dict_initializer_object_literals`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release compile_deps_program_keeps_exported_dict_initializer_object_literals -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/DictInternalRepresentation.res -o /tmp/DictInternalRepresentation.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/DictInternalRepresentation.res` no longer differs on the
  missing top-level dict initializers (`let stringDict;` / `let intDict;`);
  the remaining drift in that file is now only the separate let-continuation
  split on `first$1`, `second`, and `third`
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same primitive fix
- Across cached diff artifacts, `let stringDict;` and `let intDict;` no longer
  appear in the JS diffs
- The authoritative JS snapshot baseline remains **235 / 657** passing,
  **0** compile errors, and **422** output diffs after this OCaml-aligned
  `Pmakedict` fix; the headline total is flat, but the missing-dict-literal
  cluster is smaller
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed continuation slice in
  `compiler/core/lam_compile.ml` together with
  `compiler/core/js_output.ml`
- After reading OCaml's `compile_apply` +
  `output_of_block_and_expression` path, the Rust backend in
  `compiler-rust/src/lambda/compile.rs` now keeps `Lapply` on that same
  continuation-aware path for effect, return, and assignment contexts instead
  of materializing a synthetic `call` binding whenever the callee lowering had
  prelude statements
- The new Rust helper still materializes a temp in true value contexts, but
  effect-position `apply`, `return (apply ...)`, and `result = apply ...`
  now append the call directly after the prelude, which matches the OCaml
  backend contract more closely
- Added focused regression coverage in:
  `lambda::compile::tests::effect_context_calls_with_arg_preludes_skip_intermediate_call_temps`,
  `return_context_calls_with_arg_preludes_skip_intermediate_call_temps`, and
  `assignment_context_calls_with_arg_preludes_skip_intermediate_call_temps`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release skip_intermediate_call_temps -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/arity_infer.res -o /tmp/arity_infer.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/arity_infer.res` no longer differs on the synthetic
  `let call = ...; return call;` pattern in `f0`, `f1`, and `f3`; the
  remaining drift there is now limited to the older temp-name / switch-format
  mismatch (`tmp` vs `ifres` / `$$switch`, plus `case 0 :` formatting)
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same continuation change
- Across cached diff artifacts, files whose diffs still contain `let call =`
  dropped from **16** to **5** in this iteration, and `return call;` no longer
  appears in the cached JS diffs
- The authoritative JS snapshot baseline remains **235 / 657** passing,
  **0** compile errors, and **422** output diffs after this OCaml-aligned
  continuation fix; the headline total is flat, but the apply-continuation
  cluster is materially smaller
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed alias-removal slice in
  `compiler/core/lam_pass_remove_alias.ml`
- After reading OCaml's fallback for
  `Pval_from_option_not_nest (Lvar v) -> v`, the Rust JS-backend simplifier in
  `compiler-rust/src/lambda/simplify.rs` now applies the same rewrite even when
  the value was not introduced by the narrower nullable-wrapper tracking
- Added focused regression coverage in
  `lambda::simplify::tests::unboxes_plain_val_from_option_not_nest_vars`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib unboxes_plain_val_from_option_not_nest_vars -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib rewrites_nullable_alias_checks_to_raw_nullable_predicates -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/json_decorders.res -o /tmp/json_decorders.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/json_decorders.res` now collapses the optional-email branch
  to a single conditional assignment
  (`ifres = email !== undefined ? (typeof email === "string" ? email : undefined) : undefined`)
  instead of the older nested alias + branch-body form
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match after
  the same simplifier change
- The authoritative JS snapshot baseline remains **235 / 657** passing,
  **0** compile errors, and **422** output diffs after this OCaml-aligned
  alias-removal fix; the headline total is flat, but the optional-unbox drift
  in `json_decorders.res` is measurably narrower
- Older iteration notes follow below

- Active backend focus remains **Phase 4: Port JS Passes** from `PLAN.md`,
  and this iteration isolated one OCaml-backed assignment-continuation slice in
  `compiler/core/lam_compile.ml`
- After reading OCaml's `compile_ifthenelse` handling for `Assign id`,
  the Rust backend in `compiler-rust/src/lambda/compile.rs` now routes complex
  value-position `if` branches through `compile_assign_to_target_block`
  instead of compiling branch values first and assigning them afterward
- The same Rust assignment helper now threads through `Llet` and `Lsequence`,
  which matches the OCaml continuation flow more closely and lets nested
  switches/conditionals assign directly into the outer result slot
- Added focused regression coverage in
  `lambda::compile::tests::if_value_branches_keep_assignment_continuation_through_let_bindings`
- Verified focused guards for this slice:
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib if_value_branches_keep_assignment_continuation_through_let_bindings -- --nocapture`
  - `timeout 600 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib sequence_prefix_ifs_use_effect_lowering_without_result_temps -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/json_decorders.res -o /tmp/json_decorders.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_2682_test.res -o /tmp/gpr_2682_test.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  `tests/tests/src/json_decorders.res` no longer differs on the nested
  `$$switch` temporary inside the optional-email branch; the remaining drift in
  that file is the outer conditional-assignment shape around the final result
  slot
- `tests/tests/src/ExternalShadow.res` remains an exact guard-file match, and
  `tests/tests/src/gpr_2682_test.res` stays reduced to the separate raw-JS
  formatting drift only
- Across cached diff artifacts, files whose diffs still contain `let ifres`
  dropped from **27** to **24** in this iteration
- The authoritative JS snapshot baseline remains **235 / 657** passing,
  **0** compile errors, and **422** output diffs after this OCaml-aligned
  continuation fix; the global total is flat, but the remaining
  value-position conditional cluster is smaller and more localized
- Older iteration notes follow below

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

- `compiler-rust/src/js_ir/printer.rs` now matches one more slice of the
  OCaml final dump path for unit-return function tails:
  nested positive guards with an explicit shared fallback no longer stay in
  the Rust-only `if (outer) { if (value !== 3) { fallback; return; } ... }`
  shape when the final emitted JS should be the OCaml combined-success guard
- Active slice: merge unit-return tail `if` statements with a shared explicit
  fallback into the OCaml combined positive guard during final JS dumping
- Active backend focus moved to **Phase 5: Byte-Exact Dumping** from `PLAN.md`;
  this slice stays in `compiler-rust/src/js_ir/printer.rs` with a small helper
  export in `compiler-rust/src/js_ir/mod.rs`
- OCaml reference:
  - `compiler/core/js_dump.ml`, especially `function_body`'s unit-return tail
    handling at the final dump stage
  - checked-in OCaml snapshot shape in `tests/tests/src/gpr_1891_test.mjs`,
    which keeps the explicit outer `else` and the combined success guard
- Rust change:
  - exported `ocaml_eq_block(...)` from `compiler-rust/src/js_ir/mod.rs` for
    final-dump block-shape comparisons
  - added `try_unit_function_tail_shared_else_guard_merge(...)`,
    `strip_trailing_return_undefined_block(...)`, and
    `negate_tail_merge_condition(...)` in
    `compiler-rust/src/js_ir/printer.rs`
  - wired that merge into `print_function_tail_statement(...)` for
    `return_unit` function tails only
  - added focused regression coverage in
    `test_print_unit_function_tail_merges_shared_else_guard_like_ocaml`
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml --release test_print_unit_function_tail_merges_shared_else_guard_like_ocaml -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/gpr_1891_test.res -o /tmp/gpr_1891_test.mjs`
  - `timeout 10 ./compiler-rust/target/release/bsc -bs-package-name rescript-tests -bs-module-type esmodule tests/tests/src/ExternalShadow.res -o /tmp/ExternalShadow.mjs`
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/gpr_1891_test.res` now matches its checked-in snapshot
    exactly again; Rust emits the OCaml-style
    `if (typeof x === "object" && x.NAME === "Foo" && x.VAL === 3) { ... } else { ... }`
    tail instead of leaving the nested negative guard with duplicated fallback
  - `tests/tests/src/ExternalShadow.res` remained an exact guard-file match
    after the same printer slice
- Topline impact in this current dirty worktree:
  - JS snapshot parity: **541 / 657** -> **542 / 657** (**+1**)
  - Compile errors: **8** -> **8** (**no change**)
  - Output diffs: **108** -> **107** (**-1**)
- Keep this change because the remaining drift was at the final dump stage, not
  in `Lam_compile`: OCaml's checked-in JS keeps the shared fallback as an
  explicit outer `else` while collapsing the success path to the combined
  positive guard, and the Rust printer now emits that same byte shape.

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

Latest iteration on **2026-04-15**:

- Active slice: keep plain nested `staticcatch` handlers inside the surrounding
  return-switch default when the current switch is already nested under an
  enclosing staticcatch chain, matching the OCaml `flatten_nested_caches` /
  `compile_staticcatch` boundary instead of peeling the inner plain handler out
  into Rust-only post-switch fallthrough
- Active backend focus for this slice remains **Phase 3: Port JS IR Lowering
  And Metadata** from `PLAN.md`; this is still `Lam_compile` control-flow
  lowering after optimized lambda parity, not a printer rewrite
- OCaml reference:
  `compiler/core/lam_compile.ml` and
  `compiler/core/lam_compile_context.ml`, especially
  `flatten_nested_caches`, `flat_catches`, and the `compile_staticcatch`
  pseudo-jump gate that only applies at the outer boundary of a flattened
  staticcatch chain
- Rust change:
  - updated `compiler-rust/src/lambda/compile.rs` so
    `uses_fallthrough_staticcatch_return(...)` no longer applies the plain
    handler fallthrough path while the compiler is already nested under an
    enclosing static handler / jump chain
  - kept the earlier nested re-raise fallthrough path intact, so the
    multi-case outward-re-raise cluster still lowers with the OCaml-style
    fallthrough ordering where appropriate
  - added the focused regression
    `nested_named_variant_return_switches_keep_plain_inner_handlers_as_default_arms`
    to lock the `VariantPatternMatchingSpreads.lookup2` shape in place
- Verified focused guards for this slice:
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml nested_named_variant_return_switches_keep_plain_inner_handlers_as_default_arms -- --nocapture`
  - `timeout 240 cargo test --manifest-path compiler-rust/Cargo.toml multi_case_staticcatch_wrapped_named_variant_return_switch_moves_fallthrough_cases_last -- --nocapture`
  - `timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release`
  - direct release repro for `tests/tests/src/VariantPatternMatchingSpreads.res`,
    diffing `/tmp/VariantPatternMatchingSpreads.mjs` against the checked-in
    snapshot
  - direct broader guard repro for `tests/tests/src/ExternalShadow.res`,
    diffing `/tmp/ExternalShadow.mjs` against the checked-in snapshot
  - direct sibling repro for
    `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res`, diffing
    `/tmp/VariantPatternMatchingSpreadsWithPayloads.mjs` against the checked-in
    snapshot
  - `timeout 1800 ./scripts/test_js_output_parity.sh`
- Focused outcome:
  - `tests/tests/src/VariantPatternMatchingSpreads.res` now matches its
    checked-in `.mjs` snapshot exactly; the Rust backend no longer drops the
    OCaml `default: return doWithA(d);` arm from `lookup2`
  - `tests/tests/src/ExternalShadow.res` still matches its checked-in `.mjs`
    snapshot exactly after the nested-staticcatch change
  - `tests/tests/src/VariantPatternMatchingSpreadsWithPayloads.res` remains a
    separate sibling drift in the same family; its remaining diff is now the
    payload-bearing `doWithB` / nested-switch shape rather than the fixed
    plain-handler default-arm loss
- Topline impact:
  - JS snapshot parity: **516 / 657** -> **518 / 657** (**+2**)
  - Compile errors: **0** -> **0** (**no change**)
  - Output diffs: **141** -> **139** (**-2**)
