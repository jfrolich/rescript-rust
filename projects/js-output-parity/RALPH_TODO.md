# Ralph TODO: JS Output Parity

**Last Updated:** 2026-04-12
**Status:** 49 / 657 JS snapshots passing, 0 compile errors, 608 output diffs

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

Latest authoritative wrapper run on **2026-04-12** using:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

reported:

- JS snapshot parity: **49 / 657**
- Compile errors: **0**
- Output diffs: **608**
- Diff artifacts written under `temp/rust-parity/diffs`
- Spice PPX guard: **skipped by harness in this environment** because `SPICE_PPX` was not found at the configured path

Interpretation:

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
- `tests/tests/src/AsInUncurriedExternals.res` is now fully resolved in the
  checked-in snapshot set; `tests/tests/src/Import.res` narrowed further after
  the simplifier removed some dead-let churn, but its remaining drift is still
  later backend shaping rather than import-path resolution
- the `ExternalShadow.res` cluster is now resolved end-to-end in the checked-in
  snapshot set; the remaining frontier has moved on from that external-call /
  shadowing case
- external-corpus sweeps remain secondary; the in-repo backend frontier still has
  ample signal

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
