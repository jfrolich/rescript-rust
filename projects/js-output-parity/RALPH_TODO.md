# Ralph TODO: JS Output Parity

**Last Updated:** 2026-04-12
**Status:** 29 / 657 JS snapshots passing, 0 compile errors, 628 output diffs

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

Authoritative wrapper run on **2026-04-12** using:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

reported:

- JS snapshot parity: **29 / 657**
- Compile errors: **0**
- Output diffs: **628**
- Diff artifacts written under `temp/rust-parity/diffs`
- Spice PPX guard: **skipped by harness in this environment** because `SPICE_PPX` was not found at the configured path

Interpretation:

- the authoritative wrapper is now scoped to the canonical in-repo 657-file set
- all current internal JS snapshot files now compile under the wrapper baseline
- the former `Import.res` timeout is now exposed as a normal output-diff case
- preserving OCaml external-spec metadata through `PjsCall` is necessary for
  backend parity after optimized lambda: `@val`, `@new`, `@get`, and related
  externals cannot be lowered as a generic `primName(...)` call
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
- `compiler-rust/src/lambda/compile.rs` now applies a port of `js_pass_external_shadow.ml`, so lexical shadowing of JS globals rewrites initializer/self-property reads through `globalThis` without rewriting unrelated uses like `parseInt`.
- `compiler-rust/src/js_ir/printer.rs` no longer reorders top-level function-valued bindings ahead of earlier statements; the Rust printer now preserves OCaml's block order.
- Typedtree parity and both lambda parity stages are considered complete for this project and are not part of the remaining frontier.
