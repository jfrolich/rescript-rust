# Ralph TODO: JS Output Parity

**Last Updated:** 2026-04-12
**Status:** 0 / 2784 JS snapshots passing, 1927 compile errors, 857 output diffs

## Goal

Achieve **100% byte-for-byte emitted JavaScript parity** between the Rust
compiler and the OCaml reference implementation using:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

Execution order and phase gates live in `PLAN.md`.

## Current Baseline

Authoritative wrapper run on **2026-04-12** using:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

reported:

- JS snapshot parity: **0 / 2784**
- Compile errors: **1927**
- Output diffs: **857**
- Diff artifacts written under `temp/rust-parity/diffs`
- Spice PPX guard: **skipped by harness in this environment** because `SPICE_PPX` was not found at the configured path

Interpretation:

- the current Rust final codegen path is still fundamentally misaligned
- the first frontier is routing and backend-shape correctness, not last-mile printing
- compile failures still dominate, but one Phase 1 routing change already converted a hard failure into a diff

This wrapper baseline included the in-repo snapshots plus the configured
external corpus under `TELLA_DIR`.

## Working Rules

1. **Read the OCaml source first.** Do not infer backend semantics from JS diffs alone.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Treat compile errors as highest priority.** A crash or compile failure hides downstream diff information.
5. **Fix the backend path, not the output string by hand.** Final printer work is the last mile, not the starting point.
6. **Keep Spice enabled as a guard.** It is built into the compiler now and should not be artificially skipped in the project wrapper.

## Immediate Frontier

- [x] Run the first dedicated `./scripts/test_js_output_parity.sh` baseline and record the full results here.
- [x] Route final JS codegen in `compiler-rust/src/driver.rs` through the raw-lambda / lowering path instead of the legacy typedtree shortcut.
- [ ] Inventory the current internal compile-error files from `temp/rust-parity/diffs/js_src_*.err`.
- [ ] Inventory the current internal text-diff files from `temp/rust-parity/diffs/js_src_*.diff`.
- [ ] Pick one small internal structural file and one internal compile-error guard as the first implementation targets.

## Expected Root-Cause Buckets

- backend routing still bypasses the OCaml-aligned raw-lambda path
- missing post-lowering lambda passes
- missing coercion/grouping before JS lowering
- baseline `LambdaCompiler` shape differs from `Lam_compile`
- missing `js_pass_*` normalization
- final JS printer/dumper byte-shape differences

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

Internal compile errors already observed in the pre-wrapper run:

- `tests/tests/src/gpr_3595_test.res`
- `tests/tests/src/js_array_test.res`
- `tests/tests/src/stdlib/Stdlib_TypedArrayTests.res`

## Latest Session Findings

- A dedicated wrapper script now exists at `scripts/test_js_output_parity.sh`.
- The wrapper keeps Spice enabled by default, but the first authoritative run skipped the Spice guard because the configured external `SPICE_PPX` binary was missing in this environment.
- The existing JS-output parity check already lived inside `scripts/test_rust_parity.sh`; the new wrapper now gives it a dedicated project entry point.
- The current measured JS frontier is severe enough that project work should start at backend routing, not printer polish.
- `compiler-rust/src/driver.rs` now routes final JS generation through `raw_lambda::convert` + `raw_lambda::lower` instead of the legacy `lambda::convert::LambdaConverter` shortcut.
- The authoritative baseline moved from **1928 compile errors / 856 diffs** to **1927 compile errors / 857 diffs**, which indicates one hard failure turned into an emitted-JS mismatch.
- Focused checks after the routing change:
  - `tests/tests/src/ExternalShadow.res` still differs structurally, but it now clearly reflects the raw-lambda-backed path.
  - `tests/tests/src/js_array_test.res` still fails during type checking with `UndefinedMethod { method: "describe" }`, so that compile-error cluster remains active.
