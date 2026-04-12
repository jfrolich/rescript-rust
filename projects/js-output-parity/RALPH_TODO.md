# Ralph TODO: JS Output Parity

**Last Updated:** 2026-04-12
**Status:** 0 / 2784 JS snapshots passing, 90 compile errors, 2694 output diffs

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

- JS snapshot parity: **0 / 2784**
- Compile errors: **90**
- Output diffs: **2694**
- Diff artifacts written under `temp/rust-parity/diffs`
- Spice PPX guard: **skipped by harness in this environment** because `SPICE_PPX` was not found at the configured path

Interpretation:

- the current wrapper is now measuring project-context JS output instead of mostly standalone-file compile failures
- remaining compile failures are a much smaller, more targeted cluster
- the canonical JS baseline should still be rescoped to the same in-repo 657-file set as
  the typedtree and lambda parity projects
- external-corpus runs remain useful, but should become an explicit secondary sweep after that rescope
- typedtree/raw/optimized-lambda are not part of the active frontier

This measured baseline still includes the external corpus under `TELLA_DIR`.
Rescoping the wrapper to the canonical in-repo set remains pending.

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
- [ ] Re-run the wrapper after rescoping it to the canonical 657-file in-repo set and record the new baseline.
- [x] Route final JS codegen in `compiler-rust/src/driver.rs` through the raw-lambda / lowering path instead of the legacy typedtree shortcut.
- [x] Inventory the current internal compile-error files from `temp/rust-parity/diffs/js_src_*.err`.
- [x] Inventory the current internal text-diff files from `temp/rust-parity/diffs/js_src_*.diff`.
- [ ] Pick one small internal structural file and one internal compile-error guard as the first implementation targets.

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

Current internal compile error under the measured wrapper baseline:

- `tests/tests/src/Import.res`

## Latest Session Findings

- A dedicated wrapper script now exists at `scripts/test_js_output_parity.sh`.
- The wrapper keeps Spice enabled by default, but the authoritative runs still skip the Spice guard in this environment because the configured external `SPICE_PPX` binary is missing.
- The existing JS-output parity check already lived inside `scripts/test_rust_parity.sh`; the wrapper now exposes that section directly.
- `compiler-rust/src/driver.rs` now routes final JS generation through `raw_lambda::convert` + `raw_lambda::lower` instead of the legacy `lambda::convert::LambdaConverter` shortcut.
- `scripts/test_rust_parity.sh` now compiles JS snapshots with each file's owning ReScript project's `compiler-args` and runs `bsc` from that project's `lib/bs`.
- This removed the largest source of false compile-error noise:
  - the measured wrapper baseline moved from **1927 compile errors / 857 diffs** to **90 compile errors / 2694 diffs**
  - internal compile errors dropped to **1 file**: `js_src_Import.res.err`
  - internal text diffs now account for **656 files**
- Verified focused checks under the new project-context invocation:
  - `tests/tests/src/js_array_test.res` now compiles and lands in JS diff territory instead of failing with `UndefinedMethod { method: "describe" }`
  - `/Users/jake/dev/tella-fusion/packages/core/webapp/src/backend/Service__PublicVideo.res` now compiles and lands in JS diff territory instead of a missing-binding failure
- Typedtree parity and both lambda parity stages are considered complete for this project and are not part of the remaining frontier.
