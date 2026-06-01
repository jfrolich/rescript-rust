# Ralph TODO: JS Output Parity

## Current Baseline

Status as of 2026-04-23: **660 / 660** in the canonical in-repo JS
snapshot suite.

Measured on the `combined` branch after the typechecker-performance merge,
13.0.0-alpha.4 backports, the last typechecker crash fix, and the final two JS
output shape fixes.

- 0 compile errors
- 0 Rust crashes
- 0 output diffs
- `timeout 1800 ./scripts/test_js_output_parity.sh` reported `660 / 660`
- Spice PPX was skipped locally because the private PPX binary was not present

## Remaining JS Output Parity Diffs

None in the canonical in-repo JS snapshot suite.

## Completed Work

- [x] Run the first dedicated `./scripts/test_js_output_parity.sh` baseline and record the full results.
- [x] Re-run the wrapper after rescoping it to the canonical in-repo suite.
- [x] Route final JS codegen in `compiler-rust/src/driver.rs` through the raw-lambda / lowering path instead of the legacy typedtree shortcut.
- [x] Inventory the internal compile-error files from `temp/rust-parity/diffs/js_src_*.err`.
- [x] Inventory the internal text-diff files from `temp/rust-parity/diffs/js_src_*.diff`.
- [x] Port the OCaml lambda simplification pipeline as real Rust passes instead of a monolithic shortcut.
- [x] Remove the old `simplify_with_env` / `SimplifyEnv` monolith.
- [x] Fix the final `js_json_test.res` control-flow shape diff.
- [x] Fix the final `Stdlib_IteratorTests.res` effect-position switch diff.
- [x] Reconfirm the canonical suite at 100%.

## Final Fixed Diffs

### `tests/tests/src/js_json_test.res`

Rust previously compiled a `switch` with only one side-effecting object arm as
a wrapping `if (!Array.isArray(json) && json !== null) { switch (...) }`.
OCaml emits an early `return` for `json === null || Array.isArray(json)`, then
switches on `typeof json`.

The fix was to filter default-equivalent runtime-test cases before building the
untagged-block `typeof` switch while still using the unfiltered runtime-test
presence to prevent small-tail collapse. In unit-return tail position, Rust now
emits the OCaml-shaped early-return object guard.

### `tests/tests/src/stdlib/Stdlib_IteratorTests.res`

Rust previously elided effect-position switches whose result was unused,
turning them into `undefined` expressions and shifting later `match$N`
bindings. OCaml preserves the effectful switch structure even when every arm
returns unit.

The fix was to preserve emitted `Lswitch` and `Lstringswitch` blocks in the
statement prelude instead of reducing the whole effect-position expression to
`undefined`.

## Historical Notes

The old 1.2 MB version of this handoff was mostly repeated Ralph loop
transcripts from sessions 18-53 on 2026-04-22. Those sessions re-verified an
older **653 / 657** state with four typechecker-stage failures and no JS backend
diffs. That state is superseded by the current **660 / 660** baseline above.

Useful context retained from those logs:

- The four old 653/657 failures were typechecker failures before JS backend
  code ran, mostly around functor-instance typing and module strengthening.
- Running files outside the harness could surface different diagnostics; use
  the parity script or the harness path when rechecking historical failures.
- `compiler-rust/src/lambda/simplify.rs` should not grow a new monolithic
  simplifier. The OCaml stages should remain separate ports.
- `simplify_with_env` and `SimplifyEnv` should stay absent unless a future
  OCaml reference change introduces equivalent structure.

## Working Rules

- Preserve JavaScript output parity with the OCaml reference compiler.
- Prefer 1:1 OCaml ports over Rust-only output-shape compensations.
- Do not normalize generated JS snapshots to hide backend differences.
- Keep the parity script as the source of truth for the in-repo snapshot suite.
