# Ralph TODO: JS Output Parity

**Last Updated:** 2026-04-12
**Status:** 70 / 657 JS snapshots passing, 0 compile errors, 587 output diffs

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

- JS snapshot parity: **70 / 657**
- Compile errors: **0**
- Output diffs: **587**
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
- allocating constant blocks still need OCaml-style sharing on the JS backend
  path: record / variant / module constants cannot be substituted through
  `let` bindings the way scalar constants can, or the backend duplicates
  literals that OCaml keeps as shared bindings
- `tests/tests/src/AsInUncurriedExternals.res` is now fully resolved in the
  checked-in snapshot set; `tests/tests/src/Import.res` narrowed further after
  the simplifier removed some dead-let churn, but its remaining drift is still
  later backend shaping rather than import-path resolution
- the `ExternalShadow.res` cluster is now resolved end-to-end in the checked-in
  snapshot set; the remaining frontier has moved on from that external-call /
  shadowing case
- external-corpus sweeps remain secondary; the in-repo backend frontier still has
  ample signal
- OCaml `js_dump_program.ml` empty-deps-program output is now matched on the Rust
  printer path:
  import-free empty modules emit the checked-in
  `/* This output is empty... */` explanation instead of the generic
  `/* No side effect */` trailer
- OCaml `js_dump_program.ml` vertical spacing is now matched more closely on the
  Rust printer path:
  non-empty import-free modules keep the extra blank line after the ReScript
  header, and ES-module imports keep the blank line before the first statement

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
