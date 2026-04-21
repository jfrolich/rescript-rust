# JS Output Parity Plan

## PREREQUISITE — MUST COMPLETE FIRST

**Before doing ANY other JS output parity work, complete the performance plan in
[PERFORMANCE_PLAN.md](./PERFORMANCE_PLAN.md) in full.** This decomposes the
monolithic `simplify.rs` into the same separate passes OCaml uses. No parity
fixing, no new features, no other work until the OCaml-aligned pipeline is in place.

**Specifically: `simplify_with_env` and the entire `SimplifyEnv` struct MUST BE
DELETED.** Not kept alongside. Not gradually migrated. Deleted. The 15,000-line
monolithic simplifier is replaced by the OCaml-aligned pass pipeline. If parity
regresses, fix it by porting more OCaml code, not by keeping the monolith alive.

## CRITICAL RULE — Direct OCaml Port Only

**Never add or delete a line of Rust code unless it directly corresponds to a
specific line in the OCaml source code.** Every function, every branch, every
condition must be traceable to a concrete location in the OCaml codebase. This
applies to ALL work in this project, not just the performance plan:

- No invented workarounds or heuristics
- No "this helps with parity" logic that doesn't exist in OCaml
- No Rust-specific optimizations or cleverness
- If you cannot cite the OCaml file and line number, do not write the code
- If existing Rust code has no OCaml equivalent, delete it
- **Do NOT add parity fixes to the old monolithic code.** That code is being
  deleted. Any time spent fixing it is wasted.

## Goal

Achieve **100% byte-for-byte emitted JavaScript parity** between the Rust compiler
and the OCaml reference compiler for:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

This project targets the final emitted `.mjs` / `.bs.js` snapshots, not lambda
dumps or typedtree dumps.
The dedicated wrapper defaults to the same canonical in-repo 657-file set used
by the typedtree and lambda parity projects.

## Upstream Status

For this project, treat the upstream parity stages as already complete:

- typedtree parity: **657/657**
- raw lambda parity: **657/657**
- optimized lambda parity: **657/657**

There are no open parity issues to solve in those stages for this project. The
remaining work is strictly downstream in the backend after optimized lambda.

## Scope

The direct parity target is:

```text
typedtree
  -> raw lambda
  -> Lam_convert.convert
  -> lam_pass_* pipeline
  -> Lam_coercion.coerce_and_group_big_lambda
  -> Lam_compile.compile_group
  -> J.program / J.deps_program
  -> js_pass_* pipeline
  -> Js_dump_program / Js_dump
  -> emitted JavaScript
```

For this project, "JS output parity" means Rust must match the checked-in JS
snapshots produced by the OCaml backend.

## Critical Clarification

Typedtree parity and both lambda parity stages are already complete. The
remaining backend gap starts after the optimized-lambda dump boundary.

OCaml continues through the later backend in
`compiler/core/lam_compile_main.ml`:

1. `Lam_pass_*` over `Lam.t`
2. `Lam_coercion.coerce_and_group_big_lambda`
3. `compile_group` / `Lam_compile`
4. `Js_pass_*`
5. `Js_dump_program`

This project starts at exactly that downstream boundary.

## Non-Goals

Out of scope for direct JS output parity:

- parser AST parity
- binary AST parity
- syntax printer parity
- typedtree sexp parity
- raw lambda parity
- optimized lambda dump parity

Those stages are already green and remain guards only. They are not the active
frontier for this project.

## Current Architecture Gap

### OCaml backend path

```text
typedtree
  -> raw lambda
  -> optimized lambda
  -> lam_pass_* pipeline
  -> grouped/coerced lambda
  -> JS IR
  -> js_pass_* pipeline
  -> emitted JS
```

### Rust current path

```text
typedtree
  -> raw lambda              (used for dump parity)
  -> optimized lambda        (used for dump parity)

typedtree
  -> lambda::convert::LambdaConverter::convert_structure
  -> lambda::compile::LambdaCompiler
  -> js_ir::printer
  -> emitted JS
```

The current Rust JS path is still a legacy shortcut and does not yet go through
the OCaml-aligned backend pipeline that starts after the already-correct
typedtree/raw/optimized-lambda stages.

## Ownership Map

| OCaml source | Rust target | Role | Current status |
|-------------|-------------|------|----------------|
| `compiler/core/lam_compile_main.ml` | `compiler-rust/src/driver.rs` | route final codegen through the correct backend path | wrong path |
| `compiler/core/lam_pass_*.ml` | future `compiler-rust` lambda passes | post-lowering lambda optimization | mostly missing from codegen path |
| `compiler/core/lam_coercion.ml` | future Rust backend layer | group/export lowering before JS IR | not on JS path |
| `compiler/core/lam_compile.ml` | `compiler-rust/src/lambda/compile.rs` | lambda/group -> JS IR lowering | baseline only |
| `compiler/core/j.ml` | `compiler-rust/src/js_ir/mod.rs` | JS IR definition | partial |
| `compiler/core/js_pass_*.ml` | future Rust JS passes | JS IR cleanup/optimization | mostly missing |
| `compiler/core/js_dump_program.ml` / `js_dump.ml` | `compiler-rust/src/js_ir/printer.rs` | byte-for-byte JS emission | baseline only |

## Milestones

### Phase 0: Baseline And Harness

Objective:
- establish a dedicated JS-output parity project and wrapper command
- keep Spice parity enabled as a guard
- record the authoritative baseline from the existing snapshot harness
- make the upstream-status assumption explicit so work stays focused downstream
- default the wrapper to the canonical 657-file in-repo set instead of the
  external corpus

Acceptance:
- `./scripts/test_js_output_parity.sh` exists
- `projects/js-output-parity/` documents the current frontier
- a measured baseline is recorded in `RALPH_TODO.md`
- the default baseline only covers `tests/tests/src`

### Phase 1: Route JS Through The Real Backend Path

Objective:
- stop generating final JS from the legacy typedtree -> lowered lambda shortcut
- feed JS generation from `raw_lambda::convert` + `raw_lambda::lower`

Acceptance:
- the Rust JS path shares the same raw/optimized-lambda boundary used by dump parity
- compile-error count drops on representative files

### Phase 2: Port Post-Lowering Lambda Backend Stages

Objective:
- port the OCaml backend stages between optimized lambda and JS IR

Primary targets:
- `Lam_pass_deep_flatten`
- `Lam_pass_exits`
- `Lam_pass_remove_alias`
- `Lam_pass_alpha_conversion`
- `Lam_pass_lets_dce`
- `Lam_coercion.coerce_and_group_big_lambda`

Acceptance:
- structural JS diffs collapse on representative in-repo files
- compile-error clusters move into diff clusters instead of crashes

### Phase 3: Port JS IR Lowering And Metadata

Objective:
- match OCaml's `compile_group` / `Lam_compile` behavior
- match dependency/module/export metadata in `J.deps_program`

Acceptance:
- export/import/module-wrapper diffs shrink materially
- module dependency ordering becomes stable

### Phase 4: Port JS Passes

Objective:
- match OCaml's JS-pass pipeline before printing

Primary targets:
- `Js_pass_flatten`
- `Js_pass_external_shadow`
- `Js_pass_tailcall_inline`
- `Js_pass_flatten_and_mark_dead`
- `Js_pass_scope`
- `Js_shake`

Acceptance:
- previously broad formatting/shape diffs collapse on large files
- large-file clusters start passing exactly

### Phase 5: Byte-Exact Dumping

Objective:
- make the final printer/dumper byte-for-byte identical after IR parity exists

Acceptance:
- remaining diffs are reduced to printer-only details
- full snapshot parity reaches 100%

## Focus Files

Start with in-repo files first because they are faster to iterate and easier to
compare against checked-in snapshots. The dedicated wrapper measures only this
canonical in-repo set by default.

### Small Internal Structural Files

- `tests/tests/src/ExternalShadow.res`
- `tests/tests/src/LetUnwrap.res`
- `tests/tests/src/keep_uncurry_attribute.res`
- `tests/tests/src/return_check.res`
- `tests/tests/src/test_other_exn.res`
- `tests/tests/src/test_unsafe_cmp.res`

### Internal Compile-Error Guards

- `tests/tests/src/gpr_3595_test.res`
- `tests/tests/src/js_array_test.res`
- `tests/tests/src/stdlib/Stdlib_TypedArrayTests.res`

### Large External Clusters

Use these only after a rule seems correct on internal files:

- `@rescript/react` modules
- `rescript-webapi` modules
- `tella-fusion` frontend/backend files under `packages/core/webapp`

## Success Criteria

Only when all are true:

- `./scripts/test_js_output_parity.sh` reports full JS snapshot parity
- Spice PPX guard remains non-regressing on the same command
- no unchecked tasks remain in `RALPH_TODO.md`
- typedtree, raw lambda, and optimized lambda guards stay green when shared
  backend code changes
