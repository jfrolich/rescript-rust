# Optimized Lambda Parity Plan

## Goal

Achieve **100% optimized lambda parity** between the Rust and OCaml compilers for:

```bash
./scripts/test_lambda_parity.sh -j1
```

This project targets the output of **`-dlambda-sexp`** and **`-dlambda-sexp-locs`**.

## Scope

The direct parity target is:

```text
typedtree -> raw lambda -> Lam_convert.convert -> sexp printer
```

For this project, "optimized lambda parity" means Rust must match the OCaml lambda that
OCaml prints from `lam_compile_main.ml` immediately after `Lam_convert.convert`.

## Critical Clarification

OCaml does **not** print `-dlambda-sexp` after the later `lam_pass_*` pipeline.
In `compiler/core/lam_compile_main.ml`, OCaml does:

1. `Lam_convert.convert export_ident_sets lam`
2. print `Sexp_lambda.print_lambda lam`
3. only then continue into `Lam_pass_deep_flatten`, `Lam_pass_exits`, etc.

That means the direct parity target for this project is **`Lam_convert.convert` output**,
not the later deep-flatten / exits / alias / alpha / lets-dce passes.

Those later passes still matter for JS backend correctness, but they are **not** the
thing compared by `./scripts/test_lambda_parity.sh` in default mode.

## Non-Goals

Out of scope for direct `-dlambda-sexp` parity:

- `Lam_pass_deep_flatten`
- `Lam_pass_exits`
- `Lam_pass_remove_alias`
- `Lam_pass_alpha_conversion`
- `Lam_pass_lets_dce`
- JS IR / JS output parity

These are downstream backend concerns. Keep them as guards only unless a specific change
needs them for shared infrastructure.

## Current Baseline

Authoritative baseline from:

```bash
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Current status:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **0/657**
- Stamp-canonicalized parity: **0/657**
- Exact hunks: **1631**
- Normalized hunks: **1631**

Interpretation:

- compile coverage is already clean
- stamp numbering is not the issue
- the stage shape itself is wrong everywhere

## Current Architecture Gap

### OCaml parity path

```text
typedtree
  -> translcore/translmod raw lambda
  -> Lam_convert.convert
  -> print -dlambda-sexp
```

### Rust current path

```text
typedtree
  -> lambda::convert::LambdaConverter::convert_structure
  -> print -dlambda-sexp
```

### Desired Rust path

```text
typedtree
  -> raw_lambda::convert
  -> raw_lambda::lower  (real Lam_convert.convert port)
  -> print -dlambda-sexp
```

## Ownership Map

| OCaml source | Rust target | Role | Current status |
|-------------|-------------|------|----------------|
| `compiler/core/lam_compile_main.ml` | `compiler-rust/src/driver.rs` | route `-dlambda-sexp` through the correct stage | wrong path |
| `compiler/core/lam_convert.ml` | `compiler-rust/src/raw_lambda/lower.rs` | raw lambda -> optimized lambda conversion | stub |
| `compiler/core/sexp_lambda.ml` | `compiler-rust/src/lambda/sexp_lambda.rs` | parity printer | present; should stay dumb |
| `compiler/ml/translcore.ml` / `translmod.ml` | `compiler-rust/src/raw_lambda/convert.rs` | raw lambda producer | parity complete for `-drawlambda` |
| later `lam_pass_*` modules | later backend work | JS/backend pipeline | out of direct parity scope |

## Milestones

### Phase 0: Correct the Routing

Objective:
- make `-dlambda-sexp` use the raw-lambda path plus the real lowering boundary
- stop using the legacy typedtree-to-lambda shortcut for parity dumps

Tasks:
- add a dedicated optimized-lambda dump path in `driver.rs`
- build raw lambda with the existing raw converter
- lower raw lambda through `raw_lambda/lower.rs`
- print from the lowered result
- keep the existing JS compilation path unchanged until the dump path is stable

Acceptance:
- Rust compile coverage stays **657/657**
- raw parity stays **657/657**
- optimized output changes materially on the focus files
- the 1-hunk files become easier to interpret structurally

### Phase 1: Port `Lam_convert.convert`

Objective:
- replace the identity `raw.into_lowered()` shim with a real OCaml-aligned lowering pass

Tasks:
- read `compiler/core/lam_convert.ml` first
- port the conversion order and control flow, not just the output shape
- preserve alias synchronization behavior described in `lam_convert.mli`
- preserve module dependency collection side effects
- match let/application/primitive/module-export construction rules
- do **not** sneak in later-pass behavior here

Acceptance:
- smallest structural files start collapsing
- `AsInUncurriedExternals.res` no longer shows obviously wrong `Lsequence` / `Alias` shape
- `minimal_test.res` no longer ends in the wrong export tail

### Phase 2: Eliminate Structural Clusters

Objective:
- reduce global failures by fixing high-leverage lowering motifs

Primary motif buckets:
- module export tail shape
- let-kind selection (`Strict` / `Alias` / `StrictOpt` / `Variable`)
- application status (`App_na`, `App_uncurry`, etc.)
- JS-call primitive shape
- constant / block / pointer representation
- module/coercion-lowered forms

Acceptance:
- smallest 1-hunk files drop out steadily
- exact and normalized hunk counts both move down

### Phase 3: Large Cluster Cleanup

Objective:
- use the large hunk files to catch broad lowering discrepancies

Priority cluster:
- `js_array_test.res`
- `caml_compare_test.res`
- `js_math_test.res`
- `js_string_test.res`
- `js_float_test.res`

Acceptance:
- top-5 largest hunk counts fall materially
- file-count parity starts moving, not just hunk counts

### Phase 4: `-dlambda-sexp-locs` Hardening

Objective:
- once non-location parity is moving, use `-dlambda-sexp-locs` to verify location threading

Acceptance:
- `-dlambda-sexp` parity remains non-regressing
- loc mismatches are isolated to actual location threading issues

## Focus Files

### Smallest structural files

Use these first for fast iteration:

- `AsInUncurriedExternals.res`
- `Coercion.res`
- `DictInference.res`
- `DictInternalRepresentation.res`
- `DictPatternMatchingOptimization.res`
- `DisambiguateOptionalFields.res`
- `DotDotDot.res`

These are ideal for validating one lowering rule at a time.

### Largest cluster files

Use these after a rule seems correct:

- `js_array_test.res`
- `caml_compare_test.res`
- `js_math_test.res`
- `js_string_test.res`
- `js_float_test.res`
- `bs_queue_test.res`
- `bs_set_int_test.res`

These validate whether the rule generalizes.

## Debugging Workflow

### Stage isolation

For any failing file:

1. Compare `-drawlambda`
2. Compare `-dlambda-sexp`
3. Compare `-dlambda-sexp-locs` only if needed

Decision rule:

- if `-drawlambda` differs, the bug is upstream and does **not** belong in this project
- if `-drawlambda` matches but `-dlambda-sexp` differs, the bug belongs in `Lam_convert.convert` / `raw_lambda/lower.rs`
- if `-dlambda-sexp` matches but `-dlambda-sexp-locs` differs, the bug is location threading or location printing

### Direct repro workflow

```bash
cd tests/tests
JSON=$(../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/AsInUncurriedExternals.res)
ARGS=$(node -e 'const o=JSON.parse(process.argv[1]); console.log(o.compiler_args.map(x=>JSON.stringify(x)).join(" "))' "$JSON")
cd lib/bs

timeout 10 ../../../../compiler-rust/target/release/bsc -drawlambda $ARGS 1>/dev/null 2>/tmp/rust.raw
timeout 10 ../../../../_build/install/default/bin/bsc -drawlambda $ARGS 1>/dev/null 2>/tmp/ocaml.raw

timeout 10 ../../../../compiler-rust/target/release/bsc -dlambda-sexp $ARGS 1>/dev/null 2>/tmp/rust.lambda
timeout 10 ../../../../_build/install/default/bin/bsc -dlambda-sexp $ARGS 1>/dev/null 2>/tmp/ocaml.lambda

diff -u /tmp/ocaml.raw /tmp/rust.raw | sed -n '1,220p'
diff -u /tmp/ocaml.lambda /tmp/rust.lambda | sed -n '1,220p'
```

### Logging rule

If a structural mismatch is unclear:

- add temporary logging in OCaml `lam_convert.ml`
- add matching temporary logging in Rust `raw_lambda/lower.rs`
- compare traversal order and constructor choices directly

Do not guess from the final sexp alone if the control flow is ambiguous.

## Autonomous Loop Requirements

For a long-running autonomous effort:

1. Re-run the authoritative baseline before trusting any local conclusion.
2. Work from the current phase in this plan, not from random diffs.
3. Use one small file to validate the rule.
4. Use one large file to validate that it generalizes.
5. Re-run the baseline.
6. Commit immediately after each verified OCaml-aligned improvement.
7. Update `RALPH_TODO.md` with the new numbers and what changed.

## First Milestone

The first milestone is not "port all passes."

The first milestone is:

- reroute `-dlambda-sexp` through raw lambda
- replace the identity lowerer with the first real `Lam_convert.convert` slice
- make the first 1-hunk files structurally sane

That is the shortest path to turning the project from `0/657` everywhere into a useful
signal.
