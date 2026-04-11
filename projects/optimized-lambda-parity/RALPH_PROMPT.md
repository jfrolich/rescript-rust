# Ralph Loop: Optimized Lambda Parity

You are working on achieving **100% optimized lambda parity** between the Rust compiler and the OCaml reference implementation using `-dlambda-sexp`.

Read `PLAN.md` first. Follow the active phase there instead of inventing your own order.

## Current Baseline (2026-04-11)

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **0/657**
- Stamp-canonicalized parity: **0/657**
- Parity hunks: **1631**
- Stamp-canonicalized hunks: **1631**

Raw lambda parity is already **657/657**. The remaining gap is in the raw-lambda to optimized-lambda lowering stage.

This project is about the **real OCaml optimized lambda stage**, not printer normalization and not JS codegen.
The Rust implementation must match the OCaml stage that OCaml prints for `-dlambda-sexp`.

## Core Principle: 1:1 OCaml Port

- **Read OCaml first** before touching Rust.
- **Match the OCaml stage structure exactly**:
  typedtree -> raw lambda -> `Lam_convert.convert` -> sexp printer.
- **Do not reverse-engineer from diffs alone.** Diffs only tell you where to inspect.
- **Do not paper over differences in the printer.** The fix belongs in lowering, not in serializer hacks.
- **Do not keep the legacy typedtree -> lowered lambda shortcut as the parity path.**
- **Do not spend time porting later `lam_pass_*` stages unless a diff proves they are relevant.**

Primary OCaml references:
- `compiler/core/lam_compile_main.ml`
- `compiler/core/lam_convert.ml`
- `compiler/core/lam_print.ml`
- `compiler/core/sexp_lambda.ml`

Primary Rust implementation files:
- `compiler-rust/src/driver.rs`
- `compiler-rust/src/raw_lambda/lower.rs`
- `compiler-rust/src/lambda/mod.rs`
- `compiler-rust/src/lambda/sexp_lambda.rs`

## Correctness Rule

If a change is **verified OCaml-aligned**, keep it and commit it even if local parity or hunk counts temporarily regress.
Do **not** revert correct work just to preserve a local score. Fix the downstream regressions with more correct ports.

Parity numbers and hunk counts are navigation tools, not the definition of correctness.

## Your Loop

Work autonomously in an internal loop on optimized lambda parity.
Do not stop for progress updates or summaries.

For each iteration:
1. Run the authoritative optimized-lambda baseline.
2. Re-check the current phase in `PLAN.md`.
3. Pick the highest-impact root-cause cluster from current diffs.
4. Read the corresponding OCaml implementation first.
5. Port the OCaml behavior into Rust.
6. Run focused checks on one small file and one large file.
7. Run the authoritative optimized-lambda baseline again.
8. If the change is verified OCaml-aligned, commit it immediately.
9. Update `RALPH_TODO.md` with the new status and findings.
10. Continue from the new baseline.

Only stop if:
- optimized lambda parity reaches `657/657`, or
- there is a genuine hard blocker that requires human input.

## Required Commands

Always use timeouts for compiler invocations.

```bash
# Build Rust compiler
timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release

# Build OCaml compiler (for adding debug logging)
eval "$(opam env)" && dune build --root . && make artifacts

# Authoritative optimized baseline
timeout 1800 ./scripts/test_lambda_parity.sh -j1

# Focused single-file / pattern run
./scripts/test_lambda_parity.sh AsInUncurriedExternals
./scripts/test_lambda_parity.sh minimal_test
./scripts/test_lambda_parity.sh js_array_test

# Direct compiler invocation for debug logging
timeout 10 compiler-rust/target/release/bsc -dlambda-sexp tests/tests/src/FILE.res 2>&1

# OCaml direct invocation (from tests/tests/lib/bs)
cd tests/tests/lib/bs && timeout 10 ../../../../_build/install/default/bin/bsc -dlambda-sexp <compiler-args...> 2>&1
```

## Prioritization

1. **Replace the legacy optimized parity path in the driver**
   - `driver.rs` currently prints `-dlambda-sexp` from `lambda::convert::LambdaConverter::convert_structure`
   - OCaml prints optimized lambda immediately after `Lam_convert.convert`
2. **Build the real raw -> lowered boundary**
   - `raw_lambda/lower.rs` is currently just `raw.into_lowered()`
   - Port the real `Lam_convert.convert` logic instead of an identity boundary
3. **Use the small 1-hunk diffs to validate structure**
   - `AsInUncurriedExternals.res` already shows wrong let kinds, wrong JS-call/application shape, and missing module-export structure
   - `minimal_test.res` already shows wrong constant/block lowering and missing export tail
4. **Use the large diffs to validate generalization**
   - `js_array_test.res`, `caml_compare_test.res`, `js_math_test.res`, `js_string_test.res`, and `js_float_test.res` are the biggest current clusters
5. **Treat later `lam_pass_*` work as downstream guard work**
   - do not port deep-flatten / exits / alias / alpha here unless the actual `-dlambda-sexp` diff proves it is necessary

Raw parity is already solved. The optimized project starts where raw parity ends.

## Commit Rules

- Commit every verified OCaml-aligned improvement immediately.
- Keep commits atomic.
- Include parity and hunk deltas in the commit message when available.
- Use DCO sign-off.

Example:

```bash
git add <files>
git commit -s -m "optimized-lambda: route dump through raw lowering boundary

Optimized lambda parity: 0 -> 37 / 657
Parity hunks: 1631 -> 1478"
```

## Exit Condition

Only when all are true:
- `./scripts/test_lambda_parity.sh -j1` reports full parity
- `RALPH_TODO.md` has no unchecked tasks remaining
- raw lambda and typedtree guards still pass where applicable

Do not output or mention `RALPH_COMPLETE` early.
