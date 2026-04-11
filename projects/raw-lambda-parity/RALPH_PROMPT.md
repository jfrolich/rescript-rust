# Ralph Loop: Raw Lambda Parity

You are working on achieving **100% unoptimized lambda parity** between the Rust compiler and the OCaml reference implementation using `-drawlambda`.

## Current Baseline (2026-04-11)

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Unoptimized lambda parity: **626/657**
- Parity hunks: **89**

This project is about the **real OCaml raw lambda stage**, not printer normalization.
The Rust implementation must match the OCaml reference pipeline and control flow.

## Core Principle: 1:1 OCaml Port

- **Read OCaml first** before touching Rust.
- **Match the OCaml stage structure exactly**: typedtree -> raw lambda -> later lowering/optimization.
- **Do not reverse-engineer from diffs alone.** Diffs only tell you where to inspect.
- **Do not paper over differences in the printer.** The fix belongs in raw lambda translation.
- Use idiomatic Rust only as a translation of OCaml behavior.

Primary OCaml references:
- `compiler/ml/translcore.ml`
- `compiler/ml/translmod.ml`
- `compiler/ml/matching.ml`
- `compiler/ml/lambda.ml`
- `compiler/ml/printlambda.ml`

Primary Rust implementation files:
- `compiler-rust/src/raw_lambda/mod.rs`
- `compiler-rust/src/raw_lambda/convert.rs`
- `compiler-rust/src/raw_lambda/print.rs`
- `compiler-rust/src/driver.rs`

## Correctness Rule

If a change is **verified OCaml-aligned**, keep it and commit it even if local parity or hunk counts temporarily regress.
Do **not** revert correct work just to preserve a local score. Fix the downstream regressions with more correct ports.

Parity numbers and hunk counts are navigation tools, not the definition of correctness.

## Your Loop

Work autonomously in an internal loop on raw lambda parity.
Do not stop for progress updates or summaries.

For each iteration:
1. Run the authoritative parity baseline.
2. Pick the highest-impact root-cause cluster from current diffs/fallback traces.
3. Read the corresponding OCaml implementation first.
4. Port the OCaml behavior into Rust.
5. Run focused checks.
6. Run the authoritative parity baseline again.
7. If the change is verified OCaml-aligned, commit it immediately.
8. Update `RALPH_TODO.md` with the new status and findings.
9. Continue from the new baseline.

Only stop if:
- raw lambda parity reaches `657/657`, or
- there is a genuine hard blocker that requires human input.

## Required Commands

Always use timeouts for compiler invocations.

```bash
# Build Rust compiler
timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release

# Build OCaml compiler (for adding debug logging)
eval "$(opam env)" && dune build --root . && make artifacts

# Authoritative baseline (with canonical stamp normalization)
rm -rf .parity-cache/ && CANONICAL_STAMPS=1 ./scripts/test_lambda_parity.sh --raw

# Focused single-file / pattern run
CANONICAL_STAMPS=1 ./scripts/test_lambda_parity.sh --raw gpr_1698_test

# Direct compiler invocation for debug logging
timeout 10 compiler-rust/target/release/bsc -drawlambda tests/tests/src/FILE.res 2>&1

# OCaml direct invocation (from tests/tests/lib/bs)
cd tests/tests/lib/bs && timeout 10 ../../../../packages/@rescript/darwin-arm64/bin/bsc.exe -drawlambda -I ../ocaml -runtime-path ../../../../node_modules/@rescript/runtime -bs-package-name rescript-tests src/FILE.ast 2>&1
```

## Raw Fallback Debugging

When a file is still falling back to lowered behavior, use direct `bsc -drawlambda` repro and trace the fallback sites.

Example:

```bash
cd tests/tests
JSON=$(../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/VariantPatternMatchingSpreads.res)
ARGS=$(node -e 'const o=JSON.parse(process.argv[1]); console.log(o.compiler_args.map(x=>JSON.stringify(x)).join(" "))' "$JSON")
cd lib/bs
eval "RUST_RAW_FALLBACK_TRACE=1 timeout 10 ../../../../compiler-rust/target/release/bsc -drawlambda $ARGS 1>/dev/null 2>/tmp/raw_fallback.log"
```

Use those trace keys to map the failure back to the OCaml raw-matching code path.

## Prioritization

1. **Fix matching compiler inner compilation differences**
   - The outer `do_split_or` partitioning is identical between OCaml and Rust
   - The difference is in `compile_flattened` → `compile_match` → inner `split_precompile`
   - Compare inner compilation by adding logging to BOTH OCaml and Rust
   - Key files: `compiler-rust/src/raw_lambda/matching.rs`, `compiler/ml/matching.ml`
2. **Fix module coercion / alias resolution**
   - Thread expression env through translate_normal_path_raw for Pdot resolution
   - Fix strengthen_module_type for same-source modules with value shadowing
3. **Fix JSX PPX duplicate make positions**
   - Either fix at PPX level or in signature_runtime_value
4. **Implement Dict pattern compilation matching OCaml**
   - Use typed field accesses instead of option checks

All remaining 31 failures are in the lambda conversion stage (typed trees are identical).
Log in BOTH compilers to compare behavior at specific code points.

## Commit Rules

- Commit every verified OCaml-aligned improvement immediately.
- Keep commits atomic.
- Include parity and hunk deltas in the commit message when available.
- Use DCO sign-off.

Example:

```bash
git add <files>
git commit -s -m "raw-lambda: port OCaml constructor catch grouping

Unoptimized lambda parity: 171 -> 178 / 657
Parity hunks: 1028 -> 996"
```

## Exit Condition

Only when all are true:
- `./scripts/test_lambda_parity.sh --unoptimized -j1` reports full parity
- `RALPH_TODO.md` has no unchecked tasks remaining
- optimized lambda and typedtree guards still pass where applicable

Do not output or mention `RALPH_COMPLETE` early.
