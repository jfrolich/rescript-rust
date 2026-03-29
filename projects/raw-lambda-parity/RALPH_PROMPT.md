# Ralph Loop: Raw Lambda Parity

You are working on achieving **100% unoptimized lambda parity** between the Rust compiler and the OCaml reference implementation using `-drawlambda`.

## Current Baseline (2026-03-29)

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Unoptimized lambda parity: **171/657**
- Parity hunks: **1028**

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

# Authoritative baseline
./scripts/test_lambda_parity.sh --unoptimized -j1

# Focused single-file / pattern run
./scripts/test_lambda_parity.sh --unoptimized tests/tests/src/VariantPatternMatchingSpreads.res
./scripts/test_lambda_parity.sh --unoptimized "VariantPatternMatching"

# Optimized lambda guard (must not regress accidentally)
./scripts/test_lambda_parity.sh -j1

# Typedtree guard when raw-lambda changes touch typing-facing code
./scripts/test_typedtree_parity.sh
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

1. **Port missing OCaml raw stage structure first**
   - eliminate places where `RawLambda` still behaves as a thin wrapper over lowered lambda
2. **Port `matching.ml` grouped constructor/or/alias compilation**
   - especially grouped `switch`/`catch` control flow
3. **Port module/raw coercion paths from `translmod.ml`**
   - especially alias/module-pack handling
4. **Fix printer only after the raw IR shape is correct**

Do not chase “easy files.” The remaining failures are root-cause problems.

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
