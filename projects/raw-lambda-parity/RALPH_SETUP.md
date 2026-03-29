# Ralph Setup: Raw Lambda Parity

## Build

```bash
timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release
```

If you touch `rewatch`, rebuild it too:

```bash
timeout 600 cargo build --manifest-path rewatch/Cargo.toml --release
```

## Authoritative Baseline

Run from the project root:

```bash
./scripts/test_lambda_parity.sh --unoptimized -j1
```

This now reports:
- OCaml compile passes/failures
- Rust compile passes/failures
- parity file count
- aggregated parity hunk count

## Focused Iteration

```bash
./scripts/test_lambda_parity.sh --unoptimized tests/tests/src/VariantPatternMatchingSpreads.res
./scripts/test_lambda_parity.sh --unoptimized tests/tests/src/Import.res
./scripts/test_lambda_parity.sh --unoptimized "VariantPatternMatching"
```

## Cached Artifacts

The lambda parity script writes persistent artifacts to:

```text
.parity-cache/lambda/diffs
.parity-cache/lambda/ocaml
.parity-cache/lambda/rust
```

Use them to inspect the current baseline without rerunning the full suite.

## Useful Inspection Commands

```bash
# Largest current lambda diffs
wc -l .parity-cache/lambda/diffs/*.diff | sort -n | tail -20

# Hunk counts by file
for f in .parity-cache/lambda/diffs/*.diff; do printf "%5s %s\n" "$(grep -c '^@@' "$f")" "$f"; done | sort -n | tail -20

# Inspect a specific diff
sed -n '1,220p' .parity-cache/lambda/diffs/tests_tests_src_VariantPatternMatchingSpreads.res.diff
```

## Direct `bsc -drawlambda` Repro

```bash
cd tests/tests
JSON=$(../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/VariantPatternMatchingSpreads.res)
ARGS=$(node -e 'const o=JSON.parse(process.argv[1]); console.log(o.compiler_args.map(x=>JSON.stringify(x)).join(" "))' "$JSON")
cd lib/bs
timeout 10 ../../../../compiler-rust/target/release/bsc -drawlambda $ARGS 1>/dev/null 2>/tmp/rust.raw
```

Compare against OCaml:

```bash
timeout 10 ../../../../_build/install/default/bin/bsc -drawlambda $ARGS 1>/dev/null 2>/tmp/ocaml.raw
diff -u /tmp/ocaml.raw /tmp/rust.raw | sed -n '1,220p'
```

Trace raw fallbacks:

```bash
eval "RUST_RAW_FALLBACK_TRACE=1 timeout 10 ../../../../compiler-rust/target/release/bsc -drawlambda $ARGS 1>/dev/null 2>/tmp/raw_fallback.log"
sed -n '1,200p' /tmp/raw_fallback.log
```

## Guards

Do not accept a raw-lambda change blindly. Where relevant, also run:

```bash
./scripts/test_lambda_parity.sh -j1
./scripts/test_typedtree_parity.sh
```

Use these when raw work changes shared translation/typechecker paths.
