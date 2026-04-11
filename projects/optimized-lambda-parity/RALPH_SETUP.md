# Ralph Setup: Optimized Lambda Parity

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
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

This reports:
- OCaml compile passes/failures
- Rust compile passes/failures
- exact optimized-lambda parity file count
- aggregated exact parity hunk count

The script also writes stamp-canonicalized normalized diffs alongside the exact diffs.

## Focused Iteration

Use a mix of smallest and largest current failures:

```bash
./scripts/test_lambda_parity.sh tests/tests/src/AsInUncurriedExternals.res
./scripts/test_lambda_parity.sh tests/tests/src/minimal_test.res
./scripts/test_lambda_parity.sh tests/tests/src/js_array_test.res
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
# Smallest current optimized-lambda diffs
for f in .parity-cache/lambda/diffs/*.diff; do case "$f" in *.norm.diff) continue;; esac; printf "%5s %s\n" "$(grep -c '^@@' "$f")" "$f"; done | sort -n | head -20

# Largest current optimized-lambda diffs
for f in .parity-cache/lambda/diffs/*.diff; do case "$f" in *.norm.diff) continue;; esac; printf "%5s %s\n" "$(grep -c '^@@' "$f")" "$f"; done | sort -nr | head -20

# Inspect normalized diffs only
ls .parity-cache/lambda/diffs/*.norm.diff | sed -n '1,20p'

# Inspect a specific diff
sed -n '1,220p' .parity-cache/lambda/diffs/tests_tests_src_AsInUncurriedExternals.res.diff
```

## Direct `bsc -dlambda-sexp` Repro

```bash
cd tests/tests
JSON=$(../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/AsInUncurriedExternals.res)
ARGS=$(node -e 'const o=JSON.parse(process.argv[1]); console.log(o.compiler_args.map(x=>JSON.stringify(x)).join(" "))' "$JSON")
cd lib/bs
timeout 10 ../../../../compiler-rust/target/release/bsc -dlambda-sexp $ARGS 1>/dev/null 2>/tmp/rust.lambda
```

Compare against OCaml:

```bash
timeout 10 ../../../../_build/install/default/bin/bsc -dlambda-sexp $ARGS 1>/dev/null 2>/tmp/ocaml.lambda
diff -u /tmp/ocaml.lambda /tmp/rust.lambda | sed -n '1,220p'
```

Also compare the raw stage for the same file when needed:

```bash
timeout 10 ../../../../compiler-rust/target/release/bsc -drawlambda $ARGS 1>/dev/null 2>/tmp/rust.raw
timeout 10 ../../../../_build/install/default/bin/bsc -drawlambda $ARGS 1>/dev/null 2>/tmp/ocaml.raw
diff -u /tmp/ocaml.raw /tmp/rust.raw | sed -n '1,220p'
```

If raw matches but optimized diverges, the bug is after raw conversion.

## Guards

Do not accept an optimized-lambda change blindly. Where relevant, also run:

```bash
./scripts/test_lambda_parity.sh --raw -j1
./scripts/test_typedtree_parity.sh
```

Use these when optimized work changes shared raw-lambda or typechecker paths.
