# Ralph Setup: JS Output Parity

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
timeout 1800 ./scripts/test_js_output_parity.sh
```

This uses the existing `test_rust_parity.sh` harness with:

- parser AST section skipped
- syntax section skipped
- Spice PPX parity still enabled
- JS snapshot section enabled

The project metric is the `JS COMPILATION SNAPSHOTS` section. Spice is kept as
a guard because it is built into the compiler now.

## Upstream Status

This project starts after the upstream parity work that is already complete:

- typedtree parity: **657/657**
- raw lambda parity: **657/657**
- optimized lambda parity: **657/657**

Do not use this project to reopen those stages. Use them only as guardrails
when shared code changes.

## Artifacts

The parity harness writes artifacts to:

```text
temp/rust-parity/diffs
temp/rust-parity/js
```

The directory is recreated on each run, so treat it as ephemeral.

## Useful Inspection Commands

```bash
# List current JS diff/error artifacts
find temp/rust-parity/diffs -maxdepth 1 -type f | rg '/js_'

# Internal-only artifacts
find temp/rust-parity/diffs -maxdepth 1 -type f | rg '/js_src_'

# Compile errors only
find temp/rust-parity/diffs -maxdepth 1 -type f | rg '/js_.*\\.err$'

# Text diffs only
find temp/rust-parity/diffs -maxdepth 1 -type f | rg '/js_.*\\.diff$'

# Read one artifact
sed -n '1,220p' temp/rust-parity/diffs/js_src_ExternalShadow.res.diff
sed -n '1,220p' temp/rust-parity/diffs/js_src_js_array_test.res.err
```

## Focused Iteration

The wrapper is intentionally thin, so for focused work use direct compiler
invocations against checked-in snapshots.

### Internal `.mjs` snapshot example

```bash
timeout 10 ./compiler-rust/target/release/bsc \
  -bs-package-name rescript-tests \
  -bs-module-type esmodule \
  tests/tests/src/ExternalShadow.res \
  -o /tmp/ExternalShadow.mjs

diff -u tests/tests/src/ExternalShadow.mjs /tmp/ExternalShadow.mjs | sed -n '1,220p'
```

### External `.bs.js` snapshot example

```bash
timeout 10 ./compiler-rust/target/release/bsc \
  -bs-package-name rescript-tests \
  /absolute/path/to/File.res \
  -o /tmp/File.bs.js

diff -u /absolute/path/to/File.bs.js /tmp/File.bs.js | sed -n '1,220p'
```

## Guards

Do not accept a JS-output change blindly. Where relevant, also run:

```bash
./scripts/test_lambda_parity.sh --raw -j1
./scripts/test_lambda_parity.sh -j1
./scripts/test_typedtree_parity.sh
```

Use these when JS-output work changes shared raw-lambda, lowering, or typechecker
paths.
