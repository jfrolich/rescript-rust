# Rust GenType Setup

## Build

Use debug builds for iteration.

```sh
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
```

If a build fails with `No space left on device`, stop and inspect disk usage.
Do not use `rm -rf`; remove only explicit files after verifying what they are.

## In-Repo GenType Gates

Reference gate:

```sh
make test-gentype
```

The project-specific parity gate should be added in Phase 0:

```sh
./scripts/test_gentype_output_parity.sh --repo tests/gentype_tests/typescript-react-example
./scripts/test_gentype_output_parity.sh --repo tests/gentype_tests/stdlib-no-shims
```

The parity gate must compare raw generated files. Do not sort, normalize,
rewrite imports, strip comments, or ignore whitespace.

## Tella Gate

When `/Users/jake/dev/tella-fusion` is present:

```sh
./scripts/test_gentype_output_parity.sh --tella /Users/jake/dev/tella-fusion
```

Run Tella builds from the Tella repo root, using the compiler and stdlib from
this repository. The Tella webapp currently uses `generatedFileExtension:
".gen.ts"` and shims for `Js`, `Pervasives`, and `Spice`.

## Regression Gates

After semantic compiler changes, keep the existing compiler parity gates at
their prior levels:

```sh
./scripts/test_output_parity.sh --quick
./scripts/test_typedtree_parity.sh --quick
./scripts/test_lambda_parity.sh --quick
```

Run focused error parity around GenType stale CMT behavior after touching
`compiler-rust/src/bin/bsc.rs` or `gentype::main`.

## Reference Workflow

For each Rust change:

1. Open the OCaml/ReScript reference file first.
2. Port the same function shape and name when practical.
3. Add a comment or commit-body reference with the exact source location.
4. Run the smallest GenType parity gate that covers the change.
5. Commit before moving to another phase.

Do not improve parity by adding file-specific conditions, output
post-processing, or Rust-only compatibility layers.
