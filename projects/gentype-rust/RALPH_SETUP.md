# Rust GenType Setup

## Build

Use debug builds for iteration.

```sh
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
```

If a build fails with `No space left on device`, stop and inspect disk usage.
Do not use `rm -rf`; remove only explicit files after verifying what they are.

## GenType Gates

Reference gate:

```sh
make test-gentype
```

The project-specific parity gate is a single no-argument script that always
runs the two in-repo GenType suites and the standard local Tella checkout:

```sh
./scripts/test_gentype_output_parity.sh
```

The parity gate must compare raw generated files. Do not sort, normalize,
rewrite imports, strip comments, or ignore whitespace.

The script rejects positional arguments instead of accepting per-repo targets.
It runs Tella from `/Users/jake/dev/tella-fusion`, using the compiler and
stdlib from this repository. The Tella webapp currently uses
`generatedFileExtension: ".gen.ts"` and shims for `Js`, `Pervasives`, and
`Spice`. If that path is missing, the script fails with a clear message.

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
2. During the rewrite stages, port one file at a time, 1:1, with the same
   function names and module shape where Rust allows it. The crate does not
   need to compile during these stages.
3. Run the three per-file review passes: surface/naming, control/data flow, and
   output-sensitive semantics.
4. Patch the reviewed file until it visibly matches the reference algorithm.
5. Add a comment or commit-body reference with the exact source location.
6. Only after the rewrite and review stages are complete, start fixing
   compilation and running parity gates.
7. Commit before moving to another phase.

Do not improve parity by adding file-specific conditions, output
post-processing, or Rust-only compatibility layers.
