# Compiler Error Output Parity Fixtures

Add reduced `.res` and `.resi` files here when an OCaml compiler/typechecker
error variant is not already covered by `tests/build_tests/super_errors`.

Run:

```bash
eval $(opam env --shell=sh) && make lib
cargo build --manifest-path compiler-rust/Cargo.toml
./scripts/test_error_output_parity.sh --compiler-only
```

The harness compares OCaml `bsc` and Rust `bsc` directly. OCaml output is the
oracle.

Use `cases.tsv` when a fixture needs custom compiler flags.
