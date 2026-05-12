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
oracle. Keep iteration on the debug Rust compiler and do not normalize output:
exit status and captured stderr must match byte-for-byte.

When a fixture exposes a mismatch, read the OCaml source for the raise site and
reporter first. Rust fixes should follow the OCaml implementation 1:1 as much as
the local architecture allows: match the error constructor, control flow,
location choice, and renderer behavior before changing final text.

Use `cases.tsv` when a fixture needs custom compiler flags.
