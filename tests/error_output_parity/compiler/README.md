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

Implementation rule: when a fixture exposes a mismatch, start from the OCaml
source. The Rust change should model the OCaml implementation 1:1 where the
local architecture permits: use the same error constructor, raise/report site,
control flow, recovery behavior, location choice, and renderer before adjusting
final text. Do not paper over differences in the harness; make the compiler
produce OCaml's diagnostic output byte-for-byte.

Use `cases.tsv` when a fixture needs custom compiler flags.
