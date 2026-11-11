# Compiler Error Output Parity Fixtures

Add reduced `.res` and `.resi` files here when an OCaml compiler/typechecker
error variant is not already covered by `tests/build_tests/super_errors`.

Run:

```bash
eval $(opam env --shell=sh) && make lib
cargo build --manifest-path compiler-rust/Cargo.toml
./scripts/test_error_output_parity.sh --compiler-only
```

The harness compares OCaml `bsc` and the Rust compiler (`rescript bsc`) directly. OCaml output is the
oracle. Keep iteration on the debug Rust compiler and do not normalize output:
exit status and captured stderr must match byte-for-byte.

Implementation rule: when a fixture exposes a mismatch, start from the OCaml
source. The Rust change should model the OCaml implementation 1:1 where the
local architecture permits: use the same error constructor, raise/report site,
control flow, recovery behavior, location choice, and renderer before adjusting
final text. Do not paper over differences in the harness; make the compiler
produce OCaml's diagnostic output byte-for-byte.

Use `cases.tsv` when a fixture needs custom compiler flags.

A case that needs another compilation unit uses a fixture package under
`cases/` (a `rescript.json` and its sources) and passes
`-I cases/<package>/lib/ocaml`. The harness builds the package with the OCaml
`bsc` first (`rescript build-reference`), whose `.cmi`/`.cmj` files the OCaml
compile reads; `rescript bsc` compiles the package in memory and reads no
compiled files. A `-bs-read-cmi` case lives in `.parity-cache/error-output/compiler/`:
the harness copies it and its `.resi` there and compiles the interface with
OCaml first, while `rescript bsc -bs-read-cmi` types the `.resi` itself.
Errors only a compiled file can cause (a corrupt or foreign `.cmi`, a missing
`.cmj`) have no case: the Rust compiler never reads one.

External PPXs are intentionally unsupported by Rust. The former wrong-magic
case now lives in `rewatch/tests/fixtures/external-ppx` and is checked by
`rewatch/tests/compile/26-external-ppx-rejected.sh`: the compiler rejects the
flag before running the executable, rather than comparing its output to OCaml.
