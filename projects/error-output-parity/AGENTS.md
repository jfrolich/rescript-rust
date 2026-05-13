# AGENTS.md

Guidance for coding assistants working on error-output parity.

## OCaml Is The Implementation Oracle

The Rust compiler/parser code should match the OCaml implementation 1:1 as much
as the Rust architecture permits.

Before fixing any diagnostic mismatch:

1. Read the OCaml raise site and report function first.
2. Port the same control flow, error constructor, warning/error ordering,
   recovery behavior, and location choice into Rust where possible.
3. Keep the final rendered diagnostic byte-for-byte identical to OCaml.
4. Do not add harness output normalization, sorting, path rewriting, or
   fixture-specific text patches to hide compiler differences.

If Rust must differ from OCaml because of local architecture, document the
reason in the code or commit message and keep externally visible behavior
identical.

## Fixture Discipline

Each fixture should target one primary OCaml diagnostic branch. Add a short
top-of-file comment naming the source error when it is not obvious, then verify
the fixture against both compilers with:

```bash
cargo build --manifest-path compiler-rust/Cargo.toml
./scripts/test_error_output_parity.sh --compiler-only --no-super-errors <fixture-or-pattern>
```

Use the debug Rust compiler for iteration unless the user explicitly asks for a
release build.
