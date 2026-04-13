# Ralph Setup: Typechecker Performance

## Purpose

This project focuses on Rust typechecker performance, not parser or JS backend
performance. The main repro is `tests/tests/src/Import.res`.

## Build

From the repo root:

```bash
cargo build --release --manifest-path compiler-rust/Cargo.toml
```

## Exact Repro

Fetch the exact compiler args:

```bash
cd tests/tests
../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/Import.res
```

Compile from `tests/tests/lib/bs` using those args.

## Timing

Use:

```bash
/usr/bin/time -lp ../../../../compiler-rust/target/release/bsc <args...> -o /tmp/Import.rust.mjs
/usr/bin/time -lp ../../../../_build/install/default/bin/bsc <args...> -o /tmp/Import.ocaml.mjs
```

This is the authoritative performance comparison for this project.

## Profiling

If Rust is still slow, sample the running compiler process:

```bash
/usr/bin/sample <pid> 3 -file /tmp/import.sample.txt
```

Key functions to watch for:

- `copy_lookup_signature_for_subst`
- `copy_lookup_type_expr`
- `resolve_type_item_through_env`
- `resolve_module_signature_for_path`
- `modtypes_inner`

## Investigation Reference

Read this first before changing code:

- [IMPORT_RES_PERFORMANCE_HANDOFF.md](./IMPORT_RES_PERFORMANCE_HANDOFF.md)

## Correctness Guard

This project changes typing/module-resolution code. Do not accept a
performance-only patch without correctness checks.

Recommended minimum:

```bash
./scripts/test_typedtree_parity.sh Import
```

Recommended broader gate before finalizing a change:

```bash
./scripts/test_typedtree_parity.sh
```

If the change affects downstream compilation behavior, also run:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

## Success Signal

You are done when:

- `Import.res` matches or beats OCaml on the same machine
- Rust is no longer a multi-GB compile for this file
- the profiler no longer shows repeated whole-signature deep-copy as the top cost
- the implementation shape is recognizably closer to OCaml's lazy module view
  construction, not just a local bandaid
