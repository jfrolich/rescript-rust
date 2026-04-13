# Ralph Setup: Typechecker Performance

## Purpose

This project focuses on Rust typechecker performance, not parser or JS backend
performance. The main repro is `tests/tests/src/Import.res`, but the project
also tracks the full canonical recursive `tests/tests/src/**/*.res` corpus
(`657` files).

## Build

From the repo root:

```bash
cargo build --release --manifest-path compiler-rust/Cargo.toml
```

For the benchmark harness you also need the OCaml reference compiler and the
packaged ReScript CLI already built in this worktree.

## Exact Repro

Fetch the exact compiler args:

```bash
cd tests/tests
../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/Import.res
```

Compile from `tests/tests/lib/bs` using those args.

## Canonical Benchmark

Run the parser-free corpus benchmark from the repo root:

```bash
python3 scripts/benchmark_typechecker_performance.py --warmup 0 --runs 1 --limit 40
```

This walks the canonical recursive `tests/tests/src/**/*.res` corpus, fetches
per-file compiler args through `rescript.exe compiler-args`, and measures OCaml
vs Rust compilation using the checked-in `.ast` inputs from `tests/tests/lib/bs`.

Outputs:

- `.performance-cache/typechecker/latest.csv`
- `.performance-cache/typechecker/latest.json`

Use a selector for focused work:

```bash
python3 scripts/benchmark_typechecker_performance.py Import.res
python3 scripts/benchmark_typechecker_performance.py 'global_module_alias|module_alias'
```

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

Required canonical parity gate for every accepted change:

```bash
./scripts/test_typedtree_parity.sh
```

Focused parity slices such as the `Import` subset are useful for diagnosis, but
they do not replace the canonical full typedtree parity run:

```bash
./scripts/test_typedtree_parity.sh Import
```

Recommended performance gate before finalizing a change:

```bash
python3 scripts/benchmark_typechecker_performance.py --warmup 0 --runs 1 --limit 40
```

If the change affects downstream compilation behavior, also run:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

## Success Signal

You are done when:

- `Import.res` matches or beats OCaml on the same machine
- Rust is no slower than OCaml on every comparable file in the canonical corpus
- Rust is no longer a multi-GB compile for this file
- the profiler no longer shows repeated whole-signature deep-copy as the top cost
- the implementation shape is recognizably closer to OCaml's lazy module view
  construction, not just a local bandaid
