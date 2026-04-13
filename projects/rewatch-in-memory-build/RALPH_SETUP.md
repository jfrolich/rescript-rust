# Ralph Setup: Rewatch In-Memory Build

## Mode Matrix

- default: OCaml compiler path, file-backed compiler assets
- `--rust`: Rust compiler via `bsc` subprocess, still file-backed
- `--in-process`: Rust compiler in-process, memory-backed interfaces, JS-only outputs

This project must preserve the first two modes while implementing the third.

## Build

```bash
timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release
timeout 600 cargo build --manifest-path rewatch/Cargo.toml --release
```

Set the rewatch executable once per shell:

```bash
export REWATCH_EXECUTABLE="$(realpath ./rewatch/target/release/rewatch)"
```

## Default-Mode Compatibility Suite

Run from the project root:

```bash
timeout 600 ./rewatch/tests/suite.sh "$REWATCH_EXECUTABLE"
```

This is the top-level regression suite for compile, watch, clean, lock, suffix, format, experimental, and compiler-args behavior in the existing file-backed modes.

## Focused Iteration

Existing focused scripts:

```bash
(cd rewatch/tests && timeout 300 ./compile.sh)
(cd rewatch/tests && timeout 300 ./watch.sh)
(cd rewatch/tests && timeout 300 ./clean.sh)
```

In-process-specific scripts should be added alongside these, not instead of them.

If you touch compiler/runtime bootstrap logic, rerun the full default-mode suite and the new in-process suite rather than relying only on focused scripts.

## Parallelism Guard

`--in-process` is a transport change, not permission to make the build single-threaded.

When working in `rewatch/src/build/compile.rs`:

- Preserve the current frontier scheduler shape: once a batch of modules is dependency-ready, those modules must still compile in parallel.
- Do not accept an implementation that replaces the ready-batch `par_iter()` with a sequential `for` loop in `--in-process`.
- Do not funnel the whole batch through one mutable `PersistentEnv` token if that forces all worker threads to serialize.
- Keep parsed ASTs and published interfaces in build state. Keep typedtree/type-context state local to one compilation.

If the implementation needs interface publication for downstream compilations, solve that without giving up parallelism.

## Clean Target

Do not stop at "per-file `PersistentEnv` works."

That may be an acceptable transition step, but the target architecture for this project is:

- `--in-process` compiler entrypoints do not take or return `PersistentEnv`
- build state owns the canonical published-interface and module-metadata registry
- each file compiles with a resolver session/local memoization layer built from that registry

If a change makes `PersistentEnv` more central to the in-process design, it is moving in the wrong direction.

## Per-File `PersistentEnv`

One `PersistentEnv` per file is acceptable and may be the simplest correct design.

What is not acceptable:

- one shared mutable `PersistentEnv` for the entire ready batch
- `take_persistent_env()` -> compile one file -> `return_persistent_env()` if that makes the batch effectively single-threaded

What is acceptable:

- build or clone a `PersistentEnv` per worker/file
- seed it from the published interfaces and module metadata already visible at the start of that wave
- use it as compilation-local resolver/cache state
- publish the finished module interface back to build state when the worker completes

Why this is sound:

- modules in the same ready batch do not depend on each other
- they only depend on modules from earlier waves, whose published interfaces are already fixed
- the authoritative cross-file state is `BuildCommandState` interface publication plus module metadata
- `PersistentEnv` cache reuse is an optimization, not the semantic source of truth

If rebuilding some `PersistentEnv` caches per file costs CPU, that is still a better trade than collapsing the whole frontier to one thread.

But treat that as a migration step, not the end state.

Target smoke commands once the new mode exists:

```bash
timeout 300 "$REWATCH_EXECUTABLE" build --in-process
timeout 300 "$REWATCH_EXECUTABLE" watch --in-process
```

## No-Compiler-Assets Guard

After any `--in-process` build or watch run, verify that the test repo contains no compiler assets:

```bash
find rewatch/testrepo -type f \
  \( -name '*.ast' -o -name '*.iast' -o -name '*.cmi' -o -name '*.cmj' -o -name '*.cmt' -o -name '*.cmti' \) \
  | sort

find rewatch/testrepo -type f \
  \( -name '.compiler.log' -o -name '.sourcedirs.json' -o -name 'compiler-info.json' \) \
  | sort

find rewatch/testrepo -type f \
  \( -name 'build.ninja' -o -name '*.mlmap' -o -name '*.sexp' \) \
  | sort

find rewatch/testrepo -type f \
  \( -path '*/lib/bs/*' -o -path '*/lib/ocaml/*' \) \
  | grep -E '\.(res|resi)$' || true
```

These commands should print nothing in `--in-process` mode.

To verify that final JS outputs still exist:

```bash
find rewatch/testrepo -type f \( -name '*.mjs' -o -name '*.js' -o -name '*.cjs' \) | sort | sed -n '1,80p'
```

To verify that in-process mode is not quietly reading stale compiler assets, add poisoned files and rebuild:

```bash
printf 'stale' > rewatch/testrepo/packages/main/lib/bs/src/Main.cmi
printf 'stale' > rewatch/testrepo/packages/main/lib/ocaml/Main.ast
```

The in-process build should still succeed or fail exactly the same way after those files are planted.

## Useful Inspection Commands

```bash
rg -n "compile_file|bs-read-cmi|lib/ocaml|bsc" rewatch/src/build/compile.rs
rg -n "par_iter|take_persistent_env|return_persistent_env|compile_module_in_process" rewatch/src/build/compile.rs
rg -n "register_in_memory_interface|in_memory_interfaces|stored_asts" rewatch/src/build/build_types.rs rewatch/src/build/compile.rs
rg -n "PersistentEnv|set_persistent_env|register_in_memory_signature" compiler-rust/src/driver.rs compiler-rust/src/types/typecore.rs compiler-rust/src/cmi/persistent_env.rs
rg -n "read_ast|deps" rewatch/src/build/deps.rs rewatch/src/build/parse.rs
rg -n "compile_mlmap|mlmap" rewatch/src/build/namespaces.rs rewatch/src/build/packages.rs
rg -n "read_compile_state|compiler-info|sourcedirs" rewatch/src/build
rg -n "read_raw_sig|module_cmj_is_pure|resolve_module_source_path|find_pers_struct" compiler-rust/src/cmi/persistent_env.rs
rg -n "compile_source_to_js_with_options|typecheck_interface_source|load_pervasives" compiler-rust/src/driver.rs
rg -n "ModulePathResolver" compiler-rust/src/js_ir/mod.rs
rg -n "last_compiled_cmi|last_compiled_cmt|mark_modules_with_expired_deps_dirty" rewatch/src/build
rg -n "write_build_ninja|build.ninja" rewatch/src/build.rs
```

## Runtime Bootstrap Notes

The non-runtime dependency graph is already source-backed. The special bootstrap problem is `@rescript/runtime`, because the current compiler still loads `Pervasives` / `Stdlib` from disk-backed runtime artifacts.

Relevant files:

```bash
sed -n '1,220p' packages/@rescript/runtime/rescript.json
ls packages/@rescript/runtime/src | sed -n '1,80p'
```

Pay attention to the runtime build flags:

- `-make-runtime`
- `-nostdlib`
- `-nopervasives`
- `-open Pervasives`

The in-process compiler API needs semantic support for those flags instead of assuming disk-backed stdlib assets.

This is not late cleanup. Runtime bootstrap is an early blocker for a real no-asset `--in-process` mode.
