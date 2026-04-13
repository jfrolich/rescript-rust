# Ralph Setup: Rewatch In-Memory Build

## Build

```bash
timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release
timeout 600 cargo build --manifest-path rewatch/Cargo.toml --release
```

Set the rewatch executable once per shell:

```bash
export REWATCH_EXECUTABLE="$(realpath ./rewatch/target/release/rewatch)"
```

## Authoritative Suite

Run from the project root:

```bash
timeout 600 ./rewatch/tests/suite.sh "$REWATCH_EXECUTABLE"
```

This is the top-level regression suite for compile, watch, clean, lock, suffix, format, experimental, and compiler-args behavior.

## Focused Iteration

```bash
(cd rewatch/tests && timeout 300 ./compile.sh)
(cd rewatch/tests && timeout 300 ./watch.sh)
(cd rewatch/tests && timeout 300 ./clean.sh)
```

If you touch compiler/runtime bootstrap logic, rerun the full suite rather than relying only on focused scripts.

## No-Compiler-Assets Guard

After any build or watch run, verify that the test repo contains no compiler assets:

```bash
find rewatch/testrepo -type f \
  \( -name '*.ast' -o -name '*.iast' -o -name '*.cmi' -o -name '*.cmj' -o -name '*.cmt' -o -name '*.cmti' \) \
  | sort

find rewatch/testrepo -type f \
  \( -name '.compiler.log' -o -name '.sourcedirs.json' -o -name 'compiler-info.json' \) \
  | sort
```

Both commands should print nothing once the refactor is complete.

To verify that final JS outputs still exist:

```bash
find rewatch/testrepo -type f \( -name '*.mjs' -o -name '*.js' -o -name '*.cjs' \) | sort | sed -n '1,80p'
```

## Useful Inspection Commands

```bash
rg -n "compile_file|bs-read-cmi|lib/ocaml|bsc" rewatch/src/build/compile.rs
rg -n "read_ast|deps" rewatch/src/build/deps.rs rewatch/src/build/parse.rs
rg -n "read_compile_state|compiler-info|sourcedirs" rewatch/src/build
rg -n "read_raw_sig|module_cmj_is_pure|resolve_module_source_path|find_pers_struct" compiler-rust/src/cmi/persistent_env.rs
rg -n "compile_source_to_js_with_options|typecheck_interface_source|load_pervasives" compiler-rust/src/driver.rs
rg -n "ModulePathResolver" compiler-rust/src/js_ir/mod.rs
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
