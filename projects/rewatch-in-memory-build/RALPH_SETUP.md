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

## Clean Architecture Sketch

The intended `--in-process` architecture has four layers:

1. `BuildCommandState` as the canonical shared state
   - parsed ASTs
   - published interfaces
   - module metadata needed by downstream compilation and JS path resolution
   - dependency graph / dirty-state bookkeeping
2. An immutable registry snapshot per compile wave
   - taken once when a frontier batch becomes ready
   - contains exactly the interfaces and metadata visible to every worker in that wave
   - read-only for the duration of that wave
3. A per-file resolver session
   - borrows the immutable registry snapshot
   - owns only local memoization such as renamed-signature cache and small lookup caches
   - must not clone the entire module/interface registry into every worker
4. A publish step after successful compilation
   - returns the module's new published interface, metadata, and any alias/path updates
   - applies those updates back to `BuildCommandState`
   - makes them visible only to later waves, not sibling workers in the same wave

Key invariants:

- A worker compiles only when every required dependency interface is already present in the snapshot for that wave.
- In `--in-process`, resolver lookup is a pure registry read. It must not compile dependencies on demand and must not probe compiler assets on disk.
- Full typedtree, type arena, and unification state remain local to one file compilation and are discarded afterward.
- The scheduler, not the resolver, is responsible for ensuring that implicit opens, namespace bootstrap modules, and runtime bootstrap modules are available before a file starts compiling.

What the worker session should look like conceptually:

```text
BuildCommandState
  -> wave snapshot (read-only)
       -> worker resolver session (borrowed snapshot + tiny local caches)
            -> compile one file
            -> return delta
  -> publish delta to build state
```

This is the clean performance shape:

- one shared snapshot per wave
- many parallel workers borrowing it
- no shared mutable resolver token
- no per-file cloning of all published interfaces
- only small per-file local memoization

## Current Review Status

Do not treat the current branch as complete. Post-implementation review found four acceptance blockers:

- `rewatch/tests/in-process.sh` currently accepts a non-zero exit from `rewatch build --in-process` by matching partial progress text. The suite must require a successful process exit.
- in-memory interface invalidation currently uses generation-before vs generation-after equality, but the generation counter is bumped on every publish. That over-dirties downstream dependents even when the published interface is unchanged.
- `ModuleRegistry` currently accumulates inserts and overwrites only. Deleted modules and stale namespace aliases are not purged from the shared registry.
- `PersistentEnv` is no longer shared through `BuildCommandState`, but it still exists inside the in-process compiler path via `PersistentEnv::from_registry(...)`. That is a transition step, not the target architecture.

## Steering For The Next Iteration

Recent work on portable type graphs is legitimate and should not be reverted. But it does not change the architectural direction:

- stop broadening the in-process role of `PersistentEnv`
- stop adding more source-fallback or disk-fallback behavior to make missing interfaces "work"
- treat any in-process module lookup miss as a scheduler/bootstrap bug to be fixed at the build-state level

Work in this order:

1. Fix unchanged-interface invalidation.
2. Purge deleted/renamed modules and stale namespace aliases from the shared registry.
3. Remove in-process fallback lookup behavior so the resolver is snapshot-only.
4. Replace internal `PersistentEnv::from_registry(...)` construction with a borrowed resolver session over the wave snapshot.

Do not spend the next iteration optimizing clone cost inside the transitional design before the architectural boundary is correct.

Test discipline:

- A stubbed/simplified testrepo run is a debugging tool only.
- Do not treat edits to `rewatch/testrepo` source files as acceptance for the feature.
- Keep the acceptance suite representative of the real build graph. If you need a smaller repro, add a separate diagnostic path rather than weakening `rewatch/tests/in-process.sh`.

## Temporary Stack Policy

This project is not the stack-usage optimization project.

For `--in-process`, correctness and end-to-end functionality matter more than stack efficiency right now. If the current compiler needs extremely large stack allowances to compile successfully in-process, that is an acceptable temporary workaround.

Guidance:

- raise the allowed stack size aggressively if needed rather than blocking the project on stack-depth cleanup
- if the practical temporary fix is a very large stack reservation, even into multi-GB territory, that is acceptable for this project
- do not treat large stack settings as a final design win; they are a stopgap until the separate optimization/stack-reduction work lands
- do not let stack tuning pull focus away from the main goal: a correct, clean, fully working in-process build path

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

Acceptance note:

- `build --in-process` must exit successfully. Do not accept "Compiled N modules" text as a substitute for a zero exit code.

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
rg -n "par_iter|compile_module_in_process|is_clean" rewatch/src/build/compile.rs
rg -n "register_in_memory_interface|in_memory_interfaces|stored_asts|module_registry|deleted_modules" rewatch/src/build/build_types.rs rewatch/src/build/compile.rs rewatch/src/build/clean.rs rewatch/src/build.rs
rg -n "PersistentEnv|from_registry|set_persistent_env|register_in_memory_signature|ModuleRegistry" compiler-rust/src/driver.rs compiler-rust/src/types/typecore.rs compiler-rust/src/cmi/persistent_env.rs
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
