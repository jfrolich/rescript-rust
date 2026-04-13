# Ralph Loop: Rewatch In-Memory Build

You are working on adding a true in-process Rust build mode to `rewatch` while preserving the existing external-compiler modes.

## Goal

`rewatch` should support three explicit modes:

- no args: current OCaml/file-based build
- `--rust`: current Rust-via-`bsc` subprocess build
- `--in-process`: Rust in-process compiler build

This project is about the third mode.

For `--in-process`:

- `rewatch` does not shell out to `bsc` at parse time, namespace time, or compile time
- no compiler assets are emitted or read: `.ast`, `.iast`, `.cmi`, `.cmj`, `.cmt`, `.cmti`
- dependency interfaces are published into in-memory build state instead of serialized to disk
- only final JS output files are written
- no `build.ninja`, `.mlmap`, `.compiler.log`, `.sourcedirs.json`, or `compiler-info.json`
- `node_modules` packages continue compiling from source, as they already do today
- `@rescript/runtime` is also compiled from source and bootstrapped into the same in-memory registry
- breaking `gentype` / `reanalyze` in the first cut is acceptable

## Current Architecture Baseline

The current file-based protocol is spread across:

- `rewatch/src/build/compile.rs` — builds compiler args and shells out to `bsc`
- `rewatch/src/build/deps.rs` — rereads dependencies from emitted `.ast`
- `rewatch/src/build/read_compile_state.rs` — reconstructs build state from compiler assets on disk
- `rewatch/src/build/parse.rs` — still writes `.ast` / `.iast`
- `rewatch/src/build/namespaces.rs` — still shells out to `bsc` for namespace `mlmap` compilation
- `rewatch/src/build.rs` — still writes `build.ninja`
- `compiler-rust/src/driver.rs` — in-process compiler API returns JS text only
- `compiler-rust/src/cmi/persistent_env.rs` — resolves interfaces, source paths, and purity from `.cmi` / `.ast` / `.cmj`
- `compiler-rust/src/js_ir/mod.rs` — JS import resolution still depends on persistent-env asset lookups

## Core Principle

Keep module semantics exactly the same as the current file-based build in every mode:

- if `M.resi` exists, the published interface for `M` comes from typechecking `M.resi`
- otherwise, the published interface for `M` comes from the inferred exports of `M.res`

The refactor changes the transport, not the semantics:

- old model: publish interfaces by writing compiler assets to disk
- new `--in-process` model: publish interfaces by storing them in memory and resolving dependencies from the in-memory registry

The in-memory state boundary is also part of the design:

- parsed AST belongs in build state
- published interface belongs in build state
- full typedtree and type-checking context stay local to one compilation

Do not turn `BuildCommandState` into a store of typedtrees or live type arenas.

Do not keep any fallback compiler-asset protocol alive inside `--in-process` for runtime bootstrap, `node_modules`, namespace handling, startup reconstruction, or stale-build detection.

## Important Constraints

1. Keep the three modes explicit. `--in-process` is a new mode, not a silent behavior change to `--rust`.
2. `node_modules` packages are already source-backed in `rewatch`; do not redesign that part as if they were precompiled dependencies.
3. The real special case is `@rescript/runtime`, because the compiler currently bootstraps `Pervasives` / `Stdlib` from runtime assets on disk.
4. A fresh `rewatch` start may do a full rebuild in `--in-process`. Do not invent a persistence layer for local interfaces.
5. For `--in-process`, only final JS should be written after the refactor. Compiler metadata belongs in memory.
6. Do not spend time preserving `.cmt` / `.cmti` tooling in the first cut.
7. Solve stale-build propagation without `.cmi` / `.cmt` timestamps. Use in-memory interface generations or fingerprints instead.
8. Preserve parallel compilation. The same dependency-ready module batch that compiles in parallel in the file-backed modes must still compile in parallel in `--in-process`.
9. A sequential `for module in current_in_progress_modules` implementation in the `--in-process` path is not acceptable as the finished design.
10. Do not serialize the entire ready batch behind one shared mutable `PersistentEnv` token. If interface publication needs synchronization, keep the critical section narrow and preserve worker parallelism.

## Your Task Each Iteration

1. Open `RALPH_TODO.md`.
2. Pick the highest-impact unchecked task.
3. Read the current Rust implementation before changing anything.
4. Implement one end-to-end slice of the `--in-process` protocol.
5. Run focused tests with timeouts.
6. Run the relevant default-mode and in-process-mode test suites.
7. Update `RALPH_TODO.md` with concrete findings and status, including any performance or parallelism regressions introduced by the current approach.
8. Commit atomically with a DCO sign-off.
9. Stop.

If all tasks are checked and the JS-only / no-compiler-assets invariants hold, output:

```text
RALPH_COMPLETE
```

## Required Commands

Always use timeouts for builds and tests.

```bash
# Build the Rust compiler + rewatch
timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release
timeout 600 cargo build --manifest-path rewatch/Cargo.toml --release

# Export the executable for focused rewatch tests
export REWATCH_EXECUTABLE="$(realpath ./rewatch/target/release/rewatch)"

# Full default-mode compatibility suite
timeout 600 ./rewatch/tests/suite.sh "$REWATCH_EXECUTABLE"

# Focused test entrypoints
(cd rewatch/tests && timeout 300 ./compile.sh)
(cd rewatch/tests && timeout 300 ./watch.sh)
(cd rewatch/tests && timeout 300 ./clean.sh)
```

## Primary Files

- `rewatch/src/build/build_types.rs`
- `rewatch/src/build/parse.rs`
- `rewatch/src/build/deps.rs`
- `rewatch/src/build/compile.rs`
- `rewatch/src/build/read_compile_state.rs`
- `rewatch/src/build/namespaces.rs`
- `rewatch/src/build/compiler_info.rs`
- `rewatch/src/build/logs.rs`
- `rewatch/src/sourcedirs.rs`
- `compiler-rust/src/driver.rs`
- `compiler-rust/src/cmi/persistent_env.rs`
- `compiler-rust/src/js_ir/mod.rs`
- `packages/@rescript/runtime/rescript.json`

## Exit Condition

Only when all are true:

- no-arg builds still use the current OCaml path
- `--rust` builds still use the current Rust-subprocess path
- `--in-process` builds use the Rust compiler fully in-process
- `--in-process` still compiles dependency-independent modules in parallel
- default-mode compatibility tests pass
- in-process tests pass
- in `--in-process`, no compiler assets are emitted or read anywhere in the `rewatch/testrepo` build graph
- in `--in-process`, only final JS outputs remain on disk
- `RALPH_TODO.md` has no unchecked tasks remaining

Do not claim completion early.
