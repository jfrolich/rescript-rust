# Ralph Loop: Rewatch In-Memory Build

You are working on making `rewatch` run the compiler in-process and removing compiler assets from the build protocol entirely.

## Goal

- `rewatch` does not shell out to `bsc`
- no `.ast`, `.iast`, `.cmi`, `.cmj`, `.cmt`, or `.cmti` files are emitted or read
- dependency interfaces are published into in-memory build state instead of serialized to disk
- only final JS output files are written
- `node_modules` packages continue compiling from source, as they already do today
- `@rescript/runtime` is also compiled from source and bootstrapped into the same in-memory registry
- breaking `gentype` / `reanalyze` in the first cut is acceptable

## Current Architecture Baseline

The current file-based protocol is spread across:

- `rewatch/src/build/compile.rs` — builds compiler args and shells out to `bsc`
- `rewatch/src/build/deps.rs` — rereads dependencies from emitted `.ast`
- `rewatch/src/build/read_compile_state.rs` — reconstructs build state from compiler assets on disk
- `rewatch/src/build/parse.rs` — still writes `.ast` / `.iast`
- `compiler-rust/src/driver.rs` — in-process compiler API returns JS text only
- `compiler-rust/src/cmi/persistent_env.rs` — resolves interfaces, source paths, and purity from `.cmi` / `.ast` / `.cmj`
- `compiler-rust/src/js_ir/mod.rs` — JS import resolution still depends on persistent-env asset lookups

## Core Principle

Keep module semantics exactly the same as the current file-based build:

- if `M.resi` exists, the published interface for `M` comes from typechecking `M.resi`
- otherwise, the published interface for `M` comes from the inferred exports of `M.res`

The refactor changes the transport, not the semantics:

- old model: publish interfaces by writing compiler assets to disk
- new model: publish interfaces by storing them in memory and resolving dependencies from the in-memory registry

Do not keep any fallback compiler-asset protocol alive for runtime bootstrap, `node_modules`, or startup reconstruction.

## Important Constraints

1. `node_modules` packages are already source-backed in `rewatch`; do not redesign that part as if they were precompiled dependencies.
2. The real special case is `@rescript/runtime`, because the compiler currently bootstraps `Pervasives` / `Stdlib` from runtime assets on disk.
3. A fresh `rewatch` start may do a full rebuild. Do not invent a persistence layer for local interfaces.
4. Only final JS should be written after the refactor. Compiler metadata belongs in memory.
5. Do not spend time preserving `.cmt` / `.cmti` tooling in the first cut.

## Your Task Each Iteration

1. Open `RALPH_TODO.md`.
2. Pick the highest-impact unchecked task.
3. Read the current Rust implementation before changing anything.
4. Implement one end-to-end slice of the in-memory build protocol.
5. Run focused tests with timeouts.
6. Run the authoritative rewatch test suite.
7. Update `RALPH_TODO.md` with concrete findings and status.
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

# Full rewatch bash suite
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
- `compiler-rust/src/driver.rs`
- `compiler-rust/src/cmi/persistent_env.rs`
- `compiler-rust/src/js_ir/mod.rs`
- `packages/@rescript/runtime/rescript.json`

## Exit Condition

Only when all are true:

- `rewatch` compiles in-process
- the rewatch bash suite passes
- no compiler assets are emitted or read anywhere in the `rewatch/testrepo` build graph
- only final JS outputs remain on disk
- `RALPH_TODO.md` has no unchecked tasks remaining

Do not claim completion early.
