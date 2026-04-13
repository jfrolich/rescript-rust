# Ralph TODO: Rewatch In-Memory Build

**Last Updated:** 2026-04-13
**Status:** 0/11 tasks complete

## Goal

Make `rewatch` run the compiler in-process, keep dependency interfaces in memory, and stop emitting or reading compiler assets anywhere in the build graph. Only final JS outputs should be written.

## Current Findings

- `node_modules` packages are already source-backed in `rewatch`; the special disk-backed bootstrap case is `@rescript/runtime`.
- `rewatch/src/build/compile.rs` still shells out to `bsc` and passes a compiler-asset-oriented protocol (`-I .../lib/ocaml`, `-bs-read-cmi`, etc.).
- `rewatch/src/build/deps.rs` still rereads dependency names from emitted `.ast`.
- `rewatch/src/build/read_compile_state.rs` reconstructs state from compiler assets on disk.
- `compiler-rust/src/driver.rs` can compile to JS in-process, but the public API does not yet return the interface object or related metadata needed by `rewatch`.
- `compiler-rust/src/cmi/persistent_env.rs` still resolves interfaces, source paths, and purity from `.cmi` / `.ast` / `.cmj`.

## Phase 1: Compiler-Rust Memory Protocol

- [ ] Add a memory-backed module/interface provider abstraction to `compiler-rust/src/cmi/persistent_env.rs`, so module interfaces, source paths, and purity can come from an in-memory registry instead of compiler assets on disk.
- [ ] Extend `compiler-rust/src/driver.rs` with an in-process API that returns final JS plus the published interface and any metadata the backend still needs for downstream compilation.
- [ ] Move JS import resolution in `compiler-rust/src/js_ir/mod.rs` onto registry metadata instead of persistent-env compiler-asset lookups.

## Phase 2: Rewatch Build State

- [ ] Extend `rewatch/src/build/build_types.rs` with in-memory parsed-module and published-interface state for each module.
- [ ] Stop writing `.ast` / `.iast` in `rewatch/src/build/parse.rs`; keep parse results in memory and extract deps directly from the parsed AST.
- [ ] Switch `rewatch/src/build/deps.rs` to read dependencies from in-memory parse results instead of rereading `.ast` files.
- [ ] Replace the `bsc` subprocess path in `rewatch/src/build/compile.rs` with direct compiler-rust calls, and publish interfaces into build state rather than serializing them.
- [ ] Preserve existing module semantics exactly: `M.resi` publishes the interface when present; otherwise `M.res` publishes its inferred interface.

## Phase 3: Runtime Bootstrap And Asset Removal

- [ ] Bootstrap `@rescript/runtime` from source into the same in-memory registry, including `Pervasives` / `Stdlib` handling for `-nostdlib`, `-nopervasives`, and `-open Pervasives`.
- [ ] Remove compiler-asset-based startup reconstruction and cleanup paths from `rewatch/src/build/read_compile_state.rs` and related clean/logging code. A fresh `rewatch` start may full rebuild.
- [ ] Emit only final JS outputs. Remove local compiler-asset emission and metadata files such as `.compiler.log`, `.sourcedirs.json`, and `compiler-info.json` from the active build protocol.

## Phase 4: Bash Test Coverage

- [ ] Add a dedicated `rewatch/tests/no-compiler-assets.sh` script and wire it into `rewatch/tests/suite.sh`.
- [ ] Tighten `rewatch/tests/compile.sh`, `watch.sh`, and `clean.sh` so they explicitly fail when compiler assets appear and cover the in-memory interface flow (`.resi`, inferred interface, node_modules source-backed deps, runtime bootstrap).

## Acceptance Criteria

- `timeout 600 ./rewatch/tests/suite.sh "$REWATCH_EXECUTABLE"` passes
- `rewatch/tests/no-compiler-assets.sh` passes
- building or watching inside `rewatch/testrepo` never creates `.ast`, `.iast`, `.cmi`, `.cmj`, `.cmt`, `.cmti`, `.compiler.log`, `.sourcedirs.json`, or `compiler-info.json`
- only final JS outputs remain on disk
- `rewatch` no longer shells out to `bsc`
