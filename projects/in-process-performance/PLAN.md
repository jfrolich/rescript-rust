# In-Process Performance Plan

## Scope

This project tracks clean-build performance for the Rust in-process compiler path used by `rewatch`, with Tella as the current real-world benchmark. The goal is not incremental rebuild caching yet; the immediate target is making a full clean in-process build fast through less duplicated compiler work, less cloning, better scheduling, and better shared state.

The subprocess `bsc` path must remain supported. Optimizations here should improve the in-process path without removing the standalone compiler behavior.

## Success Criteria

- Clean in-process compile of the Tella repo below 1s on the local benchmark machine.
- Tella compiles completely with `RESCRIPT_RUNTIME` pointing at the local runtime sources.
- Codegen parity remains 100%, measured as JavaScript output parity on the test corpus.
- Canonical typedtree parity remains 100% on the test corpus.
- Benchmarks use `hyperfine` and include before/after numbers before retaining performance changes.
- Meaningful improvements are committed atomically.

## Current Direction

The highest-leverage work is removing whole classes of repeated work, not polishing already-warm inner loops. The priority order is:

1. Shared immutable dependency signatures and lazy env/component views.
2. Scheduler policy that keeps typecheck/signature production on the critical path.
3. Event-driven parse/deps/interface/typecheck pipelining.
4. Arena/indexed Lambda and JS IR before a full typedtree arena.
5. Lean normal-compile typedtree storage.
6. Dense indexed side tables for arena-keyed maps/sets.
7. Per-package/per-worker interning for paths, labels, identifiers, and common strings.
8. Cheap persistent module-registry snapshots.
9. Adaptive indexing for large signatures.
10. Built-in counters for clone/scan/allocation/queue behavior.

## Active Benchmark Target

Tella clean build:

```sh
RESCRIPT_RUNTIME=/Users/jake/dev/workspaces/rescript-rust/in-process-new/packages/@rescript/runtime \
RESCRIPT_BSC_EXE=/Users/jake/dev/workspaces/rescript-rust/in-process-new/compiler-rust/target/release/bsc \
/Users/jake/dev/workspaces/rescript-rust/in-process-new/rewatch/target/release/rescript build --in-process --no-timing true \
/Users/jake/dev/tella-fusion/packages/core/webapp
```

Use `rescript clean` as the `hyperfine --prepare` step for clean-build measurements.
