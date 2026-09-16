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

The current implementation is tracked in
[`THREAD_TYPE_STORE.md`](THREAD_TYPE_STORE.md): reuse dependency graphs only
**within a single clean build**, with no persisted compiler results. Stage 1
adds tagged handles, worker-store ownership, and mutation overlays; actual
store-backed imports are not enabled yet. The older
`PACKAGE_SIGNATURE_STORE.md` persisted-store proposal is outside this goal.

## Top 10 Improvements

1. **Finish shared immutable signatures and lazy env/component views.**
   Dependency signatures should be canonical, immutable, shared, and read through contextual lazy overlays. Avoid APIs that require cloned mutable `Signature` values. Materialize only the specific value/type/module lookup result that is forced.

2. **Keep typecheck/signature work on the critical path.**
   Typechecking signatures unlocks downstream modules; JS finishing usually does not. Scheduler changes should prioritize ready signature-producing work, then run JS/codegen when no typecheck work is ready or under a separate concurrency cap.

3. **Pipeline parse/deps/interface compile with typecheck.**
   Remove avoidable phase barriers. As soon as a module or `.resi` is parsed and deps are known, enqueue interface/typecheck if its deps are ready so signatures unlock dependents earlier.

4. **Move Lambda/JS IR to indexed arenas before typedtree.**
   Lambda still uses recursive owned trees and gets traversed/transformed repeatedly. Arena/index Lambda and JS IR should reduce allocation, cloning, and pointer chasing before attempting a full typedtree arena rewrite.

5. **Create a lean normal-compile typedtree mode.**
   Normal JS compilation should avoid storing debug/canonical-only fields on every typedtree node. Preserve the full canonical shape for sexp/debug/tooling modes.

6. **Replace dense-ID hash maps/sets with indexed vectors.**
   Extend dense `TypeExprRef` work to other arena/index keys such as type refs, location refs, lident refs, module indices, and signature item indices.

7. **Intern paths, identifiers, labels, and common short strings per package/worker.**
   Avoid repeated `String`, `Path`, label, and property-name allocation/cloning in typecheck, Lambda, and JS codegen. Prefer compact IDs and per-package/per-worker interners to avoid global lock contention.

8. **Turn module registry snapshots into cheap persistent views.**
   Registry snapshots taken for spawned compile tasks should be immutable shared chunks plus small delta overlays, not cloned large maps or alias rewrite state.

9. **Add adaptive lazy indexing for large signatures.**
   Lazy lookup should scan initially, then build a compact per-kind index after repeated distinct lookups into the same large signature. Add counters for scans, hits, misses, and forced item counts before picking thresholds.

10. **Treat measurement infrastructure as a compiler feature.**
    Add counters for signature clones avoided, component scans, env overlays, registry snapshot sizes, Lambda/typedtree node counts, allocation pressure, and queued pre-JS payloads.

## Active Benchmark Target

Tella clean build:

```sh
RESCRIPT_RUNTIME=/Users/jake/dev/workspaces/rescript-rust/in-process-new/packages/@rescript/runtime \
RESCRIPT_BSC_EXE=/Users/jake/dev/workspaces/rescript-rust/in-process-new/compiler-rust/target/release/bsc \
/Users/jake/dev/workspaces/rescript-rust/in-process-new/rewatch/target/release/rescript build --in-process --no-timing true \
/Users/jake/dev/tella-fusion/packages/core/webapp
```

Use `rescript clean` as the `hyperfine --prepare` step for clean-build measurements.
