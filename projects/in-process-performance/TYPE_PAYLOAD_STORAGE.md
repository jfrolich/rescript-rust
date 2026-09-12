# Type-payload storage performance work

## Goal and baseline

The user authorized implementation on 2026-09-12, continuing until a substantial measured improvement. The first acceptance milestone is at least 10% lower full-clean parallel Tella build time in a new controlled comparison. Serial performance is reported separately. This does not waive correctness gates or authorize merging.

The working branch is `can-you-do-a-torough-look`. It was fast-forwarded, without rewriting or dropping any commits, from `3b32bd86e625532c2c121fda9a5a4da57da6e48f` to `218e0380aa55160a81aa18a4aa5893438ebf3156`, the previously measured candidate plus documentation. Production compiler sources at that baseline equal `eba0277be2065fa85df2816fcb3fb07032cfbc18`. Main and the previous feature worktree remain read-only.

The new evidence root is `/Users/jake/.opensession/artifacts/rescript-performance-20260912/type-payload-storage`. It contains the baseline Git source archive and hashes of all 414 tracked compiler/Rewatch files. Earlier diagnostic and comparison cohorts are closed and must never be rerun or modified.

Historical controlled performance was 4.777105s parallel and 19.318480s serial. These numbers are context only, not controls to pool with a new experiment.

## Implementation direction

Investigate context-owned indexed/range storage for variable-size type payloads. The lifecycle diagnostic observed about 36.5 million type nodes and a serial call-minus-body residual of 1.012s, associated with type volume. That residual includes several owners, entry and result construction; it is not a destructor measurement or a removable budget. Native reference boundaries are `compiler/ml/types.ml:22-58` and `compiler/ml/btype.ml:46-49`.

1. Identify the high-volume payload family and document its actual allocation, copy, mutation and lifetime behavior. Reuse existing captured evidence where applicable; do not repeat a broad audit or extrapolate descriptor-read samples into allocation savings.
2. Preserve a normal-release control before source changes. Implement one coherent representation change, including its compiler consumers and focused mutation/sharing tests.
3. Preserve node identity, cycles, labels/locations, list order, captured environments, substitution scopes, force/publication order and error behavior. Do not change algorithms to compensate for the storage representation.
4. Test release compiler/Rewatch artifacts and parser, typedtree, Lambda, JavaScript and error behavior. Existing red syntax/AST0 and blocked native-external gates remain explicit and cannot conceal a new regression.
5. Measure full-clean builds, including cleanup, with fixed inputs and restored protected files. A microbenchmark or instrumented attribution run is not acceptance.

No new unsafe code, per-node reference counting, structural interning, serializer fixes, dropped diagnostics, force suppression, leaks, deferred cleanup outside timing, dependency/profile changes or scheduler workarounds. Preserve intentional sparse storage, compact handles, TypeArg layout and existing coarse environment sharing. Measure enum sizes before choosing inline containers.

## Measurement and ownership

One implementation/heavy-work owner at a time. Heavy commands use `/usr/bin/lockf -k /tmp/rescript-tella-heavy.lock`; do not remove the lock. Parent review precedes a new Tella workload admission. All new experiments use fresh roots with sealed sources, binaries, helpers, fixed slots and input inventories. Supervisor failure paths must be tested, including surviving descendants; the last lifecycle outer wrapper is not safe to reuse unchanged.

Acceptance uses a new normal-release C/N cohort with eight counterbalanced pairs per mode, plus qualifications. Preserve the 18 generated files and the four protected untracked files by hash and mtime, account for all 510 generated-copy ledger entries and the exact 12 metadata paths, and verify complete JavaScript output manifests. No retries, substitutions, sample exclusions or reopening a failed cohort. Timing uses the inner monotonic clock around `/usr/bin/time -lp`; Hyperfine is secondary. Fresh runtime sources must actually compile in memory.

Parent alone pushes this branch and manages its pull request. Every new commit includes DCO sign-off and `Co-authored-by: Jaap Frolich <jfrolich@gmail.com>`. No merge or default-branch push is authorized.

## Implementation status

The first source prototype stores published `Tarrow` argument sequences in one append-only `TypeContext` vector and keeps only an 8-byte start/length range in each internal descriptor. The external `TypeDesc` and `TypeContext` construction boundary remains unchanged: exports snapshot labels and handles from the source context, while imports and copies publish a new range in the target context. The direct low-level `TypeExpr::new` constructor is now crate-private and `TypeExpr::desc` returns an owned descriptor; context-managed code already uses `TypeExprRef` plus `TypeContext`. Unary `new_arrow`/`new_generic_arrow` append directly without first allocating an argument `Vec`; builders that already supply a `Vec` still allocate and free that temporary.

The internal and external descriptor enums are both 96 bytes on 64-bit targets, `TypeExpr` remains 112 bytes, and `TypeArg` remains 16 bytes. Focused tests cover empty argument ranges, exact labels/order/shared handles, cycles, snapshot/backtrack range restoration, and cross-context remapping. Published labels now live until `TypeContext` destruction even if their descriptor is overwritten; this may increase peak memory and must be reported with the controlled build result. All storage is still reclaimed within the build process and measured cleanup boundary.

The normal-release control built from clean `75d1ac49daf49ecf85009d8a4c7381643843bd4c` is archived under `/Users/jake/.opensession/artifacts/rescript-performance-20260912/type-payload-storage/control-bin/`; hashes and toolchain/build provenance are in `control-build/provenance.txt`.

A new measurement cohort is not yet complete. No new performance result is claimed, and the arrow prototype alone is not performance acceptance.
