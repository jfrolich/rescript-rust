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

## Approved compact-node design

The next source unit replaces the large internal descriptor with an ordinary strongly typed `Copy` enum. Each variant carries at most three typed `u32` handles or range words; the required 64-bit layout targets are 16 bytes for `StoredTypeDesc` and 24 bytes for `TypeExpr`, verified by tests rather than assumed. `TypeDesc` remains the owned public construction and export snapshot boundary. `TypeExprRef` remains the sole type-node identity; payload publication does not intern by structure, path spelling, or string content.

The compact descriptor stores arrow argument ranges directly. A common context-owned `TypeExprRef` range store owns tuple elements, constructor arguments, polymorphic binders, package arguments, object-name arguments, row-name arguments, and `Reither` type lists where those cold shapes are compacted. Constructor, package, field metadata, object-name values, and variant rows use typed context-local payload indices where they do not fit inline. `ObjectName` keeps its current immutable value semantics for this unit; the unused `ObjectNameRef` and native mutable object-name reference remain explicit parity debt rather than an unreviewed semantic change. Existing `RowFieldRef`, `FieldKindRef`, and abbreviation identities and mutation behavior remain unchanged.

This follows the native descriptor forms and mutable type record in `compiler/ml/types.ml:22-58` and the one-node allocation path in `compiler/ml/btype.ml:46-49`. In particular, row traversal must retain `compiler/ml/btype.ml:237-271` ordering: resolve each field link only when that field is reached, after callbacks for earlier fields, then inspect `repr row_more` only after all field callbacks. Published row shapes may be immutable, but linked rows must not be flattened or their mutable field links pre-resolved.

Internal borrowed readers migrate with the representation. Reading a node returns a copied compact descriptor; cold payload access uses short mapped borrows or copies only stable headers/ranges/handles, and releases every aggregate borrow before recursion, callbacks, allocation, or descriptor mutation. The current public `get_desc` boundary continues to reconstruct owned snapshots. Required traversal, representative, unification, expansion, and copy consumers in `btype`, `ctype`, `typecore`, and `typemod` move together; remaining public-boundary snapshot cost is reported rather than hidden by a whole-checker rewrite.

Every range validates its combined exclusive end before mutating storage, and no mapping callback runs while aggregate storage is mutably borrowed. Focused tests cover exact layouts, every descriptor round trip, empty and overflow arithmetic, identity and cycles, cross-context republishing, replacement, reentrant allocation, late row-field and `row_more` mutation, failed-unify restoration versus temporary `Tsubst` cleanup, and pool accounting. Pool indices never cross a `TypeContext`; imports and exports expand through owned `TypeDesc` snapshots and republish in the destination.

Cold payloads superseded by `set_desc` are retained until the owning `TypeContext` is destroyed, as pooled arrow labels already are. Empty `Vec` values do not allocate, and the node-size reduction is not a net peak-memory claim: pool lengths, capacities, overwritten publications, and reclamation timing must be disclosed. Reclamation remains inside the full build lifetime. If retained cold payloads outweigh the compact nodes, that is a failed storage hypothesis, not permission to leak or defer destruction outside measurement.

## Implementation status

The compact-node source unit now uses the typed `Copy` descriptor and context-owned cold payload stores described above. Release layout tests confirm `StoredTypeDesc` is 16 bytes and `TypeExpr` is 24 bytes on the 64-bit development target; `TypeDesc` remains 96 bytes at the public snapshot boundary. Focused release tests cover all descriptor forms, checked range arithmetic, pooled-arrow labels/order/sharing, cross-context republishing, descriptor replacement retention, failed-unify restoration, reentrant allocation, and late row-field/`row_more` observation. The unused native-style mutable `ObjectNameRef` remains parity debt: this unit deliberately preserves the existing immutable `ObjectName` value behavior. No performance result is claimed before a new controlled comparison.

The first source prototype stores published `Tarrow` argument sequences in one append-only `TypeContext` vector and keeps only an 8-byte start/length range in each internal descriptor. Internal leaf readers borrow `StoredTypeDesc` directly instead of materializing an owned `TypeDesc`; recursive arrow traversals capture the range and return handle, release the node borrow, then use an iterator that borrows aggregate storage only long enough to copy one `TypeExprRef`. Full label snapshots remain limited to operations that must preserve or rebuild labels. The external `TypeDesc` and `TypeContext` construction boundary remains unchanged: exports snapshot labels and handles from the source context, while imports and copies publish a new range in the target context. The direct low-level `TypeExpr::new`, `TypeExpr::desc`, and `TypeExpr::set_desc` operations are now crate-private; context-managed code uses `TypeExprRef` plus `TypeContext`, which is required for valid arrow access. Unary `new_arrow`/`new_generic_arrow` append directly without first allocating an argument `Vec`; builders that already supply a `Vec` still allocate and free that temporary.

The internal and external descriptor enums are both 96 bytes on 64-bit targets, `TypeExpr` remains 112 bytes, and `TypeArg` remains 16 bytes. Range construction validates the combined exclusive end before extending aggregate storage. Focused tests cover boundary arithmetic without large allocations, empty argument ranges, exact labels/order/shared handles, cycles, snapshot/backtrack range restoration, cross-context remapping, reentrant allocation, and replacement of the original arrow during child traversal. Published labels now live until `TypeContext` destruction even if their descriptor is overwritten; this may increase peak memory and must be reported with the controlled build result. All storage is still reclaimed within the build process and measured cleanup boundary.

The normal-release control built from clean `75d1ac49daf49ecf85009d8a4c7381643843bd4c` is archived under `/Users/jake/.opensession/artifacts/rescript-performance-20260912/type-payload-storage/control-bin/`; hashes and toolchain/build provenance are in `control-build/provenance.txt`.

Parent release validation of candidate `ab452b6272842b2cbea6810d3ac354249bd58b9a` passed 610 typedtree, 610 optimized Lambda, 610 raw Lambda, 344 focused plus 610 corpus JavaScript cases, and 1431 diagnostics. Raw commands, output and exit codes are preserved in `release-gates-arrow-v3/`. Earlier worker parity logs used debug binaries. Syntax remains 504/570 with an abort reported; matching counts are not baseline-equivalence proof. Legacy AST0 and native-external limitations remain unwaived.

The existing Tella dependency symlink `node_modules/@rescript/belt/node_modules/rescript` resolves to this compiler worktree. The fast-forward and compiler validation changed compiler development caches, test artifacts and tracked performance evidence reached through that link. The current inventory has 42485 inputs rather than the historical 42463. All 154 differing paths were reviewed before admission; no input was excluded from the new comparison. The exact delta is preserved in `approved-compiler-workspace-baseline-delta-02.json`. Three preparation roots were closed before any workload; the first preparation's unsaved initial inventory is not reconstructed from its later observation.

`comparison-arrow-v3-4` is permanently closed and invalid for performance analysis. Two qualifications and one timed parallel C/N pair completed with exact JavaScript output, but the executor could not attest to the prescribed stage-2 outer capture and environment. Stage 3 ran before that problem was noticed. No later stages ran, no timings were analyzed or pooled, and existing outer files were not reconstructed. Parent closeout independently verified all recorded process groups absent, unchanged sealed files, the final inventory, all 510 ledger rows, and hash/mtime restoration for 18 generated files plus six protected untracked fixtures. Evidence is in `provenance/parent-invalid-cohort-closeout.json`.

A canonical archived Python entry now owns the lockf re-exec, bytecode environment, exclusive command/log/exit capture, and validation of earlier outer captures. It invokes the existing runner in the same process, retaining its deadline and descendant supervision instead of introducing another process tree. Fifty protocol tests passed, including seven actual lockf/re-exec tests with a fake inner runner; those tests do not compile Tella.

## Completed arrow-only comparison

`comparison-arrow-v3-5` completed its original 34-stage schedule: two qualifications and 32 timed builds, eight counterbalanced pairs per mode. Parent independent audit verified all 100 child process records and absent groups, canonical outer captures, 137 input inventories, all 510 ledger rows per inventory, 24 protected files, both archived qualification outputs and all 34 matching 5048-file JavaScript manifests. Sources and binaries stayed sealed. Two external shell/path errors never entered the cohort or consumed a slot; parent zero-launch audits authorized the original unattempted slots. The explicit stage-2 authorization is preserved despite a worker transcript-visibility gap. Parent directly executed stages 10–33 and analysis.

| Mode | Control mean ± SD | Candidate mean ± SD | Min–max control / candidate | Paired candidate−control 95% CI |
| --- | --- | --- | --- | --- |
| Parallel, 12 workers | 4.779277 ± 0.045850s | 4.769424 ± 0.037044s | 4.719559–4.875899 / 4.736069–4.851970s | −0.062088 to +0.042383s |
| Serial, 1 worker | 18.145647 ± 0.149108s | 18.341646 ± 0.114378s | 17.976400–18.396278 / 18.211902–18.514997s | +0.099661 to +0.292337s |

Parallel mean improves only **0.206%**, with four of eight candidate wins and a paired interval spanning zero. Serial regresses **1.080%**, with one of eight candidate wins. This is not the required 10% improvement. Arrow-only storage is not accepted or promoted as a performance optimization.

Mean process peak footprints were 2,856,262,896 / 2,849,715,431 bytes for parallel control/candidate and 1,885,818,791 / 1,886,592,929 bytes for serial. Mean maximum RSS was 2,882,048,000 / 2,877,775,872 bytes parallel and 1,919,870,976 / 1,916,323,840 bytes serial. Neither measure establishes a material memory reduction. The prototype still leaves every type node at 112 bytes.

Raw evidence is in `comparison-arrow-v3-5/summary.json` and `provenance/parent-independent-audit.json`. The first read-only audit parser failed on macOS `time -p` field order; its original helper and failure disclosure are retained. The corrected, prewritten audit passed without rerunning workloads. This cohort is closed permanently; no sample was replaced or excluded and no earlier timings were pooled.

The substantial-improvement goal remains unmet. Continue the same storage task with a coherent representation change rather than retaining this flat arrow-only result as a win. Keep the archived candidate/control and completed evidence intact.
