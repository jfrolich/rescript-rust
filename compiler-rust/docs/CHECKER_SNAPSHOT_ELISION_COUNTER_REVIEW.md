# Snapshot-elision counter ownership review

Reviewed implementation: `913faa5ed`. This audit concerns compiler counters and
retained diagnostics, not elapsed time: attempt/rerun observations and phase
timers intentionally observe work that is subsequently abandoned.

## Ownership and publication

`driver::type_structure_two_modes` creates a fresh context, calls
`TypeContext::defer_attempt_counters` **before environment setup**, and owns
checking plus the validating continuation. `ContextCounters` in
`types/context.rs` lazily owns a boxed `perf_counters::AttemptCounters`.

- `record_attempt_counter` checks the context's cached enabled flag, then updates
  local fields. Disabled contexts allocate no counter block.
- A derived fallback, an Explain retry, or a pending `LocationRetry` does not
  call `AttemptOutput::publish`. Dropping that deferred context frees the block
  without merging it into process totals. Output buffers are dropped, not
  deduplicated. Each subsequent check gets a fresh context.
- After validation, `AttemptOutput::publish` calls `keep_attempt_counters`,
  changes publication state to Committed, and only then writes reports.
  `ContextCounters::publish` takes the block; `AttemptCounters::publish` merges
  it into totals. Repeating keep or flush without new probes adds nothing.
- Probes after keep accumulate locally again and flush on context drop.
  Non-attempt world scratch contexts flush at the end of `ViewScratch::with`.
- Counts predating deferral are explicitly flushed by `defer_attempt_counters`;
  the driver starts deferral before performing any attempt-owned work.
- `derived_snapshot(ctx)` reads only local counters, never process totals;
  retaining a sibling context cannot alter this attempt's item deltas.

## Attempt-owned inventory

All rows below commit through the same `keep_attempt_counters` →
`ContextCounters::publish` → `AttemptCounters::publish` path. All are discarded
by dropping a still-deferred context. Names are fields in `perf_counters.rs`.

| Family | Stored measurements |
| --- | --- |
| Journal | `mutations[4]`, snapshots, backtracks, restores, peak live depth |
| Lazy lookup | `lazy[6]`: hits, misses, scans, scanned items, results |
| Component lookup | Qualified hits/misses/registrations; cached stored components; find-module builds |
| Type-item resolution | Scans, scanned items, type items, found results |
| Signature copying | Calls, items, maximum items; call sites; qualification/freshening kinds and names; per-module copies/freshenings |
| Frozen store | `frozen[12]`: descriptor/level reads and overlay writes, row-field and mutability access |
| Views | Adopted views, per-compilation functor-application views; store pieces built/empty/poisoned, binders, replayed pieces/effects |
| Checker allocation/copies | Copy sessions/nodes by four causes; store builds/nodes; fresh variables by call site and expected-variable construct/case |
| Checker traversals | Three walk kinds: calls, ground calls, visits, ground visits; eight unification shapes and the dense 12×12 head-constructor table |
| Exported signatures | Units/nodes/non-ground nodes, maximum non-ground nodes, recursive-ground nodes, per-unit export census |
| Publication | Nonshareable/pool-full fallbacks; frozen/hashed nodes, hash walks, pending published signature keys |
| GenType | Translated modules/declarations for annotated and unannotated classes |
| Fallback decoding | `signature_decodes`, recorded by `signature_for_attempt(ctx)` |

`cmi::portable_types::publish_signature` uses `attribute_publication(ctx, ...)`
to transfer graph-level instrumentation into the attempt. Published signature
keys reach the process-wide set only when the block commits. This covers the
private signature freeze before raw translation, even though that freeze must
precede the eventual callback. GenType probes take the context directly.

## Explicit non-block state

| State | Why it is outside `AttemptCounters`; discard behavior |
| --- | --- |
| `OwnTypeNodes` context/node totals | Counted once at pool drop, gated by the retained bit: deferral clears it, keep restores it. A discarded attempt contributes neither context nor node totals. |
| `check_attempts`, `explain_reruns` | Intentional observations of attempts and retries; not retained semantic-work counts. CLI resets them after dependency preparation. |
| Shared world predefs/views/forced children and importer decode/acquisition | Once-per-build shared work, not owned by one compilation. These remain observable if the compilation that first needed them is discarded. Per-compilation adoption, functor views and fallback decodes are local instead. |
| Registry snapshot totals | Build/registry observations outside the attempt owner. |
| Publication ID allocator | Supplies identities, not work counts. Discarded IDs can leave gaps. |
| Test-only GenType/totals thread locals | Test instrumentation, not production reports. |

Thus **discarded attempt-owned counts and reports are not published**. It would
be incorrect to claim that retry observations, shared cache construction, IDs,
or physical elapsed work disappear.

## Hot-path review

Mutation, lookup, frozen-node and copy-node count updates use plain local
fields/dense arrays: no per-node atomic, mutex or TLS operation was added.
The head-pair census uses a dense vector, allocated once per counting block.
Maps group source sites and string/construct names without an existing dense
index; they do not replace an available node index.

Publication attribution uses TLS per graph/walk/fallback, not per visited
node. Existing module attribution reads TLS and clones the module name once
per **whole-signature copy/freshening**, not per node in that copy. Global
merging takes locks per publication, not per lookup; published-key registration
and aggregate totals can take separate locks.

This is not a claim that the optional census itself is allocation-free: its
pre-existing graph analysis has scratch vectors and a sparse type-handle map,
and `checker::identical` builds child vectors recursively. Those observer
algorithms were not introduced by the counter-ownership migration. Counter-off
instruction measurements exclude that opt-in analysis.

## Personally rerun checks

```sh
cargo test --manifest-path compiler-rust/Cargo.toml \
  perf_counters::attempt_tests -- --test-threads=1
```

Result: **11 passed, 0 failed**. Tests include 10,000 operations per probe family,
disabled contexts, discard, keep/post-keep, explicit flush, pre-deferral counts,
sibling-publication isolation, fallback decodes, publication/freezing, GenType,
and reusable world scratch contexts. The block size is pinned to 1,432 bytes.
The full compiler/build-system suites and output parity were also run for
`913faa5ed`; final project measurements are in
[the measurement record](CHECKER_SNAPSHOT_ELISION_MEASUREMENTS.md).
