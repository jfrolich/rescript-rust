# In-Process Cold-Build Performance TODO

**Last Updated:** 2026-08-30
**Status:** Two explicitly different Tella corpora are tracked. The expanded v13-migration checkout compiles 3,248 modules in `4.7-4.75s` at 16 workers, down from `15.686s` before scoped variant-layout borrowing and subsequent GenType/Env ownership work. The smaller 2,127-module output-parity checkout measures `2.478s +/- 0.024s`, range `2.452s..2.528s`, after shared persistent component views and shallow signature freshening. Do not compare these numbers as one continuous corpus. The project goal remains a subsecond clean compile with 100% codegen parity.

## Goal

Make clean in-process builds fast enough for large real projects, with Tella as the active benchmark target. The hard target is a clean parallel in-process compile of the Tella repo below 1s while preserving:

- `bsc` subprocess path support
- 100% codegen parity, measured as JavaScript output parity on the 660-file test corpus
- 100% canonical typedtree parity on the test corpus
- successful Tella compilation with the configured runtime and project output extension

## Benchmark Discipline

- [x] Use `hyperfine` for accepted before/after wall-clock comparisons.
- [x] Keep a Tella module-timing run for every serious candidate to identify the slow non-Icon files.
- [x] Validate retained compiler changes with JS output parity and canonical typedtree parity.
- [ ] Commit each retained improvement atomically with the benchmark and parity result in the commit message.
- [ ] Revert candidates that regress the 660-file parity gates or Tella `hyperfine` baseline.

## Top 10 Improvements Checklist

- [ ] **1. Finish shared immutable signatures and lazy env/component views.**
  Dependency signatures should be canonical, immutable, shared, and read through contextual lazy overlays. Avoid APIs that require cloned mutable `Signature` values. Materialize only the specific value/type/module lookup result that is forced.
  - [ ] Audit hot APIs that still return owned `Signature`, `ModuleDeclaration`, `TypeDeclaration`, or full component maps.
  - [ ] Replace hot owned signature/component returns with borrowed, shared, or forced-result views.
  - [ ] Keep mutation only in memo caches keyed by module path plus contextual overlay identity.
  - [x] Build normal in-process persistent-root component views directly over shared `Arc<Signature>` when no flattened alias rewrite is required.
  - [x] Cache normal-compile qualified record labels for local-root record paths with canonical typedtree mode disabled.
  - [x] Reuse cached persistent-root type declarations before resolving/scanning module signatures again.
  - [x] Reuse cached persistent-root type items before resolving/scanning module signatures again.
  - [x] Cache persistent-root type-item misses to avoid rescanning signatures for paths that are known absent.
  - [x] Share normal in-process persistent child alias component views over backing `Arc<Signature>` and lazily rewrite only forced value descriptions.
  - [x] Share stored child-component persistent alias views over backing `Arc<Signature>` so component descent through DOM-style reexports does not clone/rewrite whole target signatures.
  - [x] In normal compile mode, shallow-copy top-level values during type-context lazy signature freshening and deep-copy only the value types that actually need binder substitution.
  - [x] Validate retained signature/env skip-work changes with Tella `hyperfine`, JS output parity, and canonical typedtree parity.

- [ ] **2. Keep typecheck/signature work on the critical path.**
  The JS/typecheck split is useful, but cold builds must prioritize signature-producing typecheck work that unlocks downstream modules. JS/codegen should run when no typecheck work is ready or under a separate cap. A previous naive scheduler priority flip regressed Tella, so this needs measured tuning.
  - [x] Measure ready typecheck queue depth, ready JS queue depth, and worker idle time.
  - [ ] Add a scheduler policy that keeps signature-producing work ahead of JS without starving JS.
  - [ ] Benchmark the policy against the retained Tella baseline.

- [ ] **3. Pipeline parse/deps/interface compile with typecheck.**
  Remove global phase barriers where possible. As soon as a module or `.resi` is parsed and deps are known, enqueue interface/typecheck if its deps are ready so signatures unlock dependents earlier.
  - [ ] Identify the current parse/dependency/typecheck barriers in `rewatch`.
  - [ ] Introduce event-driven enqueueing for parsed modules whose dependency signatures are ready.
  - [ ] Ensure `.resi` signatures publish early enough to unlock implementation dependents.
  - [ ] Validate clean-build correctness with Tella and parity gates.

- [ ] **4. Move Lambda/JS IR to indexed arenas before typedtree.**
  Lambda still uses recursive owned trees and gets traversed/transformed repeatedly. Arena/index Lambda is likely a higher-impact local-work target than a full typedtree arena.
  - [ ] Count Lambda nodes, clone/rebuild sites, and pass traversal costs on slow non-Icon files.
  - [x] Add per-module JS-finish timing so Lambda/codegen/write costs are visible after the typecheck boundary.
  - [ ] Design a Lambda arena/index layer that preserves current output ordering.
  - [ ] Port one high-traffic Lambda pass to arena-backed traversal as a measured slice.
  - [ ] Extend to JS IR or direct/chunked emission only after Lambda wins are retained.

- [ ] **5. Create a lean normal-compile typedtree mode.**
  Normal JS compile should avoid storing debug/canonical-only fields on every typedtree node. Preserve the full canonical shape for sexp/debug/tooling modes.
  - [ ] Inventory typedtree fields used only by canonical typedtree dumps, diagnostics, or tooling.
  - [ ] Gate cold typedtree fields behind `preserve_canonical_typedtree` or side tables.
  - [ ] Confirm normal JS output is unchanged and canonical typedtree mode stays at 100%.

- [ ] **6. Replace dense-ID hash maps/sets with indexed vectors.**
  Extend the existing dense `TypeExprRef` work to other arena/index keys such as type refs, location refs, lident refs, module indices, and signature item indices.
  - [ ] Find hash maps/sets keyed by dense IDs in typecheck, Lambda, JS, and serializers.
  - [ ] Replace hot per-file scratch maps with generation-marked dense vectors where the key range is known.
  - [ ] Reject candidates that pass parity but regress Tella `hyperfine`.
  - [x] Skip row-field sort allocation for large strictly-sorted polymorphic-variant rows without changing duplicate-label behavior.

- [ ] **7. Intern paths, identifiers, labels, and common short strings per package/worker.**
  Avoid repeated `String`, `Path`, label, and property-name allocation/cloning in typecheck, Lambda, and JS codegen. Prefer compact IDs and per-package/per-worker interners to avoid global lock contention.
  - [ ] Measure clone/allocation pressure for `Path`, labels, and short strings on slow non-Icon files.
  - [ ] Add local interners only where lifetime and thread ownership are clear.
  - [ ] Resolve interned names late enough to preserve diagnostics, JS output, and parity dumps.

- [ ] **8. Turn module registry snapshots into cheap persistent views.**
  Registry snapshots taken for spawned compile tasks should be immutable shared chunks plus small delta overlays, not cloned large maps or alias rewrite state.
  - [x] Measure snapshot counts and copied map sizes during a Tella clean build.
  - [ ] Split immutable registry data from compile-local delta state.
  - [ ] Ensure worker-local overlays do not leak incomplete signatures across tasks.
  - [ ] Implement package-level signature stores as described in `projects/in-process-performance/PACKAGE_SIGNATURE_STORE.md`, starting with reusable `@rescript/runtime` signatures for clean builds.

- [ ] **9. Add adaptive lazy indexing for large signatures.**
  Lazy lookup should scan initially, then build a compact per-kind index after repeated distinct lookups into the same large signature. Add counters for scans, hits, misses, and forced item counts before picking thresholds.
  - [x] Add env-gated counters for lazy signature scans, cache hits, cache misses, scanned item counts, and forced result counts.
  - [ ] Use counters on Tella slow non-Icon modules to find repeated large-signature scans.
  - [x] Add a retained adaptive value-name index for large signatures after repeated distinct value lookups.
  - [ ] Add adaptive per-kind indexes only where counters show repeated distinct lookups and `hyperfine` shows a win.
  - [ ] Benchmark thresholds with `hyperfine`.

- [ ] **10. Treat measurement infrastructure as a compiler feature.**
  Add counters for signature clones avoided, component scans, env overlays, registry snapshot sizes, Lambda/typedtree node counts, allocation pressure, and queued pre-JS payloads.
  - [x] Add low-overhead, env-gated counters that are disabled on normal builds.
  - [x] Print compact aggregate reports suitable for comparing before/after builds.
  - [x] Add scheduler queue counters for in-process typecheck/JS ready work and idle slots.
  - [x] Add qualified record-label cache counters, including local-root labels that currently bypass caching.
  - [x] Add type-item resolve counters for positive cache hits, missing cache hits, signature scans, scanned items, and found items.
  - [x] Add signature-copy counters with top call-site reporting for retained shared-signature work.
  - [x] Add signature-qualification counters to classify full-copy candidates by root cause.
  - [x] Add signature-freshening counters by entry point and module name to separate canonical rename work from access-path qualification work.
  - [x] Attribute signature copies and freshens back to the compiling module so slow non-Icon files can be tied to global signature buckets.
  - [x] Keep measurement code committed when it guides future retained optimizations.

## Active Non-Icon File Focus

- [x] Profile current Tella after excluding Icon analytically from the top-module list.
- [x] Inspect CSS polymorphic-variant-heavy files for avoidable broad row/signature forcing.
- [x] Inspect Layout/JSX-heavy files for record/label/signature lookup amplification.
- [x] Inspect Lambda conversion, JS finish, and write costs in `Layout`, `Css_Legacy_Core`, and JSX-heavy modules.
- [ ] Keep `Icon` visible in total build timing, but do not optimize only for Icon-shaped sparse JSX records.
