# Typechecker Performance Plan

## Goal

Make the Rust parser-free compiler pipeline at least as fast as the OCaml
reference compiler on the canonical recursive `tests/tests/src/**/*.res`
corpus, starting with the extreme module-signature cliff in
`tests/tests/src/Import.res`.

This project is not about parser speed or JS backend speed. The current hotspot
is in Rust typechecking and module signature resolution.

## Baseline

Authoritative single-file `Import.res` repro on 2026-04-13:

- OCaml: about `0.07s`
- Rust: about `8.69s`
- Rust peak memory: about `5.7GB`

The output JS is close. The gap is compile-time and allocation behavior.

Authoritative canonical-corpus benchmark on 2026-04-13:

- Canonical source universe: `657` files
- Comparable files: `657`
- Rust faster or equal: `2`
- Rust slower: `655`
- Materially slower: `252`
- Aggregate Rust / OCaml ratio: `4.29x`

Detailed corpus baseline and root-cause buckets:

- [CORPUS_BASELINE.md](./CORPUS_BASELINE.md)

## Root Cause Summary

Rust repeatedly deep-copies whole module signatures and nested type graphs while
resolving module members and expanding types. OCaml instead uses lazy,
path-qualified module views with cached substitution work and much better
sharing.

Detailed investigation and fix guidance:

- [IMPORT_RES_PERFORMANCE_HANDOFF.md](./IMPORT_RES_PERFORMANCE_HANDOFF.md)

## Scope

In scope:

- module signature resolution
- module alias/path qualification
- inclusion checking setup work
- type expansion through module paths
- semantic module type lookup for unpack/module expressions
- caching/sharing of qualified module views

Out of scope:

- parser performance
- raw/optimized lambda parity
- JS output parity except as a downstream regression guard

## Desired End State

Rust should behave more like OCaml in this area:

1. rename persistent signatures once
2. build access-path-qualified module views lazily once per path
3. answer repeated value/type/module lookups from cached qualified views
4. preserve sharing inside substituted type graphs
5. avoid repeated full-signature detachment for single-member lookups

This project prefers the proper OCaml-shaped solution over bandaids:

- Rust should move toward OCaml's lazy `ps_sig` / `prefix_idents` /
  `components_of_module_maker` model
- local fixes are acceptable only if they are stepping stones toward that model
- "good enough but still slower than OCaml" is not an acceptable endpoint
- a fix is not done while any comparable canonical file is still slower than
  OCaml without an understood root cause and a concrete follow-up

## Phases

### Phase 0: Stabilize Repro And Measurement

Objective:

- keep a stable exact `Import.res` repro
- keep the canonical 657-file benchmark authoritative for broader regressions
- use `time`, `sample`, and the benchmark script as the measurement tools

Acceptance:

- repeated timing repro is documented
- profiler consistently points to the same hot path before optimization
- `scripts/benchmark_typechecker_performance.py` reproduces the canonical
  slower-than-OCaml set and writes stable machine-readable results

### Phase 1: Collapse Duplicate Module-Signature Resolution Paths

Objective:

- unify the overlapping resolution paths in `typecore.rs` and `ctype.rs`
- stop `ctype` from bypassing the more useful path-qualified caching logic

Acceptance:

- `resolve_type_item_through_env` no longer constructs throwaway whole-signature
  copies for repeated queries through the same access path

### Phase 2: Cache Qualified Module Views The OCaml Way

Objective:

- cache the final path-qualified signature or components view per access path
- reuse it across type expansion, inclusion setup, and member lookups
- move toward OCaml-style lazy qualified components instead of ad hoc memoization

Acceptance:

- `copy_lookup_signature_for_subst` and `copy_lookup_type_expr` disappear as the
  dominant `Import.res` hot path
- memory drops by orders of magnitude

### Phase 3: Implement The OCaml Lazy Components Model

Objective:

- model Rust more closely on OCaml's lazy module-components construction
- answer lookups from cached component tables rather than repeated signature scans

Acceptance:

- repeated member lookups are effectively O(1) over the cached view
- nested module-path access no longer rebuilds child signatures repeatedly

### Phase 4: Clean Up Secondary Costs

Objective:

- remove smaller retyping costs like unpack semantic-module-type recovery
- simplify remaining duplicate resolution code

Acceptance:

- no obvious secondary hotspots remain in `Import.res`

## Success Criteria

- `Import.res` matches or beats OCaml on the same machine, allowing only normal
  timing noise
- every comparable file in the canonical 657-file corpus matches or beats OCaml
  on the same machine, allowing only normal timing noise
- Rust does not allocate multi-GB for `Import.res`
- typedtree behavior remains correct
- no parity regressions are introduced in core test coverage

## Guardrails

- no `Import.res`-specific hacks
- no weakening of type expansion semantics
- no in-place mutation of shared original signatures
- cache keys must respect access-path semantics, not only module names
- do not stop at a bandaid cache if the design still materially diverges from
  OCaml's lazy module-components model
