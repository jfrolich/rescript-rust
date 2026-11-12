# Signature equality oracle: harness slice

`RESCRIPT_SIGNATURE_CHECK=1` selects the check when compiler options are
constructed. `RESCRIPT_SIGNATURE_CHECK_REPORTS` must name a report directory.
The two in-process publication paths call the oracle after extraction. The
normal path does not walk, encode, inspect the environment, or write reports.
No signature reader or stored interface format changes.

Each immutable JSON report identifies the source unit and has separate outcomes
for `fingerprint`, `item_hashes`, and `bytes`. The states are `equal`, `different`
(with detail), `not_applicable` (with a reason), and `pending`. Different outcomes
for the same source produce different files; a successful retry cannot overwrite
a mismatch. A mismatch writes its report and fails compilation naming the unit
and comparison. Byte comparison reports the first differing zero-based offset,
including when one encoding is a prefix of the other. Item comparison preserves
order and duplicate names.

Run:

```sh
python3 -m unittest discover -s scripts -p 'test_signature_equality_test.py'
python3 scripts/test_signature_equality.py --executable rewatch/target/release/rescript
```

The script cleans and builds the runtime and `tests/tests` separately, filters
out dependency reports, and prints per-comparison totals and not-applicable
reasons. Zero reports, fewer units than the committed minimum, any difference,
or any pending comparison fail. The committed minimum records the clean-build publication counts
(113 runtime, 708 tests), including pending comparisons.
Source interfaces and implementations are distinct publication units.

## Incomplete: shared computations

This slice deliberately reports `pending` for all three computations. It does
not compare the portable representation against itself and does not describe
missing implementations as not applicable. Consequently the corpus command
must fail until the next slices are implemented. This is infrastructure, **not**
the H.1.7 invariant-5 gate; it must not authorize P3b to land.

### Next-slice constraint

`portable_types::hash_type_ref` recursively expands a node on every incoming
path, using `visiting.iter().position` to detect ancestors. It does not memoize
completed nodes. Therefore:

- A chain of N nodes does N(N-1)/2 ancestor comparisons and uses N stack frames.
- A subgraph with N nodes referenced by N parents is expanded N times.
- `compute_type_graph_fingerprint` and `SignatureSummary::of` separately repeat
  traversal for signature items. Item hashing uses `DefaultHasher`; fingerprint
  hashing uses `ahash`.

Merely adding a graph-reader trait preserves these costs. Memoizing a node's
hash and feeding that digest instead of its expanded hash stream changes the
existing fingerprint and item hashes. The cycle marker also contains the
ancestor's position, so cyclic subgraphs do not have a context-free hash stream.
A linear, visit-once implementation that preserves these exact hashes needs a
separate algorithmic solution before the trait/shared-reader slice can meet its
stated cost gate. This slice does not change the portable algorithm or weaken
that gate. No 10,000-node cost claim is made for the unimplemented walkers.

### Differences from the H.1 inventory

P3a's current `publish_pers_struct` accepts `SignaturePublicationMode`: only
`Eager` shareable signatures are inserted into the shared pool; leaves can be
`OnDemand`. H.1.6 describes unconditional publication. The future check must
explicitly build a graph for on-demand units in check mode, rather than silently
omit them from coverage. The existing code remains authoritative.

The frozen serialization slice is also unimplemented. In particular, no corpus
counts are yet available for information changed by `ShapeImport`, location
scope remapping, file-name interning, or genericization of `Tlink` levels in
`internalize_signature_into_shared`. These are not proven reversible and must
not be normalized away in the byte comparison.
