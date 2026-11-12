# The signature equality check

Stage P3b of the checker redesign (`CHECKER_REDESIGN.md`, H.1.5) builds the
shared graph of a published signature first and derives the fingerprint, the
item digests and the stored bytes from it, where today they come from the
portable form. H.1.7 invariant 5 asks that both give the same data. This
check compares them, for every unit a build publishes.

`RESCRIPT_SIGNATURE_CHECK=1` turns it on when compiler options are created,
and `RESCRIPT_SIGNATURE_CHECK_REPORTS` names the directory for the reports.
With the switch off, publication tests one `Option` per unit and nothing
else changes. No reader uses the results.

## What is compared

For each published unit (an implementation without an interface, or an
interface), `portable_types::publish_pers_struct_checked`:

1. gets the unit's graph in the shared pool: the graph dependents read when
   the unit is published eagerly, and a graph built for the check otherwise
   (see "Which graph");
2. computes the fingerprint and every item digest from the frozen graph, by
   the walk that computes them from the portable graph (`graph_hash.rs`,
   read through `shared_reader::FrozenGraph`), and compares them with the
   portable ones;
3. writes the portable signature back from the frozen graph
   (`shared_reader::portable_signature`, the inverse of
   `internalize_signature_into_shared`), encodes it with the encoder the
   store uses, and compares the bytes with the encoding of the portable
   signature the unit published.

A difference writes its report and fails the compilation, naming the unit,
the comparison and the first difference: both fingerprints, the first item
whose kind, name or digest differs, or the first differing byte offset.

Each report is a JSON file with the unit, the three outcomes (`equal`,
`different` with a detail, `not_applicable` with a reason), `shared_graph`
(where the graph came from) and `carried` (below). Different outcomes for
one source are different files, so a later successful attempt cannot hide a
difference.

## The hash is over the graph

Both sides hash the same thing because the hash is defined over the type
graph and written once (`graph_hash.rs`): per hashed value (the whole
signature for the fingerprint, one top-level item for its digest), nodes
are numbered in first-visit order, a reference is hashed as its node's
number, and each node's record is hashed once. The cost is one record per
node and one number per reference reached; step-count tests pin a chain of
10,000 nodes, a node with 10,000 parents and a cycle.

The earlier hash was over the tree the graph unfolds to, which costs a
quadratic number of comparisons on a chain and re-expands a shared subgraph
once per parent. Measured before the change (expansions against distinct
nodes hashed, per fingerprint and again per summary): 17,770 against 16,035
on the runtime, 37,261 against 32,539 on `tests/tests`, 457,714 against
370,327 on a 3,735-module application. So real signatures paid 11% to 24%
more than once per node, and the hash functions were about 0.3% of a build's
instructions. The change is about the bound and about one definition for
both graph forms, not about build time.

What the graph hash distinguishes that the tree hash did not: two different
sharings of one unfolded type. That is part of an interface
(`CHECKER_REDESIGN.md` I.2.1, I.3.3 rules 5 and 8): a dependent that links
one position of a scheme changes every position that is the same node.
What it no longer distinguishes: two variant layouts that differ only in
the allocation identities of their shapes, which the tree hash read through
`Debug`. No dependent reads those identities, `Layout`'s equality ignores
them, and an import renumbers them, so the shared graph's differ from the
portable form's.

Not hashed by either algorithm: whether a node is at the generic level, and
sharing between two top-level items in the item digests (the fingerprint
covers it).

## Which graph

| `shared_graph` | When | Graph compared |
|---|---|---|
| `published` | every shareable unit, including units without dependents | the one dependents read; publication computes its fingerprint and item digests here |
| `forced: not shareable` | the graph holds a `Tsubst` | a graph of the pool that no reader is given |

Only a full pool leaves a unit without a comparison (`not_applicable`, "the
shared pool is full").

The raw signature (`PortableRawSignature`) is not compared: it has no shared
graph. P3b keeps writing it from the `TypeContext` (H.1.5, step 9).

## What the node arrays do not hold

`internalize_signature_into_shared` drops or rewrites four things one way.
The inverse reads them from `SharedGraph::carried`, recorded during every
import, not just in check mode. The comparison never changes
either side to make them agree: it carries the missing data and lists, per
unit, which of it was not empty.

| `carried` | What the import does | What the frozen graph retains |
|---|---|---|
| `file names` | A location names its file by a pool index allocated at import. The portable signature holds `cmi_longident_names`: the names with their portable keys, in order of first use, including names only the raw signature uses | the `(key, name)` list of the publication |
| `allocation scopes` | The scope of a location identity and of a shape's attribute string becomes a hash of the unit and the scope (`identity_in_namespace`) | the producer's scope of each imported scope |
| `shape allocations` | A shape allocation becomes a hash of the unit and the allocation | the producer's allocation of each imported one |
| `link levels` | Every `Tlink` entry is stored at the generic level | the level of each link that is not generic (a link's level is dead state) |

Exact without carried data: node order and descriptors, type lists, arrow
parameters with their labels, rows, package constraints, object-field
mutability cells (numbered by first use in node order, as the serializer
numbers them), the levels of nodes that are not links, variant layout
references, and location handles.

## Running it

```sh
python3 -m unittest discover -s scripts -p 'test_signature_equality_test.py'
python3 scripts/test_signature_equality.py --executable rewatch/target/release/rescript
```

The script cleans and builds the runtime and `tests/tests` in check mode and
prints, per corpus, the units compared, equal, different and not applicable
by reason for each comparison, where the shared graphs came from, and how
many units needed each kind of carried data. It fails on a failed build, on
zero reports, on fewer units than `tests/signature_equality_minimum.json`,
on any difference and on a report that is missing a field.

## P3b slice 1: ownership of serialization metadata

The four kinds of metadata now live in a cold record in each frozen graph,
not in the equality check. `portable_signature` accepts only the frozen
graph reader and shared signature; the portable comparison cannot supply
its missing inputs. Both normal and checked publication populate the record.

- File names retain their original keys and order, including raw-only names.
  Pool names alone cannot reconstruct this table. Cost: one list per graph.
- Allocation scopes and shape allocations retain inverse import maps.
  Reversing the namespace hash is impossible; keeping these sparse maps
  preserves existing identities without changing any dependent's view.
- Link levels retain a sparse list of non-generic entries. Type readers
  continue seeing generic links; stored bytes retain their original levels.

None of these fields enlarges a type node. Their lifetime is the graph's,
so inverse serialization needs neither the producer's context nor its
portable signature. Capture and reconstruction are linear in graph size
and metadata size, with maps per graph, not per node.

## P3b slice 2: publication hashes

`prepare_publication` builds the shared graph before creating the registry
Arc, computes its fingerprint and item hashes through `FrozenGraph`, then
registers that same Arc in the pool. The item hashes are retained until the
summary uses them; reference collection still reads the portable signature
in this slice. Stored units and the non-shareable/full-pool fallback retain
the portable hash. Check mode computes the portable oracle independently
and compares it against the actual published fingerprint and item hashes.

Leaf publications now also build a shared graph, rather than waiting for a
later reader. This is necessary for shared-only hashes; storage still runs
after release, and dependency scheduling is unchanged. The existing leaf
regression checks that storage discards the portable graph and later lookup
reuses the graph built for hashing, without decoding it again.
