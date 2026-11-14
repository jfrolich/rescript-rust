# Complete-unit lowering allocation scaling

The criterion is a constant number of allocation calls per unit, **not zero
allocations or constant bytes**. The four tests warm the real entry once at each
size, then measure a fresh imported input through `lower_with_resolver`, state
construction, export coercion, `complete_unit` and `finish`. Import, validation
and destruction of the returned output are outside the interval. Warming does
not pretend to retain the consumed state's storage.

Each test asserts both `count(1_000) == count(10_000)` and its numeric constant:

| Family | 1,000 elements | 10,000 elements | Release constant |
| --- | ---: | ---: | ---: |
| Conditionals | 68 | 68 | 67 |
| Ordinary switches | 85 | 85 | 84 |
| Applications | 68 | 68 | 67 |
| Mixed untagged dispatch | 138 | 138 | 137 |

Release omits the one debug-only child-uniqueness table. These are proofs for
these four shapes, not a claim about every possible program, number of exports,
argument width, inlined body or variant layout. Bytes still scale with output
size; reservations trade capacity for fewer growth operations.

## Allocation attribution

The table attributes every debug allocation to its nearest BIR/Lambda source
frame (including allocations in helpers that frame calls). Columns are
conditionals, switches, applications, untagged. Rows are sorted by their largest
per-unit count. The same totals hold at both sizes.

| Owner under `src/` | C | S | A | U | Disposition |
| --- | ---: | ---: | ---: | ---: | --- |
| `bir/lower/mod.rs` | 27 | 36 | 28 | 36 | per unit, kept: output columns, source traversal, variables, grouping and fingerprint domains reserved from imported counts; owned unit completion. |
| `lambda/untagged_dispatch.rs` | 0 | 0 | 0 | 25 | per unit, kept: pre-reserved graph/group/clause/memo pools and retained fixed-kind planning/equality scratch. |
| `bir/lower/export.rs` | 18 | 19 | 18 | 19 | per unit, kept: unchanged exporter materializes rows, names and owned output once for the fixture's single export; rows are sized from the completed variable domain. |
| `bir/lower/untagged.rs` | 0 | 1 | 0 | 18 | per unit, kept: imported runs, literal/text/emission reservations and plan-local stacks sized from known arm/action counts. |
| `bir/edit.rs` | 3 | 3 | 3 | 10 | per unit, kept: release/finalization work; mixed dispatch additionally copies one fixed-size cached fallback using retained traversal/remapping storage. Dense node rows reserve the arena domain. |
| `lambda/untagged_dispatch/metadata.rs` | 0 | 0 | 0 | 6 | per unit, kept: literal rows, sorted indexes, text bytes and canonical spelling scratch reserved before import. |
| `bir/lower/out.rs` | 4 | 4 | 4 | 4 | per unit, kept: reserved statement and deferred-realization columns. |
| `bir/lower/switch.rs` | 0 | 4 | 0 | 1 | per unit, kept: switch output runs sized from case counts, one plan frame and retained fingerprint traversal. |
| `lambda/lam_tag_info.rs` | 3 | 4 | 3 | 4 | per unit, kept: clone/serialization of the fixed export-block record at the owned compatibility boundary. |
| `bir/lower/label.rs` | 3 | 3 | 3 | 3 | per unit, kept: three scheduling spines reserved from imported occurrences. |
| `bir/lower/scope.rs` | 3 | 3 | 3 | 3 | per unit, kept: three initialized variable columns, with reserved generated-binding room. |
| `bir/mod.rs` | 3 | 3 | 3 | 3 | per unit, kept: the fixed output block's cold payload and structural interning storage. |
| `bir/lower/konst.rs` | 2 | 2 | 0 | 2 | per unit, kept: first-use retained scalar-constant work/value scratch. |
| `bir/pools.rs` | 1 | 1 | 2 | 1 | per unit, kept: reserved output operand pool; applications also initialize the retained source call-operand run. |
| `bir/j/equal.rs` | 1 | 0 | 0 | 1 | per unit, kept: first-use retained equality worklist. |
| `bir/lower/call.rs` | 0 | 0 | 1 | 0 | per unit, kept: first-use call frame storage, reused across all calls. |
| `bir/lower/variant.rs` | 0 | 1 | 0 | 1 | per unit, kept: source-switch-indexed metadata, sized from existing headers. |
| `lambda/lam_primitive.rs` | 0 | 1 | 0 | 1 | per unit, kept: fixed primitive fingerprint serialization into retained scratch. |
| **Total** | **68** | **85** | **68** | **138** | |

Removed sites: geometric growth of output node/operand/variable columns,
traversal and label spines, deferred expressions, statement slots, reference
sites, argument buffers, call payloads, switch groups/fingerprints/clauses/keys,
literal metadata and emission rows, planner groups/trees/clauses/memo, and
untagged program/action pools. Bulk capture traversal no longer snapshots wide
children. Assignment-target comparison no longer allocates a work vector for
each comparison. Each site was committed separately as it was identified.

A capacity estimate is not a rejection limit: unusual FFI/inlining expansions
can still grow safely. Small fixed-boundary scratch is retained after first use;
the measurements must not be generalized to shapes absent from these tests.

## Reproduce the counts and attribution

```sh
CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml \
  full_unit_allocation_boundary -- --nocapture --test-threads=1
CARGO_INCREMENTAL=0 cargo test --release --manifest-path compiler-rust/Cargo.toml \
  full_unit_allocation_boundary -- --nocapture --test-threads=1
TEST_BINARY=$(CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml \
  --no-run --message-format=json | python3 -c '
import json,sys
for line in sys.stdin:
    row=json.loads(line)
    if row.get("reason")=="compiler-artifact" and row.get("executable") and row["profile"]["test"] and row["target"]["name"]=="rescript_compiler":
        print(row["executable"])
')
gdb -q -batch -ex 'source scripts/profile_lowering_allocations.py' "$TEST_BINARY"
```

The debugger records allocator calls only between the test-only entry/completion
markers. It writes `temp/lowering-allocation-sites.json`, including both widths,
full source-frame stacks and owner totals. It changes no production allocator
or compiler code. The table above is the profiler's printed owner table.
