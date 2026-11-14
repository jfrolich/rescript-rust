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

## Shared files outside BIR

These changes are kept to avoid per-construct ownership in the named lowering
paths without duplicating the existing algorithms. “Allocation-free” here means
the retained inner path; the complete unit entry has the constants above.

| Source file (under `compiler-rust/src`) | Disposition | Named lowering caller and necessity |
| --- | --- | --- |
| `js_ir/printer.rs` | Kept | `lower::import::State::compile_import` and `lower::prim_block::State::primitive_field` call `convert_ident_into` to avoid temporary owned spellings. |
| `lambda/lam_analysis.rs` | Kept | `lower::call::State::inline_external_function` reaches `is_pure_primitive_with_properties` through `beta::reduce` and `bir::l::flatten`; scalar properties avoid reconstructing owned bigint constants. |
| `lambda/lam_compile_variant.rs` | Reverted | No BIR lowering caller. Restored byte-for-byte to trunk; the shared planner now exposes borrowed compatibility views for the unchanged emitter. |
| `lambda/mod.rs` | Kept | `lower::prim_block::State::flat_make_field` and `lower::import::State::compile_import` call `flat_export_name_into`; returning an owned export name would allocate per construct. |
| `lambda/untagged_dispatch.rs` | Kept | `lower::untagged::State::untagged_switch` calls `append_bucketed` on retained graph/planning storage; trunk's owned-input planner allocates for each switch. |
| `lambda/untagged_dispatch/metadata.rs` | Kept | `lower::untagged::prepare` imports handles; `State::untagged_test` and `State::untagged_instance` borrow those payloads instead of cloning strings/instance ancestry per emitted test. |
| `ocaml_float.rs` | Kept | `lower::untagged::prepare` reaches `float_of_string_in` via metadata canonical-key encoding; retained separator removal avoids a vector per literal. |
| `string_literal.rs` | Kept | `lower::prim::State::finish_primitive_values` reaches retained `TemplateBuffer` through `jm12_interpolated_template`, avoiding per-template encoding/normalization vectors. |
| `types/typecore.rs` | Kept | `lower::konst::State::constant` and `lower::variant::State::switch_key_expression` call `parse_bigint_literal_into` directly, avoiding per-bigint spelling strings. |
| `types/variant_runtime.rs` | Kept | `lower::untagged::prepare` reaches `LiteralKeyScratch::encode` through `Metadata::import_literal`, retaining canonical equality-key buffers rather than allocating intermediate strings per literal. |

The `prepare` metadata work is inside the full-unit interval. It was outside the
earlier probe-only interval. `types/typecore.rs` has direct lowerer callers;
`types/variant_runtime.rs` is reached by `lower::untagged::prepare` →
`Metadata::import_literal` → `LiteralKeyScratch::encode`. Neither is unexplained
or merely a default-path cleanup.

The differential compares **453 recorded layouts (192 distinct printed layouts) from 850 implementation files**,
with 68,352 plan pairs across full, omitted, partitioned, singleton and reversed
arm lists and all sixteen completeness/sharing/fallback configurations. Both
`differential.rs` and the verbatim `legacy_planner.rs` are test-only. Reproduce:

```sh
CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml \
  corpus_declarations_match_trunk -- --nocapture --test-threads=1
git show be1b3a482:compiler-rust/src/lambda/untagged_dispatch.rs | \
  cmp - compiler-rust/src/lambda/untagged_dispatch/legacy_planner.rs
rg -n 'parse_bigint_literal_into|convert_ident_into|flat_export_name_into|jm12_interpolated_template' compiler-rust/src/bir/lower
rg -n 'is_pure_primitive_with_properties' compiler-rust/src/bir
```

Build reference artifacts using the commands in `BACKEND_LOWERING.md` §11 before
rerunning the file-backed corpus test. A missing artifact is not a skipped case.

## Historical validation and measurements (not the default-path gate)

Measured head: `7fbf98419` (functional code `0e696cbf0`; subsequent changes are
reports only). Control: integrated trunk snapshot `be1b3a482`. Both use release
fat LTO and **one codegen unit**, one worker, and separate identical copies of
the pinned `e5ada1df93` corpus. Complete path sets and hashes match for **925**
runtime/project source files; each build compiles **738 modules**. These are new
measurements, not the earlier candidate's numbers.

| Mode | Control minimum instructions | Head minimum instructions | Change |
| --- | ---: | ---: | ---: |
| Default, backend variable unset | 4,053,902,681 | 4,052,604,641 | −0.032020% |
| Check | 20,588,118,253 | 20,074,343,029 | −2.495494% |

The default result passes the **+0.02%** gate without a waiver. Minimum of five
Cachegrind runs; each row below lists those runs in order:

- Default control: 4,055,058,651; 4,054,447,486; 4,055,651,142; 4,053,902,681; 4,055,824,607.
- Default head: 4,054,823,670; 4,052,604,641; 4,056,301,067; 4,055,920,444; 4,054,716,032.
- Check control: 20,598,311,868; 20,588,118,253; 20,603,852,298; 20,603,623,122; 20,591,330,693.
- Check head: 20,091,875,420; 20,083,081,386; 20,109,527,126; 20,117,282,106; 20,074,343,029.

Hyperfine: ten runs after two warmups, cleaning before every run:

| Mode / binary | Mean ± standard deviation, seconds | Minimum–maximum, seconds |
| --- | ---: | ---: |
| Default control | 1.650361 ± 0.084561 | 1.468943–1.805150 |
| Default head | 1.673740 ± 0.132318 | 1.474251–1.879854 |
| Check control | 4.535693 ± 0.244672 | 4.183661–4.868758 |
| Check head | 4.377297 ± 0.192919 | 3.927784–4.642459 |

The default wall-time mean is slightly slower, with overlapping variation.
**No wall-time speedup, profile-independent improvement or RSS reduction is
claimed.** Eager capacity reservations can increase peak live storage even
while reducing allocation calls and total allocated bytes. The earlier
16-codegen-unit results in `BACKEND_LOWERING.md` are historical, not this gate.

### Performance commands

Use the archived control checkout and the separate corpus copies described in
`BACKEND_LOWERING.md` §11. Do not extract a revision over another source tree:
extra files invalidate comparisons. Hash-check both complete source path sets,
not just paths from a preexisting manifest.

```sh
export CARGO_INCREMENTAL=0
CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 cargo build --release --manifest-path temp/lowering-trunk-control/rewatch/Cargo.toml
CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 cargo build --release --manifest-path rewatch/Cargo.toml
BASE="$PWD/temp/lowering-trunk-control/rewatch/target/release/rescript"
HEAD="$PWD/rewatch/target/release/rescript"
B_CORPUS="$PWD/temp/lowering-correction-base-corpus"
H_CORPUS="$PWD/temp/lowering-candidate-corpus"
export B_CORPUS H_CORPUS
python3 - <<'PY'
from pathlib import Path
import hashlib, os
def sources(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for sub in ['tests/tests', 'packages/@rescript/runtime']
            for p in (root/sub).rglob('*') if p.suffix in ('.res', '.resi')}
a,b = (sources(Path(os.environ[key])) for key in ['B_CORPUS','H_CORPUS'])
assert a == b
print(len(a))
PY
env -u RESCRIPT_BACKEND python3 scripts/compare_build_instructions.py \
  --base "$BASE" "$B_CORPUS" --head "$HEAD" "$H_CORPUS" \
  --runs 5 --threshold 0.02 --work-dir temp/scaling-final-default
RESCRIPT_BACKEND=check python3 scripts/compare_build_instructions.py \
  --base "$BASE" "$B_CORPUS" --head "$HEAD" "$H_CORPUS" \
  --runs 5 --threshold 0.02 --work-dir temp/scaling-final-check
PREPARE="'$BASE' clean '$B_CORPUS/tests/tests' && '$HEAD' clean '$H_CORPUS/tests/tests'"
for MODE in default check; do
  if [ "$MODE" = default ]; then BACKEND='-u RESCRIPT_BACKEND'; else BACKEND='RESCRIPT_BACKEND=check'; fi
  hyperfine --warmup 2 --runs 10 --prepare "$PREPARE" \
    --export-json "temp/scaling-final-$MODE-hyperfine.json" \
    "env $BACKEND RAYON_NUM_THREADS=1 RESCRIPT_RUNTIME='$B_CORPUS/packages/@rescript/runtime' '$BASE' build '$B_CORPUS/tests/tests'" \
    "env $BACKEND RAYON_NUM_THREADS=1 RESCRIPT_RUNTIME='$H_CORPUS/packages/@rescript/runtime' '$HEAD' build '$H_CORPUS/tests/tests'"
done
```

The instruction script sets one worker and each side's runtime, prepares that
runtime outside measurement, cleans before each build and prints every count
and module total. Reject results with unequal module counts.

### Validation results and commands

| Gate | Result |
| --- | --- |
| Full serial compiler unit suite | 2,465 passed; 25 existing ignores |
| BIR tests within that suite | 774 passed |
| Compiler integration tests | 4 passed |
| Compiler doctests | 5 passed; 7 existing ignores |
| Four pinned unit-entry tests, debug and release | All passed in both profiles |
| Rewatch tests | 210 unit + 9 integration passed |
| Strict all-target compiler clippy | Passed |
| Exact focused JS / canonical snapshots | 472/472 and 737/737 |
| Exact stdlib / in-repository GenType | 113/113 and 2/2 |
| Backend coverage ratchet | Passed, no baseline changes |

No new ignores or fixture changes. The external application comparison was not
run. Regenerate reference artifacts after clean/benchmark commands, which can
remove dependency artifacts:

```sh
export CARGO_INCREMENTAL=0 TMPDIR=/tmp
opam exec --switch=rescript -- dune build --root . compiler/bsc/rescript_compiler_main.exe compiler/syntax/cli/res_cli.exe
export OCAML_BSC="$PWD/_build/default/compiler/bsc/rescript_compiler_main.exe"
export RESCRIPT_RUNTIME="$PWD/packages/@rescript/runtime"
export RESCRIPT_CLI="$PWD/rewatch/target/debug/rescript"
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
"$RESCRIPT_CLI" build-reference --bsc "$OCAML_BSC" packages/@rescript/runtime
"$RESCRIPT_CLI" build-reference --bsc "$OCAML_BSC" tests/dependencies/rescript-react
"$RESCRIPT_CLI" build-reference --bsc "$OCAML_BSC" tests/tests
cargo test --manifest-path compiler-rust/Cargo.toml -- --test-threads=1
cargo test --manifest-path compiler-rust/Cargo.toml bir:: -- --test-threads=1
cargo test --release --manifest-path compiler-rust/Cargo.toml full_unit_allocation_boundary -- --nocapture --test-threads=1
cargo test --manifest-path rewatch/Cargo.toml
cargo clippy --manifest-path compiler-rust/Cargo.toml --all-targets -- -D warnings
./scripts/test_js_output_parity.sh
./scripts/test_stdlib_output_parity.sh
GENTYPE_PARITY_WITHOUT_TELLA=1 ./scripts/test_gentype_output_parity.sh
GENTYPE_PARITY_WITHOUT_TELLA=1 python3 scripts/test_backend_coverage.py --target debug
```

## Requested completion status

| Step | Status | Evidence |
| --- | --- | --- |
| 1. Pinned assertions | Done | Four independent tests pin equality across both sizes and their numeric constants; debug and release pass. |
| 2. Attribution | Done | Complete owner totals, retained reasons, removed sites and reproducible allocator backtraces above. |
| 3. Shared-file scope | Done | All nine files have named lowering consumers; unchanged default emitter; 453-layout differential. |
| 4. Final validation/report | Done | Fresh tests, parity, coverage and both instruction/wall-time comparisons; default instruction gate passes. |

The PR remains **draft** for review. No approval or merge is implied.

## Review extension: corpus cardinality

Printed-layout deduplication uses `format!("{facts:?}")`; repeated recorded
layouts still receive every comparison. These are layout counts, not a claim
that the corpus contains 453 distinct source declarations.

Command: `CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml lambda::untagged_dispatch::differential -- --nocapture --test-threads=1`

Last line printed by the corpus comparison:

```text
untagged differential: recorded layouts=453; distinct printed layouts=192; plan pairs=68352; source files=850
```

Both differential tests pass; expanding the arm subsets exposed no mismatch.

## Review extension: bounded metadata indexing

Text, literal and instance indexes now use dense AVL link pools, not sorted
vector insertion. Handles remain metadata row numbers. Import costs
O(B log U + log L) for B spelling bytes, U unique strings and L literal rows;
ancestry costs O(B log U + A log I) for A ancestors and I instance rows. Reused
keys copy no pool rows. New entries append one row and rebalance logarithmically,
without hashes or per-entry heap allocations. This supersedes the sorted-index
cost descriptions above. The link pools reserve from the same source counts.

Command: `CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml untagged_dispatch -- --nocapture --test-threads=1`

```text
reverse literal interning: literals=10000; index moves/comparisons<=1469686; limit=2657542
test result: ok. 27 passed; 0 failed; 0 ignored; 0 measured; 2466 filtered out; finished in 9.41s
```

The limit is floor(20 N log2 N). Test-only counters charge key comparisons,
height updates/comparisons and conservative rotation field-move bounds. The
reserved index vectors do not reallocate in this test. It also reimports every
literal to check stable identity and recursively checks AVL heights, balance and
parent links. String-byte comparisons are accounted for by B in the cost, not
as separate index-element comparisons.

Command: `CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml bir:: -- --test-threads=1`

```text
test result: ok. 774 passed; 0 failed; 0 ignored; 0 measured; 1719 filtered out; finished in 90.24s
```

The pinned allocation constants are unchanged. Strict all-target compiler
clippy also passes (`cargo clippy --manifest-path compiler-rust/Cargo.toml --all-targets -- -D warnings`).

## Review extension: owned planner boundary

`select` now takes `&mut Plan`, lending its retained canonical-key encoder and
iterative selector worklist. It constructs no Metadata table. A warmed string
selection, including actual test-stack traversal, allocates nothing. The owned
`plan` entry reserves graph, grouping, clause, fact, metadata and scratch pools
from the layout and arm counts; these are growth estimates, not rejection bounds.

Command: `CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml warmed_string_selection -- --nocapture --test-threads=1`

```text
warmed string select: calls=10000; allocations=0; instances materialized before emission=0
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 2493 filtered out; finished in 0.00s
```

The same test verifies layout-derived test/tree capacities, empty compatibility
cells after planning and selection, and one stable cached instance when an
emitter explicitly requests its test. Cells are `std::cell::OnceCell`, not
synchronized cells or per-node reference counts.

The previous planner did **not** allocate fresh shape identities during plan
construction: it cloned the input instances. Command:

```sh
git show origin/ocaml-to-rust-rewrite:compiler-rust/src/lambda/untagged_dispatch.rs | nl -ba | sed -n '331,358p'
```

Relevant raw lines:

```text
   335                  BlockType::Instance(i) => Some(i.clone()),
   351          match arm(&BlockType::Instance(i.clone())) {
   353                  let check = p.add_test(Test::Instance(i.clone()));
   357                  let check = p.add_test(Test::Instance(i.clone()));
```

The rewritten eager compatibility materializer did more: `ShapeAllocation::fresh`
for an array, or `ClassBlocks::fresh(0)` for a class (two fresh identities inside
that function). Those calls now run only in the compatibility cell's initializer
when `Plan::test` is asked for an owned instance. Planning and constant selection
do not initialize the cells. Inspect the exact identity allocator with:

```sh
sed -n '90,106p' compiler-rust/src/types/variant_runtime.rs
```

Additional adapter disposition: `lambda/arena.rs::LamArena::decide_switch` and
`lambda/mod.rs::Lambda::switch` must lend their local plan mutably to the shared
selector, as does `bir/l/norm.rs::decide_switch_on` (reached from lowering's inline
beta reduction). The arena edit is only the required selector-signature adapter,
not an independent default-path optimization; it has no direct bir/lower caller.

Command: `CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml untagged_dispatch -- --nocapture --test-threads=1`

```text
test result: ok. 28 passed; 0 failed; 0 ignored; 0 measured; 2466 filtered out; finished in 9.50s
```

Command: `CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml bir:: -- --test-threads=1`

```text
test result: ok. 774 passed; 0 failed; 0 ignored; 0 measured; 1720 filtered out; finished in 87.79s
```

## Review extension: cost-note coverage

Each new or rewritten non-test function in the shared planner, its metadata and
BIR lowering now states what it reads, walks, copies or appends. Scalar lookups
are distinguished from iterator consumption, pool relocation, metadata encoding,
normalizer/release visits and arbitrary equality callbacks. In particular,
payload instance ordering retains the reference algorithm's worst-case cubic
candidate scans times ancestry length; missing-arm selection may revisit its
payload plan for each unnamed literal. These are not described as linear walks.

Command: `python3 scripts/check_lowering_cost_docs.py --self-test`

```text
cost scanner self-tests: passed
cost docs: production functions=472; changed/new=188; missing/generic=0
```

The lexical checker compares qualified function bodies with the configured base,
excludes test-only items and trait declarations, preserves literal contents, and
rejects missing notes and the old generic pool-push sentence. It checks coverage,
not the truth of asymptotic bounds: those require reading the implementation.

Command: `python3 scripts/check_lowering_cost_docs.py --base b9fbbda06`

```text
cost docs: production functions=472; changed/new=0; missing/generic=0
```

This last item changes documentation and its checker, not executable Rust bodies.

## Review extension: trunk literal normalization tests

Both reference functions are copied verbatim from the recorded trunk snapshot
under test-only modules; neither production implementation changed in this item.

Command: `CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml trunk_literal_reference -- --nocapture --test-threads=1`

```text
bigint trunk comparison: table=19; generated=1000; owned and scratch agree
hex float trunk comparison: table=15; generated raw bit patterns=10000; all agree
test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 2490 filtered out; finished in 0.02s
```

All requested edge inputs are explicit table entries. Fixed seeds and generators
are in the tests; failures print the input string or raw float bits.

## Review-base merge

Integrated `61a32b487` after the base advanced. Preserve both the global-shadow
naming work and the allocation audit: function headers/indirect parameter runs
now follow the variable table, including cached fragment imports, header copies
and test capacity probes. Retain the cached immutable templates, both sides'
oracle tests, reserved scope columns and the final global-shadow decision.

Command: `CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml bir:: -- --test-threads=1`

```text
test result: ok. 799 passed; 0 failed; 1 ignored; 0 measured; 1749 filtered out; finished in 90.63s
```

The ignored nested-function naming counterexample is inherited unchanged from
the new base's T5 work, not introduced by this branch. All four pinned unit-entry
constants still pass unchanged. No allocation assertion was relaxed.

Command: `CARGO_INCREMENTAL=0 cargo test --manifest-path compiler-rust/Cargo.toml -- --test-threads=1`

```text
test result: ok. 2523 passed; 0 failed; 26 ignored; 0 measured; 0 filtered out; finished in 169.65s
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 19.66s
test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 20.28s
test result: ok. 5 passed; 0 failed; 7 ignored; 0 measured; 0 filtered out; finished in 0.00s
```

Command: `CARGO_INCREMENTAL=0 cargo test --manifest-path rewatch/Cargo.toml`

```text
test result: ok. 210 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 5.96s
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.28s
test result: ok. 8 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 18.75s
```

Command: `python3 scripts/check_lowering_cost_docs.py --self-test`

```text
cost scanner self-tests: passed
cost docs: production functions=500; changed/new=188; missing/generic=0
```

Compiler/rewatch builds and strict compiler clippy pass. The JS, stdlib, GenType
and unchanged coverage commands above also pass on the merged candidate. Older
instruction/wall-time measurements remain tied to their explicitly named head;
they do not measure this new merge or attribute upstream changes to this audit.

## Default-path regression reproduction at a42524ae0e

The CI default-path regressions are authoritative. The earlier local negative
result above does not establish that this PR is free of default-path cost. This
new reproduction uses base `7ba19b2a63916ae28741c1ccb7f3720edc68e81a` (the merge
base with trunk), head `a42524ae0e`, fat LTO and one codegen unit, with the same
base corpus at equal-depth, equal-length `base`/`head` paths. Heavy builds and
measurements run sequentially; no backend environment variable is set.

Build each archived revision, one at a time, with:

```sh
CARGO_INCREMENTAL=0 CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 cargo build --release --locked --manifest-path rewatch/Cargo.toml
```

Both archives use `yarn install --immutable`; their `tests/tests` and
`tests/dependencies` trees are identical. Preserve the resulting executables as
`temp/default-audit/bin/base` and `temp/default-audit/bin/head`.

```sh
env -u RESCRIPT_BACKEND python3 scripts/compare_build_instructions.py \
  --base temp/default-audit/bin/base temp/default-audit/base \
  --head temp/default-audit/bin/head temp/default-audit/head \
  --runs 5 --sequential --threshold 0.02 --work-dir temp/default-audit/initial
```

Raw output (each row is base then head):

```text
run 1: base 4,037,079,330  head 4,038,088,190
run 2: base 4,034,549,049  head 4,037,503,269
run 3: base 4,033,861,338  head 4,037,472,100
run 4: base 4,034,129,439  head 4,037,183,445
run 5: base 4,035,266,750  head 4,037,791,277
| base | 4,033,861,338 | 4,037.1, 4,034.5, 4,033.9, 4,034.1, 4,035.3 | 743 |
| head | 4,037,183,445 | 4,038.1, 4,037.5, 4,037.5, 4,037.2, 4,037.8 | 743 |
| change | +3,322,107 (+0.082%) | | |
```

### Callgrind attribution before changing code

One clean build per binary, one worker, default backend. For each side:

```sh
SIDE=base # then head
EXE="$PWD/temp/default-audit/bin/$SIDE"
CORPUS="$PWD/temp/default-audit/$SIDE"
env -u RESCRIPT_BACKEND RAYON_NUM_THREADS=1 RESCRIPT_RUNTIME="$CORPUS/packages/@rescript/runtime" "$EXE" clean "$CORPUS/tests/tests"
env -u RESCRIPT_BACKEND RAYON_NUM_THREADS=1 RESCRIPT_RUNTIME="$CORPUS/packages/@rescript/runtime" \
  valgrind --tool=callgrind --cache-sim=no --callgrind-out-file="temp/default-audit/callgrind/$SIDE.out" \
  "$EXE" build "$CORPUS/tests/tests"
callgrind_annotate --inclusive=yes --show-percs=no --auto=no --threshold=100 "temp/default-audit/callgrind/$SIDE.out"
```

Raw totals: base `I refs: 4,030,611,688`; head `I refs: 4,033,057,860`.
The callgrind pair differs by **2,446,172**. The separate cachegrind minima
differ by **3,322,107**: the additional **875,935** is an unexplained
measurement/tool/run difference, not assigned to a source change.

Inclusive rows below are deliberately **not additive**: parent entries include
callee entries. LTO inlines several requested functions, so a missing separate
frame is not reported as zero work. The adjacent disjoint ledger uses exclusive
instructions and reconciles the callgrind difference exactly.

| Inclusive entry | Base | Head | Delta / limitation |
| --- | ---: | ---: | --- |
| `Sw::untagged_plan` (emitter entry, including plan) | 2,621,287 | 3,503,821 | +882,534 |
| `LamArena::decide_switch` (constant entry, including plan/select) | 1,311,537 | 2,050,343 | +738,806 |
| `untagged_plan_with` / `plan` | inlined into callers | 3,571,230 | Not separately comparable |
| `reserve_layout` | absent | 1,300,438 | Added; 403 calls |
| `reserve_literals`, `reserve_kinds` | absent | inlined into plan entry | Not separately recoverable |
| `FactPool::import` | absent | 425,073 | Includes metadata imports |
| `FactPool::reserve` | absent | 76,897 | Added |
| `Metadata::import_literal` | absent | 340,273 | Includes interning/key encoding |
| `Metadata::import_kind` | absent | 134,122 | Includes name interning |
| `Metadata::intern` | absent | 216,850 | Includes AVL insertion |
| AVL insert and rotate entries | absent | 142,157 | Nested entries, not additive |
| Payload graph construction | 1,101,081 | 395,859 | -705,222 |
| Simplification entries | 476,705 | 207,509 | -269,196 |
| `select` / `select_tree` emitted entries | 547,418 | inlined into callers | Not separately comparable |
| `lam_compile_variant` emitted symbols | 440 | inlined into compile_expr | Not separately comparable |
| `Plan::test` | inlined | 27,646 | Includes lazy materialization |
| Instance cell initialization | absent | 14,347 | Included in Plan::test |
| Float parsing | 73,698 | 71,593 | -2,105 |
| Hex/number key | 531,453 | 225,119 | -306,334; hex formatting is inlined |
| Bigint parser entries | 98,047 | 80,471 | -17,576 |
| Literal value key entry | 1,223,664 | 971,331 | -252,333 |
| String escape decoder outer entry | 10,001,689 | 10,272,252 | +270,563 |
| String escape encoder outer entry | 1,484,536 | 1,514,214 | +29,678 |
| Semantic normalization | 400,260 | 400,260 | 0 |
| Identifier conversion | 14,095,804 | 13,803,746 | -292,058 |
| Identifier append helper | inlined | 620,140 | Nested in conversion; not an added total |
| Primitive purity entry | 1,231,982 | 1,231,387 | -595 |
| `mi_malloc_aligned` | 212,424,129 | 212,452,916 | +28,787 |
| `mi_realloc_aligned` | 117,147,876 | 117,226,743 | +78,867 |
| `mi_free` | 89,188,343 | 89,439,647 | +251,304 |
| memcpy entries | 192,571,086 | 192,796,784 | +225,698 |
| memset entries | 16,362,356 | 16,368,297 | +5,941 |

The planner reserve entry accounts for a substantial directly measured cost;
the metadata and encoder rows show additional work, not a license to attribute
all allocator changes to those callers.

| Disjoint exclusive bucket | Base | Head | Delta |
| --- | ---: | ---: | ---: |
| Planner symbols, including monomorphized helper names | 1,074,694 | 1,981,382 | +906,688 |
| Rust allocation plumbing | 70,076,535 | 70,794,022 | +717,487 |
| Allocator internals | 350,247,213 | 350,645,794 | +398,581 |
| compile_expr symbols (including inlined work) | 10,436,996 | 10,802,996 | +366,000 |
| string_literal symbols | 11,014,336 | 11,307,279 | +292,943 |
| Memory operations | 208,933,552 | 209,165,191 | +231,639 |
| Literal keys | 122,600 | 178,232 | +55,632 |
| Primitive purity | 99,924 | 99,567 | -357 |
| Float/hex helpers | 37,890 | 35,602 | -2,288 |
| Bigint parser | 49,147 | 46,164 | -2,983 |
| Identifier conversion helpers | 9,803,872 | 9,117,594 | -686,278 |
| Other/unexplained exclusive instructions | 3,368,714,929 | 3,368,884,037 | +169,108 |
| **Total** | **4,030,611,688** | **4,033,057,860** | **+2,446,172** |

Each function's own cost is its non-call cost lines in the callgrind file; a
`calls=` line marks the next cost line as an inclusive call edge, excluded from
this ledger. Group precedence is planner, strings, floats, bigint, literal keys,
printer conversion, purity, allocator, memory operations, Rust allocation
plumbing, compile_expr, then residual. Summing own costs reproduces each summary.
The unexplained residual within this pair is below the requested tolerance;
it is not concealed by summing overlapping inclusive entries.
