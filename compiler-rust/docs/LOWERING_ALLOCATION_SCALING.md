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

## Final validation and measurements

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
