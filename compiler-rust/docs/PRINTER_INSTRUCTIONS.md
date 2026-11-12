# Three-way printer instruction measurement

## Historical experiment

The `oxc-bir` mode measured here was an experiment and is **not on trunk**.
Its code is preserved at commit
`8242898f092fd015ca958fc0558847d8dfb4e61d` on branch
`s3-1b-oxc-bir-emitter`. [THREE_TREES.md section 9](THREE_TREES.md#9-the-saving)
uses these figures as evidence for dropping JS-level Bir emission as a product
path. This document and its summary script retain the evidence, not that mode.

## Status

The experimental direct Bir emitter and dense naming implementation were built
and parity checked. Measurements below cover `tests/tests` and the 3,735-module
application. Even excluding import, the experiment did **not** meet the
default-switch cost gate.

## Measurement setup

Measured compiler commit: `aabaaf46e580d134b9df4fed04f0e12d51aaad42`.
Binary SHA-256: `82ee4d462cfe8b7ebf0ca956dde621eff30e5d8c690329322ca9ed3667966f31`.
Linux x86-64, Rust `1.102.0-nightly (ac8310ba6 2026-11-09)`, Valgrind 3.22.0.
One release binary, fat LTO, line tables, one Rayon worker, full clean builds;
runtime preparation outside each sample. No backend or printer stats enabled.
The public corpus has one successful sample per profiler/mode; the application
has one Cachegrind sample per mode. The additional public-corpus self breakdown
is identified separately below. Native timing, for `tests/tests` only, uses one
warmup and five measured runs per mode. Profiler wall time is not native build
time. Subsequent trunk integration and documentation commits are not silently
substituted for this pinned compiler revision; no emitter optimization followed
the measurement.

## tests/tests

### Cachegrind: whole-build instructions

| Mode | Instructions | Change from legacy |
| --- | ---: | ---: |
| legacy | 4,357,226,252 | +0.00% |
| oxc | 4,422,808,687 | +1.51% |
| oxc-bir | 4,803,130,120 | +10.23% |

### Named self attribution (millions of instructions)

These buckets partition the whole build, not just rendering. Shared costs are
not assigned exclusively to a phase. The Bir-support bucket includes helpers
and destruction, not only import. Inlined construction may appear under the
emitter caller rather than the construction bucket.

| Bucket | Legacy | JS-IR oxc | Bir oxc |
| --- | ---: | ---: | ---: |
| AST construction / oxc arena | 0.141 | 2.335 | 2.201 |
| Bir support / import (named self) | 0.410 | 0.401 | 315.625 |
| Legacy printer | 80.892 | 11.261 | 10.604 |
| Naming | 0.000 | 67.694 | 56.305 |
| Other compiler/runtime | 3144.335 | 3149.517 | 3145.813 |
| Other emitter | 0.028 | 11.395 | 64.987 |
| Oxc codegen | 0.000 | 22.644 | 22.610 |
| Oxc parser | 4.853 | 4.604 | 4.604 |
| Shared allocation / containers | 1106.641 | 1132.586 | 1159.962 |
| Stats and environment | 1.192 | 1.623 | 1.623 |
| Unresolved | 18.735 | 18.748 | 18.795 |

### Callgrind: inclusive phase costs (instructions)

| Boundary | Legacy | JS-IR oxc | Bir oxc |
| --- | ---: | ---: | ---: |
| Whole build | 4,351,289,943 | 4,418,094,310 | 4,798,013,247 |
| Rendering, including import | 112,139,184 | 176,819,283 | 557,550,534 |
| Import (child of rendering) | 0 | 0 | 297,786,544 |
| Rendering minus import | 112,139,184 | 176,819,283 | 259,763,990 |

Incoming call-edge costs avoid double-counting same-function inline file splits.
The import row is already included in rendering; do not add these rows together.
Rendering minus import still includes destruction of the imported tree and any
fallback rendering. It is 131.64% above legacy and 46.91% above JS-IR oxc here.
Dense naming removes the identifier lookup path but does not make this emitter
cheaper overall. This measurement is not evidence for switching the default.

Callgrind and Cachegrind totals are reported separately: they are distinct runs
and differ slightly. No inclusive cost is subtracted from another run's total.

### What the two large emitter buckets contain

Top 12 functions by aggregated self cost in each of the **existing** buckets.
The original temporary profile was lost on sandbox restart, so this breakdown
uses a fresh `tests/tests` oxc-bir Cachegrind sample of the **identical binary**:
4,802,771,357 total instructions, Naming 56,305,015 and Other emitter 64,986,978.
It is not substituted into the earlier three-way comparison. Function names
below omit crate prefixes and expand neither long generic bounds nor closures.

The bucket classifier matches symbol substrings, including generic arguments:
**Naming is not a pure naming-phase total**. In particular, `Build<..., Names>`
functions land there despite constructing AST nodes. The table makes that
limitation explicit rather than relabeling these instructions as name choice.
“Inherent” here describes work required by name/output semantics, not a claim
that this implementation or its instruction count is optimal. Self attribution
cannot split an inlined mixed function into exact semantic costs.

| Bucket | Function (abbreviated) | Self instructions | Source of work |
| --- | --- | ---: | --- |
| Naming | `Names::collect` | 21,822,993 | Mixed: derive free/order facts in a separate tree pass, then choose scope names. |
| Naming | `Build<Bir, Names>::expr_at` | 7,698,552 | Emission: expression AST construction; caught by the generic Names argument. |
| Naming | `Names::assign` | 5,120,397 | Name choice: collision checks and suffix assignment. |
| Naming | `Build<Bir, Names>::stmt` | 2,819,341 | Emission: statement construction; caught by the generic Names argument. |
| Naming | `Names::base` | 1,772,561 | Name choice: spelling conversion/cache. |
| Naming | `Names::add` | 1,739,204 | Name choice: visible-slot lookup and printed-slot assignment. |
| Naming | `Plan::default` | 1,536,402 | Separate pass: initialize per-function analysis/schedule storage. |
| Naming | `Build<Bir, Names>::args` | 1,489,654 | Emission: construct arguments; caught by the generic Names argument. |
| Naming | `RawTable<(Name, Group)>::reserve_rehash` | 1,401,046 | Name-choice bookkeeping: grow scope/base groups; current map representation. |
| Naming | `Names::block_tasks` | 1,330,725 | Separate pass: schedule statements in print order. |
| Naming | `Build<Bir, Names>::caml_block` | 1,223,019 | Emission: runtime-block AST construction; generic Names argument. |
| Naming | `Build<Bir, Names>::id` | 931,281 | Emission: AST identifier construction, not scope name choice. |
| Naming | Remaining functions | 7,419,840 | Not part of the top 12. |
| Other emitter | `EmitterView::ek` | 23,344,236 | Adapter: decode a J expression into the shared JS-shaped view. |
| Other emitter | `emit::emit_bir` | 8,991,319 | Mixed: entry/setup and inlined view validation/assembly; not separable by symbol. |
| Other emitter | `EmitterView::expr_comment` | 4,184,261 | Adapter: read expression comment metadata. |
| Other emitter | `EmitterView::exprs` | 3,441,238 | Adapter: materialize converted expression-handle slices. |
| Other emitter | `walk::expression_comment<Bir>` | 3,417,700 | Emission support check; repeated during naming and construction. |
| Other emitter | `EmitterView::sk` | 3,370,464 | Adapter: decode a J statement into the shared view. |
| Other emitter | `EmitterView::name_key` | 3,075,729 | Adapter: convert a source handle to its dense name slot. |
| Other emitter | `EmitterView::fun` | 2,758,947 | Adapter: decode function metadata into the shared view. |
| Other emitter | `Vec<Stmt>::from_iter<Map<NodeId, emit_view::stmt>>` | 2,005,060 | Adapter: materialize converted statement-handle slices. |
| Other emitter | `walk::member_form` | 1,937,137 | Emission: choose computed/static property syntax. |
| Other emitter | `EmitterView::number` | 1,292,687 | Adapter: decode/copy numeric payload. |
| Other emitter | `EmitterView::var` | 1,127,296 | Adapter: decode declaration metadata into the shared view. |
| Other emitter | Remaining functions | 6,040,904 | Not part of the top 12. |

The 297,786,544-instruction inclusive import (about 298 M) is the conversion
from an already-built JsArena: traversal, identity association, allocation and
population of another tree, and bridge finalization. Lowering directly into
J-level Bir would not pay **that duplicate conversion**; it would still pay to
construct and maintain its one Bir tree, choose names, and emit JavaScript.
Subtracting 298 M is not a forecast that all construction or adapter costs vanish.

### Native clean-build timing (seconds)

| Mode | Mean | Standard deviation | Minimum | Maximum |
| --- | ---: | ---: | ---: | ---: |
| legacy | 0.6392 | 0.0535 | 0.5993 | 0.7288 |
| oxc | 0.6215 | 0.0558 | 0.5729 | 0.7095 |
| oxc-bir | 0.6385 | 0.0369 | 0.6029 | 0.6995 |

The timing distributions overlap; they do not establish a wall-time improvement.

## Application

One successful clean Cachegrind build per mode, using the same binary as the
public-corpus table. All three compiled the 3,735-module application. Its
byte-equality gate passes for all 3,980 generated files with zero import fallback.
No interrupted profile contributes to these totals.

| Mode | Instructions | Change from legacy |
| --- | ---: | ---: |
| legacy | 74,435,580,110 | +0.00% |
| oxc | 76,277,299,207 | +2.47% |
| oxc-bir | 82,975,332,012 | +11.47% |

### Named self attribution (millions of instructions)

These use the same substring buckets and limitations as the public corpus,
including generic `Names` arguments in the Naming bucket. They are not inclusive
phase costs; the unresolved work remains explicit.

| Bucket | Legacy | JS-IR oxc | Bir oxc |
| --- | ---: | ---: | ---: |
| AST construction / oxc arena | 0.171 | 36.828 | 35.995 |
| Bir support / import (named self) | 10.377 | 10.301 | 6092.259 |
| Legacy printer | 1894.923 | 330.312 | 285.020 |
| Naming | 0.000 | 1377.014 | 1126.670 |
| Other compiler/runtime | 53554.245 | 53729.116 | 53650.651 |
| Other emitter | 0.143 | 275.128 | 1373.300 |
| Oxc codegen | 0.000 | 401.196 | 401.027 |
| Oxc parser | 7.412 | 7.333 | 7.333 |
| Shared allocation / containers | 18846.373 | 19429.723 | 19878.306 |
| Stats and environment | 5.739 | 7.960 | 7.960 |
| Unresolved | 116.197 | 672.388 | 116.813 |

No inclusive application import measurement or repeated native timing is claimed.
The separate import/rendering measurement above is from `tests/tests`; subtracting
this application's Bir-support self bucket would not measure its emission-only
cost. The successful three-way instruction samples complete the requested
application comparison. The negative result is retained, not optimized away in
this change.

## Reproduce

The `oxc-bir` sample requires the experimental code at commit
`8242898f092fd015ca958fc0558847d8dfb4e61d` of branch
`s3-1b-oxc-bir-emitter`; current trunk does not implement that mode. Use that
revision in a separate checkout. The original samples remain pinned to the
compiler commit and binary hash recorded above, before subsequent trunk
integration; rebuilding the later preserved experiment is not a claim to
reproduce the exact original counts.

Build one release binary for all modes, with line tables for attribution:

```sh
CARGO_PROFILE_RELEASE_DEBUG=1 cargo build --release --manifest-path rewatch/Cargo.toml
```

Set `BIN` to that executable, `PROJECT` to the project, `RESCRIPT_RUNTIME` to a
prepared runtime package, and `OUT` to a local output directory. Build the
runtime before measurement. Run from the project directory with `build .`;
prepare and clean each project identically. Keep all raw profiles local.

```sh
export RAYON_NUM_THREADS=1 RESCRIPT_FULL_BUILD=1
unset RESCRIPT_JS_PRINTER_STATS RESCRIPT_BACKEND RESCRIPT_BACKEND_STATS
unset RESCRIPT_JS_PRINTER_SOURCE_MAPS
export RESCRIPT_JS_PRINTER=legacy
"$BIN" build "$RESCRIPT_RUNTIME"
cd "$PROJECT"
for mode in legacy oxc oxc-bir; do
  "$BIN" clean .
  RESCRIPT_JS_PRINTER="$mode" valgrind --tool=cachegrind \
    --cache-sim=no --branch-sim=no \
    --cachegrind-out-file="$OUT/$mode.cg" "$BIN" build .
done
```

Require a successful full build for every sample. All CLI startup, runtime
bootstrap and filesystem work that still runs inside that process is included.
Run the repository's summary tool on the three profiles:

```sh
python3 scripts/printer_instruction_summary.py legacy.cg oxc.cg oxc-bir.cg
```

Its buckets are **named self instructions**, not inclusive phase costs. Inlining
can move work into a caller's bucket. Shared allocation/container work must not
be charged exclusively to import or emission. In particular, subtracting only
the named import bucket does not establish the cost of direct emission alone.

For that separation, additionally record Callgrind profiles of the same clean
builds and binary. Inspect inclusive `driver::render_js_program` and
`bir::bridge_j::import_js` costs; import is a child of rendering, so these must
not be added together. The difference is rendering without import, including
fallback rendering. The separate `emit::emit_bir` and `emit::program::emit`
boundaries can cross-check the two oxc paths. Confirm the boundaries remain
present in the measured binary and do not substitute a self count if they are
inlined away.

```sh
for mode in legacy oxc oxc-bir; do
  "$BIN" clean .
  RESCRIPT_JS_PRINTER="$mode" valgrind --tool=callgrind \
    --cache-sim=no --branch-sim=no \
    --callgrind-out-file="$OUT/$mode.callgrind" "$BIN" build .
done
callgrind_annotate --inclusive=yes --threshold=100 --auto=no \
  --show=Ir --show-percs=no oxc-bir.callgrind
```

Report Callgrind's own totals with its inclusive costs, rather than silently
mixing counts from two profiler runs. The application has no printer fallback;
public-corpus fallbacks must remain visible in the interpretation.

For native timing, clean in hyperfine's prepare step and repeat all three modes
with the same environment and binary. Use at least one warmup and five measured
runs per mode; report all four summary statistics. Run builds and profilers
sequentially so they do not compete with each other.

Only aggregate counts and timings belong in the report. Do not commit profiles,
application paths, source names, generated code or dependency details.
