# Snapshot-elision final implementation measurements

Candidate `913faa5ed` (including composed retries and the location-retry fix)
versus base `be1b3a482`, on the same Linux machine. Both used release fat LTO
and one codegen unit. Later documentation-only commits do not change these
binaries. The earlier measurements below remain revision-pinned history.

## Commands

`ROOT` is the candidate checkout, `BASE_ROOT` the base source archive, and
`APP` the directory of the 3,735-module application. No project path was passed
to `build`: each measured command ran from the project's own directory.

```sh
CARGO_PROFILE_RELEASE_LTO=fat CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 \
  cargo build --locked --release --manifest-path "$ROOT/rewatch/Cargo.toml"
CARGO_PROFILE_RELEASE_LTO=fat CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 \
  cargo build --locked --release --manifest-path "$BASE_ROOT/rewatch/Cargo.toml"
BASE="$BASE_ROOT/rewatch/target/release/rescript"
CANDIDATE="$ROOT/rewatch/target/release/rescript"
```

For each side, set `BIN` to its executable and `RUNTIME` to its matching
`packages/@rescript/runtime`. For each project (`$APP` and `$ROOT/tests/tests`),
run the following five times. Counters were disabled for these measurements.

```sh
cd "$PROJECT"
export RAYON_NUM_THREADS=1 RESCRIPT_FULL_BUILD=1 RESCRIPT_RUNTIME="$RUNTIME"
unset RESCRIPT_COMPILER_COUNTERS RESCRIPT_CHECK_MODE
"$BIN" clean
valgrind --tool=cachegrind --cache-sim=no --branch-sim=no \
  --cachegrind-out-file="$RESULT.cachegrind" "$BIN" build
```

## Instructions

All runs completed successfully. The summary compares the minimum of five.

### 3,735-module application

| Run | Base instructions | Candidate instructions |
| --- | ---: | ---: |
| 1 | 67,833,108,969 | 67,443,864,344 |
| 2 | 67,807,158,079 | 67,303,921,893 |
| 3 | 67,805,456,282 | 67,319,613,657 |
| 4 | 67,821,062,623 | 67,321,608,494 |
| 5 | 67,810,454,456 | 67,334,303,567 |
| Minimum | 67,805,456,282 | 67,303,921,893 |

Change: **-0.740%**.

### tests/tests

| Run | Base instructions | Candidate instructions |
| --- | ---: | ---: |
| 1 | 4,992,695,709 | 4,873,336,315 |
| 2 | 4,904,256,652 | 4,873,182,639 |
| 3 | 4,906,026,731 | 4,873,487,909 |
| 4 | 4,903,493,317 | 4,875,406,139 |
| 5 | 4,902,048,912 | 4,871,669,914 |
| Minimum | 4,902,048,912 | 4,871,669,914 |

Change: **-0.620%**.

## Attempts and the default build

These are separate counter-enabled runs of the candidate, not the instruction
runs. Counts include dependency/runtime units and location retries, not just
project modules.

```sh
cd "$PROJECT" # once for "$ROOT/tests/tests", once for "$APP"
export RAYON_NUM_THREADS=1 RESCRIPT_FULL_BUILD=1
export RESCRIPT_RUNTIME="$ROOT/packages/@rescript/runtime"
"$CANDIDATE" clean
RESCRIPT_COMPILER_COUNTERS=1 "$CANDIDATE" build
```

| Project | check_attempts | explain_reruns | Exit |
| --- | ---: | ---: | ---: |
| tests/tests | 944 | 0 | 0 |
| 3,735-module application | 4,005 | 0 | 0 |

The ordinary default build also succeeded, reporting **743 modules**:

```sh
cd "$ROOT/tests/tests"
unset RAYON_NUM_THREADS RESCRIPT_FULL_BUILD RESCRIPT_COMPILER_COUNTERS RESCRIPT_CHECK_MODE
export RESCRIPT_RUNTIME="$ROOT/packages/@rescript/runtime"
"$CANDIDATE" clean
"$CANDIDATE" build
```

## Output comparison

```sh
cd "$ROOT"
RAYON_NUM_THREADS=1 python3 scripts/compare_checker_builds.py "$PROJECT" \
  "$BASE" "$CANDIDATE" \
  --base-runtime "$BASE_ROOT/packages/@rescript/runtime" \
  --candidate-runtime "$ROOT/packages/@rescript/runtime"
```

| Project | Signatures | Diagnostic files | Generated files | Differences |
| --- | ---: | ---: | ---: | ---: |
| tests/tests | 743 | 1 | 737 | 0 |
| 3,735-module application | 3,735 | 18 | 3,980 | 0 |

Both sides exited zero. The application emitted 32 diagnostics in 18 files.
The comparison includes canonical signatures, diagnostic text/order/locations,
JavaScript, generated TypeScript and source maps.

## Application wall time

From `$APP`, a wrapper `run-side.sh SIDE ACTION` selects the matching executable
and runtime and runs `ACTION`, exporting `RAYON_NUM_THREADS=1` and
`RESCRIPT_FULL_BUILD=1`, with counters and forced Explain unset:

```sh
cd "$APP"
hyperfine --warmup 1 --runs 5 --export-json application-wall.json \
  --prepare './run-side.sh {side} clean' -L side base,candidate \
  './run-side.sh {side} build'
```

| Revision | Mean | Standard deviation | Minimum | Maximum |
| --- | ---: | ---: | ---: | ---: |
| Base | 12.999 s | 0.840 s | 11.869 s | 14.103 s |
| Candidate | 13.094 s | 0.511 s | 12.239 s | 13.465 s |

The candidate mean is 0.73% slower, with overlapping ranges. This does **not**
establish a wall-time improvement; the instruction reduction is the supported
performance result. The failed-unit harness below was not rerun on this final
revision and must not be presented as final-head evidence.

---

## Snapshot-elision candidate measurements

These measurements compare `5cda5eb4b` with its then-current trunk base,
`474bbcf02`. They are **not** measurements of later merges or the final retry
composition. Both binaries were built from separate source archives on the same
Linux machine, sequentially, with release fat LTO and one codegen unit. Compiler
counters were disabled for timing and instruction measurements.

### Whole-project output

`scripts/compare_checker_builds.py` ran each executable against the same project,
with its matching runtime and `RAYON_NUM_THREADS=1`. Both sides exited zero.

| Project | Signatures | Diagnostic files | Generated files | Differences |
| --- | ---: | ---: | ---: | ---: |
| `tests/tests` | 743 | 1 | 737 | 0 |
| 3,735-module application | 3,735 | 18 | 3,980 | 0 |

The comparison covers canonical signatures, diagnostic text/order/locations,
JavaScript, generated TypeScript and source maps. The application produced 32
diagnostics in those 18 files on each side.

### Application instructions

Each run cleaned the application first, then ran a full build with one worker
under `valgrind --tool=cachegrind --cache-sim=no --branch-sim=no`. All listed runs
completed successfully; an interrupted run was discarded and repeated.

| Run | Base instructions | Candidate instructions |
| --- | ---: | ---: |
| 1 | 68,240,440,928 | 67,760,753,720 |
| 2 | 68,205,590,288 | 67,771,598,455 |
| 3 | 68,225,300,722 | 67,765,970,074 |
| 4 | 68,218,964,790 | 67,749,509,684 |
| 5 | 68,235,152,394 | 67,788,174,610 |
| Minimum | 68,205,590,288 | 67,749,509,684 |

The minimum-of-five instruction reduction is **0.669%**.

### Application wall time

Hyperfine used one warmup and five measured runs per executable, cleaning before
each run. Builds used `RESCRIPT_FULL_BUILD=1` and `RAYON_NUM_THREADS=1`.

| Revision | Mean | Standard deviation | Minimum | Maximum |
| --- | ---: | ---: | ---: | ---: |
| Base | 9.431 s | 0.263 s | 9.102 s | 9.788 s |
| Candidate | 9.219 s | 0.112 s | 9.097 s | 9.362 s |

The means improve by approximately 2.2%, but the ranges overlap. These are
single-worker Linux measurements, not a multicore throughput claim.

### Failed-unit cost

A separate release harness called `driver::compile_source_to_js_with_options`
directly with `nopervasives: true`, avoiding CLI dependency preparation. Its
source contains 1,000 exported identity functions, followed by one final
binding. The passing source ends with `let result: int = f999(1)`; the failing
source differs only in using `bool` as that annotation. Both include parsing
and checking; only the passing case reaches JavaScript generation.

Each row is the minimum of five completed cachegrind runs of the same harness.

| Case | Instructions |
| --- | ---: |
| Passing unit, Success | 449,614,867 |
| Failing unit, Success then Explain | 142,064,815 |
| Same failing unit, forced Explain | 88,968,976 |

The failed unit with retry costs **1.597×** forced Explain on the same failure,
below the 2.2× bound. Its cost is **0.316×** the passing full compilation; that
ratio is lower because the failure skips the backend, so it is not an estimate
of the type checker's retry overhead alone. This synthetic late-type-error case
does not establish a worst-case bound for all unit shapes or later validation
failures.

## Ten-thousand-item late failure (R8a review correction)

Measured checker implementation `ef00cdb84` with the checked-in
`compiler-rust/examples/check_retry_cost.rs` harness (the same direct driver
entry point and 64 MiB stack as the earlier harness). The passing twin contains
10,000 `let xN = N` items. The failing twin appends `let bad: bool = 1`.

```sh
python3 - <<'PYTHON'
from pathlib import Path
source = ''.join(f'let x{n} = {n}\n' for n in range(10_000))
Path('/tmp/pass.res').write_text(source)
Path('/tmp/fail.res').write_text(source + 'let bad: bool = 1\n')
PYTHON
CARGO_PROFILE_RELEASE_LTO=fat CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 \
  cargo build --locked --release --manifest-path compiler-rust/Cargo.toml \
  --example check_retry_cost
for case in pass fail; do
  for n in 1 2 3 4 5; do
    env -u RESCRIPT_CHECK_MODE -u RESCRIPT_COMPILER_COUNTERS \
      valgrind --tool=cachegrind --cache-sim=no --branch-sim=no \
      --cachegrind-out-file="/tmp/$case-$n.cachegrind" \
      compiler-rust/target/release/examples/check_retry_cost \
      "/tmp/$case.res" "$case"
  done
done
```

Raw cachegrind output (`I refs`, process-ID prefixes omitted), in run order:

```text
pass:
I refs: 15,354,558,787
I refs: 15,354,638,358
I refs: 15,354,745,557
I refs: 15,355,725,291
I refs: 15,355,296,076
fail:
I refs: 554,579,658
I refs: 553,799,753
I refs: 554,248,774
I refs: 554,385,788
I refs: 553,589,777
```

Minimum-of-five: passing **15,354,558,787**, failing **553,589,777** instructions.
Fail/pass = **0.036054×**, below 2.2×. This is the requested full-compilation
comparison, not isolated type-checker overhead: only the passing twin runs the
backend. It does not establish a bound for other unit shapes.
