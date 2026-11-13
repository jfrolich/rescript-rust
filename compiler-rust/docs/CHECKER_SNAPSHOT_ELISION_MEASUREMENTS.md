# Snapshot-elision candidate measurements

These measurements compare `5cda5eb4b` with its then-current trunk base,
`474bbcf02`. They are **not** measurements of later merges or the final retry
composition. Both binaries were built from separate source archives on the same
Linux machine, sequentially, with release fat LTO and one codegen unit. Compiler
counters were disabled for timing and instruction measurements.

## Whole-project output

`scripts/compare_checker_builds.py` ran each executable against the same project,
with its matching runtime and `RAYON_NUM_THREADS=1`. Both sides exited zero.

| Project | Signatures | Diagnostic files | Generated files | Differences |
| --- | ---: | ---: | ---: | ---: |
| `tests/tests` | 743 | 1 | 737 | 0 |
| 3,735-module application | 3,735 | 18 | 3,980 | 0 |

The comparison covers canonical signatures, diagnostic text/order/locations,
JavaScript, generated TypeScript and source maps. The application produced 32
diagnostics in those 18 files on each side.

## Application instructions

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

## Application wall time

Hyperfine used one warmup and five measured runs per executable, cleaning before
each run. Builds used `RESCRIPT_FULL_BUILD=1` and `RAYON_NUM_THREADS=1`.

| Revision | Mean | Standard deviation | Minimum | Maximum |
| --- | ---: | ---: | ---: | ---: |
| Base | 9.431 s | 0.263 s | 9.102 s | 9.788 s |
| Candidate | 9.219 s | 0.112 s | 9.097 s | 9.362 s |

The means improve by approximately 2.2%, but the ranges overlap. These are
single-worker Linux measurements, not a multicore throughput claim.

## Failed-unit cost

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
