# Checker R2 measurements

## Application measurements
Linux, matched fat-LTO release builds with line tables, one worker, commands run from the application's own directory. Baseline `be1b3a482e5a989d1a1bbecf33a9b4f1aab98fec`; candidate sources `0f1fa2def`. The 3,735-module application reports 3,692 compiled source modules in each clean measured build.

For each side: `env -u RESCRIPT_CHECKER RESCRIPT_RUNTIME="$RUNTIME" RAYON_NUM_THREADS=1 "$EXE" clean .`, then the same environment with `valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file="$OUT" "$EXE" build .`.

| Default-path instructions | Baseline | Candidate |
|---|---:|---:|
| Run 1 | 65,644,334,213 | 65,025,584,964 |
| Run 2 | 65,178,654,974 | 65,045,217,576 |
| Run 3 | 65,197,200,337 | 65,043,446,481 |
| Minimum | 65,178,654,974 | 65,025,584,964 |

**Instruction delta: −0.234847%, within the reviewer-specific +0.02% limit.** This is not a wall-clock speedup claim. Hyperfine (5 runs, one warmup, clean before each build): baseline **8.876 ± 0.169 s**, range **8.727–9.090 s**; candidate **9.927 ± 0.191 s**, range **9.712–10.132 s**, about **11.8% slower**. These timings need separate scrutiny despite the instruction gate passing.

Baseline inclusive `driver::publish_signature` cost: **906,128,693 instructions**, **1.390223%** of the minimum baseline build. Measured by `valgrind --tool=callgrind --collect-atstart=no '--toggle-collect=*driver*publish_signature' ... "$BASE" build .`, after cleaning, checker unset, one worker. The prompt's 1.34% reference budget corresponds to **873,393,977 instructions** on this baseline. Application inclusive `from_old::run` cost was **not measured**; the bounded same-corpus evidence below replaces that attempted measurement.


The application profile was terminated by a ten-minute command timeout and is
excluded. The scoped tests/tests profile below is complete.

## Alternating remeasurement and default-path audit

The original block timing did **not** reproduce. Ten clean measurements per
binary, paired with alternating order (base/head, then head/base), gave:

| Binary | Mean ± standard deviation | Min–max |
|---|---:|---:|
| base | 9.139722 ± 0.328504 s | 8.883928–9.966903 s |
| head | 8.970495 ± 0.195269 s | 8.726265–9.375048 s |

Mean delta: -1.851551%. No >2% regression reproduced.

Hyperfine does not alternate its two command blocks. A paired wrapper alternated
order and timed each child build separately, excluding its clean command. The
wrapper used the same environment and `EXE clean .` preparation for each child.
Ten pairs ran as five sequential, bounded invocations of:

```sh
hyperfine --runs 2 --prepare 'python3 /tmp/r2-alternate-pair.py prepare' \
  'python3 /tmp/r2-alternate-pair.py run'
```

This is ten pairs, **not** a claimed single `hyperfine --runs 10` invocation.
The wrapper's individual monotonic wall measurements, not Hyperfine's combined
pair time (which includes the between-build clean), give the table above.

| Pair | Order | Baseline seconds | Candidate seconds |
|---|---|---:|---:|
| 1 | base / head | 9.309543 | 8.761501 |
| 2 | head / base | 8.998268 | 8.808314 |
| 3 | base / head | 9.024965 | 9.028267 |
| 4 | head / base | 9.132780 | 9.048001 |
| 5 | base / head | 8.883928 | 8.848360 |
| 6 | head / base | 8.919549 | 9.087666 |
| 7 | base / head | 9.966903 | 9.375048 |
| 8 | head / base | 9.291960 | 9.076503 |
| 9 | base / head | 8.891321 | 8.726265 |
| 10 | head / base | 8.978001 | 8.945025 |

Once per side, after its clean, `/usr/bin/time -v env -u RESCRIPT_CHECKER
RESCRIPT_RUNTIME="$RUNTIME" RAYON_NUM_THREADS=1 "$EXE" build .` reported:

| Metric | Baseline | Candidate |
|---|---:|---:|
| User seconds | 8.61 | 8.44 |
| System seconds | 0.82 | 0.46 |
| Wall seconds | 8.98 | 8.55 |
| Maximum RSS, KiB | 799900 | 803004 |
| Major page faults | 0 | 0 |
| Minor page faults | 27041 | 28833 |

`perf stat -e page-faults,task-clock true` was refused by the host's
`perf_event_paranoid=4`; no perf result is claimed.

Reviewer-reported arm64 measurements of the same source candidate against the
same baseline: output identical (3980 files), determinism zero differences;
one worker 66.93→66.65 G instructions (n=6); ten workers 66.73→66.62 G,
median wall 1.170→1.170 s (n=10), peak memory 1038→1033 MB; cycles
32.31→32.35 G (n=4). These are reviewer measurements, not locally rerun results.

### Every changed hunk outside tc

```sh
git diff --stat origin/ocaml-to-rust-rewrite...HEAD -- \
  compiler-rust/src rewatch/src ':!compiler-rust/src/tc'
```

Four files, 204 insertions / 22 deletions; no rewatch hunk:

| Hunk | Default-path work per unit |
|---|---|
| portable_types.rs: with_published_graph, test-only with_shared_graph, import_checker_publication | New explicit bridge helpers; not called in Old mode; no added default allocation/lock/table |
| driver.rs: publish_signature | Existing extraction / optional signature check, plus one checker-mode comparison per publication; no conversion |
| type_expr.rs: from_name, new_persistent_batch | Inverse-only helpers; no default-path calls |
| world.rs: UnitSlot fields / construction | Two inline empty OnceLocks, 32+16 bytes; slot grows 40→88 bytes excluding Arc header. Initializing 48 additional bytes per registered unit; no converted graph allocated and no new up-front table proportional to unit count |
| world.rs: unit_slot factoring / unit | Existing one map probe, lock, registration and Arc clone; no extra lookup on ordinary import |
| world.rs: conversion methods / tests | Explicit request only; test counters absent from production |

OnceLock sizes were checked with `std::mem::size_of` on this x86_64 toolchain.
No performance code change is justified by the non-reproducing block timing.
The scoped inclusive converter profile is recorded below.

## Bounded inclusive converter measurement (tests/tests)

The **application converter instruction figure was not measured**: its
Callgrind run exceeded the command limit. Its partial count is discarded.
The accepted scope for this informational measurement is instead `tests/tests`,
from its own directory, one worker, checker Both, clean before each run.
No application converter count or percentage is extrapolated from this corpus.

| Inclusive region | Executable source | Instructions | Calls |
|---|---|---:|---:|
| `tc::bridge::from_old::run` (including its publisher and callees) | candidate `0f1fa2def` | 52,032,132 | 748 |
| Old `driver::publish_signature` (including callees) | baseline `be1b3a482e` | 127,992,448 | 748 |

Both runs exited 0 and compiled **743 source modules**. Publication/conversion
calls are 748, not an old-source-node count. The ratio is
**0.406525× (40.652502%)**. This same-corpus ratio is the measured evidence
R3/R5c start from, not an application performance gate.

The denominator deliberately uses the old baseline publication function,
as did the 906,128,693-instruction application reference: the candidate's
Both-mode `driver::publish_signature` additionally contains conversion and
canonical comparison, which would not be the old publication cost.
Both executions below use `RESCRIPT_CHECKER=both`.

With absolute `BASE`, `CANDIDATE`, `RUNTIME`, and `OUT` paths prepared:

```sh
cd tests/tests
export RESCRIPT_RUNTIME="$RUNTIME" RAYON_NUM_THREADS=1 RESCRIPT_CHECKER=both
"$CANDIDATE" clean .
timeout 85 valgrind --tool=callgrind --collect-atstart=no \
  '--toggle-collect=*from_old*run' \
  --callgrind-out-file="$OUT/tests-from-old.callgrind" "$CANDIDATE" build .
"$BASE" clean .
timeout 85 valgrind --tool=callgrind --collect-atstart=no \
  '--toggle-collect=*driver*publish_signature' \
  --callgrind-out-file="$OUT/tests-publisher.callgrind" "$BASE" build .
grep -E '^(summary|totals):' "$OUT/tests-from-old.callgrind" "$OUT/tests-publisher.callgrind"
callgrind_annotate --auto=no --inclusive=yes --tree=both --threshold=100 \
  "$OUT/tests-from-old.callgrind"
callgrind_annotate --auto=no --inclusive=yes --tree=both --threshold=100 \
  "$OUT/tests-publisher.callgrind"
```

The collected `summary` and `totals` match the inclusive region counts above;
annotation confirms 748 calls each. No instructions-per-old-source-node figure
is reported: the release artifact does not emit the test-only source counter.
No separate instrumented binary was built.

## Reproduce the alternating-pair measurement

The +0.02% default-path instruction limit is **the reviewer's criterion for
this slice**, not a change to the repository-wide CI threshold.

The complete wrapper is inline below (not a tracked executable). It is the
measured pairing/timing algorithm with machine-specific paths supplied as
environment variables. A smoke run of this portable form completed one pair;
that smoke run is not substituted for the ten historical pairs above.
Save the following block as `/tmp/r2-alternating-repro.py`:

```python
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import time

# All paths are supplied by the caller; RESULTS must be a fresh directory.
corpus = Path(os.environ["CORPUS"]).resolve()
results = Path(os.environ["RESULTS"]).resolve()
results.mkdir(parents=True, exist_ok=True)
binaries = {
    "base": Path(os.environ["BASE"]).resolve(),
    "head": Path(os.environ["CANDIDATE"]).resolve(),
}
env = dict(os.environ, RESCRIPT_RUNTIME=str(Path(os.environ["RUNTIME"]).resolve()),
           RAYON_NUM_THREADS="1")
env.pop("RESCRIPT_CHECKER", None)
rows_file = results / "alternating.jsonl"
rows = [json.loads(line) for line in rows_file.read_text().splitlines()] if rows_file.exists() else []
round_number = len(rows) // 2
order = ["base", "head"] if round_number % 2 == 0 else ["head", "base"]

def clean(side):
    subprocess.run([str(binaries[side]), "clean", "."], cwd=corpus, env=env,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)

mode = sys.argv[1]
if mode == "prepare":
    clean(order[0])
elif mode == "run":
    for index, side in enumerate(order):
        if index:
            clean(side)
        with (results / f"round-{round_number}-{side}.log").open("w") as log:
            start = time.perf_counter()
            subprocess.run([str(binaries[side]), "build", "."], cwd=corpus, env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
            elapsed = time.perf_counter() - start
        with rows_file.open("a") as out:
            out.write(json.dumps({"round": round_number, "side": side,
                                  "seconds": elapsed}) + "\n")
elif mode == "summary":
    for side in binaries:
        times = [row["seconds"] for row in rows if row["side"] == side]
        print(side, "n=", len(times), "mean=", statistics.mean(times),
              "sd=", statistics.stdev(times) if len(times) > 1 else 0,
              "min=", min(times), "max=", max(times))
else:
    raise SystemExit("expected prepare, run, or summary")
```

Provide absolute paths to the two built binaries, the runtime package and the
application. Use a fresh results directory, and run the two binaries within
each pair (not as two independent Hyperfine command blocks):

```sh
export BASE=/absolute/path/to/baseline/rescript
export CANDIDATE=/absolute/path/to/candidate/rescript
export RUNTIME=/absolute/path/to/packages/@rescript/runtime
export CORPUS=/absolute/path/to/application
export RESULTS="$(mktemp -d)"
hyperfine --runs 10 \
  --prepare 'python3 /tmp/r2-alternating-repro.py prepare' \
  'python3 /tmp/r2-alternating-repro.py run' \
  --export-json "$RESULTS/hyperfine-pairs.json"
python3 /tmp/r2-alternating-repro.py summary
```

The earlier measurements ran five consecutive `--runs 2` invocations of this
pairing algorithm to bound individual commands. The wrapper's individual
measurements exclude clean time; Hyperfine's combined pair includes the clean
between the two children. Use `alternating.jsonl` for per-binary statistics.

## CI command using an already-built rescript

Run from the repository root, with `RESCRIPT_EXE` optionally naming the already
built binary (default `rewatch/target/release/rescript`). No workflow change is
part of this slice. Cleaning ensures Both mode actually checks each module
rather than merely reusing a previous build:

```sh
set -eu
ROOT="$PWD"
RESCRIPT_EXE=$(realpath "${RESCRIPT_EXE:-rewatch/target/release/rescript}")
export RESCRIPT_RUNTIME="$ROOT/packages/@rescript/runtime"
export RESCRIPT_CHECKER=both RAYON_NUM_THREADS=1
(cd "$RESCRIPT_RUNTIME" && "$RESCRIPT_EXE" clean . && "$RESCRIPT_EXE" build .)
(cd "$ROOT/tests/tests" && "$RESCRIPT_EXE" clean . && "$RESCRIPT_EXE" build .)
```

The exact sequence passes with `RESCRIPT_EXE=rewatch/target/debug/rescript` on
the reviewed code: **113 runtime modules and 743 test modules**, exit 0.

## Finishing-review evidence

- Shared/stored determinism: `cargo test --locked --manifest-path compiler-rust/Cargo.toml shared_and_stored_publications --lib` passes. Both actual reader branches are exercised; every Segment pool, including template ranges, is compared. No numbering change or renumbering pass was needed. R1 runtime code is unchanged; `TemplatePools` has test-only equality/debug derives for this assertion.
- Generator: `cargo test --locked --manifest-path compiler-rust/Cargo.toml generated_signatures_keep --lib` passes all **512 fixed seeds**, combining terms to depth 3 and retaining every requested declaration family. Failures print the full source and seed; no failing seed or shape was removed.
- Equality bounds: `cargo test --locked --manifest-path compiler-rust/Cargo.toml tc::canonical::normalize --lib` passes the 10,000-field linear-merge bound and 10,000-partner radix-probe bound. Unnormalized conjunction children may require temporary sorting; the normalized path borrows sorted runs. Hyperfine on clean Both-mode tests/tests, one worker, five runs: before 1.082 ± .037 s (1.037–1.120), after 1.087 ± .045 s (1.036–1.147); no wall improvement claimed.
- One longident traversal: `shared_longident_walk_preserves_both_rendering_contracts` passes, preserving diagnostic raw indices, structural unresolved spelling and application handling.
- Pins: VField 12, OField 8, SigFrame 24, ObjectField 12, PathRoot 1, Line 1 bytes. All requested entry-point/helper cost comments are present.
- Final checks: all **69 checker tests**, both strict Clippy feature configurations, strict Rustdoc, compiler/rewatch builds and rewatch tests pass. Both-mode worker determinism again reports 737 files, 743 signatures, one diagnostic and 850 stored interfaces identical in four configurations; the actual identity fixture's complete snapshot passes.
- Full local compiler suite: **2401 passed, 50 failed, 25 ignored**. All 50 failing tests also fail in the matched baseline run (53 failures); no candidate-only failure. The OCaml bsc is unavailable, so complete OCaml-oracle parity is not claimed.
