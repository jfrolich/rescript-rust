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

**Instruction delta: −0.234847%, within the +0.02% limit.** This is not a wall-clock speedup claim. Hyperfine (5 runs, one warmup, clean before each build): baseline **8.876 ± 0.169 s**, range **8.727–9.090 s**; candidate **9.927 ± 0.191 s**, range **9.712–10.132 s**, about **11.8% slower**. These timings need separate scrutiny despite the instruction gate passing.

Baseline inclusive `driver::publish_signature` cost: **906,128,693 instructions**, **1.390223%** of the minimum baseline build. Measured by `valgrind --tool=callgrind --collect-atstart=no '--toggle-collect=*driver*publish_signature' ... "$BASE" build .`, after cleaning, checker unset, one worker. The prompt's 1.34% reference budget corresponds to **873,393,977 instructions** on this baseline. Candidate inclusive `from_old::run` cost is **pending**, not inferred from a partial profile.


The complete converter profile is outstanding. A partial run terminated by a
ten-minute command timeout is excluded. The PR remains draft until that
measurement and the final acceptance record are complete.
