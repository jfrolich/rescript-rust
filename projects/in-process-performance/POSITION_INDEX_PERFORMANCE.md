# Position-index removal: fixed performance comparison

## Result

The second, user-authorized comparison completed all 32 registered timed builds. Removing the unused parser position-content index improved parallel mean build time by **1.08%** and serial mean time by **1.84%** in this cohort. All builds produced identical JavaScript.

| Mode | Variant | n | Mean, s | SD, s | Min, s | Max, s |
|---|---|---:|---:|---:|---:|---:|
| Parallel, w12 | Main | 8 | 4.829113 | 0.058523 | 4.737269 | 4.930479 |
| Parallel, w12 | Candidate | 8 | 4.777105 | 0.072770 | 4.638447 | 4.850058 |
| Serial, w1 | Main | 8 | 19.680941 | 1.073595 | 18.595370 | 20.715246 |
| Serial, w1 | Candidate | 8 | 19.318480 | 1.049442 | 18.277777 | 20.359065 |

Paired candidate-minus-main differences:

| Mode | Mean difference | 95% paired t interval | Candidate faster |
|---|---:|---:|---:|
| w12 | −52.008 ms | [−92.135, −11.881] ms | 7/8 pairs |
| w1 | −362.461 ms | [−406.135, −318.787] ms | 8/8 pairs |

This is a small measured win, not the one-second target. Keep the candidate on draft [jfrolich/rescript-rust#20](https://github.com/jfrolich/rescript-rust/pull/20). Main remains untouched. The red and blocked correctness gates in [POSITION_INDEX_VALIDATION.md](POSITION_INDEX_VALIDATION.md) remain unwaived; the result is experimental, not production acceptance.

## Method and independent checks

The main binaries represent `d98b8b9430045d40d08ed89dd75174b5669fa829`. Candidate binaries were built at `eba0277be2065fa85df2816fcb3fb07032cfbc18`; documentation-only feature head `3dfa96dab` remained frozen during measurement. Both immutable pairs used the same main runtime and fixed Tella source revision.

Each build followed a full clean. Hashing and input inventories were outside the measured interval, with a warm filesystem and no purge. The authoritative value is inner `perf_counter_ns` around `/usr/bin/time -lp` and the compiler process. Hyperfine used one run and zero warmups per slot as a secondary wrapper. The 32-slot order was fixed before execution: eight pairs per mode, alternating mode and variant order. No timed slot was retried, replaced, excluded or added. Qualification times and older comparison cohorts were not pooled into these results.

The parent independently verified:

- Exactly 32 timed builds in the registered order, 32 Hyperfine drivers, two qualification builds and 35 clean processes. All 101 process records report exit zero without timeout.
- Both qualification byte archives and all 32 per-file manifests match the expected 5,048-file JavaScript digest `1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49`.
- Every build reports 3,248 project modules. The 107 freshly compiled runtime modules and minimum two runtime workers are supported by the sealed fresh-process registry/bootstrap implementation and source inventory, not by a dynamic counter or disk CMJ timestamps.
- Per-slot before-clean, after-clean and final input checks passed, including exact compiler metadata transitions. The 18 protected generated files and four protected untracked files retained their hashes and original mtimes.
- Raw timing/resource logs match the recorded metrics. Independent recomputation agrees with the means, deviations and paired intervals above.

## Preserved failures and protocol amendment

The first comparison remains closed. Its single initial clean removed 510 generated source copies, exceeding its registered metadata-only allowance. It ran no qualification or timed builds. All 510 copies matched surviving authored sources in the same packages. The user authorized this second comparison with those exact hash-bound copies classified before execution; unknown paths or changed copy contents still fail.

The second comparison's main qualification completed successfully with exact output, but timestamp restoration failed afterward. The compiler had rewritten 18 equal-content generated files, and the restoration helper skipped equal-content files. The parent restored their original mtimes, verified all hashes and inputs, and finalized the same captured qualification result without rerunning a clean or build. The restoration fix and explicit, hash-bound postprocessing-repair amendment preceded candidate qualification and every timed slot. Original failure records and pre-amendment code/seals remain preserved. This was not an entirely unamended protocol, even though every timed slot ran exactly once.

Separate syntax-control provenance losses and red syntax/AST0/external gates are documented in the validation report. This performance result does not erase them.

## Evidence

Organization-controlled artifacts under `/Users/jake/.opensession/artifacts/rescript-performance-20260907/simplify-and-speed/`:

- `position-index-comparison-2/`: plan, raw process records, inventories, qualification archives, completed rows, `summary.json`, `parent-independent-audit.json` and `parent-process-census.json`.
- `position-index-comparison-2-protocol/`: versioned runner, tests, seals and per-slot execution logs.
- `position-index-comparison-2-parent-audit.py`: independent read-only verifier.

Plan SHA256: `975d2f814b8f3d66ea9f4b87db8bc4776c4c6907fdc8ee4c2606ec318faea231`.
Active amended seal SHA256: `40b6c9fa682e0cb07ea37f0f7befb5758496ff98effb78ad78cc0909c6c15d94`.

## Next performance work

The user requested further performance wins. The existing traces put type checking at 8.402 serial seconds, versus 1.983 seconds of parsing. The next task will investigate a concrete removable cost in that larger type-checker budget before selecting a change. Full signature-copy fusion remains vetoed by required native ownership, and the measured 24 ms export scan and 67 ms identifier scans do not justify treating either as a large opportunity. Another broad codebase audit is unnecessary.
