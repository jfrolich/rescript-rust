# TypeArg storage experiment

Current rollback proposal: the compiler implementation described below is removed on `revert-unaccepted-performance`. Historical evidence is retained. See [rollback scope and validation](ROLLBACK_UNACCEPTED_EXPERIMENTS.md). Main is unchanged until the PR is merged.

Owner: bks-fb2a0e85-f454-79be-9857-52c9cb1ece14. Start: clean 8ad31ffe0 on can-you-do-a-torough-look. Sole compiler/worktree/heavy-test ownership. Hybrid map stays experimental and unchanged; M6 stays paused. No push or PR edits.

## Preregistration

Hypothesis: moving the rare owned ArgLabel into Option<Box<ArgLabel>> reduces TypeArg from 80 to 16 bytes on 64-bit targets, reducing arrow-vector copying and capacity. None represents Nolabel without allocation. Borrowed reads return the original label, not reconstructed metadata. Extra allocations and indirection for labeled/optional arguments may erase or reverse the benefit. No improvement is assumed.

Scope is typed TypeArg only, not parser ArgLabel, TypeDesc, arrow containers, scheduler, maps, lazy forcing or identity. Preserve Debug field output and move/clone ownership. OCaml asttypes.ml:48-51 defines all three labels with located strings; types.ml:22-28 defines identity and n-ary arrows. btype.ml:422-423 preserves labels and argument-list order while mapping types. Its tuple expression does not establish native argument-versus-result evaluation order. This experiment preserves the existing Rust traversal without claiming a native sequencing proof. ctype.ml:2646-2662 filters matching n-ary labels and returns the original parameter identities. typecore.ml:2302-2314 lowers arguments in order; 4071-4135 matches each parameter in order and retains labels in application results. Storage must not alter any of these boundaries.

Validation: size, no cold allocation for Nolabel, exact label name and all location fields, independent owned clones, moves/replacement/drop and exact TypeExprRef handles. Exercise generic, labeled, optional and n-ary typechecking, portable serialization, diagnostics and OCaml parity. cargo check and focused default tests first; commit the coherent refactor with DCO; request fresh independent source review at a clean exact head. Freeze source during review and all heavy gates.

Run full default compiler tests; release/default compiler and rewatch builds and tests; release typedtree/raw/optimized Lambda, focused JS and snapshots, diagnostics and external JS parity. Use default features, Rust 1.93.1, unset RUSTFLAGS and Node 22.22.0. Record the known benchmark_index threshold failure once, never retry into green. External OCaml bs-css missing Belt is not a Rust comparison pass. Unresolved gates mean research candidate only.

Dedicated artifacts: /tmp/rescript-type-arg-experiment and durable /Users/jake/.opensession/artifacts/rescript-performance-20260905/type-arg. Preserve all 18 existing Tella gen.ts files individually and inventory actual resolved source/config/lock/PPX inputs. Separate pre-test and frozen post-test, selected-clean pre-timing inventories; classify only the exact known generated metadata paths and verified source mirrors. Do not waive source drift. Never overwrite or chmod C binaries.

Control C source 8311daed8 with documentation-only head 8ad31ffe0. Immutable bsc SHA ea88922a083db2818a6b4e4c4887ccc15df502f4f523b8a96dcc788727b6e8f4; rescript SHA 1390bdf0409d28504c63f5678cb023e632263dad02395aae080925cd7359aeea. Candidate D must be uninstrumented. Profile separately with per-context/local counters only, measuring hot capacities plus owned cold label/string/path storage once and allocation counts. Distinguish cumulative capacity, live/retained storage and peak RSS; the old 528MB gross capacity bound is not a measured gain.

Fixed timing: hyperfine two screening runs per C/D and w1/w12 cell, separate from eight paired C/D builds per worker mode. Odd pairs w1 then w12 and CD; even pairs w12 then w1 and DC. No additional or excluded samples, no significance fishing. Full process perf_counter_ns with time -lp; selected clean, source checks and JS manifests outside timer. Record wall/user/system/RSS/instructions/cycles/load, failures, counts, hashes, mean/SD/min/max/median and paired 95% Student-t CI. No A comparison or new-best claim planned.

Tella remains 66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa. Explicit RESCRIPT_BSC_EXE, this worktree RESCRIPT_RUNTIME and RAYON_NUM_THREADS; build --in-process --no-timing true. Runtime bootstrap is 107 modules with minimum two workers even at project w1. Warm filesystem, no cache purge. Every measured build must compile 3248 modules and emit 5048 JS files with digest 1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49.

All heavy commands use /usr/bin/lockf -k /tmp/rescript-tella-heavy.lock /bin/bash -lc. Builds bounded at 600s and individual compiler fixtures at 5-10s. Flat/regression means normal revert of this candidate only. Improvement requires exact-head review and proof, with red gates explicitly pending. Release ownership at final handoff.


## Reviewed implementation and gates

Source 5dc38ba2154e158d43436ada2142a13eef9f2c8c is frozen. Independent read-only reviewer bks-52275976-2a5c-7d56-abd7-171b46031403 found an avoidable cold allocation at two no-op substitution sites. Fixed by traversing type handles in the same existing order, then building labels only for changed arrows. The extra small handle vector on changed paths is a measurement risk. Re-review found no further source-level finding. No snapshot API expansion or unrelated algorithm change.

Four focused default tests pass. Six standalone exact OCaml comparisons pass, including typedtree locations, raw/optimized Lambda and wrong-label/arity diagnostics. The original seven-pass claim is retracted: the original JS check compared empty stderr rather than emitted JS. The corrected JS check fails, as detailed below. The successful fixture covers generic/labeled/optional/n-ary and nested arrows plus record spread with unchanged and substituted arrow fields. No expected-output normalization.

Final default and release compiler suites each report 1337 lib, 16 comptime and 9 doc tests passed; ignored 108/23/7; bins zero. Rewatch release 150 passed. The initial c6278e795 runs and final 5dc38ba21 runs have separate logs. Both release harnesses reported benchmark_index ok without threshold changes. Successful stdout was captured by Cargo, so actual ratio/times are unavailable. Required binaries and index fixture exist; no repeat was made just to expose stdout. This is not evidence that TypeArg fixes parser benchmark instability.

Release parity passes 610 typedtrees, 610 raw Lambda, 610 optimized Lambda, 344 focused JS, 610 JS snapshots and 1431 diagnostics. External parity fails in OCaml bs-css/Css_AtomicTypes.res:1446 with missing Belt before Rust comparison. Acceptance remains pending.

## Storage probe before timing

Archived 5dc38ba21 release/default rewatch only, with per-context counters and a destruction census. Normal compiler source/binaries never contain instrumentation. 3511 contexts; probe build exits 0 and matches 5048 JS files and the required digest.

Arena-arrow payloads retained at context destruction, summed across lifetimes: 5,135,539 arrows / 8,209,181 arguments; 135,943,648 hot vector capacity bytes + 92,339,928 cold box bytes + 10,713,799 owned string capacity bytes = 238,997,375 bytes. There are 1,282,499 cold boxes/nonempty strings, including 467,703 optional labels. NoLabel has no box. File names remain StrIdx handles in locations, so no filename strings are separately owned by labels or counted twice here.

Cumulative get_desc arrow snapshots: 5,042,791 arrows / 8,271,164 arguments; 132,338,624 hot bytes + 96,930,000 cold box bytes + 10,913,683 string bytes = 240,182,307 requested bytes. These snapshot shapes imply 1,346,250 logical cold-box clone requests plus their nonempty strings. These are not allocator-intercepted calls. This is a measured allocation subset, not an exhaustive count of every transient TypeArg/Vec creation. Retained-at-destruction sums are not simultaneous peak, cumulative all-allocation traffic or DRAM traffic. The two populations overlap over time and must not be added as total allocations. Allocator metadata/rounding and separately owned filename arenas are excluded. Peak process RSS comes from uninstrumented timings.

Repro scripts and all raw private logs/inventories stay in the dedicated artifact directory. Before timing, freeze a separate inventory after all tests and selected C clean. No timing samples yet at this documentation checkpoint.


## Fixed cohort result

All 32 prescribed builds exited 0, compiled 3248 modules and produced 5048 JS files with the required digest. No excluded or additional samples. Screening had eight builds with the same count/hash and remains separate.

| Variant / workers | Wall mean ± SD, seconds | Median | Min–max | User / system, seconds | Mean peak RSS, GB |
|---|---:|---:|---:|---:|---:|
| C / 1 | 20.040806 ± .115167 | 20.074060 | 19.767503–20.136503 | 19.09875 / .86250 | 2.08353 |
| D / 1 | 19.961624 ± .121632 | 19.981096 | 19.731313–20.104589 | 19.03000 / .85750 | 2.08471 |
| C / 12 | 4.956757 ± .048697 | 4.953509 | 4.907526–5.036602 | 40.42125 / 2.10375 | 3.01567 |
| D / 12 | 4.907486 ± .039427 | 4.908891 | 4.844735–4.966733 | 39.91125 / 2.09375 | 3.02957 |

Eight paired D-minus-C differences per worker mode, 95% Student-t intervals with seven degrees of freedom:

- w1: −79.18ms [−129.53, −28.84], 0.395% lower mean wall time. All eight differences favored D.
- w12: −49.27ms [−93.86, −4.68], 0.994% lower mean wall time. Two pairs regressed 33.74ms and 7.29ms. The interval only narrowly excludes zero; confidence in repeatability beyond this cohort is limited.

Screening means C/D were 19.543/19.629s at w1 and 5.019/4.907s at w12. Screening's serial direction disagreed with confirmation. No samples were added to resolve this disagreement. The warm-filesystem paired design does not eliminate scheduling, frequency or temporal drift. Load averages are preserved per confirmation sample. Final AC power was connected; pmset reported no recorded thermal/performance warning, not continuous power telemetry.

Retired instructions C→D were 252.922B→252.238B at w1 and 253.453B→252.967B at w12. Cycles were 81.159B→80.622B and 140.657B→138.957B. Mean peak RSS INCREASED by 1.18MB serial and 13.90MB parallel. The smaller 16-byte TypeArg and reduced retained arrow capacity did not produce a measured whole-process memory reduction. No DRAM-bandwidth claim is supported.

This is a small isolated candidate gain over current C, not a fresh A comparison, new global best or one-second result. The hybrid map remains untouched and experimental. No M6 work occurred.

## Corrected standalone JS validation and remaining blockers

After timing and inventory verification, the parent identified the fixture harness's stale-output/fallback risk. The first strict fresh-file fix failed because standalone bsc emits JavaScript to stdout when no package output flag is supplied. That failure is preserved. The next correction requires fresh, nonempty JS stdout from each process and saves variant-specific .js files. It revealed an exact output difference: Rust places `let text = "first"` before the curried/project functions, whereas OCaml places it after `integer`. The corrected harness remains red; no normalization or expected-output rebaseline was made.

One untimed immutable C compilation produces byte-identical JS to D, SHA-256 `0e379e0f23dc45ed2a5d5540fd3dbed526b2094d73b47bd6a4524684d1006aaf`. OCaml is `8e0f739734e387cfa499217ae46cdf90f3199fbf6cbf75ab1fde46e1047ae802`. This establishes preexisting control debt, not an excuse to call parity passed. Node runtime assertions pass for all three outputs, including generic selection, optional application, nested arrows and record-spread projection; runtime success does not replace exact JS parity.

Both original false-pass evidence and subsequent failed validations are retained. The compiler source and .res fixtures were unchanged during the entire timing cohort. No timing or release benchmark was repeated because of this harness correction.

Full acceptance is NOT met: external OCaml Tella compilation still fails on missing Belt, and the standalone exact JS fixture has preexisting declaration-order debt. The normal internal suites passed as reported above; successful benchmark_index stdout was hidden, so no ratio or parser-speed attribution is claimed. Retain TypeArg only as a reviewed, measured experimental candidate pending the parent's decision. No production retention or merge permission follows.

## Inventory, restoration and durable evidence

The pre-gate inventory has 92 classified changes: eleven external compiler-info outputs, fifty compiler-test compiler-info outputs reached through the existing rescript symlink, 28 Cargo incremental lock paths and the three new experiment fixtures. No new source mirrors appeared in this run; existing mirrors were included. All raw inventories and this exact path classification are preserved.

A separate pre-timing inventory after all tests and selected C clean had 41,577 paths; post-timing had 41,589. Verification before fixture-harness edits found only the exact eleven compiler-info files and webapp/lib/bs/.sourcedirs.json, with no unexpected changes. Nothing was broadly excluded by extension or directory. All eighteen preexisting gen.ts modifications match their individual backups byte-for-byte; Tella remains at 66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa with exactly those modifications.

[Raw cohort](type-arg-5dc38/runs.jsonl), [statistics](type-arg-5dc38/timing-summary.json), [storage census](type-arg-5dc38/storage-summary.json), [provenance and log hashes](type-arg-5dc38/provenance.json), [corrected fixture verdicts](type-arg-5dc38/fixture-results.json). Reproduce fixed-order analysis and census totals with `python3 scripts/type_arg_analyze.py`. Reproduce fresh fixture checks with `python3 scripts/type_arg_fixtures.py`; its current exact JS failure is intentional evidence, not a passing check.

Raw logs, manifests, input inventories, backups, restored archived source and immutable binaries are preserved locally in `/Users/jake/.opensession/artifacts/rescript-performance-20260905/type-arg/`. No private corpus source or JS was committed or uploaded. Temporary working evidence also remains under `/tmp/rescript-type-arg-experiment/`.

Candidate bsc SHA-256: `a5ed9a622e3b787a8dae0cb5228a5eb5717849314d0af40c05f9689c6a6788af`. Candidate rewatch: `5fe8158df5d3201d4cf07fd962cf61b22edf63874b03bfd5328e1fe16f47c3c4`. Control hashes are unchanged. Reviewed/measured compiler source is exactly 5dc38ba2154e158d43436ada2142a13eef9f2c8c; later commits are fixture harness/scripts/evidence only. Archive instrumentation has been removed from the archived source; its patch and probe binary remain separate.

No push, PR edit, merge, other worker or background process was started. At handoff all compiler/shared-worktree/heavy-test ownership is explicitly released. M6 stays paused; this session takes no next optimization task.
