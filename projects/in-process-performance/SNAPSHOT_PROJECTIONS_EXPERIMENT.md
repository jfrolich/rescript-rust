# Snapshot projections experiment

Owner bks-a6d8d8ba-711d-7981-b177-2be13b15413d. Start clean f4e6672ab. Sole compiler/shared-worktree/heavy ownership; M6 paused. No push, PR, subworkers or unrelated edits.

## Preregistration

Replace only five redundant inspections in types/typecore.rs and types/ctype.rs with lexical borrow_desc projections. Keep both owned TypeArg vectors, lower_args' owned child vector and substitution's later owned snapshot. Preserve short circuit, identity, metadata, mutation, expansion, instancing and existing traversal order. Reference typecore.ml:2302-2313/4030-4095 and subst.ml:130-165. Native constructor text is not an evaluation-order proof.

The audited group requests 2,371,770 snapshots and 89,310,173 nested logical bytes. These are redundant source requests, not allocator, DRAM or elapsed-time predictions. No gain is assumed.

Focused mutation/identity/metadata tests and cargo check precede a DCO source commit and fresh independent exact-clean-head source review requested from parent. Freeze compiler source after review; fix findings before timing. Run default compiler lib/bins/comptime/docs, release compiler and rewatch builds/tests, release typed/raw/optimized parity, focused JS/snapshots, diagnostics and external JS. Use -- --show-output for planned final release tests. Preserve benchmark_index failure or skip honestly; if lib stops Cargo, run remaining bins/comptime/docs once. No retries for green or output. Preserve corrected standalone TypeArg JS mismatch and external OCaml missing Belt as inherited red gates, not waived acceptance.

Dedicated temporary artifacts /tmp/rescript-snapshot-projections-experiment; durable /Users/jake/.opensession/artifacts/rescript-performance-20260905/snapshot-projections. New scripts/data, no append to old cohorts. Reuse measurement_rebaseline/type_arg policy. Immutable D control source 5dc38ba2154e158d43436ada2142a13eef9f2c8c: bsc a5ed9a622e3b787a8dae0cb5228a5eb5717849314d0af40c05f9689c6a6788af, rewatch 5fe8158df5d3201d4cf07fd962cf61b22edf63874b03bfd5328e1fe16f47c3c4 from /tmp/rescript-type-arg-experiment/bin or durable type-arg/bin. Candidate E uninstrumented, Rust 1.93.1 LLVM 21.1.8 default release LTO true/codegen-units 1, RUSTFLAGS unset, Node 22.22.0. Record source/toolchain/commands/hashes before timing.

Fixed D/E cohort: two hyperfine screening builds per D/E w1/w12 cell, separate from eight paired builds per mode. Odd pairs w1 then w12, DE; even pairs w12 then w1, ED. Afterwards run a separate eight A/E parallel pairs at w12 regardless of D/E effect size, odd AE/even EA, if correctness eligible. No A serial, no pooling, extra or excluded samples. A is same-toolchain rebuild of fb4497659fdf53b491fc5480d6588ec800e92e0a, not historical executable. Read-only /tmp/rescript-measure-rebaseline-542/bin/bsc-A 7c39a09c163088ac7db372ff8139fa62e2a9b76960eafccfe4ed2385f9172ca0 and rescript-A 0187abee145aebdcc1b43db8d60e28ed851840dd3c75397959f64223420c4332; durable measurement-542/bin fallback. Never overwrite/chmod controls.

Time full build processes using perf_counter_ns and time -lp, with clean/input checks/JS manifest outside. Preserve exits/counts/hashes/wall/user/sys/RSS/instructions/cycles/load and report mean/SD/range/median/paired 95% t intervals. No instrumentation or profiler pooled. Flat/negative isolation means normal revert of only candidate after full planned cohort. A/E is new-best comparison, not isolated causality. Historical 4.5–4.6s remains best; one second unachieved/unproven.

Pin Tella 66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa at /Users/jake/dev/tella-fusion/packages/core/webapp, runtime this worktree packages/@rescript/runtime. Individually backup/hash/restore 18 preexisting gen.ts modifications and exact HEAD/status. Explicit BSC/runtime/RAYON, selected clean outside build --in-process --no-timing true, warm filesystem, no cache purge. Runtime 107 fresh bootstrapped modules per process, minimum two workers even project w1. Every full build must exit zero, compile 3248 modules and match 5048 JS files digest 1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49.

Freeze resolved source/config/dependency/PPX inventory after all setup/tests and selected clean. Verify before report/data edits reachable through rescript symlink. Only exact eleven compiler-info outputs and .sourcedirs allowed; compiler-info is read for clean policy but absent-before/present-after here. No broad exclusions, preserve failed inventories. All heavy commands under /usr/bin/lockf -k /tmp/rescript-tella-heavy.lock /bin/bash -lc with Cargo PATH /Users/jake/.cargo/bin, 600s builds and 5–10s fixture compilers. No private source/JS committed or public upload. Preserve raw evidence and hashes durably, report limitations, then explicitly release all ownership to parent.

## Source review checkpoint

Candidate source 08c884be8412d44d4ca32ef76a8792febeae35e8 changes only the five requested production boundaries. Fresh independent reviewer ef2a1650-88bc-7b3b-b6aa-21d761dea55a returned NO FINDINGS against D. Parent confirmed the exact clean head. This is source review, not gate or performance acceptance. The projection unit test models the two owned stages; standalone fixtures and full gates exercise actual application typing.

Cargo check and five focused default tests pass. Development failures are preserved: an initial row-name argument assertion missed the existing row-more tuple marker; a test used a nonexistent constructor helper; generic alias instancing bypassed the intended level capture; and the alias test initially omitted the terminal int expansion. Tests now assert the existing marker identity and M.t then int expansion order. No production semantic adjustment was made to satisfy them. Full planned gates are running once with successful-test output retained.

## Final gates and timing eligibility

Default and release compiler builds and complete tests pass: 1342 library tests, 108 ignored; both bins zero tests; comptime 16 passed/23 ignored; docs 9 passed/7 ignored. Default and release rewatch builds/tests pass, 150 tests. The planned release output shows benchmark_index actually executed: Rust 9052us, OCaml 7747us, ratio 1.17 against unchanged 1.20. Both compiler paths and the 38896-byte index fixture existed. No retry was used; this one result does not establish that historical parser benchmark instability is fixed. Default benchmark skips are the existing debug-assertions policy, despite their misleading missing-binaries message.

Release parity passes 610 typedtrees, 610 raw Lambda, 610 optimized Lambda, 344 focused JS, 610 JS snapshots and 1431 diagnostics. External JS exits 2 at OCaml bs-css/Css_AtomicTypes.res:1446 missing Belt, before Rust comparison. The new SnapshotProjections fixture passes all five exact OCaml comparisons including fresh nonempty JS stdout. Together with TypeArg fixtures, 11/12 exact comparisons pass; the single red remains TypeArgStorage JS declaration placement. All 12 E/D comparisons pass, including saved actual stdout. Six Node executions of saved OCaml/D/E outputs pass runtime assertions. Runtime success does not waive exact JS red.

The source remains exactly reviewed 08c884be8. E binaries are uninstrumented, copied read-only before timing: bsc cc1fed85b54b36b3f1dbea9f6104baca7a0d26b45727bb3940dae9bd14ffeac7; rewatch 3398d2ef48f0be2acd0a003ff2bd6d6f99905c208639eb6bb1b12c4c3cb66068. A/D source, toolchain provenance, hashes and read-only permissions were verified without modifying controls. All timing commands and hashes are saved in provenance-before-timing.json. Candidate is eligible for the preregistered research comparison, not production acceptance. No timing results yet.

## Fixed results and rejection

All eight screening builds and all 48 prescribed paired builds exited zero, compiled 3248 modules and produced the required 5048-file JS digest. D/E contains eight pairs per mode; A/E contains eight separate parallel pairs afterwards. No samples were added, excluded or repeated.

| Cohort / variant / workers | Wall mean ± SD, s | Median, s | Min–max, s | User / system mean, s | Peak RSS mean, GB |
|---|---:|---:|---:|---:|---:|
| D/E D / 1 | 19.551231 ± .048583 | 19.537509 | 19.470603–19.612130 | 18.670 / .7975 | 2.083115 |
| D/E E / 1 | 19.449171 ± .150347 | 19.449436 | 19.260479–19.697511 | 18.560 / .7988 | 2.080051 |
| D/E D / 12 | 4.907762 ± .048433 | 4.900663 | 4.856175–4.998467 | 40.0325 / 2.0638 | 3.022819 |
| D/E E / 12 | 4.883602 ± .035160 | 4.881044 | 4.839237–4.938741 | 40.0813 / 2.0963 | 3.019194 |
| A/E A / 12 | 4.647931 ± .043119 | 4.645318 | 4.591640–4.739460 | 38.665 / 2.0738 | 2.918984 |
| A/E E / 12 | 4.878642 ± .038378 | 4.894645 | 4.796668–4.911458 | 39.9413 / 2.0800 | 3.025578 |

Paired E-minus-control differences, 95% Student-t intervals with seven degrees of freedom:

- D/E serial: −102.06ms [−196.69, −7.43], a 0.522% mean reduction. Seven of eight pairs improve. This cohort supports a small serial gain; the interval narrowly excludes zero.
- D/E parallel: −24.16ms [−59.89, +11.57], a 0.492% point estimate improvement. Two pairs regress. The parallel result is **inconclusive**, not proof of zero benefit or a slowdown.
- Separate A/E parallel: +230.71ms [+193.37, +268.06], E 4.964% slower. E loses all eight pairs. This is a current same-toolchain historical-stack comparison, not isolated attribution to the five projections.

Screening stayed separate: D/E means were 19.238079/19.064831s at w1 and 4.912922/4.827921s at w12. SDs were .234686/.018760s and .004658/.032833s; ranges were 19.072131–19.404027/19.051566–19.078096s and 4.909628–4.916215/4.804705–4.851138s. Its larger parallel point estimate does not replace the fixed paired interval.

Mean D/E retired instructions fell 252.175B→251.585B serial and 252.968B→252.414B parallel. Cycles changed 79.449B→78.770B serial and 139.111B→139.266B parallel. Mean peak RSS fell 3.06MB serial and 3.62MB parallel. A/E instructions were 240.663B→252.443B, cycles 134.431B→138.766B and RSS rose 106.59MB. Full mean/SD/min/max/median for CPU, instructions, cycles and RSS are in timing-summary.json; per-run load averages remain in raw rows. Load changed during the cohort; no sample was removed for that. Warm-filesystem paired timing does not control every scheduling/frequency effect or prove DRAM bandwidth savings.

Parent agreed to conservative rejection under the preregistered primary parallel goal. The supported serial gain is preserved, but inconclusive parallel isolation does not justify retaining this performance candidate. Normally revert only candidate 08c884be8 after evidence preservation, leaving map/TypeArg and all sibling commits intact. No further timing, threshold changes or optimization is authorized. One second remains unachieved and unproven; the historical 4.5–4.6s stack remains the best comparison. This experiment does not disprove short borrows generally.

## Inventory and evidence

The frozen post-test, selected-D-clean inventory had 41978 paths. Final inventory had 41990. Differences were exactly eleven named compiler-info outputs plus .sourcedirs, with no unexpected drift. Before-paired and before-historical checks also passed the same exact policy. Verification completed before any report or data edits reachable through the rescript symlink. compiler-info is read for clean policy, but absent-before/present-after under this selected-clean protocol; it is not universally unread. No broad JSON/directory waiver or source-mirror exception was used.

Separate pre-gate differences number 457: 61 compiler-info outputs, one .sourcedirs, 370 Cargo rewatch debug fingerprints, 21 Cargo debug locks and four debug object files. Each path/hash is preserved and classified locally. They predate the frozen timing inventory and were not waived during timing. An initial classification missed two extensionless try-lock fingerprint outputs; their exact paths were added without redoing inventories or samples. No source mirrors changed.

All original gate/test-development failures and exact fixture payloads are retained. The initial setup tool returned a 10s timeout while lockf/Python continued and finished; setup was not repeated. The read tool denied the external skill path, then bash read it. A post-cohort summary glob included JS manifests rather than only hyperfine JSON; exact paths corrected the read without any execution rerun. Two generated diagnostic .mjs files were preserved locally and removed by exact filename after their writer was identified. No instrumentation, archive instrumentation, dependency change, public upload, push, PR edit or subworker was used.

Reproduction uses scripts/snapshot_projections_{gates,fixtures,runtime,prepare,measure,analyze,finalize}.py and measurement_rebaseline.py. Original logs, inventories, manifests, binaries, backups and candidate source archive live in /tmp/rescript-snapshot-projections-experiment and the durable organization-controlled directory /Users/jake/.opensession/artifacts/rescript-performance-20260905/snapshot-projections. Candidate patch/tests/fixture remain in history and the preserved patch/archive. Committed summaries are in snapshot-projections-08c884; private corpus JS and backup contents are not committed. The final artifact-hashes.json covers the durable evidence.

## Completed disposition

Normal signed-off revert 9c24683a75ec32c6ed1865344b5c991694811f76 removes only candidate 08c884be8. Compiler and rewatch source now match D, 5dc38ba2154e158d43436ada2142a13eef9f2c8c, exactly. A targeted cargo check passes after restoration. Full gates were not repeated for unchanged D source; the gate results above belong to E. Existing target/release executables remain E build artifacts, not a claim of rebuilt D binaries. Immutable D and E copies are separately labeled and hash-verified.

Tella remains pinned with exactly the original 18 gen.ts modifications, individually restored and hash-verified. All 414 compiler/rewatch files are verified against the restored D archive. No heavy process or profiler remains. Candidate code/tests/fixture remain recoverable at 08c884be8 and in saved candidate.patch/candidate-source.tar. The fixture reproduction script reads the exact historical source if the normal revert removed its path; it does not silently skip the new fixture.

The implementation, review, gates and fixed measurement task is complete, with the candidate rejected for inconclusive primary parallel performance. Exact-output acceptance remains blocked by the inherited standalone declaration-order difference and external missing Belt; neither was fixed or waived. No new best or one-second result was achieved. At final handoff all compiler, shared-worktree and heavy ownership is explicitly released. M6 stays paused; no next task is started.
