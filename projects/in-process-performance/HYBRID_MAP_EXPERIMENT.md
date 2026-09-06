# Hybrid map experiment

Owner: session bks-5f227324-a8e2-75b0-bbb0-f33135ca210e. Starting clean head `16caa9a93`. M6 remains paused. No campaign edits, push or PR actions.

## Preregistration

Restore only the safe map implementation from `fb4497659fdf53b491fc5480d6588ec800e92e0a`. Keep inline capacity 8, dense ratio 8, minimum sparse span 256, sparse promotion count 32 and ratio 4 unchanged. First collect current B map counts, occupied entries, spans, capacity and resize request estimates from a disposable archive. Timing executables remain untouched. Stop and report if shapes falsify the hypothesis.

Artifact directory: `/tmp/rescript-hybrid-map-experiment`. All heavy commands use `/usr/bin/lockf -k /tmp/rescript-tella-heavy.lock /bin/bash -lc`. No global filesystem cache clearing. Back up and restore the 18 existing Tella generated files individually. Use the existing measurement input inventory and exact generated compiler-info classification; preserve dependency inputs.

After implementation and review: hyperfine screening, two runs each for B and C at w1 and w12. Separate confirmation: eight B/C pairs per worker mode. Odd pairs use w1 then w12, B then C; even pairs use w12 then w1, C then B. No sample extension. Full process `perf_counter_ns` timing includes `/usr/bin/time -lp`; clean, source hashes and JS manifests are outside timing. Warm filesystem, same Rust 1.93.1 release defaults, unset RUSTFLAGS, Node 22.22.0 and current worktree runtime. Runtime bootstrap retains minimum two workers even for w1 project builds. Each valid build must compile 3248 modules and match the 5048-file JS manifest. Retain errors and exclusions. Record wall, CPU, RSS, instructions, cycles and paired t intervals. No absolute-best claim or A comparison is planned.

Run full compiler default tests, release compiler/rewatch builds and tests, release typedtree/raw/optimized Lambda, JS/snapshots, diagnostics and external JS parity. The known release benchmark_index failure is not to be retried into green, suppressed or threshold-adjusted. A gain with unresolved gates remains a candidate, not accepted optimization.

## Source boundaries checked

OCaml `types.ml:22` defines node identity, `btype.ml:46-48` allocates identities, and `subst.ml:241-309` preserves copy scopes across declarations. All current map references are in `typecore.rs`: polymorphic-send instantiation, recursive lookup type/constructor/label/declaration/value/module/signature copying and qualified record-label copying. They use only `new`, `get` and `insert`. The current map has no remove, get_mut, clear or iteration API; no iteration ordering is observable. All instantiated values are compact TypeExprRef handles. Captured Env, mutation snapshots and traversal order remain outside this storage change. Probe counters are per map; there is no type graph census or normal-build instrumentation.

Completed results and acceptance limitations are recorded below.

## B shape probe

Archived B release rewatch, default features, full serial Tella build: exit 0, 5048 JS files with expected digest. Input inventory unchanged, all 18 generated files restored. Probe added only map-owned counters and drop logging in the disposable archive. No timing baseline was overwritten. Initial archive-path assertion failed because macOS resolves `/tmp` to `/private/tmp`; corrected before the instrumented build. An uninstrumented archive build occurred first and is not measurement evidence.

294,527 map lifetimes, 11,410,887 inserted entries, 1,275,473,220 logical span slots. Sum of final vector capacities: 10.744GB; initialized logical slot bytes: 10.204GB; prepend-moved logical slot bytes: .514GB. 820,154 observed allocation/resize requests, 12.201GB summed requested capacities. These are source-operation estimates, not malloc traces or actual DRAM traffic. Capacity growth can happen in place; nested payloads are excluded. Here T is TypeExprRef and Option<T> is 8 bytes. Largest individual capacity was 2.104MB; this is not aggregate concurrent peak memory.

214,998 maps held at most eight entries, summing 8.582GB final capacity. Qualified record-label copying at typecore.rs:28473 dominated: 161,798 maps / 753,364 entries / 9.444GB capacity; its 145,346 tiny maps used 8.429GB. 115,817 maps had span >256 and >8 times occupancy. Dense signature copying remains substantial: persistent_env.rs:3497 created 32,324 maps with 7,451,453 entries and 203MB final capacity. These shapes support the unchanged tiny/dense/sparse policy. The full-build probe does not isolate Layout__Types; prior module timings identify its regression, but no per-module map attribution is claimed.

Raw local log: `/tmp/rescript-hybrid-map-experiment/logs/map-probe.log`. Durable aggregate: [hybrid-map-probe-summary.json](hybrid-map-probe-summary.json). Reproduce by archiving compiler-rust/rewatch from 16caa9a93 into the dedicated probe-source directory, running `scripts/hybrid_map_probe.py`, release-building archived rewatch, then `scripts/hybrid_map_measure.py init`, `probe`, `verify`, `restore-generated` under the lock. Run init only once before corpus mutations. `scripts/hybrid_map_analyze_probe.py` aggregates the log. No compiler instrumentation exists in the shared tree.

## Candidate source and focused checks

Copied only the historical safe map constants/storage/implementation plus its four tests. No other historical code was imported. Added bounds at zero/u32::MAX without dense allocation, descending offset movement, sparse-to-dense promotion, independent clone mutation, assignment reset/reuse, non-Copy drop ownership across transitions and a typechecker copy fixture with shared/distinct variables and a recursive tuple over widely separated handles. There is still no new map API. No unsafe code was introduced.

`cargo check --manifest-path compiler-rust/Cargo.toml` passed. Focused default-feature lib tests: 7/7 passed in .02s. The initial test compile used the wrong Location module path; corrected to crate::location before success. No unrelated edits. Source now ready for independent review; full gates and paired measurement remain pending.

## Gates and pre-timing inventory correction

Independent source review by session bks-07f65088-608b-7554-adb9-897e55dd0c9a found no issues at exact 8311daed8. Default compiler: 1334 lib tests pass, 108 ignored; bins have zero tests; comptime 16 pass/23 ignored; docs 9 pass/7 ignored. Release compiler and rewatch builds pass. Release lib: 1333 pass/1 fail/108 ignored, benchmark_index reports 1.31x against 1.20x limit. No retry. Remaining release bins/comptime/docs were run once separately after Cargo stopped at the lib failure and pass with the same counts. Rewatch release: 150 pass.

Release parity: 610/610 typedtree, raw Lambda and optimized Lambda; 344/344 focused JS plus 610/610 snapshots; 1431/1431 diagnostics. External gate repeats local passes but fails in the OCaml build at bs-css/Css_AtomicTypes.res:1446:19-35, unresolved Belt. This occurs before the Rust comparison. Dependencies were not upgraded or changed. Acceptance remains pending on these two known blockers.

The original pre-probe inventory cannot also serve as the post-build/test inventory: the existing rescript package symlink points into this compiler worktree, so Cargo test output/lock paths and new experiment JSON change that inventory. The external OCaml build also creates lib/bs and lib/ocaml source mirrors. Raw inventories retain all 562 differences: 251 lib/bs paths, 240 lib/ocaml paths, 71 linked compiler-repository paths; no other path differences. This is not silently excluded from verification. Before any timing samples, selected B clean runs and a separate timing-inputs-before.json is frozen. Verification of that timing cohort permits only the exact eleven known compiler-info.json output paths, not a broad JSON/source exclusion. Original 18 generated-file backups stay unchanged. No acceptance samples existed when this correction was made.

## Fixed-cohort result: small candidate gain, acceptance pending

All 32 prescribed B/C builds exited 0, compiled 3248 modules and matched the 5048-file JS digest `1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49`. No samples were excluded or added. Screening is separate and not pooled.

| Variant / workers | Wall mean ± SD, seconds | Median | Min–max | User / system, seconds | Mean peak RSS, GB |
|---|---:|---:|---:|---:|---:|
| B / 1 | 20.23018 ± .11379 | 20.22944 | 19.98456–20.34350 | 19.2725 / .8950 | 2.0844 |
| C / 1 | 20.14258 ± .11079 | 20.16233 | 19.93956–20.26443 | 19.1663 / .9025 | 2.0825 |
| B / 12 | 5.03591 ± .05935 | 5.02094 | 4.95412–5.13888 | 41.0225 / 2.1288 | 3.0367 |
| C / 12 | 4.96683 ± .04815 | 4.97006 | 4.88520–5.03953 | 40.3688 / 2.1063 | 3.0139 |

Eight paired C-minus-B differences per mode, 95% Student-t intervals with seven degrees of freedom:

- w1: **−87.60ms [−130.56, −44.64]**, 0.43% reduction in mean wall time.
- w12: **−69.09ms [−136.86, −1.31]**, 1.37% reduction. One pair regressed 85ms. The interval barely excludes zero; confidence in a repeatable parallel gain beyond this cohort is limited.

Retired instructions B→C: 254.255B→252.989B at w1, 254.854B→253.408B at w12. Cycles: 81.944B→81.370B and 142.771B→140.491B. Mean RSS fell about 2MB serial and 23MB parallel, not gigabytes. The probe's multi-GB lifetime capacity sums must not be confused with these peak RSS measurements or with memory bandwidth. The large storage count translated to a small wall-time effect.

Hyperfine screening, two runs per cell: B/C w1 20.278/20.739s, w12 5.131/4.952s. Screening's serial direction disagreed with confirmation. Both are retained. The paired design controls some drift, not OS scheduling/frequency variation. Load averages are in every sample; final AC power was connected, and pmset reported no recorded thermal/performance warning, without continuous CPU power telemetry.

This does not beat or freshly compare against the historical 4.65s A baseline. It restores one old storage design and measures its isolated effect on current B. The A/B stack gap is neither attribution nor a cap on this map's possible effect. No one-second claim is supported.

### Inventory disposition

The first post-timing check failed on exactly one additional path: `node_modules/@tella-fusion/webapp/lib/bs/.sourcedirs.json`. The raw failed report/log remain intact. `rewatch/src/sourcedirs.rs:74-77` writes this file; `rewatch/src/build.rs:517-518` calls that writer after compilation. Its readers are editor analysis at `analysis/src/find_files.ml:159` and `analysis/reanalyze/src/paths.ml:138-150`, not compiler/build input lookup. The corrected checker classifies only that exact path in addition to the exact eleven compiler-info paths. No build/timing rerun occurred. The final check confirms all 41,568 pre-timing inventoried paths unchanged except generated output metadata, with twelve newly created output paths bringing the total to 41,580.

For the earlier external-gate inventory, all 480 `.res`/`.resi` mirrors had byte hashes matching an original source in the same package. Their writer is `rewatch/src/build/compile.rs:3887-3928`, which copies the original SourceFile path after compilation. Source discovery uses original package paths, not these mirrors. The remaining eleven lib/bs paths were compiler-info metadata. The 71 linked compiler-repository changes were 50 test compiler-info outputs, 20 Cargo incremental lock paths and this experiment's new JSON aggregate. No dependency input was waived or changed. The fixed pre-timing inventory was taken after those gates and selected B clean; all raw gate/timing inventories are retained separately.

All 18 existing `.gen.ts` files were checked against their individual exact backups after restoration. Tella remains at the required commit with exactly the same 18 tracked modifications. No sources, lockfiles or dependencies were edited. Archive instrumentation was confined to the probe binary/source, never the authoritative binaries; the archive source has now also been restored, with `map-probe.patch` retained locally.

### Evidence and handoff

- [Raw 32-run cohort](hybrid-map-8311/runs.jsonl), [statistics](hybrid-map-8311/timing-summary.json), [provenance, verification and log hashes](hybrid-map-8311/provenance.json). Screening JSON is in the same directory.
- Reproduce analysis with `python3 scripts/hybrid_map_analyze.py`. It validates the fixed order and all exits/counts/manifests before calculating statistics.
- Full build/test/parity/probe logs, per-run JS manifests, inventories and exact backups remain in `/tmp/rescript-hybrid-map-experiment/`. No uploads. The durable files contain lightweight evidence; local raw artifacts need preservation before `/tmp` cleanup.
- C bsc SHA-256: `ea88922a083db2818a6b4e4c4887ccc15df502f4f523b8a96dcc788727b6e8f4`; C rewatch: `1390bdf0409d28504c63f5678cb023e632263dad02395aae080925cd7359aeea`. B hashes remain the supplied immutable baseline hashes. Candidate and control hashes were rechecked after timing.
- Reviewed compiler source remains exactly `8311daed8a67141e834c92db97d5bff7bea6e166`; later commits contain only experiment docs/scripts/evidence. No push, PR edit, merge, M6 activation or other optimization occurred.

Retain as a reviewed, measured candidate pending the parent's decision. Full acceptance is **not met** because release benchmark_index and external OCaml parity remain blocked. Do not retry them into green or represent this as accepted performance work. All compiler/shared-worktree/heavy-test ownership is released at handoff; no child workers or background commands remain.
