# Hybrid map experiment

Owner: session bks-5f227324-a8e2-75b0-bbb0-f33135ca210e. Starting clean head `16caa9a93`. M6 remains paused. No campaign edits, push or PR actions.

## Preregistration

Restore only the safe map implementation from `fb4497659fdf53b491fc5480d6588ec800e92e0a`. Keep inline capacity 8, dense ratio 8, minimum sparse span 256, sparse promotion count 32 and ratio 4 unchanged. First collect current B map counts, occupied entries, spans, capacity and resize request estimates from a disposable archive. Timing executables remain untouched. Stop and report if shapes falsify the hypothesis.

Artifact directory: `/tmp/rescript-hybrid-map-experiment`. All heavy commands use `/usr/bin/lockf -k /tmp/rescript-tella-heavy.lock /bin/bash -lc`. No global filesystem cache clearing. Back up and restore the 18 existing Tella generated files individually. Use the existing measurement input inventory and exact generated compiler-info classification; preserve dependency inputs.

After implementation and review: hyperfine screening, two runs each for B and C at w1 and w12. Separate confirmation: eight B/C pairs per worker mode. Odd pairs use w1 then w12, B then C; even pairs use w12 then w1, C then B. No sample extension. Full process `perf_counter_ns` timing includes `/usr/bin/time -lp`; clean, source hashes and JS manifests are outside timing. Warm filesystem, same Rust 1.93.1 release defaults, unset RUSTFLAGS, Node 22.22.0 and current worktree runtime. Runtime bootstrap retains minimum two workers even for w1 project builds. Each valid build must compile 3248 modules and match the 5048-file JS manifest. Retain errors and exclusions. Record wall, CPU, RSS, instructions, cycles and paired t intervals. No absolute-best claim or A comparison is planned.

Run full compiler default tests, release compiler/rewatch builds and tests, release typedtree/raw/optimized Lambda, JS/snapshots, diagnostics and external JS parity. The known release benchmark_index failure is not to be retried into green, suppressed or threshold-adjusted. A gain with unresolved gates remains a candidate, not accepted optimization.

## Source boundaries checked

OCaml `types.ml:22` defines node identity, `btype.ml:46-48` allocates identities, and `subst.ml:241-309` preserves copy scopes across declarations. All current map references are in `typecore.rs`: polymorphic-send instantiation, recursive lookup type/constructor/label/declaration/value/module/signature copying and qualified record-label copying. They use only `new`, `get` and `insert`. The current map has no remove, get_mut, clear or iteration API; no iteration ordering is observable. All instantiated values are compact TypeExprRef handles. Captured Env, mutation snapshots and traversal order remain outside this storage change. Probe counters are per map; there is no type graph census or normal-build instrumentation.

Results pending.

## B shape probe

Archived B release rewatch, default features, full serial Tella build: exit 0, 5048 JS files with expected digest. Input inventory unchanged, all 18 generated files restored. Probe added only map-owned counters and drop logging in the disposable archive. No timing baseline was overwritten. Initial archive-path assertion failed because macOS resolves `/tmp` to `/private/tmp`; corrected before the instrumented build. An uninstrumented archive build occurred first and is not measurement evidence.

294,527 map lifetimes, 11,410,887 inserted entries, 1,275,473,220 logical span slots. Sum of final vector capacities: 10.744GB; initialized logical slot bytes: 10.204GB; prepend-moved logical slot bytes: .514GB. 820,154 observed allocation/resize requests, 12.201GB summed requested capacities. These are source-operation estimates, not malloc traces or actual DRAM traffic. Capacity growth can happen in place; nested payloads are excluded. Here T is TypeExprRef and Option<T> is 8 bytes. Largest individual capacity was 2.104MB; this is not aggregate concurrent peak memory.

214,998 maps held at most eight entries, summing 8.582GB final capacity. Qualified record-label copying at typecore.rs:28473 dominated: 161,798 maps / 753,364 entries / 9.444GB capacity; its 145,346 tiny maps used 8.429GB. 115,817 maps had span >256 and >8 times occupancy. Dense signature copying remains substantial: persistent_env.rs:3497 created 32,324 maps with 7,451,453 entries and 203MB final capacity. These shapes support the unchanged tiny/dense/sparse policy. The full-build probe does not isolate Layout__Types; prior module timings identify its regression, but no per-module map attribution is claimed.

Raw local log: `/tmp/rescript-hybrid-map-experiment/logs/map-probe.log`. Durable aggregate: [hybrid-map-probe-summary.json](hybrid-map-probe-summary.json). Reproduce by archiving compiler-rust/rewatch from 16caa9a93 into the dedicated probe-source directory, running `scripts/hybrid_map_probe.py`, release-building archived rewatch, then `scripts/hybrid_map_measure.py init`, `probe`, `verify`, `restore-generated` under the lock. Run init only once before corpus mutations. `scripts/hybrid_map_analyze_probe.py` aggregates the log. No compiler instrumentation exists in the shared tree.
