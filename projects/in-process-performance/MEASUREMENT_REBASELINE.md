# Fresh production rebaseline (542)

## Preregistered protocol — before timings

Compare A: archived `fb4497659fdf53b491fc5480d6588ec800e92e0a` with B: `542b505076e73552325566d45116f5d2d9b60024` compiler/rewatch source (HEAD `0af66c28b` differs only in campaign documentation). No indexed activation or optimization edits. Historical executables are missing; rebuild both with current identical Rust toolchain, default features, release profiles, unset RUSTFLAGS. This tests source stacks under today's toolchain, not identity with historical executable hashes.

Artifact root: `/tmp/rescript-measure-rebaseline-542`. Historical sources are a git archive, not a worktree. Save immutable binaries, hashes and raw logs there. All heavy commands hold `/tmp/rescript-tella-heavy.lock` via `lockf -k`.

Fixed corpus: Tella `66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa`, webapp directory `/Users/jake/dev/tella-fusion/packages/core/webapp`. Fixed runtime: this campaign worktree's `packages/@rescript/runtime`. Save exact backups and SHA-256 of the 18 pre-existing generated TypeScript modifications before building. Hash tracked source/config/lockfiles before/after; generated files are excluded from source invariance checks. Verify 3,248 compiled modules and a 5,048-file JS content manifest (outside node_modules) on each authoritative run. A different count or failed build is invalid and stops the run; retain failures. Output differences between stacks must be reported, not normalized away.

Clean policy: run the selected executable's `clean <webapp>` before each build, outside timing. Build command: `build --in-process --no-timing true <webapp>`, explicit RESCRIPT_BSC_EXE, RESCRIPT_RUNTIME and RAYON_NUM_THREADS. Do not clear OS filesystem caches or change runtime policy between variants. Initial screening warms filesystem caches. Clean is compiler-artifact clean, not cold disk/cache benchmarking.

Preset samples:
1. Hyperfine screening: 2 runs per stack/mode at w1/w12, cleanup in prepare. Not acceptance evidence.
2. Authoritative: 8 pairs per mode, w1 then w12 on odd pairs, reversed on even pairs; AB on odd pairs, BA on even pairs. `perf_counter_ns` encompasses the complete build process plus `/usr/bin/time -lp` wrapper; clean and manifest hashing excluded. Record CPU, RSS, raw OS metrics, status and manifests. No extending samples in response to significance. Report paired B-minus-A mean and 95% Student-t interval, plus mean/SD/median/range.
3. Scaling: faster valid w12 source stack, 3 runs each at 1/2/4/6/8/10/12/16, orders ascending, descending, ascending. Hardware is Apple Mac16,10, 4 performance + 6 efficiency cores; worker count is not equivalent CPU capacity. Separate knee confirmation: 4 alternating pairs of minimum-mean screen worker count versus 12 (versus 10 if winner is 12). No interpretation of oversubscription as homogeneous-core efficiency.
4. Separate fresh serial and parallel profiles on the faster valid stack, built-in phase/module/scheduler metrics, OS sampling and mimalloc statistics. Preserve raw outputs; do not count overlapping sampled stacks as additive savings or aggregate thread wall as elapsed time. Missing allocation/counter evidence remains a limitation. No production optimization in this session.

Machine at registration: macOS 15.6 (24G84), rustc/cargo 1.93.1, LLVM 21.1.8, Node 22.22.0, AC power; load 2.95/2.61/2.47. Xcode CommandLineTools selected. Record per-run load and power/thermal snapshots where available; do not infer bandwidth saturation from IPC or RSS alone.

Execution and ranked experiments follow.

## Results — fresh measurement, not a speedup

**The current production stack is slower than the historical source stack by 357ms at 12 workers. The reproduced fast baseline remains about 4.65s, not one second.** All 32 paired builds exited successfully, compiled 3,248 modules and produced the identical 5,048-file JS manifest `1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49`. No optimization was implemented or activated.

| Stack / workers | Mean ± SD (s) | Median | Min–max | User / system (s) | Peak RSS mean (GB) |
|---|---:|---:|---:|---:|---:|
| A / 1 | 19.0288 ± .1113 | 19.0452 | 18.7764–19.1622 | 18.110 / .858 | 2.087 |
| B / 1 | 20.2044 ± .1316 | 20.1990 | 19.9745–20.3604 | 19.283 / .859 | 2.085 |
| A / 12 | 4.6511 ± .0128 | 4.6563 | 4.6339–4.6690 | 38.710 / 2.074 | 2.957 |
| B / 12 | 5.0086 ± .0268 | 5.0080 | 4.9646–5.0501 | 41.075 / 2.121 | 3.040 |

Eight paired B-minus-A deltas: **+1.1756s [1.1181, 1.2330]** at w1 and **+.35748s [.33007, .38489]** at w12 (95% paired t intervals, seven degrees of freedom). These intervals describe this cohort, not variability across machines/days. A and B retire approximately 240.3B and 254.2B instructions at w1: the current stack does measurably more work. It is not merely clock noise.

Screening (two hyperfine runs each, separate batches): A 18.483/4.664s, B 19.826/5.042s at w1/w12. Screening is not pooled into the paired cohort. Serial drift is visible: early/late four-run A means 18.972/19.086s, B 20.156/20.253s. Parallel early/late A 4.655/4.647s, B 5.015/5.002s. Per-run load averages are retained; they include our own build load and rose above ten. AC power remained connected; final `pmset -g therm` reported no recorded thermal/performance warning, but supplied no continuous CPU power telemetry. We did not control background OS work or frequency.

Historical 18.688/4.615s is reasonably reproduced in parallel, not exactly in serial. A uses today's compiler toolchain and the **campaign runtime**, whereas the historical report used its own worktree runtime. This is a new same-toolchain source comparison. Its hashes intentionally differ from the missing historical executables. The older a023 campaign measurements are not pooled here.

### Scaling: there is no large worker-count win

Three fixed runs per worker count on A:

| Workers | Wall mean ± SD (s) | CPU user+system (s) | RSS (GB) |
|---:|---:|---:|---:|
| 1 | 19.1580 ± .1824 | 19.083 | 2.087 |
| 2 | 10.6441 ± .0020 | 20.920 | 2.156 |
| 4 | 6.4572 ± .0288 | 24.907 | 2.339 |
| 6 | 5.6905 ± .0190 | 31.557 | 2.506 |
| 8 | 5.1561 ± .0249 | 35.770 | 2.628 |
| 10 | 4.8207 ± .0221 | 38.550 | 2.834 |
| 12 | 4.6406 ± .0144 | 40.593 | 2.996 |
| 16 | 4.6010 ± .0426 | 41.330 | 3.150 |

Separate four-pair confirmation: w16 4.5916s versus w12 4.6196s; paired difference **−28.1ms [−48.9, −7.2]**, at roughly **226MB more RSS**. Twelve is the practical elbow; sixteen is slightly faster on this corpus/machine, not a major solution. Four performance plus six efficiency cores prevent homogeneous-core efficiency claims.

A's w1/w12 instructions remain approximately constant (240.30B/240.62B), while cycles rise 77.21B→134.64B and IPC falls 3.11→1.79. This is consistent with costly parallel execution, allocation and locality effects. It does **not** establish bandwidth saturation: memory-controller bandwidth, cache-miss counters and per-core frequency/IPC were unavailable. No privilege escalation was attempted; Instruments is unavailable under the selected CommandLineTools installation.

## Fresh profiles: where time and storage go

Profiles are separate executions. Their wall times are not substituted for acceptance samples. Existing timing/counter modes and allocator reporting are environment-gated; the additional census/trace binary was built only from disposable archived A sources. Timing binaries remained unchanged.

### Phases and the current-stack gap

| Phase | A serial aggregate (s) | B serial aggregate (s) | A w12 summed thread elapsed (s) |
|---|---:|---:|---:|
| Parse | 1.496 | 1.494 | 3.152 |
| Typecheck | 8.095 | 8.856 | 20.566 |
| Raw Lambda/lowering | 2.393 | 2.634 | 6.360 |
| Lambda optimization | 1.335 | 1.320 | 4.182 |
| JS/codegen | 1.721 | 1.706 | 4.105 |
| GenType | .288 | .291 | .786 |

Typechecking and raw lowering explain most of the observed serial source-stack difference. The inactive indexed optimizer is not responsible for a gain or demonstrated loss. `Layout__Types` alone took **263ms versus 579ms** typechecking at w1, and **512ms versus 1,465ms** at w12. A's typecheck module p50/p90/p99/max were .903/5.165/23.057/263.048ms (serial), versus 2.014/14.046/64.149/511.591ms (parallel). Other large modules include `Service__PublicClip`, `UI__LayoutPickerStructured`, `Service__PublicClipLegacy` and `LayoutDetail`; full rankings are in the aggregates.

The phase timer's serial residual is 3.77s. It includes untimed setup, copies, destruction, registry/output work and measurement gaps; it is **not a measured serialization phase**. In parallel, the timer prints percentages above 100% because its numerator is summed thread elapsed and its denominator is build wall. Those percentages are not used here. JS output writes were .258s serial / .697s summed parallel, with parallel per-module p99 1.601ms. OS `time` reported zero major page faults, swaps and block I/O operations: warm filesystem behavior, not proof of zero filesystem cost. Whole-clean timing includes compiler startup, package discovery, runtime bootstrap, parsing, dependencies and final outputs.

### Scheduling and critical dependencies

The isolated event/census profile measured AST+dependency barrier **2.012s serial / .304s parallel**, of which dependency analysis was 8.25/4.67ms. The larger serial barrier than the phase parse total includes surrounding work/PPX and instrumentation variation. Runtime bootstrap covered 107 modules in 93.1ms (w1) / 48.1ms (w12). “Serial” here means the one-worker project pool; the existing runtime bootstrap uses a minimum two-worker pool in both source stacks. Runtime is rebuilt from source into a new process registry (`rewatch/src/build/compile.rs:2410–2458`), not read from a reusable disk CMI/CMJ cache. Built-in runtime/module logs preserve the separate runtime timing.

The production counter profile had only **7.4ms idle-slot wait** at w12; the dispatcher's 4.08s wait mostly means workers were executing. The more intrusive dispatcher trace scheduled occupied slots for **96.7%** of the 12-worker scheduler interval (99.0% at w1). This includes queue residence/preemption, not CPU utilization. There is no evidence that a ready-queue tweak can remove seconds.

A longest-path calculation using actual signature dependency edges and measured dispatch-to-signature durations gives **1.624s at w12**, versus .695s with serial service costs. It runs through Webapi → TellaStd → geometry/schema → `Layout__Types` → Wasm/Layout → backend services → public-clip test helpers. Full paths and dispatch events are preserved. This is a **signature-DAG diagnostic**, not a hardware-independent lower bound or the complete JS-metadata DAG: queue residence is included, early signature publication is modeled, and later JS dependencies are not all reconstructed. It shows that concentrating only on many tiny modules misses a substantial dependent chain. The longest pre-JS task in this trace was `Layout__Types`, 872ms.

### Sampling and actual data-layout measurements

Full-duration `/usr/bin/sample` profiles captured 15,124 serial and 43,548 parallel compiler-worker samples. Exclusive counts are computed by subtracting direct children, avoiding recursive inclusive double counting. `_platform_memmove` accounts for **14.1% / 11.8%**; direct mimalloc frames **10.7% / 8.5%**. Memmove callers span `resolve_type_item_through_env`, portable signature internalization, Lambda constructors, alias removal, deep flatten and path formatting. This is broad data movement, not one universal cache miss. The matching B serial sample exposes `TypeExprRefMap::insert` among its top frames (187/15,715); portable internalization also rises. Sampling does not isolate a causal per-change gain.

Fresh measurement-only probes used context-owned `Cell` counters and an end-of-context arena census. No new unsafe code, RefCell, global mutable counters, force-order changes or source-tree walks in timing executables were introduced. All archive edits were removed afterward; the patch, scripts and separately named profiling executable remain reproducible.

Serial census across **3,511 destroyed contexts**:

- **36,914,670 allocated type nodes**. `TypeExpr` is **112B**, `TypeDesc` **96B**, `RowDesc` **96B**, `TypeArg` **80B**. These imply **4.135GB of logical inline node payload across context lifetimes**, not peak heap, DRAM traffic or measured allocation bytes. The arena's existing pointer index adds another indirection.
- End-of-context descriptors: 20.594M constructors (55.8%), 7.119M links (19.3%), 5.136M arrows (13.9%), .742M variants (2.0%). These are final descriptor shapes, not allocation-time variants; mutations can change them.
- **33,246,824 actual `get_desc` clone calls**. A 96B descriptor shape per call implies 3.192GB of logical inline clone payload, but compiler optimization may remove writes, and nested clone allocations are not fully counted. This is not a measured memory-bandwidth number.
- **58,277 portable internalizations**, **17,382,703 actual allocated nodes**, **.726s inclusive serial time** (1.664s summed w12). This accounts for 47.1% of census nodes; it overlaps typechecking and descriptor-copy work.
- Existing production counters: **55,502 whole signature copies / 1,460,718 signature items**. The largest callsite is archived `persistent_env.rs:3497`: 32,324 calls / 1,065,951 items. These are copy counts, not exclusive copy CPU; signature-content sharing or per-declaration laziness is not justified by them.
- Selected owned descriptor Vec buffers total **869.9MB capacity across lifetimes**. Collection-length buckets 0/1/2/3/4–8/>8: **14.691M / 8.754M / 2.603M / .700M / .545M / .126M**. These mix arrow args, constructor args, tuples, rows and poly/package args; they do not justify the same inline capacity for every collection.
- A second census separates arrow storage: **660.5MB argument-vector capacity**; **6.927M unlabeled / .815M labeled / .468M optional arguments**. **84.4% are unlabeled**, yet every argument reserves the 80B layout dictated by `ArgLabel`'s located-string payload. A 16B hot argument representation would reduce the *same counted capacity* by about **528MB**, before cold label storage. That is a storage bound, not a speedup prediction.
- `Lambda` is **464B**, JS `Expression` **256B**, JS `ExpressionDesc` **192B**. These are measured sizes, but no fresh exhaustive Lambda node/lifetime census was obtained. Do not multiply them by the old inlining-size heuristic or claim total backend memory saved.
- Already-active sparse records handled 10,421/10,422 large records, with 4,743,290 logical labels versus only 35,129 populated fields. That win already executes; it is not new headroom.

Each census visits every type arena entry once at context destruction, including unreachable nodes retained by the arena. Owned selected Vec buffers are counted once per owner; no graph recursion or shared-payload duplication occurs in that subset. It does **not** account for all nested paths/strings, other owner roots, live reachability, Lambda metadata/export roots, total allocator requests or peak retained heap. Mimalloc reported peak commit 2.1GiB/3.1GiB, not a callsite allocation profile. These missing measurements limit architectural savings claims.

Instrumentation overhead is not negligible: census-only wall was 19.69/4.70s against paired A means 19.029/4.651s (about +3.5%/+1.1%); census+dispatcher trace was 20.01/4.91s (+5.2%/+5.6%). These are single-run diagnostics, not paired overhead estimates. The added clone counter runs on each clone; treat probe time as perturbed. The initial three-second serial sample was early-phase-biased, so it was retained but replaced for interpretation by a full-duration sample.

## Ranked experiments and decision

Ranking distinguishes measured work from hypothetical savings. The bounds below overlap and **must not be added**. Every retained experiment needs exact OCaml-equivalent type identity/sharing, traversal, lazy whole-component forcing and mutation behavior; fresh release typedtree/raw/optimized Lambda/JS/diagnostic gates plus fixed-corpus paired timing remain mandatory. Tella JS hashes alone are not compiler acceptance.

### 1. Typechecker copy/storage work — highest-impact measured family

**Evidence:** 8.095s serial typechecking on A, 20.566s summed parallel; 36.9M arena nodes, 33.2M descriptor clones, 80B sparse argument payloads, hot copy/allocation samples, and the measured B typecheck/critical-module regression. A 25% reduction in this phase would remove about 2s serial work; translating through the observed whole-build speedup gives a rough .5s parallel *scenario*, not a forecast. Faster dependent modules and lower parallel inflation could change that ratio.

**First implementation experiment on the current branch: identity-exact hybrid `TypeExprRefMap` storage**, isolated from other historical changes. Compare current dense `offset + Vec<Option<T>>` against A's tiny-inline/dense/sparse representation at `compiler-rust/src/types/type_expr.rs:278+`. This is not a name cache or semantic shortcut: keys stay physical `TypeExprRef` identity. B's `insert` is sampled hot; the source stacks demonstrably differ here. Reimplement/review the storage change on the existing branch; do not integrate the 70-commit historical stack or cherry-pick around sibling work.

Planning range: **0–.36s parallel / 0–1.18s serial recovered**, using the observed entire stack gap as a conservative opportunity envelope, **not attribution to this map**. It can regress; no per-map capacity histogram on B was obtained. The decisive falsification is a bounded one-change build, actual map length/span/capacity counters in a separate probe binary, then the same fixed paired test. Stop retaining it if timing does not improve. Snapshot mutation trails, flattened-component copying and single-write portable internalization also differ between A and B, so success/failure cannot be inferred from the aggregate comparison. Source references: OCaml physical identity/allocation `compiler/ml/types.ml:22`, `btype.ml:46–48`; copy/substitution semantics `subst.ml:241–309`. Confidence: high that current typechecking has recoverable stack-level headroom, medium that this map explains a useful part.

**Next new-speed experiment beyond A:** compact `TypeArg` hot storage, retaining cold `Located<String>` labels in explicit owned/arena storage with the same names and locations. The measured 84.4% unlabeled rate and 660.5MB owned vector capacity justify this more strongly than arbitrary struct shrinking. Preserve `Tarrow` argument ordering, labels, locations and n-ary boundaries exactly (`compiler/ml/types.ml`, `ctype.ml` and `typecore.ml` argument traversal); no RC per node, unsafe or interning-based identity substitution. Target a ≤16B hot argument, measure cold-label bytes too. The 528MB gross capacity reduction before cold storage is roughly 10.5% of counted node-plus-selected-buffer payload; equal-cost proportional scaling would suggest only around .2s parallel type-phase savings. Use **0–.3s as a planning range including zero**, not a measured gain. Clone traffic may amplify it, extra indirection may erase it. This is preferable to indiscriminately boxing every type variant. Confidence: high storage opportunity, low-to-medium timing prediction.

### 2. Recursive Lambda/JS storage and lifetime — large ceiling, incomplete retention evidence

**Evidence:** A raw lowering + optimization + codegen totals **5.450s serial**, about 29% of build wall; large 464B/256B node layouts and repeated backend memmove/allocation samples. Optimization alone is only **1.335s**. Eliminating the entire recorded backend would be an impossible upper scenario, not a 5.45s available saving; translating all of it through present speedup gives roughly 1.3s parallel, with unknown dependency/scaling effects.

M6 can matter only when raw lowering, all optimization passes and the JS consumer execute through the same owned indexed representation without recursive materialization. Its inactive state provides **no current benefit**. An actual halving of this whole backend would suggest roughly .65s parallel in a proportional scenario; no fresh data establishes that halving is achievable. Planning range for activation remains **zero through that scenario**, including regression risk.

Before retaining M6, collect allocation-site counts and peak reachable/retained/unreachable storage across **all** optimizer, grouping, export, CMJ and JS owner roots. Shared payloads must be counted once. Arena generations can retain more memory than promptly dropped recursive trees; node-size tests do not answer this. Preserve OCaml pass order, identifier generation, effects, warnings, CMJ query/inlining boundaries and final JS output (`compiler/core/lam_compile.ml`, `lam_pass_*`, `lam_stats_export.ml`). Bound the experiment to production activation after completion and review, not another inactive refactor. Confidence: medium that backend movement is costly, low on the indexed design's net end-to-end gain until retention data exists. This ranks behind typechecking, despite sunk M6 effort.

### 3. Portable signature materialization — measurable but smaller subset

**Evidence:** 17.38M node allocations in .726s serial inclusive internalization, plus repeated signature copying. A already removes placeholder writes; B still allocates placeholders and then sets descriptors (`cmi/portable_types.rs:934+`). The first bounded B probe is direct contiguous allocation with the same DFS order/ids, not lazy per-declaration signatures. Review against `subst.ml:351–400` and `btype.ml:46–48` and retain only after parity plus timing. The entire A internalization timer corresponds to roughly .18s parallel under proportional scaling; even deleting all of it would not explain seconds. On A, avoiding clone/capacity overhead while preserving whole-component materialization is the remaining storage question. On B, the actual removed-write opportunity is smaller than deleting internalization; **0–.18s** is a loose planning envelope, not a forecast. This overlaps rank 1 and must not be added to it. Rejected selective forcing/signature-sharing schemes remain rejected. Confidence: high allocation count, medium mechanism, low isolated wall gain.

### 4. Frontend barrier, outputs and worker tuning — bounded secondary work

The measured parallel parse/deps barrier is about **.304s**; full overlap is its best-case wall headroom, not a likely saving. At high occupancy, overlap can worsen contention. Any parse/compile pipeline must preserve PPX behavior, dependency discovery and diagnostics (`rewatch/src/build.rs:409–450`) and should first prove spare capacity or faster critical signature release. JS writes total only .258s serial. Sixteen workers already established just **28ms** improvement with more memory. These do not plausibly produce the required multi-second gain. No scheduling change was made.

### Is one second feasible?

**Not with the measured opportunities alone, and not by finishing only M6.** Today's fast source stack consumes about 19s serial work and 41s CPU at w12 on ten heterogeneous cores. A recorded signature chain alone takes 1.62s under parallel conditions, before accounting for the full JS dependency graph. That is not a universal physical floor, but it rejects a claim that scheduling alone gets to 1s. Even a hypothetical 50% reduction in all recorded backend work leaves the majority of the build. Reaching 1s would require a substantial reduction in typechecking/materialization *and* backend work, and improved parallel execution costs. No additive headroom calculation here establishes it.

## Reproduction, artifacts and limitations

Durable lightweight evidence:

- [Raw per-run samples](measurement-542/runs.jsonl): all 32 paired, 24 scaling and 8 confirmation builds; exit status, scope/hash, CPU/RSS/counters and load.
- [Statistics, module distributions and dependency trace aggregates](measurement-542/aggregates.json).
- [Source/toolchain/binary provenance](measurement-542/provenance.json), [serial census](measurement-542/census-summary-w1.json), [parallel census](measurement-542/census-summary-w12.json), [argument census](measurement-542/argument-census.json), [sample callsite owners](measurement-542/sample-owners.json).
- Scripts: `scripts/measurement_rebaseline.py`, `measurement_profiles.py`, `measurement_instrument_archive.py`, `measurement_analyze.py`. Run from this worktree. Every heavy invocation is wrapped as:
  ```sh
  /usr/bin/lockf -k /tmp/rescript-tella-heavy.lock /bin/bash -lc 'python3 scripts/measurement_rebaseline.py paired'
  ```
  Use a new dedicated artifact directory for a new campaign; the saved `runs.jsonl` is append-only. The preregistered run order is encoded in the script. Hyperfine screening uses `--prepare` for cleanup; high-resolution timing includes only `/usr/bin/time -lp` plus the build process. Build both crates with `/Users/jake/.cargo/bin/cargo build --release --locked --manifest-path ...`, unset RUSTFLAGS, then copy binaries before profiling. The archive instrumentation script targets only `/tmp/rescript-measure-rebaseline-542/historical-source`; apply it to clean archived sources, rebuild rewatch, save as `rescript-census-trace`, and restore those four archive source files from exact `git show fb4497659:<path>` bytes afterward. It must never be applied to the shared source tree.

Local private raw artifacts remain at `/tmp/rescript-measure-rebaseline-542/`: `bin/`, original before/after input manifests, individual generated-file backups, every JS manifest, build/profiling/timing logs, full sample call graphs and `measurement-only.patch`. The raw manifests include resolved dependency/PPX content and private module paths; they are deliberately not committed. Nothing was uploaded. `/tmp` is not permanent storage: the committed hashes/statistics/scripts survive, but exact raw traces require preserving that local directory through an organization-controlled channel.

Compiler source B is exactly 542; the later parent HEAD changed documentation only. Immutable timing executable hashes:

| Binary | SHA-256 |
|---|---|
| A bsc | `7c39a09c163088ac7db372ff8139fa62e2a9b76960eafccfe4ed2385f9172ca0` |
| A rewatch | `0187abee145aebdcc1b43db8d60e28ed851840dd3c75397959f64223420c4332` |
| B bsc | `88a0fb844cdf437420e6c432aa997300d6e71e527ffc4b3e5473a85a4d325641` |
| B rewatch | `f291b43ab5c5f942eff934fecae3881406d26e989ec93454562c5ed2ad57ef32` |

**Input checker correction:** the original broad JSON inventory flagged 11 `lib/bs/compiler-info.json` files. Original before/after manifests remain intact. Source inspection established these are generated compiler metadata (`rewatch/src/build/compiler_info.rs:128+`, `build.rs:584+`), also read to trigger cleanup on compiler/config mismatch (`compiler_info.rs:35–122`). They are not semantic compiler inputs and cannot bypass the explicit clean/full in-process builds. Both variants use the same selected-compiler clean policy; any metadata checking/cleanup within build remains timed. Only these exact generated-output paths were classified out of the invariance check. All genuine tracked/resolved sources, configs, locks and PPX binaries in the 41,573-path inventory stayed identical. No cohort rerun or broad JSON normalization occurred.

All 18 pre-existing `.gen.ts` files were backed up individually and restored from exact backups only where our builds changed them. Tella still has exactly those 18 modifications. No compiler optimization/source change, indexed activation, dependency upgrade, PR edit, push or merge occurred. Python scripts pass `py_compile`; both production release builds succeeded. No full current-head test/parity acceptance is claimed. The known release `benchmark_index` timing failure and external OCaml Tella `bs-css`/Belt blocker remain unresolved and were not retried or suppressed.

Remaining uncertainty is explicit: no exhaustive allocation-callsite/clone-byte profile across all owner roots, no full JS-metadata critical-path reconstruction, no isolated attribution of the A/B source gap, and no validated optimization gain. The measurement task establishes a fresh comparison, profiles, concrete layout/copy evidence and the next bounded experiments; it does not establish a one-second compiler.
