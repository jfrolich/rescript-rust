# Architecture benchmarks

## Preregistration

Owner bks-86001e17-97c6-78b7-b1c7-6d0030a78065, starting clean e4370df0a. No production refactor, M6 activation, push, PR or subworkers. Parent selects implementation after independent OCaml and literature reports. Parent notified to stop documentation edits before frozen inventories.

Question: which larger change removes actual compiler work? Recovering the historical source-stack gap is distinct from beating A. Prior descriptor counts already establish copy frequency; repeating that census does not answer the causal question. Unanswered: current A/D instruction and phase difference, running samples in instancing/substitution/Env/Raw versus allocator/copy/drop, and shared reference-count work not captured by owned-byte counters. Sampling may not resolve all of these.

Controls are existing read-only same-toolchain release binaries: A source fb4497659fdf53b491fc5480d6588ec800e92e0a, D source 5dc38ba2154e158d43436ada2142a13eef9f2c8c. A bsc 7c39a09c163088ac7db372ff8139fa62e2a9b76960eafccfe4ed2385f9172ca0, rescript 0187abee145aebdcc1b43db8d60e28ed851840dd3c75397959f64223420c4332. D bsc a5ed9a622e3b787a8dae0cb5228a5eb5717849314d0af40c05f9689c6a6788af, rescript 5fe8158df5d3201d4cf07fd962cf61b22edf63874b03bfd5328e1fe16f47c3c4. Symlink controls into dedicated durable artifacts; never overwrite or chmod originals. Ordinary release targets remain D. Rust 1.93.1, LLVM 21.1.8, default release features/profiles; preserve original build provenance and current environment.

Artifacts: /Users/jake/.opensession/artifacts/rescript-performance-20260905/architecture-round. Reuse measurement_rebaseline.py and exact generated-output inventory policy from snapshot_projections_measure.py. Before timing, verify controls/source/runtime/toolchain, exact Tella pin 66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa and all eighteen original gen.ts backups against prior verified backups. Capture resolved tracked and dependency/config/PPX inventory including symlinks after setup and selected clean. Verify before report/data edits. Only eleven exact compiler-info outputs and webapp .sourcedirs have existing writer proof; no broad exclusions or cosmetic reruns.

Fixed timing: two hyperfine screen repetitions separately per A/D w1/w12 cell, then eight pairs per mode, 32 full builds. Odd pairs A/D with w1 first; even D/A with w12 first. No added/excluded samples, extension or pooling. Selected clean outside timer, full build --in-process --no-timing true, explicit BSC/runtime/RAYON, warm FS without purge. Runtime is this worktree's packages/@rescript/runtime, 107 source-bootstrap modules per process with minimum two runtime workers. perf_counter_ns + time -lp covers full process; record wall/user/sys/RSS/instructions/cycles/load/exits/counts/hashes. Every build must exit zero, compile 3248 modules and reproduce 5048 JS files digest 1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49. Report hyperfine mean/SD/min/max separately and paired Student-t intervals with seven degrees of freedom.

Diagnostics registered before heavy work: four whole-duration samples in order A w1, D w1, D w12, A w12. Existing /usr/bin/sample, interval 1ms, requested durations 35s serial and 15s parallel, bounded 90s wrapper; independently await child exit to record process elapsed before sample symbolication finishes. Attach latency and sample header coverage are explicit limitations. Whole duration means request extends beyond expected child duration, not zero missed startup. Uninstrumented controls only. Partition exclusive leaf samples into blocking/wait and running/unknown; retain thread roles and raw frames. Inclusive semantic families overlap and cannot be added. No CPU milliseconds inferred from clone counts or sample wrapper time.

Four further separate phase diagnostics, same order, with existing RESCRIPT_PHASE_TIMINGS=1, RESCRIPT_MODULE_TIMINGS=1, RESCRIPT_SCHEDULER_COUNTERS=1. No source instrumentation or archive build needed for these existing modes. They compare current phase/module costs, not fresh allocation census. Summed thread elapsed is neither wall time nor CPU utilization. No signature-only DAG floor. Additional probes require a separate preregistration before their outcomes; no open-ended diagnostic repetition. Capability inspection found sample and hyperfine 1.20.0. xctrace is a stub that fails because CommandLineTools is selected; no install, permissions or toolchain changes attempted.

All heavy commands hold /usr/bin/lockf -k /tmp/rescript-tella-heavy.lock via /bin/bash -lc. No full tests repeated for unchanged D. Inherited D/E gates remain labeled by head; missing Belt external OCaml and standalone TypeArg exact JS declaration-order mismatch remain red and unwaived. One-second target unproven. Preserve failures and restore eighteen original modified files. No archived or normal source changes planned.

## Separate graph diagnostic registration

After the completed timing and eight initial diagnostics, register exactly four additional builds: immutable D w1, archived probe P w1, D w12, P w12. No acceptance timing added. Fresh A/D already establishes about 11.90B/12.19B more D instructions; this D-only probe cannot attribute that difference. Existing snapshot census misses CopyAction's direct payload clones. Measure actual copy_type_cached entry count, node-cache probes/hits, row-marker hits, action variants, copied container element counts and explicit path-bearing action counts. Measure outermost copy scope elapsed and allocations during that scope, plus cache length/capacity at outermost scope completion. These are scope endpoints, not unique cache lifetimes or total visited-node identities. An entry is an edge traversal, not a unique node; generic cache hits identify revisits inside the active copy cache. No set added to deduplicate all graph entries. No CPU milliseconds inferred from these counters.

Only a fresh archived D source is instrumented, using TypeContext-owned Cell counters and explicit scoped depth. Preserve source archive before/after, patch, compiler/rewatch binaries and logs durably. Build rewatch release once with --locked and the existing default feature/profile/toolchain, 600s timeout. Do not build or overwrite normal targets. No new unsafe, global/thread-local mutable counters, force or sharing change. Output per destroyed context, no per-node logging. Check aggregate invariants, full corpus JS and resolved inventories; comparison with adjacent immutable D estimates single-run probe overhead only. No fresh descriptor census, allocator install or privileged profiler. Available disk is about4.4GiB, so use an independent release target without duplicating prior target caches. Restore all archived source files and eighteen generated originals after diagnostics.

The initial samples show substantial perturbation at w12, about8.1–8.5s child duration versus4.6–4.9s unprofiled. They are qualitative sampled work attribution, not CPU-time forecasts. swtch_pri/thread_switch are yield/wait, not running work; raw_lambda must be included in Raw lowering classification. These analyzer corrections require no repeat runs.

## Results and decision

**The best next large investigation is component/Env ownership and construction, with phase-owned Raw/Lambda storage second. Neither has an established end-to-end saving yet. A native copy-marker rewrite alone is not supported as the main large performance change.** The additional actual-copy probe makes that distinction stronger; it does not establish a complete instance-lifetime cost.

No production code changed. M6 remains paused. Parent should choose one bounded implementation only after resolving the attribution gaps below. A larger patch is not itself evidence of a larger gain.

### Fresh matched A/D builds

All eight screen builds and32 paired builds exited0, compiled3248 modules and reproduced the required5048-file JS digest. D lost all eight pairs in each mode. No sample was repeated, dropped or added.

| Stack / project workers | Wall mean ± SD, s | Median | Min–max | User / system mean, s | Peak RSS mean, GB |
|---|---:|---:|---:|---:|---:|
| A /1 |18.265164 ± .110758|18.263181|18.094869–18.452500|17.3575 / .8300|2.088497|
| D /1 |19.200754 ± .165177|19.233049|18.943179–19.418475|18.2925 / .8313|2.080678|
| A /12 |4.600557 ± .037185|4.591444|4.560554–4.678858|39.3513 /2.1700|2.964173|
| D /12 |4.856618 ± .037467|4.851794|4.816582–4.938216|40.8425 /2.1613|3.012119|

Paired D-minus-A,95% Student-t intervals with seven degrees of freedom:

- w1 **+935.59ms [846.76,1024.42]**,5.12% slower.
- w12 **+256.06ms [244.54,267.58]**,5.57% slower.

This is whole-stack recovery headroom, not attribution to any one optimization. Same-toolchain A reproduces the historical parallel range; its old missing executable was not used. The faster serial absolute times than earlier rounds illustrate why dates/cohorts are not pooled. No new best compiler implementation was produced.

Retired instructions A/D are240.346/252.246B serial and240.840/253.026B parallel. D performs about11.90B/12.19B more instructions. Cycles are75.890/79.405B serial and136.390/141.371B parallel. Their difference is real process work, but sampling does not assign those extra instructions to a source change. Parallel CPU user+system increases1.483s while wall increases.256s. IPC/RSS do not establish memory-bandwidth saturation, CPU frequency or per-core utilization.

Separate two-run hyperfine screens, mean ± SD and min–max in seconds:

| Cell | Mean ± SD | Min–max |
|---|---:|---:|
| A w1|17.939050 ± .112199|17.859713–18.018387|
| D w1|18.886373 ± .157172|18.775235–18.997510|
| A w12|4.618861 ± .010356|4.611539–4.626184|
| D w12|4.855577 ± .022467|4.839691–4.871464|

Screening is not pooled with paired data. Screen logs retain time-lp metrics and hyperfine full-process times; unlike paired rows, the reused screening helper did not capture per-screen load or a separate perf_counter_ns value. All paired rows contain those fields. No replacement screens were run to fill that reporting limitation.

### Current phase evidence

Four separate existing-instrumentation builds passed full output checks. Times below are phase aggregates, milliseconds. Parallel columns sum elapsed time across workers, not wall time or CPU time.

| Phase | A w1 | D w1 | A w12 sum | D w12 sum |
|---|---:|---:|---:|---:|
| Parse|1491.760|1494.438|3069.289|3052.096|
| Typecheck|7765.990|8389.804|20346.447|21362.305|
| Raw/lowering|2312.992|2566.559|5867.274|6704.605|
| Lambda optimization|1303.054|1294.069|4389.459|4446.164|
| Codegen|1651.280|1635.864|4271.795|4221.967|
| GenType|266.509|267.239|707.791|727.368|

Current typechecking differs by623.8ms serial; Raw/lowering differs by253.6ms. These single phase diagnostics corroborate where to investigate the stack gap; they do not causally decompose the fixed paired935.6ms. Residual serial time is3767.4ms A and3746.8ms D, including setup, registry, allocation/destruction and untimed work. Do not call it a serialization phase.

`Layout__Types` typecheck is262.523/586.593ms A/D serial and447.455/1418.870ms parallel. Its serial difference alone is324ms, over half the phase's623.8ms difference in these diagnostic runs. That identifies an important dependent module for a falsification experiment, not a full-JS critical-path measurement. No new DAG claim is made.

### Whole-duration samples and their limits

All four uninstrumented control profile builds passed full output checks. Requested35s/15s windows exceed actual child lifetimes. Header launch-to-sampling timestamps miss51ms A w1,33ms D w1,33ms D w12 and35ms A w12 at startup. No end timestamp or uniform active-CPU coverage is supplied by sample; no claim of gap-free coverage follows. The sampler completed naturally after process exit.

| Cell | Observed child duration, s | Wrapper including symbolication, s | Worker samples | Explicit wait/yield samples |
|---|---:|---:|---:|---:|
| A w1|19.655365|20.439806|14613|201|
| D w1|20.665331|21.395025|15240|185|
| D w12|8.504948|10.369452|47445|5563|
| A w12|8.085069|9.845697|44196|4244|

Child duration is measured independently of sampler completion, but Popen.wait timeout polling can delay observed exit by up to roughly50ms. These are diagnostics, not compiler acceptance times. Parallel sampling perturbs execution severely, about1.75× the unprofiled cohort means. Symbolication adds another.7–1.9s; that is not compiler wall time.

The parser subtracts direct-child counts to get exclusive leaf samples and verifies total conservation. Main/other threads are retained separately and mostly wait. Compiler-worker wait includes condition variables, mutex waits, ulock, semaphores, Mach/kevent and swtch_pri/thread_switch yielding. Remaining samples are **running or unknown**, not proven CPU-active samples; e.g. an open syscall may block.

Among remaining worker samples, A/D serial memory-copy leaves account for16.27/15.50%, allocator leaves10.64/11.22%, drop leaves7.92/7.66%. Parallel values are13.97/14.47%,10.16/9.89%,8.15/8.12%. These are one disjoint leaf-mechanism partition, not removable-work estimates. Explicit Arc clone/drop leaves account for only.50–.94%; Path/SmolStr reference-count operations can inline into other frames, so this is not total atomic/refcount cost. Path drop itself is a prominent leaf; it is categorized as drop rather than being double-counted as Arc work.

A separate nearest-semantic-ancestor partition assigns roughly23–25% to Env,28–29% to other typechecking,4% to portable operations,2% to instancing,1–2% to substitution,7–8% to Raw and17–18% to other backend. Mechanism and semantic percentages describe the same samples and must not be added. These heuristic names are not phase boundaries: Env/type operations inside Raw appear under Env/type, and outlined/inlined symbols limit attribution.

Selected non-additive running stack unions in D w1/w12: `resolve_type_item_through_env`945/2708, `env_lazy`1173/3148, `PersistentEnv::clone`242/1007, internalization527/1443, Raw1969/5863. Raw's union includes Env calls and differs from the nearest-ancestor partition. These counts identify source paths to examine, not CPU milliseconds or independently summable costs. Raw and Env are both substantial enough to warrant architectural work; no one sampled family explains12B extra instructions.

### Actual copy graph diagnostic

The separately registered four D/P builds all passed. D/P serial walls18.761230/19.080779s and parallel4.820512/4.845540s give single-run probe overhead differences+319.5/+25.0ms. They are not paired estimates or optimization results. P retires about3.87B/3.83B extra instructions because the probe itself counts/times work.

Both modes emitted3511 destroyed contexts. Counters observe actual CopyAction construction in `ctype.rs:10325–10845`, including direct borrow_desc payload clones omitted by the prior descriptor census. Serial findings:

- 9,591,316 copy entries and node-cache probes;575,403 cache hits, about6%. Entries are graph-edge traversals, not globally unique nodes.
- 3,857,831 non-generic identity actions,946,036 variable actions,3,434,242 constructor actions,587,265 arrows and76,115 variants. No row-more-marker or variant-marker hit occurred in this corpus; that is not proof those semantic paths are unnecessary.
- 5,943,446 outermost copy scopes;5,296,088 nodes allocated during them, of36,914,484 total arena nodes across destroyed contexts. The scoped allocation count can include nested Env/abbreviation work. It is not peak live memory.
- 6,310,810 summed map lengths and10,233,632 capacities at outer-scope endpoints; largest length386. Repeated roots can use the same cache, so these are not unique cache counts or cumulative allocator bytes.
- 3,141,080 selected copied container elements;974,762 arrow elements including168,266 labeled elements;3,462,111 path-bearing actions. These are actual action requests, not nested owned bytes, observed malloc calls or measured Arc operations. Referenced Path/Ident storage may be shared.

Outermost copy-function elapsed totals **416.53ms serial /954.30ms summed parallel**, including instrumentation and nested operations. Cache creation/destruction outside copy_type_cached is excluded. This is neither complete instance-lifetime cost nor an upper bound on it. It demotes a map-only mechanism as the obvious large target, while leaving that excluded lifecycle attribution unresolved. Independent sample copy unions are similarly modest. No claim that all instancing costs416ms follows.

Parallel entries/actions mostly match serial, with two additional cache hits and two fewer constructor actions/allocations. Total arena nodes differ by10609. Preserve this scheduling-dependent difference rather than pooling modes. Every context satisfies entries = row-marker hits + probes = all actions + cache hits + marker hits. The probe is not a semantic change, but panic unwinding does not restore its diagnostic depth counter; all recorded full builds exited normally. The archive was restored after the runs.

## Ranked larger opportunities and falsification

### 1. Component/Env ownership and one mandatory component-construction boundary

This has the strongest current breadth: about23% of non-wait/unknown worker samples fall in the Env semantic family, with work in both typechecking and Raw. `ctype.rs:2370–2480` resolves a type through a local PersistentEnv clone, clones the returned declaration and may perform a second alias lookup. `env_lazy.rs:1378–1678` obtains raw signatures, qualifies them, applies child substitutions and constructs the evolving environment and child thunks. `typecore.rs:26011+` and32124+ implement copy/qualification paths. This is broader than five descriptor projections.

The defensible large change is an explicit per-compilation owner for component descriptors and lookup state, constructing the final required substituted component image once at its existing force boundary, with handles/borrows for repeated descriptor queries. It is **not** cross-environment signature caching, structural interning, selective per-item forcing, suppressing forces or sharing mutable types between compilation contexts. PersistentEnv already shares several registry maps through Arc; merely replacing those again removes nothing. Its remaining owned override/hidden/prepared-alias state and declaration copies need actual lifetime attribution.

Native contract: `env.ml:1472–1559` captures env/sub/path/module type, scrapes aliases, prefixes identifiers, substitutes values/types and creates separate lazy module/child components while extending the working environment. `subst.ml:130–165` preserves physical copy identities and stub order;303–309 defines value substitution. A new owner must preserve probe-versus-force API boundaries, exact captured Env, separate child/module-declaration thunk identities, mutation sharing and stamp order. The current source contains already-qualified caching; do not infer that every source clone is a duplicate graph allocation.

**Missing decisive evidence:** inclusive counts/time for complete component construction and descriptor lookup lifetimes, number of repeated same-identity queries versus newly forced components, and bytes/retained roots of copied declaration/Env state. Present samples cannot separate required traversal from transport copying or identify how much of `Layout__Types`'324ms serial regression belongs here. Before implementation selection, parent should require that accounting for the proposed boundary, then a bounded owner prototype with exact identity/force traces and full output gates. Falsify it if query/construction work or instructions do not fall, or if fewer copies merely retain more graphs and parallel wall does not improve. Confidence high in affected family, medium in ownership direction, low in numerical saving.

### 2. Phase-owned Raw/Lambda representation across the real conversion

D's Raw+optimization+codegen is5.496s serial diagnostic work; optimization alone is1.294s. This is large enough that changing the whole producer/consumer ownership can matter more than one clone site. The Raw running union is13.1/14.0% of D's remaining worker samples and includes Env operations; it is not independent of rank1.

Keep the actual OCaml stages: `js_implementation.ml:160–166` invokes Translmod, and `lam_compile_main.ml:278` invokes `Lam_convert.convert`. `lam_convert.ml:357–660` performs real transformations, including FFI, aliases/exits, optional names, exception wrapping, dependencies and smart constructors. Rust `raw_lambda/lower.rs` explicitly ports that stage. An indexed producer/consumer may remove recursive storage transport and destruction; it must not delete or reorder this logical transformation, fresh identifiers, warning order or CMJ query/inlining boundaries.

**Missing decisive evidence:** fresh counts and allocator/ownership attribution for Raw construction, Raw→Lambda conversion, optimizer replacements and JS construction; reachable versus unreachable storage at every phase boundary including CMJ/export/debug roots. Large464B/256B node sizes and memmove samples alone do not establish retained volume. An arena can keep obsolete generations alive longer. Require these before resuming M6. Falsify a prototype if it ends with recursive materialization, changes any transformation/query ordering, or fails to reduce full-process work and fixed parallel wall. Confidence high in broad phase weight, low-to-medium in indexed net benefit until lifetimes are measured.

### 3. Native copy frames or type-node storage, not another tiny borrow batch

`ctype.ml:725–865` uses temporary Tsubst and row-more markers, with cleanup at865–887; Rust uses CopyCache and direct CopyAction payload ownership. A faithful context-owned copy frame could remove repeated map work and restore a closer native mechanism, but the fresh probe does not justify this alone as the principal speed effort. Required destination labels/paths remain owned even if saved descriptors move. Partial types, recursive rows, abbreviation scopes, GADT effects, error cleanup and native evaluation order must remain exact. No unmeasured speed forecast.

A hot-header/cold-descriptor arena is a larger alternative, but needs access affinity and allocation/lifetime evidence that this round did not obtain.36.9M arena nodes and broad copy/drop samples do not prove SoA or boxing wins. Current indexed handles and sparse representations are already active and must not be counted as new work removed.

Historical mutation journaling's focused63.5→2.6ms improvement but near-flat full Tella result is contrary macro evidence. Direct-final portable internalization's roughly30ms prior parallel result is a recovery mechanism, not a new large opportunity. The five-site E experiment's serial gain but inconclusive parallel result further rejects ranking by logical clone volume. Neither is automatically resumed.

Public research supports these conditional mechanisms, not predicted Tella gains. See parent-owned [COMPILER_PERFORMANCE_RESEARCH.md](COMPILER_PERFORMANCE_RESEARCH.md), particularly [Sampson's flattening experiment](https://www.cs.cornell.edu/~asampson/blog/flattening.html), [rustc ownership documentation](https://rustc-dev-guide.rust-lang.org/memory.html) and [Roofline's actual DRAM-byte model](https://www.osti.gov/servlets/purl/1407078). This owner used the separately supplied read-only research and checked local reference source; it did not rerun public research with private queries.

### One second

A's4.6006s requires removing3.6006s,78.3% of current elapsed time, to reach1s on this protocol. D first has.2561s historical-stack recovery to make. The prior TypeArg point gain around49ms and rejected E parallel point gain around24ms are two orders of magnitude smaller than the3.6s gap. They are not additive experiments and do not establish a speed ceiling. Even the entire observed copy-function timer is not complete instancing lifetime and cannot be converted into parallel savings. No evidence here establishes one-second feasibility or impossibility. It requires major work reduction across broad families, not choosing more tiny borrows from a census.

## Preservation, validation and release

Durable raw evidence is `/Users/jake/.opensession/artifacts/rescript-performance-20260905/architecture-round`; compact committed data is `architecture-e4370/`. A/D links resolve directly to existing durable read-only controls, never /tmp. Hashes and permissions are rechecked, not overwritten. Probe rescript is separately saved under graph/bin. Original archive tar, two changed source originals, patch and before/instrumented/restored414-file source hashes preserve the probe. Cargo target caches are excluded from the evidence manifest because the archive, patch and separate executable are sufficient reproduction artifacts.

Both initial timing/diagnostic inventories were41986→41998, exactly the eleven proven compiler-info files and .sourcedirs. The separate graph inventory had the same counts and exact allowed paths. Parent documentation edits occurred only between frozen windows. Verification preceded report/summary edits. Writers are `rewatch/src/build/compiler_info.rs:127–211` and sourcedirs output through `rewatch/src/build.rs:517–518`; compiler-info is also read for clean policy. No general JSON waiver, source mirror exclusion, failed-inventory rerun or extra benchmark was used.

Restoration verifies normal compiler/rewatch source and ordinary release binaries against D, archive source against its saved original, runtime input hashes, Tella pin/status and all eighteen gen.ts hashes/backups. No normal binary build, full-test repetition, source/config/dependency/lock upgrade or production refactor occurred. Probe release build and all graph counter invariants passed; all52 full builds across screens, paired, initial diagnostics and graph diagnostics passed the same complete output digest. The final compact summaries and scripts were checked with Python compilation and executed assertions.

D's inherited tests/parity and E's later gates remain historical, head-specific evidence, not rerun claims. External missing Belt and standalone TypeArg exact-JS declaration-order mismatch remain red and unwaived. The old passing benchmark harness did not expose its ratio; E's single1.17 observation does not prove instability fixed. No merge, push, PR change or new implementation is authorized by this round.

Tool limitations: local read rejected the external skill file, then bash read it; xctrace was unavailable under CommandLineTools and no installation was attempted. sample perturbation and excluded cache-lifecycle timing are material limits, retained rather than hidden. No profiling/build process remains after completion. All compiler/shared-worktree/heavy measurement ownership is RELEASED at final handoff; parent owns the next selection, and no next task is started.
