# Descriptor snapshot attribution on D

## Preregistration

Registered before probe construction or diagnostic results, on shared head 299ce2649186d82f653408ea5978ff1be7797fb4. Production compiler/rewatch source must remain exactly 5dc38ba2154e158d43436ada2142a13eef9f2c8c. This task implements no optimization. Parent owns campaign documentation and PR 19.

Use a new git archive at `/tmp/rescript-descriptor-snapshots/probe-source`, with separate saved patch and probe executables. Immutable uninstrumented D binaries come from `/tmp/rescript-type-arg-experiment/bin`. Never modify those binaries. Preserve evidence under `/Users/jake/.opensession/artifacts/rescript-performance-20260905/descriptor-snapshots`.

Fixed diagnostic order: D w1, probe P w1, D w12, P w12. Exactly one full clean build per cell. No screening, acceptance cohort, retries into green, confidence intervals or new-best claim. Clean outside perf_counter_ns + time -lp process timing, manifest hashes outside timing. Reuse measurement_rebaseline.py cleanup, command, environment, timer and input inventory. Freeze resolved inputs after setup and before builds. Permit only the individually listed eleven compiler-info files and webapp .sourcedirs output proven in type_arg_measure.py. Preserve failures. Preserve and restore the eighteen original generated TypeScript modifications individually. Each build must exit zero, report 3248 modules and hash 5048 JavaScript outputs to 1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49. Runtime is this worktree's source runtime, freshly compiled 107 modules per process with minimum two runtime workers, even with one project worker. Warm filesystem; no OS cache purge. All heavy commands use the shared lock.

Probe adds explicit per-TypeContext Cell-owned counters keyed by immediate source file, line, column and descriptor variant. `#[track_caller]` on get_desc changes code generation and adds overhead. Cell take/set moves a counter map rather than cloning it. No mutable global/thread-local counters, new unsafe, RefCell workaround, forcing or semantic change. Emit aggregate records at context destruction and aggregate out of process. No module inference from paths.

Count each get_desc invocation once. Inline logical payload = calls * size_of(TypeDesc), not actual writes. For nested ownership count nonempty Vec clone requests and len * element size, nonempty String requests and length bytes, TypeArg cold Box requests and size_of(ArgLabel), recursive Longident Box requests and size_of(Longident). These are logical requested payload estimates, not source capacities, allocator rounded bytes, bandwidth, live heap or proof LLVM executes every allocation. Count nested buffers separately from inline owners so bytes do not overlap. Path's Arc parents and SmolStr/Ident's inline/static/Arc strings do not deep-clone their referenced storage. Row fields own a Vec plus Reither type vectors; row links, field kinds, abbreviation refs, type handles and location StrIdx values do not own their referents. Object names own argument vectors. Package lids own recursive Longident boxes, but StrIdx strings stay shared. This covers nested ownership under TypeDesc::clone only, not all compiler clones.

Rank caller/variant clusters by call count and nested requested payload. Audit leading sites for tag/scalar-only reads, short read-only borrows, and mutation requiring old immutable payload. Use prior full-duration sampling only as historical corroboration, not D callsite attribution. If fresh sampling is necessary, preregister a separate full-duration run before execution and keep it outside these four builds. Single-run P-minus-D is an overhead estimate only.

## Source contract before instrumentation

Rust types/context.rs:44-85 uses stable arena nodes with mutable descriptors. get_desc at 1598 clones; borrow_desc at 1607 returns a Ref guard. Stable node addresses do not make a guard safe across mutation of that node, even through a shared context reference. TypeDescSnapshot owns the old descriptor containers but preserves referenced type-node, memo and row-link identities. It is not a frozen transitive type graph.

OCaml types.ml:22-66 stores a mutable descriptor slot referring to immutable variant/list payloads and shared mutable reference cells. ctype.ml:725-765 saves the old descriptor, writes Tsubst, then recursively copies from the old payload; subst.ml:130-165 follows the same stub boundary. btype.ml:420-458 maps descriptors and saves originals for cleanup. Such consumers need access to old payload after replacing the slot. A tag test or extracted Copy scalar does not inherently need an owned snapshot. Neither finding licenses borrowing across recursive Env/Ctype operations. Env component construction and Subst.value_description preserve lookup/substitution/force boundaries, not content-based normalization. Source line numbers in old reports can drift; final audit will cite current definitions.

Native OCaml tuple/constructor evaluation can be right-to-left. The textual argument/result ordering in btype.copy_type_desc does not prove native execution order. This measurement preserves existing Rust traversal and changes none of those contracts.

## Acceptance limits inherited

One second remains unachieved and unproven; historical 4.5–4.6s remains best. TypeArg D's prior fixed cohort improved C by 79.18ms serial and 49.27ms parallel, with increased RSS and contrary screens. It was not an A comparison. Map/TypeArg remain experimental. Inherited final D tests: compiler default/release 1337 library passed, 108 ignored; binary targets 0/0; comptime 16 passed/23 ignored; docs 9 passed/7 ignored; rewatch 150. Internal typed/raw/optimized 610 each, focused JS 344, snapshots 610, diagnostics 1431 passed. No rerun is planned for unchanged production source. Benchmark_index passing harness hides ratio/possible skip, not parser-speed proof; C previously measured 1.31 against 1.20. External OCaml Tella remains blocked by bs-css missing Belt. Corrected standalone fixture has preexisting C=D versus OCaml declaration-order mismatch; the original empty-stderr seven-pass claim was invalid. Runtime passes do not clear exact JS failure. No backend/dependency fix, normalization, waived gate, merge or production acceptance.

## Diagnostic checkpoint and separate sampling registration

The four prescribed builds completed with matching full output hashes. Serial D/P walls were 19.387689209/23.843461541s; parallel D/P were 4.909889875/6.030056458s. The 3511-context serial census counted 36,304,460 get_desc calls and 489,020,525 nested requested bytes. Arrow totals exactly reproduce the previous D arrow-only probe, including 1,346,250 cold Box requests. Resolved input drift was exactly the twelve registered generated outputs; all eighteen original generated files were restored.

Before choosing between short descriptor projections and mutation-heavy substitution, register separate full-duration sampling on immutable D: one w1 build then one w12 build, sample interval 1ms with duration 30s/10s, stop naturally at process exit. Use the same cleanup, corpus and output checks; no phase instrumentation. These are two additional labeled profile executions, not diagnostic overhead or acceptance samples. Freeze and verify inputs separately before changing report/data reached through dependency symlinks. Sampling setup necessarily misses attach latency; report start/end coverage and do not use the old three-second startup-biased profile. Preserve failed sampling without retries.

## Findings

The largest justified next experiment is **short-lived descriptor projections at application/lowering and substitution's initial tag check**, not another node layout. Five measured sites request 89.31 MB of nested copying solely to inspect a tag or immediately make the smaller owned copy that the caller actually keeps. That is 18.26% of this probe's nested requested bytes. Removing that duplication is a bounded API-use experiment; it is not an 18% speedup prediction. No implementation was made.

### What was counted

Both modes destroyed 3,511 contexts. Counts include runtime compilation and any auxiliary contexts, not one context per project module. Every emitted source location was checked against an actual get_desc call. Raw probe locations remain in the data; `source_line` maps them to reviewed D. Only context.rs has shifted lines from instrumentation. All thirteen variants are represented in the aggregate, including zero observed Tsubst calls.

| Descriptor, w1 | Snapshot calls | Nested requested bytes |
|---|---:|---:|
| Tconstr | 23,029,667 | 63,832,496 |
| Tvar | 5,866,352 | 6,288,192 |
| Tarrow | 5,042,791 | 240,182,307 |
| Tvariant | 826,293 | 173,997,420 |
| Tlink | 552,310 | 0 |
| Ttuple | 393,582 | 3,766,504 |
| Tpoly | 199,614 | 37,284 |
| Tnil | 156,159 | 0 |
| Tfield | 121,043 | 822,000 |
| Tobject | 103,793 | 0 |
| Tunivar | 12,107 | 60,050 |
| Tpackage | 749 | 34,272 |
| Tsubst | 0 | 0 |
| Total | 36,304,460 | 489,020,525 |

The logical 96-byte descriptor multiplier is 3,485,228,160 inline bytes. Nested requests split into 14,682,918 nonempty Vec requests / 374,006,600 bytes; 2,566,883 nonempty String requests / 18,083,925 bytes; and 1,346,250 Box requests / 96,930,000 bytes. The boxes observed here are all TypeArg labels, each 72 bytes. Package Longident recursion is instrumented but no package Box request occurred. Row labels are SmolStr, not cloned String allocations.

Parallel totals were 36,289,530 calls, 3,483,794,880 inline bytes and 488,480,578 nested bytes. They are not bit-identical to serial: 14,930 fewer calls and 539,947 fewer nested bytes. No rows were discarded or averaged to hide this difference. Persistent rewrite traversals account for visible differences, but this probe does not identify their scheduling/cache cause. Both modes produced identical complete JS output. Serial arrows exactly match the prior arrow-only D probe's 240,182,307 bytes and 1,346,250 boxes. The older A count of 33.247M calls is a different source stack, not evidence of a TypeArg-caused increase.

Nested accounting audits these definitions:

- types/type_expr.rs:159-255, 577-602, 652-738 derive Clone. Vec cloning owns new element buffers; TypeArg clones its optional owned Box and Located<String>. Location and Position carry Copy scalar/StrIdx fields, not owned filename strings.
- types/path.rs:35-44 derives Clone over Ident, Arc<Path> and SmolStr. ident.rs:119-124 stores SmolStr. Pdot/Papply retain Arc references, not recursively cloned parent trees. Pident does not allocate a new name buffer when cloned. Pinned smol_str **0.3.2**, Cargo.lock:1953-1954, implements inline/static copying or Arc<str> retain at lib.rs:105-113 and 480-486. Its clone can still incur refcount/inline work; zero newly owned nested bytes does not mean free.
- RowDesc owns row_fields and optional row_name arguments. Reither owns a type-handle vector but its RowFieldRef link remains shared. No traversal into the link, row_more, abbreviation, FieldKindRef or TypeExprRef is counted as owned cloning. ObjectName's optional vector is owned; object field graph handles stay shared. No named-object vector occurred in these runs.
- parser/longident.rs:18-27 owns Box children but only copies StrIdx strings. Package vector element storage and child boxes are separate nonoverlapping owners.

These are logical clone requests based on source payload lengths, not measured destination capacities or malloc calls. Source capacity slack is deliberately excluded. Allocator size classes, reserve behavior, allocation elision, memcpy lowering, shared refcounts and compiler inlining are not measured by the counters. Direct TypeDesc::clone, explicit args.clone, row clones in iter_type_expr, mutation snapshots outside get_desc, and all other compiler allocations remain outside this census. Do not call 489 MB “all clone bytes.”

### Largest measured callers and lifetime audit

Numbers below sum variants at the named immediate site, with source lines in reviewed D. They overlap the variant table; do not add tables together.

| Site | Calls | Nested bytes | Classification |
|---|---:|---:|---|
| persistent_env.rs:4369, substitute_type_expr_path | 5,420,791 | 67,741,422 | Mixed traversal and same-node mutation |
| ctype.rs:972, deep_occur_rec | 4,928,774 | 14,567,457 | Traversal; not automatically borrow-safe |
| ctype.rs:5175, unify first descriptor | 3,117,290 | 35,819,288 | Old payload across linking/recursion |
| ctype.rs:5176, unify second descriptor | 3,117,290 | 41,128,086 | Old payload across linking/recursion |
| persistent_env.rs:5371, single-prefix rewrite | 1,291,621 | 21,809,847 | Recursive mutation |
| context.rs:1647, mutation-state snapshot | 1,069,027 | 9,232,148 | Owned state retained for rollback |
| persistent_env.rs:5485, multiple-prefix rewrite | 951,868 | 18,694,526 | Recursive mutation |
| ctype.rs:9925, subst_identity_copy_rec guard | 807,599 | 14,126,347 | Tag-only guard, snapshot dropped |
| ctype.rs:8533, lower_args | 632,772 | 19,459,891 | Short handle-vector projection |
| typecore.rs:9868/9898/9918, application | 931,399 | 55,723,935 | Tag test and duplicate argument snapshots |

Largest individual caller/variant cluster is substitution's Tarrow, 856,599 calls / 33,740,241 bytes, followed by its Tvariant, 183,957 / 25,238,056. Unify's two arrow sites request 22,399,730 and 21,914,306 bytes; lower_args arrows request 18,839,996. The full site/variant tables are committed rather than only selected successes.

1. **Application and lower_args.** typecore.rs:9868 clones an arrow even though it asks only whether the tag is Tvar. At 9898 and 9918 it clones the descriptor, then clones args from that owned temporary. The kept args vectors are necessary across subsequent instancing, expansion and argument typing; the first clone is not. ctype.rs:8533 similarly immediately projects args into a Vec<TypeExprRef> and copies ret, ending the snapshot before any unify_var. Use the existing borrow_desc in a lexical block, extract only the existing owned result, and drop the Ref before all Env/Ctype calls. Do not hold borrowed args across instance or unify_var, skip expansion, or fuse the two application instances. OCaml typecore.ml:2302-2313 and 4030-4095 preserve these expansion, argument-list and mutation boundaries.
2. **Substitution tag guard.** ctype.rs:9925 examines only Tvar/Tunivar/Tnil, drops desc on both branches, and later obtains a separate payload snapshot at 9941 after allocating/registering a stub. A short boolean classification can replace the initial snapshot while leaving the later owned payload and stub order intact. OCaml subst.ml:130-165 distinguishes identity returns from the saved-descriptor/stub path. Do not fold this into one long-lived borrow across recursive copying.
3. **Iterative substitution.** persistent_env.rs:4369 clones every traversed descriptor. Arrow/tuple/link/field branches only push handles onto a separate work stack; they can use a short borrow without descriptor ownership. Constructor, named variant and package branches may set_desc on the same node before pushing old children. A bounded follow-up could borrow to compute the replacement and enqueue the same handles in the same order, release the guard, then write at the original boundary before popping the next node. Changed descriptors still need an owned replacement. The measured arrow subset alone offers 33.74 MB of avoidable nested requests; 67.74 MB is only a gross whole-site ceiling, not all removable. This must not change substitution mappings, selected components, descriptor identity or force order. References are subst.ml:69-100 and 154-238; env.ml:800-814 and 1475-1505 create component substitutions. No content-based or path-spelling shortcut is justified.
4. **Recursive prefix rewrites.** persistent_env.rs:5371/5485 hold old payload while mutating and recursing. A cycle can revisit a node or invoke helpers that change its descriptor. The visited set does not prove every nested helper safe. These are not candidates for mechanical get_desc-to-borrow_desc replacement. The two sites' 40.50 MB is a gross request count, not an eliminated-work estimate.
5. **Unification.** ctype.rs:5175-5290 inspects both sides, may expand, and in the arrow case links t1 before recursively unifying arguments, retaining original_desc1 for recovery. Payload/vector clones after get_desc are outside the probe. A projection of tags could avoid rejected-branch copies, or an owning snapshot consuming API could avoid a second deep copy, but this requires branch-by-branch lifetime and error-path proof. OCaml ctype.ml:2100-2145 dispatches into mutation; its saved old payload does not become the new slot contents when the slot is linked. The full 76.95 MB at these two sites is not proven removable.
6. **Deep occurrence and rollback.** ctype.rs:972 is the second-largest call-count site, dominated by constructors, but only 14.57 MB nested. Recursion calls repr, whose path compression writes through a shared context reference, context.rs:2614 onward; the fallback uses btype.rs:298-365's child extraction. Keep short projected children or prove the complete reachable mutation behavior before borrowing recursively. OCaml ctype.ml:1622-1637 also mutates traversal levels. context.rs:1647 must retain old descriptor containers across speculative mutation for restoration. A borrow is categorically not a replacement for that rollback snapshot. It still shares referenced type identities, as OCaml btype.save_desc/cleanup does.

### Ranked next options

**First, short projection API use, one bounded experiment.** Scope the five sites in application, lower_args and the initial substitution guard. Preserve all existing owned parameter/child vectors that survive mutation. The directly counted redundant get_desc work is 2,371,770 calls, 227,689,920 logical inline bytes and 89,310,173 nested requested bytes: 1,663,800 Vec requests / 49,498,200 bytes, 548,124 String requests / 4,385,309 bytes, 492,037 Box requests / 35,426,664 bytes. These estimates exclude existing second copies that remain necessary. Confidence is high that the source requests are redundant, moderate that eliminating them improves whole-build time, low on the size of any gain. This is the largest audited short-borrow-safe group, not a claim that every callsite was audited or that byte rank equals CPU rank. Validate guard release, labeled/optional metadata, cyclic types, errors, exact typedtree/lambda/JS and fresh fixed-pair release timing in the next authorized task.

**Second, substitution traversal projections.** Start with the explicit work-stack site rather than recursive rewrites. Its arrow-only 33.74 MB subset has a clear read-only handle extraction boundary. Broadening to changed constructors/variants must retain old payload and exact write order. This option is less immediately certain despite its high call count and two largest individual nested-byte clusters.

**Third, owned snapshot consumption or immutable descriptor payload storage.** Unification and copy operations need old payload across slot mutation. A consuming TypeDescSnapshot API could remove some subsequent desc/args clones without holding a borrow, but those second clones are not measured here and cannot be included in the 89.31 MB claim. An immutable descriptor arena would model OCaml's old payload survival more directly, but requires separate mutable slots for memo/row/object state, preserves physical type identity and adds indirection plus retention of superseded payloads. Current arena-at-context-drop retention could increase. Before choosing it, measure descriptor replacement counts, peak live old snapshots and reclamation/retention, plus all extra explicit clones in those consumers. No per-node Rc/Arc or new unsafe is proposed. Neither arena superiority nor “borrow everything” follows from this census.

### Whole-build sampling corroboration, not causal savings

Fresh immutable D sample runs were requested for the full build, not a three-second prefix. Apple sample header Date/Time minus Launch Time is 65ms serial and 36ms parallel. Those header differences are not proof of the exact first-sample time. Both samplers completed successfully and both builds passed the full JS hash. Requested durations were longer than normal builds and sampling completed after process exit. The reports do not supply exact first/last observation timestamps, so startup/termination coverage gaps cannot be quantified precisely. Processing symbols is included in the recorded wrapper durations, 23.23s and 10.93s, so those are **not build wall timings**. Sample launch delays of about 1.8ms are Python-to-sample invocation only, not actual attachment latency or first-sample coverage. The profiler perturbs execution and does not provide exact per-thread CPU time.

| Sample family | w1 exclusive / inclusive-union samples | w12 exclusive / inclusive-union samples |
|---|---:|---:|
| Named compiler/runtime worker denominator | 16,496 | 49,883 |
| memmove | 2,287 / 2,287 | 5,634 / 5,634 |
| direct mimalloc frames, exclusive only | 1,637 | 4,361 |
| visible TypeDesc::clone | 121 / 204 | 419 / 646 |
| type_application | 59 / 5,052 | 174 / 14,303 |
| unify-name family | 98 / 2,623 | 245 / 6,981 |
| substitute_type_expr_path | 13 / 170 | 29 / 372 |
| prefix-rewrite family | 8 / 112 | 18 / 210 |
| deep_occur | 10 / 68 | 31 / 192 |

Exclusive residuals subtract direct children and sum exactly to the worker denominators. Inclusive-union counts include a matching stack only once within each family, avoiding recursive self-double-counting. Different families still overlap: application includes unification, clones and allocation. Worker denominators include blocked/descheduled samples, particularly in parallel; they are not retired CPU ticks. lower_args has no visible frame, likely inlined, so zero named samples is not zero cost. TypeDesc::clone samples include direct clones outside get_desc; inlining also hides some get_desc clone work. The 13.86%/11.29% memmove shares and 9.92%/8.74% direct allocator shares corroborate broad movement/allocation cost, consistent with prior A profiles, not ownership of those costs by the five proposed sites. No bandwidth saturation, allocator-intercept, exact snapshot CPU attribution or wall saving is claimed.

### Diagnostic overhead and invariance

| Mode | D wall s | Probe wall s | Single-run added wall | D user/sys s | Probe user/sys s |
|---|---:|---:|---:|---:|---:|
| w1 | 19.387689 | 23.843462 | +4.455772s, +22.98% | 18.41 / .81 | 20.78 / 2.85 |
| w12 | 4.909890 | 6.030056 | +1.120167s, +22.81% | 40.04 / 2.04 | 36.71 / 4.86 |

RSS was 2,089,205,760 versus 2,071,199,744 bytes serial and 3,022,979,072 versus 3,062,480,896 bytes parallel. Parallel user CPU fell despite instrumentation; logging serialization, changed scheduling and single-run noise prevent interpreting that as a benefit. BTreeMap lookup, Cell moves, payload traversal, track_caller codegen and locked stderr emission all perturb these runs. Do not isolate one component's overhead from this comparison. There are no confidence intervals or fresh acceptance timings.

Frozen inventories contained 41,586 paths before and 41,598 after diagnostics. The only changes were the eleven individually named compiler-info.json outputs and webapp .sourcedirs.json, listed in input-verification.json. The separate sample inventory also changed only approved metadata. rewatch build.rs:584-585 writes compiler-info; clean.rs:429-455 removes it before each build. compiler_info.rs:34 onward does read this metadata to decide cleaning, so it is not generally an unread file. In this clean protocol it is regenerated output, as proven by the absent-before/present-after inventories. sourcedirs.rs:74-77 writes the exact .sourcedirs output. No broad JSON, directory or mirror exclusion was needed. The resolved inventories include dependency/PPX sources and config through symlinks, beyond tracked Tella input. No report/data was added through the linked compiler package during either frozen cohort.

## Reproduction and handoff

Run scripts from this shared repository root. Scripts pin the dedicated temporary directory rather than appending old cohorts. Preparation creates a git archive of 5dc38ba21's compiler-rust and rewatch, copies immutable D binaries without modifying their originals, then runs descriptor_snapshot_probe.py. Build both archived crates with `/Users/jake/.cargo/bin` first in PATH, unset RUSTFLAGS, default release settings. Use the shared `lockf -k` for both cargo builds, `descriptor_snapshot_measure.py setup/run/verify/restore`, and `descriptor_snapshot_profile.py`. Build timeout was 600s, full builds 180s, sampling command 45s. There were no fixture compiler invocations.

`descriptor_snapshot_analyze.py` verifies and aggregates raw counters; `descriptor_snapshot_samples.py` parses full sample call trees. `descriptor_snapshot_finalize.py` restores every tracked archived source file from git archive, compares production files byte-for-byte against reviewed source, rechecks original/copied D binary hashes, restores/verifies the eighteen generated modifications and preserves local artifacts excluding Cargo target caches. The saved probe patch, patched context source and both probe binaries remain separate from restored archived source. The analyzer uses saved patched context for source-line mapping and works after restoration. Existing data files prevent a second diagnostic or sampling cohort.

See [raw diagnostic rows](descriptor-snapshots-5dc38/runs.jsonl), [w1 counters](descriptor-snapshots-5dc38/counts-w1.json), [w12 counters](descriptor-snapshots-5dc38/counts-w12.json), [sample aggregates](descriptor-snapshots-5dc38/samples.json), and [provenance](descriptor-snapshots-5dc38/provenance.json). Provenance records binary/toolchain/source/runtime/input/patch/log/profile hashes. Full raw profiles, private input inventories, output hash manifests, generated-file backups and restored archive are local at `/Users/jake/.opensession/artifacts/rescript-performance-20260905/descriptor-snapshots`; artifact-hashes.json covers the preserved files. No private corpus source or JavaScript was committed or uploaded.

No production optimization, TypeArg/map/M6/backend/dependency change, gate rerun, push, PR edit, branch change or subworker was performed. An external skill read hit the read tool's workspace boundary; the same local skill was read through bash. A few provisional source-path lookups also failed and were corrected through repository search. No failed compiler build or measurement was retried. This measurement meets its attribution/output-invariance scope, not production performance acceptance. One second remains unachieved and no new best is established. At final handoff all compiler, shared-worktree and heavy-measurement ownership is explicitly released. No next optimization is started.
