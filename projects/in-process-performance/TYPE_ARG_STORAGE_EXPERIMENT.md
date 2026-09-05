# TypeArg storage experiment

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

Four focused default tests pass. Seven standalone exact OCaml comparisons pass, including typedtree locations, raw/optimized Lambda, JS and wrong-label/arity diagnostics. The successful fixture covers generic/labeled/optional/n-ary and nested arrows plus record spread with unchanged and substituted arrow fields. No expected-output normalization.

Final default and release compiler suites each report 1337 lib, 16 comptime and 9 doc tests passed; ignored 108/23/7; bins zero. Rewatch release 150 passed. The initial c6278e795 runs and final 5dc38ba21 runs have separate logs. Both release harnesses reported benchmark_index ok without threshold changes. Successful stdout was captured by Cargo, so actual ratio/times are unavailable. Required binaries and index fixture exist; no repeat was made just to expose stdout. This is not evidence that TypeArg fixes parser benchmark instability.

Release parity passes 610 typedtrees, 610 raw Lambda, 610 optimized Lambda, 344 focused JS, 610 JS snapshots and 1431 diagnostics. External parity fails in OCaml bs-css/Css_AtomicTypes.res:1446 with missing Belt before Rust comparison. Acceptance remains pending.

## Storage probe before timing

Archived 5dc38ba21 release/default rewatch only, with per-context counters and a destruction census. Normal compiler source/binaries never contain instrumentation. 3511 contexts; probe build exits 0 and matches 5048 JS files and the required digest.

Context-destruction retained arrow storage summed across lifetimes: 5,135,539 arrows / 8,209,181 arguments; 135,943,648 hot vector capacity bytes + 92,339,928 cold box bytes + 10,713,799 owned string capacity bytes = 238,997,375 bytes. There are 1,282,499 cold boxes/nonempty strings, including 467,703 optional labels. NoLabel has no box. File names remain StrIdx handles in locations, so no filename strings are separately owned by labels or counted twice here.

Cumulative get_desc arrow snapshots: 5,042,791 arrows / 8,271,164 arguments; 132,338,624 hot bytes + 96,930,000 cold box bytes + 10,913,683 string bytes = 240,182,307 requested bytes. These snapshot clones allocate 1,346,250 cold boxes plus their nonempty strings. This is a measured allocation subset, not an exhaustive count of every transient TypeArg/Vec creation. Retained-at-destruction sums are not simultaneous peak, cumulative all-allocation traffic or DRAM traffic. The two populations overlap over time and must not be added as total allocations. Allocator metadata/rounding and separately owned filename arenas are excluded. Peak process RSS comes from uninstrumented timings.

Repro scripts and all raw private logs/inventories stay in the dedicated artifact directory. Before timing, freeze a separate inventory after all tests and selected C clean. No timing samples yet at this documentation checkpoint.
