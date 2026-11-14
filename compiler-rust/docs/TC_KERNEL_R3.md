# R3a and R3b kernel measurements

Measured base: `d1a9d3a5c` (trunk). Measured bench addition: `ac3416c1f`.
Only the benchmark changed; no function under `compiler-rust/src` changed.
No tuning was performed. These are kernel costs, not compiler-build savings.

## Machine and method

Linux x86-64 (Ubuntu 24.04), AMD Ryzen 9 9950X 16-Core Processor,
8 virtual CPUs exposed, Valgrind 3.22.0, pinned nightly-2026-11-10 Rust.
Fat LTO, one codegen unit, line tables, one million operations. Follow
TC_KERNEL_R1.md: run the reference script first, subtract each operation's
zero-iteration run, then subtract that executable's own harness control.
Both zero/full cachegrind profiles were retained and annotated for every
production-bench operation. The reference script reproduced every published
raw integer count.

Commands (run from repository root; `BENCH` is the executable Cargo prints):

```sh
export PATH="$HOME/.cargo/bin:$PATH"
CARGO_TARGET_DIR=/tmp/checker-reference cargo build --release \
  --manifest-path compiler-rust/docs/prototypes/checker-kernel/Cargo.toml
bash compiler-rust/docs/prototypes/checker-kernel/measure.sh \
  /tmp/checker-reference/release/checker-kernel
CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 \
CARGO_PROFILE_BENCH_DEBUG=line-tables-only \
  cargo bench --manifest-path compiler-rust/Cargo.toml --bench tc_kernel --no-run
# Repeat for every operation listed below, on each revision:
valgrind --tool=cachegrind --cache-sim=no \
  --cachegrind-out-file=OP.zero.cg "$BENCH" OP 0
valgrind --tool=cachegrind --cache-sim=no \
  --cachegrind-out-file=OP.full.cg "$BENCH" OP 1000000
cg_annotate --auto=yes --threshold=0 OP.zero.cg
cg_annotate --auto=yes --threshold=0 OP.full.cg
```

Let `raw(OP) = (full I refs - zero I refs) / 1000000`.
Instances subtract `raw(empty)`; generalize7 and lower7 subtract
`raw(instance7)`; repr, restore and keep subtract `raw(instance1)`.
Restore/keep include speculation and one write, not just the final action.
Copy7 is reported as its existing combined instance/generalize/copy workload
minus empty: there is no exact setup-only twin for this older operation.
Empty and build-only controls are shown raw, with no second subtraction.
Each new unification case subtracts its matching `build_*` control, **not**
empty as well. Both sides create and consume identical fresh operand handles
and reset pools every 4,096 iterations; only the unification side calls
`Checker::unify` and checks success. Counts include this call-site overhead
and amortized scratch-pool growth. Graph mode is `Success`, with default
empty declaration facts and memo. Operands use the existing bench helpers
and their GENERIC level. Nothing is pre-unified or reused as an operand.

The three-node case is `C<int, string>` against a fresh `C<int, string>`.
Section 2.2's 386 is for `option<array<int>>`, a chain, so it is a contextual
comparison, not an equivalent workload or a gate. Section 2.2's 26 measures
**one node passed twice**, not two fresh variables; it is not a reference
figure for `unify_vars`.

## Raw output

Reference script (instructions per iteration, before harness subtraction):

```text
empty 18
instance1 107
instance3 187
instance5 239
instance7 268
two_instance1 200
unify_ground1 318
two_instance3 360
unify_ground3 746
two_instance5 464
unify_fun5 1095
unify_same 213
var_instance3 201
bind_var3 501
apply7 1238
generalize7 672
lookup_name 23
lookup_binder 23
bind_close 62
```

Production bench: raw instructions per iteration, before harness subtraction.
Every operation present on trunk is included; `—` means not present on trunk.

```text
operation                    trunk raw       added-bench raw
instance1                      167.060605          167.060591
instance3                      254.308905          255.308891
instance5                      348.337326          349.337312
instance7                      372.271605          373.271591
generalize7                    860.271605          862.271619
empty                           18.002260           18.002246
lower7                         822.271591          832.271605
copy7                         1823.580021         1826.580007
repr                           178.060619          178.060605
restore                        236.060980          234.060991
keep                           218.060994          216.060977
checker_instance1              159.060599          159.060585
checker_instance3              246.308899          247.308885
checker_instance5              341.337320          342.337306
checker_instance7              364.271599          365.271585
build_vars                              —           79.070354
unify_vars                              —          304.070548
build_ground1                           —           99.077721
unify_ground1                           —          302.077915
build_ground3                           —          203.440818
unify_ground3                           —         1081.398728
```

Exact cachegrind I refs (zero, full), before and after:

```text
revision operation zero full
trunk instance1 331643 167392248
trunk instance3 331649 254640554
trunk instance5 331655 348668981
trunk instance7 331659 372603264
trunk generalize7 331665 860603270
trunk empty 331592 18333852
trunk lower7 331603 822603194
trunk copy7 331598 1823911619
trunk repr 331562 178392181
trunk restore 331615 236392595
trunk keep 331563 218392557
trunk checker_instance1 331737 159392336
trunk checker_instance3 331751 246640650
trunk checker_instance5 331759 341669079
trunk checker_instance7 331768 364603367
added-bench instance1 327708 167388299
added-bench instance3 327714 255636605
added-bench instance5 327720 349665032
added-bench instance7 327725 373599316
added-bench generalize7 327716 862599335
added-bench empty 327657 18329903
added-bench lower7 327669 832599274
added-bench copy7 327662 1826907669
added-bench repr 327641 178388246
added-bench restore 327666 234388657
added-bench keep 327642 216388619
added-bench checker_instance1 327800 159388385
added-bench checker_instance3 327814 247636699
added-bench checker_instance5 327823 342665129
added-bench checker_instance7 327831 365599416
added-bench build_vars 327871 79398225
added-bench unify_vars 327876 304398424
added-bench build_ground1 327909 99405630
added-bench unify_ground1 327915 302405830
added-bench build_ground3 327920 203768738
added-bench unify_ground3 327925 1081726653
```

## Results after harness subtraction

All values below are measured on the added benchmark, not copied from R1.
Section 2.2 values and gates are quoted, not new measurements. N/A means
no comparable published figure/gate. A benchmark-only change can shift
machine-code layout and dispatch: the before raw counts above must not be
silently substituted for the after counts.

| Operation | Instructions | Section 2.2 | Gate | Above kernel figure? | Above gate? |
|---|---:|---:|---:|---|---|
| `instance1` | 149.06 | 89 | — | Yes | N/A |
| `instance3` | 237.31 | 169 | — | Yes | N/A |
| `instance5` | 331.34 | 221 | — | Yes | N/A |
| `instance7` | 355.27 | 250 | — | Yes | N/A |
| `generalize7` | 489.00 | 404 | — | Yes | N/A |
| `empty` | 18.00 | — | — | N/A | N/A |
| `lower7` | 459.00 | — | — | N/A | N/A |
| `copy7` | 1808.58 | — | — | N/A | N/A |
| `repr` | 11.00 | — | — | N/A | N/A |
| `restore` | 67.00 | — | — | N/A | N/A |
| `keep` | 49.00 | — | — | N/A | N/A |
| `checker_instance1` | 141.06 | 89 | 143 | Yes | No |
| `checker_instance3` | 229.31 | 169 | 223 | Yes | Yes |
| `checker_instance5` | 324.34 | 221 | 308 | Yes | Yes |
| `checker_instance7` | 347.27 | 250 | 330 | Yes | Yes |
| `build_vars` | 79.07 | — | — | N/A | N/A |
| `unify_vars` | 225.00 | — | — | N/A | N/A |
| `build_ground1` | 99.08 | — | — | N/A | N/A |
| `unify_ground1` | 203.00 | 118 | — | Yes | N/A |
| `build_ground3` | 203.44 | — | — | N/A | N/A |
| `unify_ground3` | 877.96 | 386 | — | Yes (different shape) | N/A |

**R3b gate verdict:** instance1 passes; instance3, instance5 and instance7
exceed their gates. Ground1 unification exceeds the kernel's figure;
ground3 exceeds the quoted chain figure, with the shape caveat above.
There is no published two-fresh-variable figure to compare. This report
makes no claim that R3 meets all its performance gates.

## Build and application checks

```text
cargo build --manifest-path compiler-rust/Cargo.toml
Finished `dev` profile [unoptimized + debuginfo] target(s) in 1m 13s
CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 CARGO_PROFILE_BENCH_DEBUG=line-tables-only cargo bench --manifest-path compiler-rust/Cargo.toml --bench tc_kernel --no-run
Finished `bench` profile [optimized + debuginfo] target(s) in 1m 40s
cargo build --release --manifest-path rewatch/Cargo.toml
Finished `release` profile [optimized] target(s) in 4m 31s
```

The release build reports an existing unused `console::style` import.
During bench editing an attempted `Graph::newvar` call failed with E0599
(no such method); the bench now uses its existing `var` helper. The final
bench builds and all 21 operations run successfully. Full compiler tests
were deliberately not run locally; CI owns the full suite and parity gates.

A 3,735-module application was checked with the unchanged production
release binary. **BASE and CANDIDATE were two copies of the same executable**,
not independently built revisions: no production input changed in this PR.
This is a repeatability/output sanity check, not evidence of an optimization
or an independently built before/after comparison. Default-path savings:
none claimed.

```sh
# APP is the application checkout outside this repository.
cp rewatch/target/release/rescript /tmp/tc-base-rescript
cp rewatch/target/release/rescript /tmp/tc-candidate-rescript
scripts/bench_project.sh "$APP" /tmp/tc-base-rescript /tmp/tc-candidate-rescript \
  --runtime-from "$PWD"
RESCRIPT_RUNTIME="$PWD/packages/@rescript/runtime" \
  python3 scripts/compare_checker_builds.py "$APP" \
  /tmp/tc-base-rescript /tmp/tc-candidate-rescript
```

```text
base: instructions=64170477379 source_lines=656677 instructions_per_line=97720.001
candidate: instructions=64183364303 source_lines=656677 instructions_per_line=97739.626
Outputs identical
Instructions difference: +0.0201%
base: exit code 0, 3735 signatures, 32 diagnostics in 18 files, 3980 generated files
candidate: exit code 0, 3735 signatures, 32 diagnostics in 18 files, 3980 generated files
outcome: both exit with 0
signatures: no difference (3735 compared)
diagnostics: no difference (18 compared)
javascript: no difference (3980 compared)
no differences
```
