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

The original column is measured at `ac3416c1f`; the local-level bench column
is measured at `2d93b31cf`. Neither is copied from R1. All gate/comparison
verdicts are the same for both columns. The Attribution section uses the
original executable only, not the later local-level executable.
Section 2.2 values and gates are quoted, not new measurements. N/A means
no comparable published figure/gate. A benchmark-only change can shift
machine-code layout and dispatch: the before raw counts above must not be
silently substituted for the after counts.

| Operation | Original instructions | Local-level bench instructions | Section 2.2 | Gate | Above kernel figure? | Above gate? |
|---|---:|---:|---:|---:|---|---|
| `instance1` | 149.06 | 150.06 | 89 | — | Yes | N/A |
| `instance3` | 237.31 | 238.31 | 169 | — | Yes | N/A |
| `instance5` | 331.34 | 332.34 | 221 | — | Yes | N/A |
| `instance7` | 355.27 | 356.27 | 250 | — | Yes | N/A |
| `generalize7` | 489.00 | 489.00 | 404 | — | Yes | N/A |
| `empty` | 18.00 | 19.00 | — | — | N/A | N/A |
| `lower7` | 459.00 | 459.00 | — | — | N/A | N/A |
| `copy7` | 1808.58 | 1803.58 | — | — | N/A | N/A |
| `repr` | 11.00 | 12.00 | — | — | N/A | N/A |
| `restore` | 67.00 | 70.00 | — | — | N/A | N/A |
| `keep` | 49.00 | 49.00 | — | — | N/A | N/A |
| `checker_instance1` | 141.06 | 140.06 | 89 | 143 | Yes | No |
| `checker_instance3` | 229.31 | 228.31 | 169 | 223 | Yes | Yes |
| `checker_instance5` | 324.34 | 323.34 | 221 | 308 | Yes | Yes |
| `checker_instance7` | 347.27 | 346.27 | 250 | 330 | Yes | Yes |
| `build_vars` | 79.07 | 101.07 | — | — | N/A | N/A |
| `unify_vars` | 225.00 | 225.00 | — | — | N/A | N/A |
| `build_ground1` | 99.08 | 121.08 | — | — | N/A | N/A |
| `unify_ground1` | 203.00 | 203.00 | 118 | — | Yes | N/A |
| `build_ground3` | 203.44 | 231.44 | — | — | N/A | N/A |
| `unify_ground3` | 877.96 | 878.96 | 386 | — | Yes (different shape) | N/A |
| `build_vars_local` | — | 101.07 | — | — | N/A | N/A |
| `unify_vars_local` | — | 285.00 | — | — | N/A | N/A |
| `build_ground1_local` | — | 121.08 | — | — | N/A | N/A |
| `unify_ground1_local` | — | 263.00 | 118 | — | Yes | N/A |
| `build_ground3_local` | — | 231.44 | — | — | N/A | N/A |
| `unify_ground3_local` | — | 1120.96 | 386 | — | Yes (different shape) | N/A |

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

## Attribution

These are exclusive instruction counts grouped by the function name in
Cachegrind debug information, including inlined library lines attributed to
that function. They are not inclusive call costs or independent experiments
turning individual instructions off. Shares use the raw full-minus-zero total,
before harness subtraction. Every function above 2 instructions/operation is
listed; all remaining functions (including negative startup differences) are
summed into `other`. Line tables use the same function-specific full-minus-zero
counts, **not** the file-wide sum across functions. Lines strictly above 2
instructions/operation are listed for the two largest functions.

The original executable survived, but the temporary profiles did not survive
the workspace restart. These profiles were rerun from that exact retained
executable (build ID `011a0efb770d84e6f53c2bbd042618b958209217`), before
adding the local-level cases. Same machine, tool and profile as above. Raw
counts differ from the first run by at most 0.000108 instructions/operation;
all displayed two-decimal results are unchanged. This rerun is not substituted
silently for the original raw counts.

```sh
# Original BENCH, for each operation and its control:
valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file=OP.zero.cg "$BENCH" OP 0
valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file=OP.full.cg "$BENCH" OP 1000000
cg_annotate --diff --auto=yes --threshold=0 --show-percs=no OP.zero.cg OP.full.cg
rustup component add rust-src
```

The tables aggregate the `cg_annotate` Function:file summary; line counts are
read from those same Cachegrind records by `(function, file, line)` to avoid
charging a file's other functions to the selected one. `rust/library/...`
denotes the pinned toolchain's rust-src, not repository code. Repository
line numbers below are at `ac3416c1f` (before the local-level additions).
Values retain six decimals so that the function totals sum exactly.

### `unify_vars`

| Function | Instructions/operation | Share of raw |
|---|---:|---:|
| `tc_kernel::main` | 147.002036 | 48.3447% |
| `<tc::graph::Graph>::link` | 55.000000 | 18.0879% |
| `tc_kernel::main::{closure#2}` | 54.000063 | 17.7591% |
| `<tc::unify::Checker>::bind` | 48.000000 | 15.7858% |
| other | 0.068435 | 0.0225% |
| **Raw total** | **304.070534** | **100%** |

Subtract `build_vars` **79.070340**: 304.070534 − 79.070340 = **225.000194** instructions/operation, matching the results table after rounding.

#### `tc_kernel::main`: source lines above 2 instructions/operation

| File:line | Source text | Instructions/operation |
|---|---|---:|
| `compiler-rust/benches/tc_kernel.rs:115` | `if i & 0xfff == 0 {` | 2.000490 |
| `compiler-rust/benches/tc_kernel.rs:133` | `sink += left.0 as u64 + right.0 as u64;` | 6.000000 |
| `compiler-rust/src/tc/graph.rs:0` | `<no source line>` | 3.000000 |
| `compiler-rust/src/tc/graph.rs:29` | `self.head & 15` | 8.000000 |
| `compiler-rust/src/tc/graph.rs:211` | `Self::repr_parts(&mut self.nodes, &mut self.trail, self.speculation_depth, ty)` | 4.000000 |
| `compiler-rust/src/tc/graph.rs:224` | `while nodes[root.0 as usize].tag() == LINK {` | 29.000000 |
| `compiler-rust/src/tc/unify.rs:0` | `<no source line>` | 7.000000 |
| `compiler-rust/src/tc/unify.rs:160` | `let top = self.depth == 0;` | 4.000000 |
| `compiler-rust/src/tc/unify.rs:164` | `let token = if top && explain {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:173` | `self.depth += 1;` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:217` | `if l.tag() == VAR {` | 6.000000 |
| `compiler-rust/src/tc/unify.rs:624` | `match frame.kind {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:628` | `if left != right && self.unify_pair(left, right).is_err() {` | 3.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:635` | `self.ptr.cast()` | 3.000000 |
| `rust/library/alloc/src/vec/mod.rs:3160` | `let len = self.len;` | 7.000000 |
| `rust/library/core/src/hint.rs:491` | `crate::intrinsics::black_box(dummy)` | 5.000000 |
| `rust/library/core/src/iter/range.rs:0` | `<no source line>` | 3.000015 |
| `rust/library/core/src/ptr/mod.rs:1754` | `crate::intrinsics::read_via_copy(src)` | 4.000000 |
| `rust/library/core/src/ptr/mod.rs:1962` | `intrinsics::write_via_move(dst, src)` | 3.000000 |
| `rust/library/core/src/slice/index.rs:238` | `&(*slice)[self]` | 4.000000 |

#### `<tc::graph::Graph>::link`: source lines above 2 instructions/operation

| File:line | Source text | Instructions/operation |
|---|---|---:|
| `compiler-rust/src/tc/graph.rs:140` | `self.nodes[ty.0 as usize] = node;` | 5.000000 |
| `compiler-rust/src/tc/graph.rs:145` | `pub fn link(&mut self, from: Ty, to: Ty) {` | 7.000000 |
| `compiler-rust/src/tc/graph.rs:149` | `let source = self.nodes[from.0 as usize];` | 8.000000 |
| `compiler-rust/src/tc/graph.rs:150` | `let target = self.nodes[to.0 as usize];` | 8.000000 |
| `compiler-rust/src/tc/graph.rs:160` | `if source.tag() == VAR` | 4.000000 |
| `compiler-rust/src/tc/graph.rs:173` | `}` | 8.000000 |
| `rust/library/core/src/slice/index.rs:238` | `&(*slice)[self]` | 6.000000 |


### `unify_ground1`

| Function | Instructions/operation | Share of raw |
|---|---:|---:|
| `tc_kernel::main` | 173.002036 | 57.2707% |
| `tc_kernel::main::{closure#2}` | 74.000108 | 24.4970% |
| `<tc::graph::Graph>::link` | 55.000000 | 18.2072% |
| other | 0.075799 | 0.0251% |
| **Raw total** | **302.077943** | **100%** |

Subtract `build_ground1` **99.077749**: 302.077943 − 99.077749 = **203.000194** instructions/operation, matching the results table after rounding.

#### `tc_kernel::main`: source lines above 2 instructions/operation

| File:line | Source text | Instructions/operation |
|---|---|---:|
| `compiler-rust/benches/tc_kernel.rs:115` | `if i & 0xfff == 0 {` | 2.000490 |
| `compiler-rust/benches/tc_kernel.rs:133` | `sink += left.0 as u64 + right.0 as u64;` | 6.000000 |
| `compiler-rust/src/tc/graph.rs:0` | `<no source line>` | 3.000000 |
| `compiler-rust/src/tc/graph.rs:29` | `self.head & 15` | 8.000000 |
| `compiler-rust/src/tc/graph.rs:211` | `Self::repr_parts(&mut self.nodes, &mut self.trail, self.speculation_depth, ty)` | 4.000000 |
| `compiler-rust/src/tc/graph.rs:224` | `while nodes[root.0 as usize].tag() == LINK {` | 29.000000 |
| `compiler-rust/src/tc/unify.rs:0` | `<no source line>` | 13.000000 |
| `compiler-rust/src/tc/unify.rs:160` | `let top = self.depth == 0;` | 4.000000 |
| `compiler-rust/src/tc/unify.rs:164` | `let token = if top && explain {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:173` | `self.depth += 1;` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:217` | `if l.tag() == VAR {` | 6.000000 |
| `compiler-rust/src/tc/unify.rs:220` | `if r.tag() == VAR {` | 5.000000 |
| `compiler-rust/src/tc/unify.rs:225` | `if l.tag() == CONSTR` | 9.000000 |
| `compiler-rust/src/tc/unify.rs:235` | `self.g.link(left, right);` | 4.000000 |
| `compiler-rust/src/tc/unify.rs:624` | `match frame.kind {` | 3.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:635` | `self.ptr.cast()` | 3.000000 |
| `rust/library/alloc/src/vec/mod.rs:3160` | `let len = self.len;` | 7.000000 |
| `rust/library/core/src/hint.rs:491` | `crate::intrinsics::black_box(dummy)` | 5.000000 |
| `rust/library/core/src/iter/range.rs:0` | `<no source line>` | 3.000015 |
| `rust/library/core/src/ptr/mod.rs:1754` | `crate::intrinsics::read_via_copy(src)` | 4.000000 |
| `rust/library/core/src/ptr/mod.rs:1962` | `intrinsics::write_via_move(dst, src)` | 3.000000 |
| `rust/library/core/src/slice/index.rs:238` | `&(*slice)[self]` | 4.000000 |

#### `tc_kernel::main::{closure#2}`: source lines above 2 instructions/operation

| File:line | Source text | Instructions/operation |
|---|---|---:|
| `compiler-rust/benches/tc_kernel.rs:0` | `<no source line>` | 4.000000 |
| `compiler-rust/benches/tc_kernel.rs:118` | `let mut operand = &#124;&#124; match shape {` | 18.000000 |
| `compiler-rust/benches/tc_kernel.rs:127` | `};` | 12.000000 |
| `compiler-rust/src/tc/graph.rs:126` | `assert!(self.nodes.len() < (1 << 30));` | 4.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:635` | `self.ptr.cast()` | 4.000000 |
| `rust/library/alloc/src/vec/mod.rs:1002` | `if len == self.buf.capacity() {` | 8.000000 |
| `rust/library/alloc/src/vec/mod.rs:1009` | `self.len = len + 1;` | 4.000000 |
| `rust/library/alloc/src/vec/mod.rs:3160` | `let len = self.len;` | 4.000000 |
| `rust/library/core/src/ptr/mod.rs:1962` | `intrinsics::write_via_move(dst, src)` | 10.000000 |
| `rust/library/core/src/ptr/mut_ptr.rs:978` | `unsafe { intrinsics::offset(self, count) }` | 4.000000 |


### `unify_ground3`

| Function | Instructions/operation | Share of raw |
|---|---:|---:|
| `tc_kernel::main` | 409.002036 | 37.8216% |
| `<tc::unify::Checker>::reaches` | 214.049256 | 19.7937% |
| `tc_kernel::main::{closure#2}` | 178.000155 | 16.4602% |
| `<tc::graph::Graph>::link` | 165.000000 | 15.2580% |
| `<tc::unify::Checker>::push_lists` | 70.000000 | 6.4731% |
| `<tc::unify::Checker>::push_children` | 45.000000 | 4.1613% |
| other | 0.347389 | 0.0321% |
| **Raw total** | **1081.398836** | **100%** |

Subtract `build_ground3` **203.440878**: 1081.398836 − 203.440878 = **877.957958** instructions/operation, matching the results table after rounding.

#### `tc_kernel::main`: source lines above 2 instructions/operation

| File:line | Source text | Instructions/operation |
|---|---|---:|
| `compiler-rust/benches/tc_kernel.rs:115` | `if i & 0xfff == 0 {` | 2.000490 |
| `compiler-rust/benches/tc_kernel.rs:133` | `sink += left.0 as u64 + right.0 as u64;` | 6.000000 |
| `compiler-rust/src/tc/graph.rs:0` | `<no source line>` | 8.000000 |
| `compiler-rust/src/tc/graph.rs:11` | `#[derive(Clone, Copy, Debug, PartialEq, Eq)]` | 5.000000 |
| `compiler-rust/src/tc/graph.rs:29` | `self.head & 15` | 21.000000 |
| `compiler-rust/src/tc/graph.rs:211` | `Self::repr_parts(&mut self.nodes, &mut self.trail, self.speculation_depth, ty)` | 9.000000 |
| `compiler-rust/src/tc/graph.rs:224` | `while nodes[root.0 as usize].tag() == LINK {` | 70.000000 |
| `compiler-rust/src/tc/unify.rs:0` | `<no source line>` | 39.000000 |
| `compiler-rust/src/tc/unify.rs:160` | `let top = self.depth == 0;` | 4.000000 |
| `compiler-rust/src/tc/unify.rs:164` | `let token = if top && explain {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:173` | `self.depth += 1;` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:211` | `let l = self.g.nodes[left.0 as usize];` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:212` | `let r = self.g.nodes[right.0 as usize];` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:217` | `if l.tag() == VAR {` | 18.000000 |
| `compiler-rust/src/tc/unify.rs:220` | `if r.tag() == VAR {` | 15.000000 |
| `compiler-rust/src/tc/unify.rs:225` | `if l.tag() == CONSTR` | 21.000000 |
| `compiler-rust/src/tc/unify.rs:235` | `self.g.link(left, right);` | 8.000000 |
| `compiler-rust/src/tc/unify.rs:354` | `if self.reaches(node, ty, false) {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:392` | `let l = self.g.nodes[left.0 as usize];` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:393` | `let r = self.g.nodes[right.0 as usize];` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:395` | `if l.tag() == VAR {` | 4.000000 |
| `compiler-rust/src/tc/unify.rs:400` | `if r.tag() == VAR {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:405` | `if l.head & r.head & EXTENDED != 0 {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:415` | `self.g.link(left, right);` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:429` | `let pushed = self.push_children(l, r);` | 5.000000 |
| `compiler-rust/src/tc/unify.rs:620` | `while self.frames.len() > base {` | 6.000000 |
| `compiler-rust/src/tc/unify.rs:624` | `match frame.kind {` | 9.000000 |
| `compiler-rust/src/tc/unify.rs:628` | `if left != right && self.unify_pair(left, right).is_err() {` | 5.000000 |
| `compiler-rust/src/tc/unify.rs:646` | `self.memo.live != 0 && self.find_expansion(ty, true).0 != NONE` | 4.000000 |
| `compiler-rust/src/tc/unify.rs:656` | `if level == GENERIC {` | 6.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:635` | `self.ptr.cast()` | 6.000000 |
| `rust/library/alloc/src/vec/mod.rs:1784` | `&*core::intrinsics::aggregate_raw_ptr::<*const [T], _, _>(self.as_ptr(), self.len)` | 4.000000 |
| `rust/library/alloc/src/vec/mod.rs:1823` | `&mut *core::intrinsics::aggregate_raw_ptr::<*mut [T], _, _>(self.as_mut_ptr(), self.len)` | 4.000000 |
| `rust/library/alloc/src/vec/mod.rs:2925` | `self.len -= 1;` | 6.000000 |
| `rust/library/alloc/src/vec/mod.rs:3160` | `let len = self.len;` | 9.000000 |
| `rust/library/core/src/hint.rs:491` | `crate::intrinsics::black_box(dummy)` | 5.000000 |
| `rust/library/core/src/iter/range.rs:0` | `<no source line>` | 3.000015 |
| `rust/library/core/src/ptr/const_ptr.rs:879` | `unsafe { intrinsics::offset(self, count) }` | 6.000000 |
| `rust/library/core/src/ptr/mod.rs:1754` | `crate::intrinsics::read_via_copy(src)` | 12.000000 |
| `rust/library/core/src/ptr/mod.rs:1962` | `intrinsics::write_via_move(dst, src)` | 3.000000 |
| `rust/library/core/src/result.rs:2182` | `match self {` | 3.000000 |
| `rust/library/core/src/slice/index.rs:0` | `<no source line>` | 3.000000 |
| `rust/library/core/src/slice/index.rs:238` | `&(*slice)[self]` | 19.000000 |

#### `<tc::unify::Checker>::reaches`: source lines above 2 instructions/operation

| File:line | Source text | Instructions/operation |
|---|---|---:|
| `compiler-rust/src/tc/graph.rs:0` | `<no source line>` | 3.000000 |
| `compiler-rust/src/tc/graph.rs:11` | `#[derive(Clone, Copy, Debug, PartialEq, Eq)]` | 3.000000 |
| `compiler-rust/src/tc/graph.rs:29` | `self.head & 15` | 9.000000 |
| `compiler-rust/src/tc/graph.rs:33` | `self.head >> 8` | 3.000000 |
| `compiler-rust/src/tc/graph.rs:211` | `Self::repr_parts(&mut self.nodes, &mut self.trail, self.speculation_depth, ty)` | 3.000000 |
| `compiler-rust/src/tc/graph.rs:224` | `while nodes[root.0 as usize].tag() == LINK {` | 21.000000 |
| `compiler-rust/src/tc/level.rs:0` | `<no source line>` | 3.000000 |
| `compiler-rust/src/tc/level.rs:22` | `match node.tag() {` | 15.000000 |
| `compiler-rust/src/tc/level.rs:38` | `self.work.push(self.lists[(node.b + 1 + i) as usize]);` | 4.000000 |
| `compiler-rust/src/tc/unify.rs:705` | `if self.marks.len() < self.g.nodes.len() {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:708` | `if self.mark_generation == u32::MAX {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:720` | `fn reaches(&mut self, node: Ty, ty: Ty, deep: bool) -> bool {` | 10.000000 |
| `compiler-rust/src/tc/unify.rs:726` | `if self.marks[ty.0 as usize] == generation {` | 6.000000 |
| `compiler-rust/src/tc/unify.rs:731` | `if ty == node {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:735` | `self.marks[ty.0 as usize] = generation;` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:736` | `let descriptor = self.g.nodes[ty.0 as usize];` | 12.000000 |
| `compiler-rust/src/tc/unify.rs:737` | `if deep &#124;&#124; !self.stops_occurrence(descriptor) {` | 3.000000 |
| `compiler-rust/src/tc/unify.rs:742` | `}` | 8.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:635` | `self.ptr.cast()` | 14.000000 |
| `rust/library/alloc/src/vec/mod.rs:1002` | `if len == self.buf.capacity() {` | 7.000000 |
| `rust/library/alloc/src/vec/mod.rs:1009` | `self.len = len + 1;` | 4.000000 |
| `rust/library/alloc/src/vec/mod.rs:1784` | `&*core::intrinsics::aggregate_raw_ptr::<*const [T], _, _>(self.as_ptr(), self.len)` | 8.000000 |
| `rust/library/alloc/src/vec/mod.rs:1823` | `&mut *core::intrinsics::aggregate_raw_ptr::<*mut [T], _, _>(self.as_mut_ptr(), self.len)` | 3.000000 |
| `rust/library/alloc/src/vec/mod.rs:2922` | `if self.len == 0 {` | 9.000000 |
| `rust/library/alloc/src/vec/mod.rs:2925` | `self.len -= 1;` | 6.000000 |
| `rust/library/alloc/src/vec/mod.rs:3160` | `let len = self.len;` | 2.000026 |
| `rust/library/core/src/cmp.rs:2201` | `fn lt(&self, other: &Self) -> bool { *self <  *other }` | 4.000000 |
| `rust/library/core/src/iter/range.rs:1103` | `if self.start < self.end {` | 5.000000 |
| `rust/library/core/src/ptr/mod.rs:1754` | `crate::intrinsics::read_via_copy(src)` | 3.000000 |
| `rust/library/core/src/ptr/mod.rs:1962` | `intrinsics::write_via_move(dst, src)` | 7.000000 |
| `rust/library/core/src/slice/index.rs:238` | `&(*slice)[self]` | 19.000000 |


### `instance7`

| Function | Instructions/operation | Share of raw |
|---|---:|---:|
| `<tc::graph::Graph>::instance` | 351.000307 | 94.0335% |
| `tc_kernel::main` | 22.002030 | 5.8944% |
| other | 0.269284 | 0.0721% |
| **Raw total** | **373.271621** | **100%** |

Subtract `empty` **18.002260**: 373.271621 − 18.002260 = **355.269361** instructions/operation, matching the results table after rounding.

#### `<tc::graph::Graph>::instance`: source lines above 2 instructions/operation

| File:line | Source text | Instructions/operation |
|---|---|---:|
| `compiler-rust/src/tc/graph.rs:29` | `self.head & 15` | 12.000000 |
| `compiler-rust/src/tc/template.rs:0` | `<no source line>` | 8.000000 |
| `compiler-rust/src/tc/template.rs:364` | `pub fn instance(&mut self, template: Template) -> Ty {` | 9.000000 |
| `compiler-rust/src/tc/template.rs:365` | `if template.node_len == 0 {` | 4.000000 |
| `compiler-rust/src/tc/template.rs:373` | `let pools = self.template_pools[template.pools as usize];` | 6.000000 |
| `compiler-rust/src/tc/template.rs:374` | `if pools.external_len == 0 {` | 5.000000 |
| `compiler-rust/src/tc/template.rs:379` | `}` | 9.000000 |
| `compiler-rust/src/tc/template.rs:406` | `assert!(nodes.len() + (template.node_len as usize) < (1 << 30));` | 3.000000 |
| `compiler-rust/src/tc/template.rs:421` | `if ty.0 == NONE {` | 39.000000 |
| `compiler-rust/src/tc/template.rs:426` | `Ty(base + (ty.0 & !RELATIVE))` | 4.000000 |
| `compiler-rust/src/tc/template.rs:430` | `&template_lists[pools.lists as usize..(pools.lists + template.list_len) as usize];` | 3.000000 |
| `compiler-rust/src/tc/template.rs:439` | `params.extend(arguments.iter().map(&#124;&param&#124; {` | 6.000000 |
| `compiler-rust/src/tc/template.rs:450` | `let b_addend = [0, 0, list_base, list_base, param_base];` | 4.000000 |
| `compiler-rust/src/tc/template.rs:454` | `let a_mask = [NONE, 0, 0, 0, 0];` | 4.000000 |
| `compiler-rust/src/tc/template.rs:464` | `node.a &#124;= a_mask[node.tag() as usize];` | 41.000000 |
| `compiler-rust/src/tc/template.rs:465` | `node.b += b_addend[node.tag() as usize];` | 6.000000 |
| `compiler-rust/src/tc/template.rs:466` | `if node.tag() == ARROW {` | 12.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:640` | `if elem_size == 0 { usize::MAX } else { self.cap.as_inner() }` | 3.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:695` | `if self.needs_to_grow(len, additional, elem_layout) {` | 3.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:795` | `additional > self.capacity(elem_layout.size()).wrapping_sub(len)` | 3.000000 |
| `rust/library/alloc/src/vec/mod.rs:1784` | `&*core::intrinsics::aggregate_raw_ptr::<*const [T], _, _>(self.as_ptr(), self.len)` | 5.000000 |
| `rust/library/alloc/src/vec/set_len_on_drop.rs:19` | `self.local_len += increment;` | 6.000000 |
| `rust/library/alloc/src/vec/set_len_on_drop.rs:31` | `*self.len = self.local_len;` | 7.000000 |
| `rust/library/core/src/num/uint_macros.rs:1192` | `if self < rhs {` | 9.000000 |
| `rust/library/core/src/num/uint_macros.rs:2784` | `intrinsics::wrapping_sub(self, rhs)` | 4.000000 |
| `rust/library/core/src/ptr/const_ptr.rs:738` | `unsafe { intrinsics::ptr_offset_from_unsigned(self, origin) }` | 4.000000 |
| `rust/library/core/src/ptr/mod.rs:1962` | `intrinsics::write_via_move(dst, src)` | 34.000000 |
| `rust/library/core/src/slice/index.rs:90` | `let ptr = unsafe { crate::intrinsics::offset(ptr, offset) };` | 6.000000 |
| `rust/library/core/src/slice/index.rs:238` | `&(*slice)[self]` | 3.000000 |
| `rust/library/core/src/slice/iter/macros.rs:0` | `<no source line>` | 9.000000 |
| `rust/library/core/src/slice/iter/macros.rs:25` | `($this:ident, $len:ident => $zst_body:expr, $end:ident => $other_body:expr,) => {{` | 8.000000 |
| `rust/library/core/src/slice/iter/macros.rs:274` | `acc = f(acc, unsafe { & $( $mut_ )? *self.ptr.add(i).as_ptr() });` | 4.000000 |
| `rust/library/core/src/slice/iter/macros.rs:279` | `if i == len {` | 54.000000 |

#### `tc_kernel::main`: source lines above 2 instructions/operation

| File:line | Source text | Instructions/operation |
|---|---|---:|
| `compiler-rust/benches/tc_kernel.rs:0` | `<no source line>` | 5.000000 |
| `compiler-rust/benches/tc_kernel.rs:154` | `match index {` | 7.000000 |
| `compiler-rust/benches/tc_kernel.rs:158` | `3 => sink += g.instance(black_box(scheme7)).0 as u64,` | 3.000000 |
| `rust/library/core/src/hint.rs:491` | `crate::intrinsics::black_box(dummy)` | 3.000000 |


### `checker_instance7`

| Function | Instructions/operation | Share of raw |
|---|---:|---:|
| `<tc::graph::Graph>::instance` | 351.000307 | 96.0930% |
| `tc_kernel::main` | 14.002024 | 3.8333% |
| other | 0.269298 | 0.0737% |
| **Raw total** | **365.271629** | **100%** |

Subtract `empty` **18.002260**: 365.271629 − 18.002260 = **347.269369** instructions/operation, matching the results table after rounding.

#### `<tc::graph::Graph>::instance`: source lines above 2 instructions/operation

| File:line | Source text | Instructions/operation |
|---|---|---:|
| `compiler-rust/src/tc/graph.rs:29` | `self.head & 15` | 12.000000 |
| `compiler-rust/src/tc/template.rs:0` | `<no source line>` | 8.000000 |
| `compiler-rust/src/tc/template.rs:364` | `pub fn instance(&mut self, template: Template) -> Ty {` | 9.000000 |
| `compiler-rust/src/tc/template.rs:365` | `if template.node_len == 0 {` | 4.000000 |
| `compiler-rust/src/tc/template.rs:373` | `let pools = self.template_pools[template.pools as usize];` | 6.000000 |
| `compiler-rust/src/tc/template.rs:374` | `if pools.external_len == 0 {` | 5.000000 |
| `compiler-rust/src/tc/template.rs:379` | `}` | 9.000000 |
| `compiler-rust/src/tc/template.rs:406` | `assert!(nodes.len() + (template.node_len as usize) < (1 << 30));` | 3.000000 |
| `compiler-rust/src/tc/template.rs:421` | `if ty.0 == NONE {` | 39.000000 |
| `compiler-rust/src/tc/template.rs:426` | `Ty(base + (ty.0 & !RELATIVE))` | 4.000000 |
| `compiler-rust/src/tc/template.rs:430` | `&template_lists[pools.lists as usize..(pools.lists + template.list_len) as usize];` | 3.000000 |
| `compiler-rust/src/tc/template.rs:439` | `params.extend(arguments.iter().map(&#124;&param&#124; {` | 6.000000 |
| `compiler-rust/src/tc/template.rs:450` | `let b_addend = [0, 0, list_base, list_base, param_base];` | 4.000000 |
| `compiler-rust/src/tc/template.rs:454` | `let a_mask = [NONE, 0, 0, 0, 0];` | 4.000000 |
| `compiler-rust/src/tc/template.rs:464` | `node.a &#124;= a_mask[node.tag() as usize];` | 41.000000 |
| `compiler-rust/src/tc/template.rs:465` | `node.b += b_addend[node.tag() as usize];` | 6.000000 |
| `compiler-rust/src/tc/template.rs:466` | `if node.tag() == ARROW {` | 12.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:640` | `if elem_size == 0 { usize::MAX } else { self.cap.as_inner() }` | 3.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:695` | `if self.needs_to_grow(len, additional, elem_layout) {` | 3.000000 |
| `rust/library/alloc/src/raw_vec/mod.rs:795` | `additional > self.capacity(elem_layout.size()).wrapping_sub(len)` | 3.000000 |
| `rust/library/alloc/src/vec/mod.rs:1784` | `&*core::intrinsics::aggregate_raw_ptr::<*const [T], _, _>(self.as_ptr(), self.len)` | 5.000000 |
| `rust/library/alloc/src/vec/set_len_on_drop.rs:19` | `self.local_len += increment;` | 6.000000 |
| `rust/library/alloc/src/vec/set_len_on_drop.rs:31` | `*self.len = self.local_len;` | 7.000000 |
| `rust/library/core/src/num/uint_macros.rs:1192` | `if self < rhs {` | 9.000000 |
| `rust/library/core/src/num/uint_macros.rs:2784` | `intrinsics::wrapping_sub(self, rhs)` | 4.000000 |
| `rust/library/core/src/ptr/const_ptr.rs:738` | `unsafe { intrinsics::ptr_offset_from_unsigned(self, origin) }` | 4.000000 |
| `rust/library/core/src/ptr/mod.rs:1962` | `intrinsics::write_via_move(dst, src)` | 34.000000 |
| `rust/library/core/src/slice/index.rs:90` | `let ptr = unsafe { crate::intrinsics::offset(ptr, offset) };` | 6.000000 |
| `rust/library/core/src/slice/index.rs:238` | `&(*slice)[self]` | 3.000000 |
| `rust/library/core/src/slice/iter/macros.rs:0` | `<no source line>` | 9.000000 |
| `rust/library/core/src/slice/iter/macros.rs:25` | `($this:ident, $len:ident => $zst_body:expr, $end:ident => $other_body:expr,) => {{` | 8.000000 |
| `rust/library/core/src/slice/iter/macros.rs:274` | `acc = f(acc, unsafe { & $( $mut_ )? *self.ptr.add(i).as_ptr() });` | 4.000000 |
| `rust/library/core/src/slice/iter/macros.rs:279` | `if i == len {` | 54.000000 |

#### `tc_kernel::main`: source lines above 2 instructions/operation

| File:line | Source text | Instructions/operation |
|---|---|---:|
| `compiler-rust/src/tc/expand.rs:669` | `return self.g.instance(template);` | 3.000000 |

### What changed since R1's instance7

`git diff 3ce75c9b4 d1a9d3a5c -- compiler-rust/src/tc/template.rs`
and `git blame -L 447,470 compiler-rust/src/tc/template.rs` identify two
new executable source lines in `instance_inner`: the mask declaration at
454 and its application at 464. Blame assigns both to the squashed R3b
commit `d1a9d3a5c`; the original change is `774b8a2a7`, **Checker rewrite
R3b: instances drop variable names**. The `Graph::copy` VAR arm also changed,
but does not execute in this instance benchmark. The other changes to this
file since R1 are comments and a test-only derive.

| New source | Attributed instructions/call | Per copied node (six nodes) |
|---|---:|---:|
| `template.rs:454`, `let a_mask = [NONE, 0, 0, 0, 0];` | 4.00 | 0.666667 amortized |
| `template.rs:464`, `node.a \|= a_mask[node.tag() as usize];` | 41.00 | 6.833333 average |
| Total charged to these source lines | 45.00 | 7.500000 average |

There are **six**, not seven, distinct nodes in scheme7. The mask is applied
to all six, not only its two variables. Declaration cost is once per call;
per-node figures divide the observed line totals by six, not a claim that
each node executes identical machine instructions.

R1 publishes 327.27 net (327 rounded); this executable measures 355.269361
net for Graph::instance7, approximately **28.00 more per call** (4.67 per
copied node). **45 is a source-attribution charge, not the marginal cost of
the change.** Optimized code combines and redistributes work between lines;
45 cannot be added to 327 to predict this executable. Relative to that
published total, all other attributed code and harness differences net to
about −17.00. R1's per-line raw profiles are not available in this report,
so that residual is not asserted to be a measured line-by-line R1 comparison.
No counterfactual compiler edit or tuning was used to assign causality.

Both instance paths have exactly the same measured Graph::instance body
(351.000307 raw instructions/call). The eight-instruction difference between
their totals is in the benchmark caller (22.002030 vs 14.002024), not a faster
Graph implementation. Thus their net figures depend on the specified common
empty-loop subtraction; they should not be read as an isolated eight-instruction
saving from Checker::instance's memo test.

## Local-level unification measurements

Revision `2d93b31cf`, same machine, Rust toolchain, fat-LTO bench profile,
codegen units, debug information and zero/full subtraction method. The six
new operations are the three requested unifications and their three controls.
Each local case calls `c.g.begin_def()` exactly once before the loop, taking
Graph's initial level 1 to level 2; `clear_instances` does not change that
level. `var_at` and `constr_at` build **every** operand node at that level
(including the two nullary children), without GENERIC nodes or a second walk.
The generic cases still explicitly construct all their nodes at GENERIC.
The benchmark-only helpers state their construction cost; no compiler-path
function or data structure was added or changed.

The whole bench was rebuilt and all 27 operations were run, including
build-only controls, at both 0 and 1,000,000 iterations. The setup-level choice
and any extra operand construction overhead appear on both sides of each
unification/control subtraction. `begin_def` is outside both loops and is
also removed by the zero-iteration subtraction.

```sh
CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 CARGO_PROFILE_BENCH_DEBUG=line-tables-only \
  cargo bench --manifest-path compiler-rust/Cargo.toml --bench tc_kernel --no-run
# Finished `bench` profile [optimized + debuginfo] target(s) in 3m 04s
# Run the zero/full valgrind and cg_annotate commands above for every operation.
```

Raw output (exact I refs and raw instructions/iteration):

```text
operation zero full raw
instance1 327852 169388439 169.060587
instance3 327886 257636773 257.308887
instance5 327920 351665228 351.337308
instance7 327954 375599541 375.271587
generalize7 327886 864599501 864.271615
empty 327832 19330074 19.002242
lower7 327850 834599451 834.271601
copy7 327872 1822907875 1822.580003
repr 327838 181388439 181.060601
restore 327866 239388853 239.060987
keep 327878 218388851 218.060973
checker_instance1 328009 159388617 159.060608
checker_instance3 328043 247636951 247.308908
checker_instance5 328077 342665406 342.337329
checker_instance7 328111 365599719 365.271608
build_vars 328121 101398449 101.070328
unify_vars 328155 326398677 326.070522
build_ground1 328169 121405846 121.077677
unify_ground1 328203 324406074 324.077871
build_ground3 328237 231768995 231.440758
unify_ground3 328271 1110726939 1110.398668
build_vars_local 328062 101398390 101.070328
unify_vars_local 328096 386398618 386.070522
build_ground1_local 328096 121405824 121.077728
unify_ground1_local 328130 384406052 384.077922
build_ground3_local 328170 231768979 231.440809
unify_ground3_local 328199 1352726918 1352.398719
```

| Local operation | Full-minus-zero raw | Build-only twin | Net instructions | Generic net in same executable | Local minus generic |
|---|---:|---:|---:|---:|---:|
| `unify_vars_local` | 386.070522 | 101.070328 | 285.000194 | 225.000194 | 60.000000 |
| `unify_ground1_local` | 384.077922 | 121.077728 | 263.000194 | 203.000194 | 60.000000 |
| `unify_ground3_local` | 1352.398719 | 231.440809 | 1120.957910 | 878.957910 | 242.000000 |

The local cases are more expensive, not faster: +60, +60 and +242
instructions respectively versus their generic counterparts in this executable.
No attribution of that difference to individual checker mechanisms is claimed
without a local-case profile analysis. The old executable's generic three-node
net was 877.96; the new one is 878.96. This one-instruction dispatch/layout
change is reported, not hidden by reusing the previous executable's baseline.
Similarly, the empty loop is now 19.002242, not 18.002246; the results table
uses each executable's own empty loop. The three failing R3b gates still fail.

No full compiler test suite was run locally. No files under
`compiler-rust/src` changed. The earlier application sanity check was not
repeated: this addition still changes only bench code and documentation.

## K1

Revisions: before `f3f78af19` (trunk, with this report's bench), after
`4b1162ede` (this branch merged with that trunk). Same method as above: Valgrind 3.22
cachegrind, pinned toolchain, fat LTO, one codegen unit, line tables, one
million operations minus the zero-iteration run of the same program;
instances minus `empty`, `generalize7` and `lower7` minus `instance7`,
`repr`, `restore` and `keep` minus `instance1`, `copy7` minus `empty`,
unification minus its `build_*` twin. Both columns are measured on this
machine; the "before" column is not copied from the tables above (trunk
moved since: unification costs more there than at `2d93b31cf`). The
per-commit figures below were measured before the merge, against
`3b5b5b61e` (trunk `8ca6c42dbb` with this report's bench), whose figures
equal `f3f78af19`'s to the instruction.

| Operation | Before | After | Change | Gate |
|---|---:|---:|---:|---|
| `instance1` | 150.06 | 137.06 | -13.00 | ≤ 143: met |
| `instance3` | 238.31 | 217.31 | -21.00 | ≤ 223: met |
| `instance5` | 332.34 | 305.34 | -27.00 | ≤ 308: met |
| `instance7` | 356.27 | 325.27 | -31.00 | ≤ 330: met |
| `checker_instance1` | 140.06 | 126.06 | -14.00 | ≤ 143: met |
| `checker_instance3` | 228.31 | 207.31 | -21.00 | ≤ 223: met |
| `checker_instance5` | 323.34 | 294.34 | -29.00 | ≤ 308: met |
| `checker_instance7` | 346.27 | 314.27 | -32.00 | ≤ 330: met |
| `unify_vars` | 258.00 | 192.00 | -66.00 | lower: met |
| `unify_ground1` | 222.00 | 157.00 | -65.00 | lower: met |
| `unify_ground3` | 885.96 | 700.95 | -185.01 | lower: met |
| `unify_vars_local` | 337.00 | 267.00 | -70.00 | lower: met |
| `unify_ground1_local` | 306.00 | 235.00 | -71.00 | lower: met |
| `unify_ground3_local` | 1223.96 | 1013.95 | -210.01 | lower: met |
| `generalize7` | 489.00 | 449.00 | -40.00 | ≤ +2: met |
| `lower7` | 459.00 | 422.00 | -37.00 | ≤ +2: met |
| `copy7` | 1803.58 | 1709.58 | -94.00 | ≤ +2: met |
| `repr` | 12.00 | 9.00 | -3.00 | ≤ +2: met |
| `restore` | 70.00 | 63.00 | -7.00 | ≤ +2: met |
| `keep` | 49.00 | 44.00 | -5.00 | ≤ +2: met |

Per commit (net instructions, each built and measured whole):

| Operation | Before | 1: `5ca6d85e5` | 2: `94fd9d07d` | 3: `2a3d37c22` |
|---|---:|---:|---:|---:|
| `instance1/3/5/7` | 150/238/332/356 | 140/220/305/327 | 139/219/304/326 | 137/217/305/325 |
| `checker_instance1/3/5/7` | 140/228/323/346 | 130/210/296/317 | 131/211/297/318 | 126/207/294/314 |
| `unify_vars/ground1/ground3` | 258/222/886 | 258/222/886 | 214/174/753 | 192/157/701 |
| `…_local` | 337/306/1224 | 337/306/1224 | 293/258/1087 | 267/235/1014 |
| `generalize7`, `lower7` | 489, 459 | 489, 459 | 469, 439 | 449, 422 |
| `copy7` | 1803.58 | 1774.58 | 1772.58 | 1709.58 |
| `repr`, `restore`, `keep` | 12, 70, 49 | 12, 70, 49 | 12, 63, 45 | 9, 63, 44 |

### Raw output

```text
revision operation zero full raw
before instance1 329598 169390165 169.060567
before instance3 329632 257638579 257.308947
before instance5 329670 351667070 351.337400
before instance7 329707 375601306 375.271599
before generalize7 329664 864601235 864.271571
before empty 329578 19331848 19.002270
before lower7 329610 834601195 834.271585
before copy7 329618 1822909825 1822.580207
before repr 329598 181390151 181.060553
before restore 329640 239390551 239.060911
before keep 329646 218390571 218.060925
before checker_instance1 329761 159390326 159.060565
before checker_instance3 329803 247638748 247.308945
before checker_instance5 329839 342667237 342.337398
before checker_instance7 329873 365601470 365.271597
before build_vars 329880 99400209 99.070329
before unify_vars 329914 357400443 357.070529
before build_ground1 329914 119407620 119.077706
before unify_ground1 329948 341407854 341.077906
before build_ground3 329982 229770801 229.440819
before unify_ground3 330016 1115728703 1115.398687
before build_vars_local 329821 99400150 99.070329
before unify_vars_local 329855 436400384 436.070529
before build_ground1_local 329869 119407547 119.077678
before unify_ground1_local 329903 425407781 425.077878
before build_ground3_local 329937 229770728 229.440791
before unify_ground3_local 329971 1453728630 1453.398659
after instance1 331871 156392472 156.060601
after instance3 331905 236640902 236.308997
after instance5 331943 324669445 324.337502
after instance7 331980 344603682 344.271702
after generalize7 331923 793603625 793.271702
after empty 331851 19334107 19.002256
after lower7 331855 766603571 766.271716
after copy7 331891 1728912170 1728.580279
after repr 331857 165392444 165.060587
after restore 331899 219392871 219.060972
after keep 331905 200392863 200.060958
after checker_instance1 332034 145392633 145.060599
after checker_instance3 332076 226641071 226.308995
after checker_instance5 332112 313669612 313.337500
after checker_instance7 332146 333603846 333.271700
after build_vars 332124 98402464 98.070340
after unify_vars 332158 290402697 290.070539
after build_ground1 332186 118409875 118.077689
after unify_ground1 332220 275410108 275.077888
after build_ground3 332254 228773056 228.440802
after unify_ground3 332288 929726848 929.394560
after build_vars_local 332079 98402391 98.070312
after unify_vars_local 332113 365402624 365.070511
after build_ground1_local 332127 118409816 118.077689
after unify_ground1_local 332161 353410049 353.077888
after build_ground3_local 332195 228772997 228.440802
after unify_ground3_local 332229 1242726789 1242.394560
```

### 1. Instances copy nameless variables

Capture stores a variable's scheme name in the template node's level field
and NONE in `a`. Every template node is generic and an instance overwrites
the level, so the instance copies the node as stored; the `a_mask` table and
its OR per copied node (`template.rs:464`, 41 attributed instructions in
`instance7`) are gone. Readers of a variable's name in a template or
segment:

| Reader | Needs the scheme name? | Where it reads it now |
|---|---|---|
| `Graph::instance` (template.rs) | No: an instance is nameless (compiler/ml/btype.ml:510) | — |
| Canonical printer, `View::raw` (tc/canonical/view.rs) | Yes: prints `'a` of a scheme | `template::descriptor` of the stored node |
| Old-graph bridge, template nodes (tc/bridge/to_old.rs) | Yes: `Tvar (Some name)` of the published scheme | `template::descriptor` of the stored node |
| `publish` (tc/publish.rs) | No: moves the pools; shared nodes are not templates | — |
| `from_old` `resolve_roots` (tc/bridge/from_old.rs) | No: reads a synthetic tuple's list and arity | — |
| Differential printer (tc/differential.rs `node_form`) | No template read: prints live graph nodes | unchanged |
| `Segment::graph` (tc/publish.rs) | No: copies the pool as stored | — |

`Graph::copy` keeps its `VAR => node.a = NONE` arm: its source is a live
node whose name the unit still prints, so the source cannot hold no name,
and the store sits in a match arm the copy takes anyway.

### 2. `Graph::link` and `Graph::write`

`link` takes one slot borrow: one bounds check, one 16-byte load and the
link store. Only inside a speculation or for a named variable source does
the out-of-line `link_logged` run (trail entry, then the name rule, which
loads the target). `write` reads the old node only inside a speculation.
Small enough now, `link` is inlined by LLVM into its callers, so it has no
function row in the attribution. Function attribution of `unify_ground1`:

| Function | Before | After |
|---|---:|---:|
| `Checker::unify_distinct` | 131.000008 | 132.000007 |
| `tc_kernel::main::{closure#2}` | 92.000072 | 92.000072 |
| `tc_kernel::main` | 63.002027 | 51.002024 |
| `Graph::link` | 55.000000 | — (inlined) |

`Graph::link`'s inlined lines in `unify_distinct` after the change:
`graph.rs:158` (slot load) 2, `graph.rs:159` (link store) 5,
`graph.rs:165` (speculation and named-variable test) 4: **11**, plus its
bounds check and the Vec pointer/length loads charged to the library lines
`slice/index.rs:245`, `vec/mod.rs:1823` and `raw_vec/mod.rs:635`: about
15 per call, against 55. The call site's argument setup (`unify.rs:235`, 4)
is gone with the call. Gate (≤ 25): met.

### 3. `Graph::repr`

`repr_parts` returns a node whose head is not exactly `LINK` at once and
calls the cold, out-of-line `compress` (the former walk, unchanged step
counts and trail entries) for a link. Every link is written with
`head: LINK` (no arity or flag bits; documented on `LINK`), so the test
compares the whole head. x86-64 code of the fast path in `tc_kernel::main`:

```text
cmp    %r13,%rsi                 ; slice bounds check
jbe    <panic_bounds_check>
mov    %r13,%rax
shl    $0x4,%rax
cmpl   $0x1,(%rdi,%rax,1)        ; head == LINK
je     <call Graph::compress>    ; untaken for a representative
```

`graph.rs:248` is charged 12 instructions in `main` (two calls) against 29
for the two calls before. The bounds check stays: a handle is not known to be
in range without `unsafe`.

The changed inlining moved the register allocation of `Graph::instance`
(`self` spilled to the stack in the closed copy: `instance1` 139 → 148
with only the repr change). The closed path is now alone in `instance`: the
zero-node external root and the specialization with external references are
out-of-line calls (`instance_external_root`, `instance_with_externals`).

### Checks

```text
cargo test --manifest-path compiler-rust/Cargo.toml --lib tc::
test tc::differential::tests::kernel_tier_agrees_on_generated_cases ... ok
test tc::differential::tests::structural_tier_agrees_on_generated_cases ... ok
test tc::differential::tests::expand_tier_agrees_on_generated_cases ... ok
test result: ok. 137 passed; 0 failed; 22 ignored; 0 measured; 2606 filtered out
cargo clippy --locked --manifest-path compiler-rust/Cargo.toml --all-targets --all-features -- -D warnings
Finished `dev` profile [unoptimized + debuginfo] target(s)
```

That is the merged head. Before the merge the branch ran 131 passed and 28
ignored, the same as its base; this branch adds, removes and ignores no test
(the merged trunk brings the difference). `tc` is not on a compiler build's path, so
no application or `tests/tests` saving is claimed; the CI `Instruction
count` check reports the build's figures.

## K2

The hot paths of unification (CHECKER_REWRITE.md section 8.7), with no
change of behaviour. Same machine and method as "K1": Valgrind 3.22
cachegrind, pinned toolchain, fat LTO, one codegen unit, line tables, one
million operations minus the zero-iteration run of the same program;
unification minus its `build_*` twin, the other operations as in "K1".

The bench gained `bind_ground1` and `bind_ground1_local`, a fresh variable
unified with a fresh nullary constructor (generic and local level), with
their twins `build_bind_ground1` and `build_bind_ground1_local`
(`bbb4c39a9`, no change under `src`). They take the path of item (d).

### Per commit

Measured before the merge with trunk, on `0b175b7d0` with the bench
(`bbb4c39a9`); each column is a whole build and run of that commit.
(c) `034ae28c6`, (b) `c93cb0f78`, (a) `751e311c3`, (b) 2 `4ac02619b`,
(c) 2 `b3b746bc3`, (d) `9473631be`.

| Operation | Before | (c) | (b) | (a) | (b) 2 | (c) 2 | (d) |
|---|---:|---:|---:|---:|---:|---:|---:|
| `unify_vars` | 203.00 | 208.00 | 198.00 | 161.00 | 113.00 | 113.00 | 118.00 |
| `unify_ground1` | 155.00 | 155.00 | 155.00 | 121.00 | 121.00 | 121.00 | 119.00 |
| `unify_ground3` | 940.95 | 937.95 | 937.95 | 914.95 | 920.95 | 903.95 | 902.95 |
| `unify_vars_local` | 280.00 | 223.00 | 198.00 | 161.00 | 113.00 | 113.00 | 118.00 |
| `unify_ground1_local` | 231.00 | 158.00 | 158.00 | 124.00 | 124.00 | 121.00 | 119.00 |
| `unify_ground3_local` | 1253.95 | 968.95 | 968.95 | 945.95 | 951.95 | 903.95 | 902.95 |
| `bind_ground1` | 339.18 | 342.17 | 341.17 | 303.17 | 309.17 | 309.17 | 122.00 |
| `bind_ground1_local` | 339.18 | 342.17 | 341.17 | 303.17 | 309.17 | 309.17 | 122.00 |
| `instance1` | 137.06 | 137.06 | 137.06 | 137.06 | 137.06 | 137.06 | 137.06 |
| `instance3` | 217.31 | 217.31 | 217.31 | 217.31 | 217.31 | 217.31 | 217.31 |
| `instance5` | 305.34 | 305.34 | 305.34 | 305.34 | 305.34 | 305.34 | 305.34 |
| `instance7` | 325.27 | 325.27 | 325.27 | 325.27 | 325.27 | 325.27 | 325.27 |
| `checker_instance1` | 126.06 | 126.06 | 126.06 | 126.06 | 126.06 | 126.06 | 126.06 |
| `checker_instance3` | 207.31 | 207.31 | 207.31 | 207.31 | 207.31 | 207.31 | 207.31 |
| `checker_instance5` | 294.34 | 294.34 | 294.34 | 294.34 | 294.34 | 294.34 | 294.34 |
| `checker_instance7` | 314.27 | 314.27 | 314.27 | 314.27 | 314.27 | 314.27 | 314.27 |
| `generalize7` | 449.00 | 449.00 | 449.00 | 449.00 | 449.00 | 449.00 | 449.00 |
| `lower7` | 422.00 | 422.00 | 422.00 | 422.00 | 422.00 | 422.00 | 422.00 |
| `copy7` | 1709.58 | 1709.58 | 1709.58 | 1709.58 | 1709.58 | 1709.58 | 1709.58 |
| `repr` | 9.00 | 9.00 | 9.00 | 9.00 | 9.00 | 9.00 | 9.00 |
| `restore` | 63.00 | 63.00 | 63.00 | 63.00 | 63.00 | 63.00 | 63.00 |
| `keep` | 44.00 | 44.00 | 44.00 | 44.00 | 44.00 | 44.00 | 44.00 |

- (c) `lower_to` takes the representative and returns when it is not
  above the target.
- (b) two variables: the link, then one level write.
- (a) the root pair goes to `unify_pair` without a frame. `run_frames`
  takes the root pair and keeps one call site of `unify_pair`: a first
  form with a second call in `unify_distinct` made LLVM call `unify_pair`
  out of line (`unify_ground3` +22 over (b)).
- (b) 2: the two-variable arm out of `bind_routed` (whose entry and exit
  save six registers: 61 instructions a binding) into an always-inline
  helper called from `unify_pair`. Out of line it cost 47.
- (c) 2: the level tests of the nullary shortcut and of `unify_expanded`
  read the descriptors they hold. Without it `unify_ground3_local` was 25
  over `unify_ground3` for four level tests (24 allowed), all 25 in the
  two `lower_to` calls of `unify_expanded`. When neither head expanded and
  no type has a scope, at most one side is above the lower level and the
  four `repr` calls after the lowering returned the heads; they are not
  made. A form with the level test alone cost `unify_ground3` +12 in
  register pressure.
- (d) no walk for a node without a child: `bind_leaf` binds a variable to
  a variable or (no scoped types) to a childless node, one call site in
  `unify_pair`; `unify3` skips `occur` for a childless `t2'`. Two forms
  were dropped: a test at the start of `reaches` and `binding_scan` (11
  instructions on every walk of a node with children: `unify_ground3`
  +11), and three inlined binding bodies in `unify_pair` (+12 to +42 on
  every unification in spills).

### Merged head

Before: trunk `2f5d0c3b8` with only the bench file of this branch. After:
the merge `19226b5e1`. Trunk's new frame kinds (`Fields`, `Field`,
`FieldEnd`) and their arms in `run_frames` moved the figures on both
sides: on trunk alone `unify_ground3` went from 940.95 to 963.95. Against
this branch before the merge (column (d) above), the merged head is
`unify_vars` +1, `unify_ground1` +3, `unify_ground3` +12,
`bind_ground1` +2, each `_local` form the same; trunk's arms are as trunk
has them.

| Operation | Before (trunk) | After (merged) | Change |
|---|---:|---:|---:|
| `unify_vars` | 209.00 | 119.00 | -90.00 |
| `unify_ground1` | 161.00 | 122.00 | -39.00 |
| `unify_ground3` | 963.95 | 914.95 | -49.00 |
| `unify_vars_local` | 288.00 | 119.00 | -169.00 |
| `unify_ground1_local` | 239.00 | 122.00 | -117.00 |
| `unify_ground3_local` | 1284.95 | 914.95 | -370.00 |
| `bind_ground1` | 345.18 | 124.00 | -221.18 |
| `bind_ground1_local` | 345.18 | 124.00 | -221.18 |
| `instance1` | 137.06 | 137.06 | 0.00 |
| `instance3` | 217.31 | 217.31 | 0.00 |
| `instance5` | 305.34 | 305.34 | 0.00 |
| `instance7` | 325.27 | 325.27 | 0.00 |
| `checker_instance1` | 126.06 | 126.06 | 0.00 |
| `checker_instance3` | 207.31 | 207.31 | 0.00 |
| `checker_instance5` | 294.34 | 294.34 | 0.00 |
| `checker_instance7` | 314.27 | 314.27 | 0.00 |
| `generalize7` | 449.00 | 449.00 | 0.00 |
| `lower7` | 422.00 | 422.00 | 0.00 |
| `copy7` | 1709.58 | 1709.58 | 0.00 |
| `repr` | 9.00 | 9.00 | 0.00 |
| `restore` | 63.00 | 63.00 | 0.00 |
| `keep` | 44.00 | 44.00 | 0.00 |

Relations of section 8.7 on the merged head:

| Relation | Figure | Met |
|---|---|---|
| `_local` at most 6 over generic per level test | 0 for vars, ground1, ground3 | yes |
| `unify_vars` at most 150 | 119 | yes |
| `bind` inside `unify_vars` at most 20 | 26 executed (+7 to choose the side) | no |
| `bind_ground1` within 25 of `unify_vars` | 124 against 119 | yes |
| Operations that are not unification move at most 2 | 0 | yes |

**The binding inside `unify_vars`.** Counted per instruction (callgrind
`--dump-instr`, the addresses mapped to source lines). `Graph::link` is
16 of the 26: the `from == to` test 2, the slot load and the link store 8,
the speculation and name test 6. The other 10 are the bounds check of the
side chosen to be the variable (one call site serves both sides, so LLVM
does not know it was checked), reloading the vector pointer after the
link, the target's level load and the compare. A form with its own arm
for two variables measured 22 (`unify_vars` 114) but cost `bind_ground1`
+9, `unify_ground1` +3 and `unify_ground3` +2, so it was not kept. The 16
of the link are in `graph.rs`, which K2 does not change; the bounds checks
stay without `unsafe`.

**Targets of the table in 8.7.** They were arithmetic on the K1 figures;
trunk has since moved (the "before" here is above K1's: `unify_ground3`
963.95 against K1's 701). `unify_vars` (≤ 150), `unify_ground1` (≤ 125),
`unify_vars_local` (≤ 155) and `unify_ground1_local` (≤ 130) are met.
`unify_ground3` 914.95 (≤ 640) and `unify_ground3_local` 914.95 (≤ 660)
are not: 214 of them are `Checker::reaches`, the occurrence walk of the
right side of the structure pair, which stays (item (d) skips only a
side without a child, and the deferred check is K2b); 261 are
`unify_distinct` with the inlined loop, 132 `unify3`, 121
`unify_expanded`, 92 `expand_once`, 70 `push_lists`.

Function attribution on the merged head (net of the twin):

| Operation | `unify_distinct` | `reaches` | `unify3` | `unify_expanded` | `expand_once` | `push_lists` | bench `main` |
|---|---:|---:|---:|---:|---:|---:|---:|
| `unify_vars` | 94 | — | — | — | — | — | 25 |
| `unify_ground1` | 97 | — | — | — | — | — | 25 |
| `bind_ground1` | 99 | — | — | — | — | — | 25 |
| `unify_ground3` | 261 | 214.05 | 132 | 121 | 92 | 70 | 25 |

On trunk `unify_ground3_local` also spent 200 in `Graph::lower` and 88 in
`Checker::lower`, and `bind_ground1` 165.06 in `bind_routed` and 33 in
`push_flagged`; none of those run in these operations now.

### Raw output

```text
revision operation zero full raw
base empty 332891 19335163 19.002272
base instance1 332911 156393784 156.060873
base instance3 332945 236642294 236.309349
base instance5 332979 324671009 324.338030
base instance7 333013 344605243 344.272230
base generalize7 332973 793605175 793.272202
base lower7 332923 766605139 766.272216
base copy7 332931 1728913930 1728.580999
base repr 332911 165393770 165.060859
base restore 332953 219394178 219.061225
base keep 332951 200394190 200.061239
base checker_instance1 333068 145393937 145.060869
base checker_instance3 333102 226642447 226.309345
base checker_instance5 333136 313671162 313.338026
base checker_instance7 333170 333605396 333.272226
base build_vars 333201 78403662 78.070461
base unify_vars 333235 281403904 281.070669
base build_ground1 333235 98411226 98.077991
base unify_ground1 333269 253411468 253.078199
base build_ground3 333303 200774422 200.441119
base unify_ground3 333337 1141728428 1141.395091
base build_vars_local 333142 78403603 78.070461
base unify_vars_local 333176 358403845 358.070669
base build_ground1_local 333190 98411153 98.077963
base unify_ground1_local 333224 329411395 329.078171
base build_ground3_local 333258 200774349 200.441091
base unify_ground3_local 333292 1454728355 1454.395063
base build_bind_ground1 333234 88425486 88.092252
base bind_ground1 333336 427602896 427.269560
base build_bind_ground1_local 333315 88425567 88.092252
base bind_ground1_local 333278 427602838 427.269560
trunk empty 328580 19330838 19.002258
trunk instance1 328600 156389459 156.060859
trunk instance3 328634 236637969 236.309335
trunk instance5 328668 324666684 324.338016
trunk instance7 328702 344600918 344.272216
trunk generalize7 328652 793600868 793.272216
trunk lower7 328592 766600822 766.272230
trunk copy7 328628 1728909613 1728.580985
trunk repr 328594 165389439 165.060845
trunk restore 328628 219389867 219.061239
trunk keep 328633 200389858 200.061225
trunk checker_instance1 328777 145389632 145.060855
trunk checker_instance3 328817 226638148 226.309331
trunk checker_instance5 328859 313666871 313.338012
trunk checker_instance7 328895 333601107 333.272212
trunk build_vars 328882 78399357 78.070475
trunk unify_vars 328920 287399603 287.070683
trunk build_ground1 328948 98406925 98.077977
trunk unify_ground1 328981 259407166 259.078185
trunk build_ground3 329014 200770119 200.441105
trunk unify_ground3 329048 1164724125 1164.395077
trunk build_vars_local 328843 78399290 78.070447
trunk unify_vars_local 328872 366399527 366.070655
trunk build_ground1_local 328885 98406862 98.077977
trunk unify_ground1_local 328925 337407110 337.078185
trunk build_ground3_local 328954 200770059 200.441105
trunk unify_ground3_local 328988 1485724065 1485.395077
trunk build_bind_ground1 328909 88421175 88.092266
trunk bind_ground1 329031 433598577 433.269546
trunk build_bind_ground1_local 329016 88421254 88.092238
trunk bind_ground1_local 328958 433598532 433.269574
merged empty 330904 19333176 19.002272
merged instance1 330920 156391793 156.060873
merged instance3 330957 236640306 236.309349
merged instance5 330994 324669024 324.338030
merged instance7 331027 344603257 344.272230
merged generalize7 330978 793603180 793.272202
merged lower7 330928 766603144 766.272216
merged copy7 330951 1728911950 1728.580999
merged repr 330916 165391775 165.060859
merged restore 330966 219392191 219.061225
merged keep 330956 200392195 200.061239
merged checker_instance1 331093 145391962 145.060869
merged checker_instance3 331127 226640472 226.309345
merged checker_instance5 331167 313669193 313.338026
merged checker_instance7 331209 333603435 333.272226
merged build_vars 331226 78401687 78.070461
merged unify_vars 331260 197401721 197.070461
merged build_ground1 331260 98409251 98.077991
merged unify_ground1 331298 220409289 220.077991
merged build_ground3 331331 200772450 200.441119
merged unify_ground3 331364 1115726452 1115.395088
merged build_vars_local 331173 78401634 78.070461
merged unify_vars_local 331202 197401663 197.070461
merged build_ground1_local 331215 98409178 98.077963
merged unify_ground1_local 331255 220409218 220.077963
merged build_ground3_local 331290 200772381 200.441091
merged unify_ground3_local 331319 1115726379 1115.395060
merged build_bind_ground1 331253 88423505 88.092252
merged bind_ground1 331361 212423613 212.092252
merged build_bind_ground1_local 331346 88423598 88.092252
merged bind_ground1_local 331302 212423554 212.092252
```

### Checks

```text
cargo test --manifest-path compiler-rust/Cargo.toml --lib tc::
test result: ok. 192 passed; 0 failed; 17 ignored; 0 measured; 2621 filtered out
```

That is the merged head. Each commit before the merge ran 181 passed and
6 ignored, as its base did; this branch adds, removes and ignores no test,
and no step count changed an assertion (the unification step tests bound
the count from above). `tc` is not on a compiler build's path (the driver's
default checker is the old one), so no application or `tests/tests` saving
is claimed; the CI `Instruction count` check reports the build's figures.

## K3a: where unification's instructions go

### 1. Now: trunk `c4e9326eb`

Measured on x86-64 Linux with Valgrind 3.22.0 and the pinned
`rustc 1.102.0-nightly (ac8310ba6 2026-11-09)`. R1 method: fat LTO,
one codegen unit, line tables, 1,000,000 iterations minus zero, then
subtract the operation's own build-only twin. No compiler source changed.
The reference script was run first and reproduced R1's raw figures
(in particular `empty 18`, `unify_ground1 318`, `unify_ground3 746`).

```sh
CARGO_TARGET_DIR=/tmp/checker-reference cargo build --release \
  --manifest-path compiler-rust/docs/prototypes/checker-kernel/Cargo.toml
bash compiler-rust/docs/prototypes/checker-kernel/measure.sh \
  /tmp/checker-reference/release/checker-kernel
CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 CARGO_PROFILE_BENCH_DEBUG=line-tables-only \
  cargo bench --manifest-path compiler-rust/Cargo.toml --bench tc_kernel --no-run
# Finished `bench` profile [optimized + debuginfo] target(s) in 3m 32s
# For every operation, retain and annotate both files:
valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file=OP.zero.cg BENCH OP 0
valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file=OP.full.cg BENCH OP 1000000
cg_annotate --auto=yes --threshold=0 OP.full.cg
cg_annotate --auto=yes --threshold=0 OP.zero.cg
```

All operations, including controls. A dash means the row is a control,
not an additional subtraction. R4's `binder` is cheaper than the common
empty loop; its negative adjusted result is a control mismatch, not negative
execution cost. Use its raw column for the absolute loop measurement.

| Operation | Raw (full − zero)/million | Subtract | Net |
|---|---:|---|---:|
| `instance1` | 156.060859 | `empty` | 137.058573 |
| `instance3` | 236.309335 | `empty` | 217.307049 |
| `instance5` | 324.338016 | `empty` | 305.335730 |
| `instance7` | 344.272216 | `empty` | 325.269930 |
| `generalize7` | 793.272216 | `instance7` | 449.000000 |
| `empty` | 19.002286 | — | 19.002286 |
| `lower7` | 766.272202 | `instance7` | 421.999986 |
| `copy7` | 1728.581013 | `empty` | 1709.578727 |
| `repr` | 165.060901 | `instance1` | 9.000042 |
| `restore` | 219.061239 | `instance1` | 63.000380 |
| `keep` | 200.061281 | `instance1` | 44.000422 |
| `checker_instance1` | 145.060825 | `empty` | 126.058539 |
| `checker_instance3` | 226.309301 | `empty` | 207.307015 |
| `checker_instance5` | 313.337982 | `empty` | 294.335696 |
| `checker_instance7` | 333.272182 | `empty` | 314.269896 |
| `build_vars` | 78.070447 | — | 78.070447 |
| `unify_vars` | 197.070447 | `build_vars` | 119.000000 |
| `build_ground1` | 98.077977 | — | 98.077977 |
| `unify_ground1` | 220.077977 | `build_ground1` | 122.000000 |
| `build_ground3` | 200.441105 | — | 200.441105 |
| `unify_ground3` | 1117.395074 | `build_ground3` | 916.953969 |
| `build_vars_local` | 78.070445 | — | 78.070445 |
| `unify_vars_local` | 197.070445 | `build_vars_local` | 119.000000 |
| `build_ground1_local` | 98.077947 | — | 98.077947 |
| `unify_ground1_local` | 220.077947 | `build_ground1_local` | 122.000000 |
| `build_ground3_local` | 200.441075 | — | 200.441075 |
| `unify_ground3_local` | 1117.395044 | `build_ground3_local` | 916.953969 |
| `binder` | 11.000245 | `empty` | -8.002041 |
| `find_local` | 66.000251 | `empty` | 46.997965 |
| `find_open` | 243.000267 | `empty` | 223.997981 |
| `find_miss2` | 643.000253 | `empty` | 623.997967 |
| `bind_leave` | 191.184379 | `empty` | 172.182093 |
| `intern` | 179.000246 | `empty` | 159.997960 |
| `build_bind_ground1` | 88.092208 | — | 88.092208 |
| `bind_ground1` | 212.092266 | `build_bind_ground1` | 124.000058 |
| `build_bind_ground1_local` | 88.092266 | — | 88.092266 |
| `bind_ground1_local` | 212.092208 | `build_bind_ground1_local` | 123.999942 |

Raw output (I refs, including startup):

```text
operation zero full raw
instance1 330998 156391857 156.060859
instance3 331035 236640370 236.309335
instance5 331072 324669088 324.338016
instance7 331105 344603321 344.272216
generalize7 331042 793603258 793.272216
empty 330954 19333240 19.002286
lower7 330992 766603194 766.272202
copy7 331001 1728912014 1728.581013
repr 330938 165391839 165.060901
restore 331030 219392269 219.061239
keep 330978 200392259 200.061281
checker_instance1 331171 145391996 145.060825
checker_instance3 331205 226640506 226.309301
checker_instance5 331245 313669227 313.337982
checker_instance7 331287 333603469 333.272182
build_vars 331290 78401737 78.070447
unify_vars 331324 197401771 197.070447
build_ground1 331338 98409315 98.077977
unify_ground1 331376 220409353 220.077977
build_ground3 331409 200772514 200.441105
unify_ground3 331442 1117726516 1117.395074
build_vars_local 331223 78401668 78.070445
unify_vars_local 331252 197401697 197.070445
build_ground1_local 331279 98409226 98.077947
unify_ground1_local 331313 220409260 220.077947
build_ground3_local 331347 200772422 200.441075
unify_ground3_local 331381 1117726425 1117.395044
binder 421253 11421498 11.000245
find_local 913190 66913441 66.000251
find_open 890467 243890734 243.000267
find_miss2 1112031 644112284 643.000253
bind_leave 332865 191517244 191.184379
intern 625677 179625923 179.000246
build_bind_ground1 331317 88423525 88.092208
bind_ground1 331407 212423673 212.092266
build_bind_ground1_local 331360 88423626 88.092266
bind_ground1_local 331366 212423574 212.092208
```
