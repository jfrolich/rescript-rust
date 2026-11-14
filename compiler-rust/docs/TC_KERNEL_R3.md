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

Revisions: before `3b5b5b61e` (trunk `8ca6c42dbb` with this report's
bench merged), after `2a3d37c22`. Same method as above: Valgrind 3.22
cachegrind, pinned toolchain, fat LTO, one codegen unit, line tables, one
million operations minus the zero-iteration run of the same program;
instances minus `empty`, `generalize7` and `lower7` minus `instance7`,
`repr`, `restore` and `keep` minus `instance1`, `copy7` minus `empty`,
unification minus its `build_*` twin. Both columns are measured on this
machine; the "before" column is not copied from the tables above (trunk
moved since: unification costs more there than at `2d93b31cf`).

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
before instance1 329581 169390148 169.060567
before instance3 329615 257638562 257.308947
before instance5 329653 351667053 351.337400
before instance7 329690 375601289 375.271599
before generalize7 329647 864601218 864.271571
before empty 329561 19331831 19.002270
before lower7 329593 834601178 834.271585
before copy7 329601 1822909808 1822.580207
before repr 329581 181390134 181.060553
before restore 329623 239390534 239.060911
before keep 329629 218390554 218.060925
before checker_instance1 329744 159390309 159.060565
before checker_instance3 329786 247638731 247.308945
before checker_instance5 329822 342667220 342.337398
before checker_instance7 329856 365601453 365.271597
before build_vars 329863 99400192 99.070329
before unify_vars 329897 357400426 357.070529
before build_ground1 329897 119407603 119.077706
before unify_ground1 329931 341407837 341.077906
before build_ground3 329965 229770784 229.440819
before unify_ground3 329999 1115728686 1115.398687
before build_vars_local 329804 99400133 99.070329
before unify_vars_local 329838 436400367 436.070529
before build_ground1_local 329852 119407530 119.077678
before unify_ground1_local 329886 425407764 425.077878
before build_ground3_local 329920 229770711 229.440791
before unify_ground3_local 329954 1453728613 1453.398659
after instance1 331871 156392472 156.060601
after instance3 331905 236640902 236.308997
after instance5 331943 324669445 324.337502
after instance7 331980 344603682 344.271702
after generalize7 331923 793603625 793.271702
after empty 331851 19334107 19.002256
after lower7 331869 766603557 766.271688
after copy7 331891 1728912170 1728.580279
after repr 331843 165392458 165.060615
after restore 331899 219392871 219.060972
after keep 331891 200392877 200.060986
after checker_instance1 332034 145392633 145.060599
after checker_instance3 332076 226641071 226.308995
after checker_instance5 332112 313669612 313.337500
after checker_instance7 332146 333603846 333.271700
after build_vars 332138 98402450 98.070312
after unify_vars 332172 290402683 290.070511
after build_ground1 332186 118409875 118.077689
after unify_ground1 332220 275410108 275.077888
after build_ground3 332254 228773056 228.440802
after unify_ground3 332288 929726848 929.394560
after build_vars_local 332065 98402405 98.070340
after unify_vars_local 332099 365402638 365.070539
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
test result: ok. 131 passed; 0 failed; 28 ignored; 0 measured; 2606 filtered out
cargo clippy --locked --manifest-path compiler-rust/Cargo.toml --all-targets --all-features -- -D warnings
Finished `dev` profile [unoptimized + debuginfo] target(s)
```

The count (131 passed, 28 ignored) is the same before and after; no test
was added, removed or ignored. `tc` is not on a compiler build's path, so
no application or `tests/tests` saving is claimed; the CI `Instruction
count` check reports the build's figures.
