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

Measured on x86-64 Linux (AMD Ryzen 9 9950X, eight virtual CPUs) with
Valgrind 3.22.0 and the pinned
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

### 2–3. Existing operations: function and source attribution

For each `(file, function, line)` recorded by cachegrind and displayed by
`cg_annotate --auto=yes --threshold=0`, compute
`(operation.full − operation.zero − twin.full + twin.zero) / 1,000,000`.
The same subtraction is applied to runtime and benchmark instructions;
negative runtime entries are retained, not rounded away. The tables sum to
the measured net, with no unassigned instructions (rounding <0.0001).
`unify_ground3` is **916.953969**, not the older K2 executable's 914.95;
`expand_once` is 94 here rather than 92. This is a new measurement, not a
reuse of the K2 table. `unify_pair` and `run_frames` inline into
`unify_distinct`; `expand_head` and `lower_to` inline into callers;
`occur` calls `reaches`; `Graph::link` is inlined. There is no separate
out-of-line charge for these functions. `lower_to` executes no attributed
instructions in these four generic operations.

Classes refer to the work, not an assertion that its machine sequence is
minimal. REQUIRED means OCaml performs the corresponding test/traversal or
write on this input. OVERHEAD is limited to work with an established
redundancy or representation-only dispatch. UNSURE means that the profile
cannot separate required work from avoidable machine implementation cost.
In particular, for every UNSURE library, line-zero, prologue/epilogue,
representative or caller bucket, instruction-address inline stacks and a
separately measured candidate would be needed to price a safe removal.
For the target reload after a link, the named-variable rule must first be
proved not to affect the reused descriptor. The explicit stack replaces
OCaml recursion: its *entire* cost is not declared removable.

The occurrence traversal is REQUIRED: ctype.ml:2330 calls `occur` for this
structure pair, and :1488–1490 selects the reachability shortcut. However,
the current OCaml shortcut (:1432–1465) uses a 256-node budget and **no
marks**. Generation setup and mark loads/stores are OVERHEAD on these
small successful walks, not proof that marking can be deleted on arbitrary
cyclic or shared graphs. Library costs for those marks remain UNSURE,
because inline line tables mix them with stack and descriptor indexing. Likewise
an attempted expansion on an unexpandable constructor is not automatically
overhead: :2279–2282 explicitly asks for the head expansions. A declaration
eligibility test may implement that request cheaply, but cannot be removed
merely because this particular input does not expand.

Function totals (all source files, including inlined library code):

| Function | unify_ground3 | unify_ground1 | unify_vars | bind_ground1 |
|---|---:|---:|---:|---:|
| `unify_distinct` | 261.000000 | 97.000000 | 94.000000 | 99.000000 |
| `reaches` | 214.045160 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` | 132.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` | 121.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` | 94.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` | 70.000004 | 0.000000 | 0.000000 | 0.000000 |
| `tc_kernel::main` | 25.000000 | 25.000000 | 25.000000 | 25.000000 |
| `__memcpy_avx_unaligned_erms` | -0.141984 | 0.000000 | 0.000000 | 0.000000 |
| `__memset_avx2_unaligned_erms` | 0.045056 | 0.000000 | 0.000000 | 0.000000 |
| Other runtime | 0.005733 | 0.000000 | 0.000000 | 0.000058 |
| **Total** | 916.953969 | 122.000000 | 119.000000 | 124.000058 |

Disjoint source-line groups. Function names are machine-code owners; inline
function names are in the work column. `0` is DWARF line zero, not source
line one. Library groups retain their individual source lines rather than
pretending a bounds check can be assigned uniquely to a Rust call site.
All citations below are `compiler/ml/ctype.ml` unless explicitly marked.

| Machine function / source lines | Work | Class; OCaml lines | unify_ground3 | unify_ground1 | unify_vars | bind_ground1 |
|---|---|---|---:|---:|---:|---:|
| `expand_once` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` / `core/src/slice/index.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` / `core/src/slice/index.rs:184` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 10.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` / `expand.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 16.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` / `expand.rs:532–555` | find_expansion: arity/private test and memo lookup | REQUIRED; 2279–2282; 1193–1196 | 6.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` / `expand.rs:631–631` | expand_once: function entry | UNSURE; 2279–2282; 1187 | 16.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` / `expand.rs:632–646` | expand_once: tag, memo miss and declaration lookup | REQUIRED; 2279–2282; 1188–1216 | 12.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` / `expand.rs:647–674` | expand_once: memo hit, eligibility, arity, result/return | REQUIRED; 2279–2282; 1196–1223 | 16.000000 | 0.000000 | 0.000000 | 0.000000 |
| `expand_once` / `graph.rs:28–36` | Node tag/arity extraction | REQUIRED; 2239; 2308; 2347–2350 | 6.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `alloc/src/vec/mod.rs:1002` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `alloc/src/vec/mod.rs:1009` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `alloc/src/vec/mod.rs:999` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `core/src/cmp.rs:2201` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `core/src/iter/range.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `core/src/iter/range.rs:1145` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 7.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `core/src/ptr/mod.rs:1962` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `core/src/ptr/mut_ptr.rs:978` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 8.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `unify.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `push_lists` / `unify.rs:1106–1122` | push_lists/push_pair: iterate children and save pairs | UNSURE; 2347–2350; 2440–2445 | 23.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 14.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/raw_vec/mod.rs:640` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/raw_vec/mod.rs:695` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/raw_vec/mod.rs:795` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/mod.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/mod.rs:1002` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/mod.rs:1009` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 8.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/mod.rs:2922` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 9.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/mod.rs:2925` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/mod.rs:3141` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/mod.rs:3160` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000026 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/mod.rs:999` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/spec_extend_with.rs:100` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `alloc/src/vec/spec_extend_with.rs:86` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `core/src/cmp.rs:2201` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `core/src/iter/range.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `core/src/iter/range.rs:1103` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 5.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `core/src/num/uint_macros.rs:2784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `core/src/ptr/mod.rs:1754` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `core/src/ptr/mod.rs:1962` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 5.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `core/src/ptr/mod.rs:570` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.008192 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `core/src/ptr/mut_ptr.rs:978` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.008192 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `core/src/slice/index.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 19.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `graph.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `graph.rs:234–252` | Graph::repr: representative loads/tests (inlined) | UNSURE; 2231–2233; 2278–2288 | 21.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `graph.rs:28–36` | Node tag/arity extraction | REQUIRED; 2239; 2308; 2347–2350 | 9.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `level.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `level.rs:1–200` | Graph::children: occurrence child traversal | REQUIRED; 2330; 1384–1408 | 19.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `unify.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 6.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `unify.rs:1280–1290` | fresh_marks: generation and storage checks | OVERHEAD; 2330; 1432–1465 (bounded walk has no marks) | 7.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `unify.rs:1296–1301` | reaches: entry, work stack and representative | UNSURE; 2330; 1432–1465 | 11.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `unify.rs:1302–1306` | reaches: visited-mark test | OVERHEAD; 2330; 1432–1465 (bounded walk has no marks) | 6.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `unify.rs:1307–1310` | reaches: occurrence identity test | REQUIRED; 2330; 1436 | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `unify.rs:1311–1311` | reaches: visited-mark store | OVERHEAD; 2330; 1432–1465 (bounded walk has no marks) | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `reaches` / `unify.rs:1312–1318` | reaches: descriptors, row exclusion, children and exit | REQUIRED; 2330; 1439–1458 | 26.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `core/src/slice/index.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `core/src/slice/index.rs:245` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 5.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `graph.rs:154–156` | Graph::link: repeated identity guard | OVERHEAD; 2233; 2257; 2331 (distinct pair already established) | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `graph.rs:157–164` | Graph::link: load source, write link | REQUIRED; 2221; 2257; 2331 | 7.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `graph.rs:165–167` | Graph::link: speculation/name-rule guard | REQUIRED; 2221; 2257; 2331 (btype.ml:713–731) | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `graph.rs:28–36` | Node tag/arity extraction | REQUIRED; 2239; 2308; 2347–2350 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `graph.rs:47` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `unify.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 21.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `unify.rs:1334–1337` | childless: prove occurrence walk unnecessary | REQUIRED; 2218; 2330 | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `unify.rs:37` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `unify.rs:502–510` | occur: call reaches and test its answer | REQUIRED; 2330; 1488–1490 | 11.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `unify.rs:740–748` | unify3: entry and descriptor loads | UNSURE; 2305–2308 | 8.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `unify.rs:749–785` | unify3: variable/field/mode and create_recursion tests | REQUIRED; 2309–2332 | 16.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `unify.rs:789–793` | unify3: occurrence and link routing | REQUIRED; 2330–2331 | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `unify.rs:794–834` | unify3: explain/repair continuations, children and result | UNSURE; 2333–2438 | 16.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify3` / `unify.rs:909–944` | push_children: shape, arity, path match and child ranges | REQUIRED; 2334–2350 | 20.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 1.000000 | 1.000000 | 1.000000 |
| `unify_distinct` / `alloc/src/vec/mod.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 2.000000 | 2.000000 | 2.000000 |
| `unify_distinct` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 1.000000 | 1.000000 | 1.000000 |
| `unify_distinct` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 2.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `alloc/src/vec/mod.rs:2925` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `alloc/src/vec/mod.rs:3160` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 8.000000 | 6.000000 | 6.000000 | 6.000000 |
| `unify_distinct` / `core/src/ptr/const_ptr.rs:879` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `core/src/ptr/mod.rs:1754` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 12.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `core/src/slice/index.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 1.000000 | 1.000000 | 1.000000 |
| `unify_distinct` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 18.000000 | 6.000000 | 9.000000 | 9.000000 |
| `unify_distinct` / `core/src/slice/index.rs:245` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 2.000000 | 3.000000 | 3.000000 |
| `unify_distinct` / `graph.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 4.000000 | 1.000000 | 2.000000 | 2.000000 |
| `unify_distinct` / `graph.rs:154–156` | Graph::link: repeated identity guard | OVERHEAD; 2233; 2257; 2331 (distinct pair already established) | 2.000000 | 1.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `graph.rs:157–164` | Graph::link: load source, write link | REQUIRED; 2221; 2257; 2331 | 16.000000 | 8.000000 | 8.000000 | 8.000000 |
| `unify_distinct` / `graph.rs:165–167` | Graph::link: speculation/name-rule guard | REQUIRED; 2221; 2257; 2331 (btype.ml:713–731) | 8.000000 | 4.000000 | 6.000000 | 6.000000 |
| `unify_distinct` / `graph.rs:234–252` | Graph::repr: representative loads/tests (inlined) | UNSURE; 2231–2233; 2278–2288 | 28.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `graph.rs:47` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 2.000000 | 2.000000 | 2.000000 | 2.000000 |
| `unify_distinct` / `unify.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 24.000000 | 8.000000 | 8.000000 | 8.000000 |
| `unify_distinct` / `unify.rs:1186–1199` | run_frames: pair result, loop bound and pop | UNSURE; 2347–2350; 2440–2445 | 8.000000 | 2.000000 | 2.000000 | 2.000000 |
| `unify_distinct` / `unify.rs:1200–1201` | run_frames: tagged continuation dispatch | OVERHEAD; 2347–2350 (recursive calls, no FrameKind) | 6.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `unify.rs:1202–1223` | run_frames: child identity test and other continuations | REQUIRED; 2231–2233; 2428–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `unify.rs:1334–1337` | childless: prove occurrence walk unnecessary | REQUIRED; 2218; 2330 | 0.000000 | 0.000000 | 0.000000 | 4.000000 |
| `unify_distinct` / `unify.rs:187–227` | unify_distinct: depth, explain/snapshot entry and exit | UNSURE; 2271–2274; 2732–2737 | 30.000000 | 30.000000 | 30.000000 | 30.000000 |
| `unify_distinct` / `unify.rs:238–258` | unify_pair: load descriptors, choose variable side | REQUIRED; 2239–2243 | 27.000000 | 9.000000 | 6.000000 | 6.000000 |
| `unify_distinct` / `unify.rs:268–280` | unify_pair: nullary same-head shortcut and level test | REQUIRED; 2248–2257 | 29.000000 | 11.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `unify.rs:281–282` | unify_pair: route to unify2 | REQUIRED; 2270 | 3.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_distinct` / `unify.rs:337–339` | binds_leaf: prove binding needs no walk | REQUIRED; 2218–2222; 2240–2243 | 0.000000 | 0.000000 | 4.000000 | 5.000000 |
| `unify_distinct` / `unify.rs:359–371` | bind_leaf: reload target and compare level after link | UNSURE; 2221–2222 | 0.000000 | 0.000000 | 3.000000 | 3.000000 |
| `unify_expanded` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `core/src/cmp.rs:2289` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 5.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `core/src/result.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `core/src/slice/index.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `expand.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 1.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `expand.rs:792–820` | expand_head: repr, expansion loop and stop tests | REQUIRED; 2279–2282; 1267–1280 | 15.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `graph.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 11.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 4.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `graph.rs:234–252` | Graph::repr: representative loads/tests (inlined) | UNSURE; 2231–2233; 2278–2288 | 25.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `unify.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 7.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `unify.rs:671–676` | unify_expanded: function entry | UNSURE; 2276 | 9.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `unify.rs:677–683` | unify_expanded: expansion/re-expansion decision | REQUIRED; 2278–2282 | 2.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `unify.rs:684–716` | unify_expanded: levels, identity and lowering | REQUIRED; 2283–2288 | 9.000000 | 0.000000 | 0.000000 | 0.000000 |
| `unify_expanded` / `unify.rs:717–728` | unify_expanded: choose direction, call unify3 and return | REQUIRED; 2299–2303 | 18.000000 | 0.000000 | 0.000000 | 0.000000 |
| `runtime` / `other:—` | Allocation, bulk memory, startup and twin-layout remainder | UNSURE; 2227–2438 (allocator cost not specified) | -0.092257 | 0.000000 | 0.000000 | 0.000058 |
| `tc_kernel::main` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 1.000000 | 1.000000 | 1.000000 |
| `tc_kernel::main` / `core/src/result.rs:1182` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 2.000000 | 2.000000 | 2.000000 |
| `tc_kernel::main` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 1.000000 | 1.000000 | 1.000000 | 1.000000 |
| `tc_kernel::main` / `graph.rs:234–252` | Graph::repr: representative loads/tests (inlined) | UNSURE; 2231–2233; 2278–2288 | 14.000000 | 14.000000 | 14.000000 | 14.000000 |
| `tc_kernel::main` / `tc_kernel.rs:282` | Benchmark call-site / result consumption difference | UNSURE; 2227 (harness has no OCaml counterpart) | 2.000000 | 2.000000 | 2.000000 | 2.000000 |
| `tc_kernel::main` / `unify.rs:169–176` | unify: identity test and call | REQUIRED; 2229–2233 | 5.000000 | 5.000000 | 5.000000 | 5.000000 |
| Sub-millithreshold groups | Startup/library attribution below 0.001 each | UNSURE; 2227–2438 | 0.001144 | 0.000000 | 0.000000 | 0.000000 |
| **Total including remainder** | | | 916.953969 | 122.000000 | 119.000000 | 124.000058 |

### 4. Declared datatype and parameterised abbreviation

The existing `unify_ground3` uses an **empty** `TypeTable`; its constructor
indices take the out-of-range abstract-type default. It is therefore not
the requested populated declaration-table case. Added four operations in
`benches/tc_kernel.rs::constructor_application`:

- `unify_datatype2` / `build_datatype2`: fresh `c<a,b>` on both sides;
  `a`, `b` have distinct indices and DATATYPE rows; `c` has a DATATYPE row
  with arity 2. No manifest or memo exists.
- `unify_abbrev2` / `build_abbrev2`: the same operands, but `c<x,y> = (x,y)`.
  One captured template contains the parameters and tuple body. Relative
  references are recovered by a setup-only instance through the public API.
  Both heads expand; the post-loop assertion verifies exactly two memo
  entries per unification in the final reset batch. Datatype/control runs
  assert zero entries. Nothing is pre-expanded.

All nodes remain GENERIC, as in the original ground3 operation. Every 4096
iterations both twins clear the instance pools and memo-entry vector; this
avoids retaining stale slot indices. No inherited or nullary memo is made
by this template. The per-operation operands are fresh; expansion nodes
are additional work on the unification side, never charged to the control.
The sink consumes both handles on both sides; its numeric value differs
for abbreviation runs because expansion allocates nodes between operands.
The same loop, arithmetic and construction instructions run in both twins.
The assertion runs outside the loop; its measured constant cost is retained.

Measured the final formatted bench, same flags and tool as section 1.
The four original unification/control pairs were rerun too: their net
figures are unchanged to 0.0001. Thus the new measurements are not silently
substituted for the original executable's source attribution.

| Operation | Raw | Twin raw | Net |
|---|---:|---:|---:|
| `unify_datatype2` | 1147.398252 | 186.443838 | **960.954414** |
| `unify_abbrev2` | 3012.710757 | 186.441869 | **2826.268888** |

The populated datatype row adds **44.000445** over `unify_ground3`:
`expand_once` rises from 94 to 138, while the other major function totals
stay fixed. The empty-table case skips the flags loaded from an actual row.
That is declaration lookup/eligibility work OCaml also needs, not 44
instructions proven removable. The abbreviation case spends 798 in
`expand_once` (including inlined `subst`), 458 in template instances, 306
in link compression and 82 in memo writes. `reaches` rises to 434 because
`create_recursion` also asks whether the expanded left occurs in the
original right (:2309); it is not a second accidental `occur` call.

Raw output:

```text
operation zero full raw
build_datatype2 319583 186763421 186.443838
unify_datatype2 319588 1147717840 1147.398252
build_abbrev2 325112 186766981 186.441869
unify_abbrev2 325118 3013035875 3012.710757
build_vars 331399 78401846 78.070447
unify_vars 331433 197401880 197.070447
build_ground1 331458 98409435 98.077977
unify_ground1 331492 220409469 220.077977
build_ground3 331526 200772631 200.441105
unify_ground3 331560 1117726634 1117.395074
build_bind_ground1 331426 88423664 88.092238
bind_ground1 331520 212423786 212.092266
```

Function totals (all source files, including inlined library code):

| Function | unify_datatype2 | unify_abbrev2 |
|---|---:|---:|
| `expand_once` | 138.000000 | 798.000000 |
| `instance` | 0.000000 | 458.000169 |
| `reaches` | 214.045163 | 434.045160 |
| `compress` | 0.000000 | 306.000000 |
| `unify_distinct` | 261.000000 | 281.000000 |
| `unify_expanded` | 121.000000 | 251.000000 |
| `unify3` | 132.000000 | 191.000005 |
| `memorize` | 0.000000 | 82.000072 |
| `push_lists` | 70.000004 | 0.000000 |
| `tc_kernel::main` | 25.000000 | 25.000000 |
| `__memcpy_avx_unaligned_erms` | -0.141888 | 0.160316 |
| `__memset_avx2_unaligned_erms` | 0.045056 | 0.049152 |
| Other runtime | 0.006079 | 0.014014 |
| **Total** | 960.954414 | 2826.268888 |

Disjoint source-line groups. Function names are machine-code owners; inline
function names are in the work column. `0` is DWARF line zero, not source
line one. Library groups retain their individual source lines rather than
pretending a bounds check can be assigned uniquely to a Rust call site.
All citations below are `compiler/ml/ctype.ml` unless explicitly marked.

| Machine function / source lines | Work | Class; OCaml lines | unify_datatype2 | unify_abbrev2 |
|---|---|---|---:|---:|
| `compress` / `graph.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 0.000000 | 48.000000 |
| `compress` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 0.000000 | 12.000000 |
| `compress` / `graph.rs:254–330` | Graph::compress: follow and compress parameter links | REQUIRED; 2231–2232; 2278–2288 | 0.000000 | 234.000000 |
| `compress` / `graph.rs:28–36` | Node tag/arity extraction | REQUIRED; 2239; 2308; 2347–2350 | 0.000000 | 12.000000 |
| `instance` / `alloc/src/raw_vec/mod.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `instance` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `instance` / `alloc/src/raw_vec/mod.rs:640` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `instance` / `alloc/src/raw_vec/mod.rs:695` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `instance` / `alloc/src/raw_vec/mod.rs:795` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `instance` / `alloc/src/vec/mod.rs:1384` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `instance` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 6.000000 |
| `instance` / `alloc/src/vec/mod.rs:3160` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `instance` / `alloc/src/vec/set_len_on_drop.rs:19` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 10.000000 |
| `instance` / `alloc/src/vec/set_len_on_drop.rs:31` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 10.000000 |
| `instance` / `core/src/num/uint_macros.rs:1113` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `instance` / `core/src/num/uint_macros.rs:1192` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 12.000000 |
| `instance` / `core/src/num/uint_macros.rs:2784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 6.000000 |
| `instance` / `core/src/ptr/const_ptr.rs:738` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 6.000000 |
| `instance` / `core/src/ptr/mod.rs:1962` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 44.000000 |
| `instance` / `core/src/ptr/non_null.rs:1709` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `instance` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 6.000000 |
| `instance` / `core/src/slice/index.rs:90` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `instance` / `core/src/slice/iter/macros.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 18.000000 |
| `instance` / `core/src/slice/iter/macros.rs:25` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `instance` / `core/src/slice/iter/macros.rs:274` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 12.000000 |
| `instance` / `core/src/slice/iter/macros.rs:279` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 80.000000 |
| `instance` / `core/src/slice/iter/macros.rs:28` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 10.000000 |
| `instance` / `graph.rs:28–36` | Node tag/arity extraction | REQUIRED; 2239; 2308; 2347–2350 | 0.000000 | 16.000000 |
| `instance` / `template.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 0.000000 | 16.000000 |
| `instance` / `template.rs:1–1000` | Graph::instance: relocate and copy manifest template | REQUIRED; 2279–2282; 1100–1123 | 0.000000 | 174.000000 |
| `expand_once` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 28.000000 |
| `expand_once` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 28.000000 |
| `expand_once` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 14.000000 |
| `expand_once` / `alloc/src/vec/mod.rs:3160` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 6.000000 |
| `expand_once` / `core/src/cmp.rs:2201` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 28.000000 |
| `expand_once` / `core/src/iter/range.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `expand_once` / `core/src/iter/range.rs:1103` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 6.000000 |
| `expand_once` / `core/src/slice/index.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 4.000000 |
| `expand_once` / `core/src/slice/index.rs:184` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 4.000000 |
| `expand_once` / `core/src/slice/index.rs:186` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 4.000000 |
| `expand_once` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 10.000000 | 82.000000 |
| `expand_once` / `expand.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 18.000000 | 44.000000 |
| `expand_once` / `expand.rs:245–250` | TypeTable::info: declaration facts | REQUIRED; 2279–2282; 1207–1216 | 12.000000 | 12.000000 |
| `expand_once` / `expand.rs:532–555` | find_expansion: arity/private test and memo lookup | REQUIRED; 2279–2282; 1193–1196 | 10.000000 | 16.000000 |
| `expand_once` / `expand.rs:631–631` | expand_once: function entry | UNSURE; 2279–2282; 1187 | 16.000000 | 64.000000 |
| `expand_once` / `expand.rs:632–646` | expand_once: tag, memo miss and declaration lookup | REQUIRED; 2279–2282; 1188–1216 | 22.000000 | 50.000000 |
| `expand_once` / `expand.rs:647–674` | expand_once: memo hit, eligibility, arity, result/return | REQUIRED; 2279–2282; 1196–1223 | 26.000000 | 82.000000 |
| `expand_once` / `expand.rs:717–746` | subst: manifest relocation, memo and instance | REQUIRED; 2279–2282; 1100–1123 | 0.000000 | 84.000000 |
| `expand_once` / `expand.rs:747–784` | subst: parameter binding and result | REQUIRED; 2279–2282; 1100–1123 | 0.000000 | 50.000000 |
| `expand_once` / `graph.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `expand_once` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `expand_once` / `graph.rs:154–156` | Graph::link: repeated identity guard | OVERHEAD; 1100–1123; 2216–2222 (fresh parameter distinct from argument) | 0.000000 | 4.000000 |
| `expand_once` / `graph.rs:157–164` | Graph::link: load source, write link | REQUIRED; 2221; 2257; 2331 | 0.000000 | 28.000000 |
| `expand_once` / `graph.rs:165–167` | Graph::link: speculation/name-rule guard | REQUIRED; 2221; 2257; 2331 (btype.ml:713–731) | 0.000000 | 24.000000 |
| `expand_once` / `graph.rs:234–252` | Graph::repr: representative loads/tests (inlined) | UNSURE; 2231–2233; 2278–2288 | 0.000000 | 100.000000 |
| `expand_once` / `graph.rs:28–36` | Node tag/arity extraction | REQUIRED; 2239; 2308; 2347–2350 | 6.000000 | 26.000000 |
| `memorize` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 6.000000 |
| `memorize` / `alloc/src/vec/mod.rs:1002` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `memorize` / `alloc/src/vec/mod.rs:1009` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `memorize` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `memorize` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `memorize` / `alloc/src/vec/mod.rs:999` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `memorize` / `core/src/ptr/mod.rs:1962` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `memorize` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 8.000000 |
| `memorize` / `core/src/slice/index.rs:245` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `memorize` / `expand.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `memorize` / `expand.rs:571–604` | memorize: save expansion in memo | REQUIRED; 2279–2282; 1113 | 0.000000 | 46.000000 |
| `push_lists` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 |
| `push_lists` / `alloc/src/vec/mod.rs:1002` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 |
| `push_lists` / `alloc/src/vec/mod.rs:1009` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 |
| `push_lists` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 |
| `push_lists` / `alloc/src/vec/mod.rs:999` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 |
| `push_lists` / `core/src/cmp.rs:2201` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 0.000000 |
| `push_lists` / `core/src/iter/range.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 0.000000 |
| `push_lists` / `core/src/iter/range.rs:1145` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 7.000000 | 0.000000 |
| `push_lists` / `core/src/ptr/mod.rs:1962` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 0.000000 |
| `push_lists` / `core/src/ptr/mut_ptr.rs:978` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 0.000000 |
| `push_lists` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 8.000000 | 0.000000 |
| `push_lists` / `unify.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 2.000000 | 0.000000 |
| `push_lists` / `unify.rs:1106–1122` | push_lists/push_pair: iterate children and save pairs | UNSURE; 2347–2350; 2440–2445 | 23.000000 | 0.000000 |
| `reaches` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 14.000000 | 28.000000 |
| `reaches` / `alloc/src/raw_vec/mod.rs:640` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.004096 |
| `reaches` / `alloc/src/raw_vec/mod.rs:695` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.004096 |
| `reaches` / `alloc/src/raw_vec/mod.rs:795` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.004096 |
| `reaches` / `alloc/src/vec/mod.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.004096 |
| `reaches` / `alloc/src/vec/mod.rs:1002` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 12.000000 |
| `reaches` / `alloc/src/vec/mod.rs:1009` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 8.000000 |
| `reaches` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 8.000000 | 16.000000 |
| `reaches` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 6.000000 |
| `reaches` / `alloc/src/vec/mod.rs:2922` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 9.000000 | 18.000000 |
| `reaches` / `alloc/src/vec/mod.rs:2925` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 12.000000 |
| `reaches` / `alloc/src/vec/mod.rs:3141` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 2.000000 |
| `reaches` / `alloc/src/vec/mod.rs:3160` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000026 | 4.000026 |
| `reaches` / `alloc/src/vec/mod.rs:999` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 4.000000 |
| `reaches` / `alloc/src/vec/spec_extend_with.rs:100` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.004096 |
| `reaches` / `alloc/src/vec/spec_extend_with.rs:86` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.004096 |
| `reaches` / `core/src/cmp.rs:2201` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 10.000000 |
| `reaches` / `core/src/iter/range.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 2.000000 |
| `reaches` / `core/src/iter/range.rs:1103` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 5.000000 | 10.000000 |
| `reaches` / `core/src/num/uint_macros.rs:2784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.004096 | 0.004096 |
| `reaches` / `core/src/ptr/mod.rs:1754` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 6.000000 |
| `reaches` / `core/src/ptr/mod.rs:1962` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 5.000000 | 10.000000 |
| `reaches` / `core/src/ptr/mod.rs:570` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.008192 | 0.008192 |
| `reaches` / `core/src/ptr/mut_ptr.rs:978` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.008192 | 0.008192 |
| `reaches` / `core/src/slice/index.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 2.000000 |
| `reaches` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 19.000000 | 38.000000 |
| `reaches` / `graph.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 3.000000 | 4.000000 |
| `reaches` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 3.000000 | 6.000000 |
| `reaches` / `graph.rs:234–252` | Graph::repr: representative loads/tests (inlined) | UNSURE; 2231–2233; 2278–2288 | 21.000000 | 48.000000 |
| `reaches` / `graph.rs:28–36` | Node tag/arity extraction | REQUIRED; 2239; 2308; 2347–2350 | 9.000000 | 18.000000 |
| `reaches` / `level.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 3.000000 | 6.000000 |
| `reaches` / `level.rs:1–200` | Graph::children: occurrence child traversal | REQUIRED; 2330; 1384–1408 | 19.000000 | 38.000000 |
| `reaches` / `unify.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 6.000000 | 12.000000 |
| `reaches` / `unify.rs:1280–1290` | fresh_marks: generation and storage checks | OVERHEAD; 2330; 1432–1465 (bounded walk has no marks) | 7.000000 | 14.000000 |
| `reaches` / `unify.rs:1296–1301` | reaches: entry, work stack and representative | UNSURE; 2330; 1432–1465 | 11.000000 | 22.000000 |
| `reaches` / `unify.rs:1302–1306` | reaches: visited-mark test | OVERHEAD; 2330; 1432–1465 (bounded walk has no marks) | 6.000000 | 14.000000 |
| `reaches` / `unify.rs:1307–1310` | reaches: occurrence identity test | REQUIRED; 2330; 1436 | 3.000000 | 6.000000 |
| `reaches` / `unify.rs:1311–1311` | reaches: visited-mark store | OVERHEAD; 2330; 1432–1465 (bounded walk has no marks) | 3.000000 | 6.000000 |
| `reaches` / `unify.rs:1312–1318` | reaches: descriptors, row exclusion, children and exit | REQUIRED; 2330; 1439–1458 | 26.000000 | 52.000000 |
| `unify3` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 3.000000 |
| `unify3` / `alloc/src/vec/mod.rs:1002` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `unify3` / `alloc/src/vec/mod.rs:1009` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 6.000000 |
| `unify3` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 3.000000 |
| `unify3` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 1.000000 |
| `unify3` / `alloc/src/vec/mod.rs:999` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `unify3` / `core/src/cmp.rs:2201` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 3.000000 |
| `unify3` / `core/src/iter/range.rs:1145` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 9.000000 |
| `unify3` / `core/src/ptr/mod.rs:1962` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 6.000000 |
| `unify3` / `core/src/ptr/mut_ptr.rs:978` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 4.000000 |
| `unify3` / `core/src/slice/index.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 8.000000 |
| `unify3` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 12.000000 |
| `unify3` / `core/src/slice/index.rs:245` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 2.000000 |
| `unify3` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 5.000000 | 5.000000 |
| `unify3` / `graph.rs:154–156` | Graph::link: repeated identity guard | OVERHEAD; 2233; 2257; 2331 (distinct pair already established) | 1.000000 | 1.000000 |
| `unify3` / `graph.rs:157–164` | Graph::link: load source, write link | REQUIRED; 2221; 2257; 2331 | 7.000000 | 7.000000 |
| `unify3` / `graph.rs:165–167` | Graph::link: speculation/name-rule guard | REQUIRED; 2221; 2257; 2331 (btype.ml:713–731) | 4.000000 | 4.000000 |
| `unify3` / `graph.rs:28–36` | Node tag/arity extraction | REQUIRED; 2239; 2308; 2347–2350 | 2.000000 | 2.000000 |
| `unify3` / `graph.rs:47` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 1.000000 | 1.000000 |
| `unify3` / `unify.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 21.000000 | 22.000000 |
| `unify3` / `unify.rs:1106–1122` | push_lists/push_pair: iterate children and save pairs | UNSURE; 2347–2350; 2440–2445 | 0.000000 | 8.000000 |
| `unify3` / `unify.rs:1334–1337` | childless: prove occurrence walk unnecessary | REQUIRED; 2218; 2330 | 3.000000 | 3.000000 |
| `unify3` / `unify.rs:37` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 1.000000 | 1.000000 |
| `unify3` / `unify.rs:502–510` | occur: call reaches and test its answer | REQUIRED; 2330; 1488–1490 | 11.000000 | 11.000000 |
| `unify3` / `unify.rs:658–660` | deep_occur: reachability call | REQUIRED; 2309; 1775 | 0.000000 | 10.000000 |
| `unify3` / `unify.rs:740–748` | unify3: entry and descriptor loads | UNSURE; 2305–2308 | 8.000000 | 8.000000 |
| `unify3` / `unify.rs:749–785` | unify3: variable/field/mode and create_recursion tests | REQUIRED; 2309–2332 | 16.000000 | 15.000000 |
| `unify3` / `unify.rs:789–793` | unify3: occurrence and link routing | REQUIRED; 2330–2331 | 1.000000 | 1.000000 |
| `unify3` / `unify.rs:794–834` | unify3: explain/repair continuations, children and result | UNSURE; 2333–2438 | 16.000000 | 15.000000 |
| `unify3` / `unify.rs:909–944` | push_children: shape, arity, path match and child ranges | REQUIRED; 2334–2350 | 20.000000 | 14.000000 |
| `unify_distinct` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 6.000000 |
| `unify_distinct` / `alloc/src/vec/mod.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 2.000000 |
| `unify_distinct` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 3.000000 |
| `unify_distinct` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 8.000000 |
| `unify_distinct` / `alloc/src/vec/mod.rs:2925` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 4.000000 |
| `unify_distinct` / `alloc/src/vec/mod.rs:3160` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 8.000000 | 8.000000 |
| `unify_distinct` / `core/src/ptr/const_ptr.rs:879` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 2.000000 |
| `unify_distinct` / `core/src/ptr/mod.rs:1754` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 12.000000 | 12.000000 |
| `unify_distinct` / `core/src/slice/index.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 3.000000 | 3.000000 |
| `unify_distinct` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 18.000000 | 18.000000 |
| `unify_distinct` / `core/src/slice/index.rs:245` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 4.000000 |
| `unify_distinct` / `graph.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 4.000000 | 2.000000 |
| `unify_distinct` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 4.000000 | 4.000000 |
| `unify_distinct` / `graph.rs:154–156` | Graph::link: repeated identity guard | OVERHEAD; 2233; 2257; 2331 (distinct pair already established) | 2.000000 | 2.000000 |
| `unify_distinct` / `graph.rs:157–164` | Graph::link: load source, write link | REQUIRED; 2221; 2257; 2331 | 16.000000 | 16.000000 |
| `unify_distinct` / `graph.rs:165–167` | Graph::link: speculation/name-rule guard | REQUIRED; 2221; 2257; 2331 (btype.ml:713–731) | 8.000000 | 8.000000 |
| `unify_distinct` / `graph.rs:234–252` | Graph::repr: representative loads/tests (inlined) | UNSURE; 2231–2233; 2278–2288 | 28.000000 | 46.000000 |
| `unify_distinct` / `graph.rs:47` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 2.000000 | 2.000000 |
| `unify_distinct` / `unify.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 24.000000 | 24.000000 |
| `unify_distinct` / `unify.rs:1186–1199` | run_frames: pair result, loop bound and pop | UNSURE; 2347–2350; 2440–2445 | 8.000000 | 8.000000 |
| `unify_distinct` / `unify.rs:1200–1201` | run_frames: tagged continuation dispatch | OVERHEAD; 2347–2350 (recursive calls, no FrameKind) | 6.000000 | 6.000000 |
| `unify_distinct` / `unify.rs:1202–1223` | run_frames: child identity test and other continuations | REQUIRED; 2231–2233; 2428–2438 | 4.000000 | 4.000000 |
| `unify_distinct` / `unify.rs:187–227` | unify_distinct: depth, explain/snapshot entry and exit | UNSURE; 2271–2274; 2732–2737 | 30.000000 | 30.000000 |
| `unify_distinct` / `unify.rs:238–258` | unify_pair: load descriptors, choose variable side | REQUIRED; 2239–2243 | 27.000000 | 27.000000 |
| `unify_distinct` / `unify.rs:268–280` | unify_pair: nullary same-head shortcut and level test | REQUIRED; 2248–2257 | 29.000000 | 29.000000 |
| `unify_distinct` / `unify.rs:281–282` | unify_pair: route to unify2 | REQUIRED; 2270 | 3.000000 | 3.000000 |
| `unify_expanded` / `alloc/src/raw_vec/mod.rs:635` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 8.000000 |
| `unify_expanded` / `alloc/src/vec/mod.rs:1784` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 0.000000 | 2.000000 |
| `unify_expanded` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 4.000000 | 10.000000 |
| `unify_expanded` / `core/src/cmp.rs:2289` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 5.000000 | 5.000000 |
| `unify_expanded` / `core/src/result.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 0.000000 |
| `unify_expanded` / `core/src/slice/index.rs:0` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 1.000000 |
| `unify_expanded` / `core/src/slice/index.rs:238` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 6.000000 | 6.000000 |
| `unify_expanded` / `expand.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 1.000000 | 2.000000 |
| `unify_expanded` / `expand.rs:792–820` | expand_head: repr, expansion loop and stop tests | REQUIRED; 2279–2282; 1267–1280 | 15.000000 | 62.000000 |
| `unify_expanded` / `graph.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 11.000000 | 21.000000 |
| `unify_expanded` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 4.000000 | 9.000000 |
| `unify_expanded` / `graph.rs:234–252` | Graph::repr: representative loads/tests (inlined) | UNSURE; 2231–2233; 2278–2288 | 25.000000 | 76.000000 |
| `unify_expanded` / `unify.rs:0` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 7.000000 | 10.000000 |
| `unify_expanded` / `unify.rs:1232–1241` | lower_to: generic/level guard and lower | REQUIRED; 2284–2285; 633–640 | 0.000000 | 2.000000 |
| `unify_expanded` / `unify.rs:671–676` | unify_expanded: function entry | UNSURE; 2276 | 9.000000 | 9.000000 |
| `unify_expanded` / `unify.rs:677–683` | unify_expanded: expansion/re-expansion decision | REQUIRED; 2278–2282 | 2.000000 | 1.000000 |
| `unify_expanded` / `unify.rs:684–716` | unify_expanded: levels, identity and lowering | REQUIRED; 2283–2288 | 9.000000 | 6.000000 |
| `unify_expanded` / `unify.rs:717–728` | unify_expanded: choose direction, call unify3 and return | REQUIRED; 2299–2303 | 18.000000 | 21.000000 |
| `runtime` / `other:—` | Allocation, bulk memory, startup and twin-layout remainder | UNSURE; 2227–2438 (allocator cost not specified) | -0.091886 | 0.221425 |
| `tc_kernel::main` / `alloc/src/vec/mod.rs:1823` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 1.000000 | 1.000000 |
| `tc_kernel::main` / `core/src/result.rs:1182` | Inlined standard-library indexing, vector or control support | UNSURE; 2239–2438 | 2.000000 | 2.000000 |
| `tc_kernel::main` / `graph.rs:13` | Unlocated/generated code or inlined support | UNSURE; 2239–2438 | 1.000000 | 1.000000 |
| `tc_kernel::main` / `graph.rs:234–252` | Graph::repr: representative loads/tests (inlined) | UNSURE; 2231–2233; 2278–2288 | 14.000000 | 14.000000 |
| `tc_kernel::main` / `tc_kernel.rs:443` | Benchmark call-site / result consumption difference | UNSURE; 2227 (harness has no OCaml counterpart) | 2.000000 | 2.000000 |
| `tc_kernel::main` / `unify.rs:169–176` | unify: identity test and call | REQUIRED; 2229–2233 | 5.000000 | 5.000000 |
| Sub-millithreshold groups | Startup/library attribution below 0.001 each | UNSURE; 2227–2438 | 0.001218 | 0.002381 |
| **Total including remainder** | | | 960.954414 | 2826.268888 |

Verification so far (real output):

```text
cargo build --manifest-path compiler-rust/Cargo.toml
Finished `dev` profile [unoptimized + debuginfo] target(s) in 1m 34s
cargo test --manifest-path compiler-rust/Cargo.toml --lib tc::
test result: ok. 197 passed; 0 failed; 12 ignored; 0 measured; 2621 filtered out; finished in 262.88s
CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 CARGO_PROFILE_BENCH_DEBUG=line-tables-only cargo bench --manifest-path compiler-rust/Cargo.toml --bench tc_kernel --no-run
Finished `bench` profile [optimized + debuginfo] target(s) in 9.97s
# timeout 10 BENCH OP 4097, for each added operation:
build_datatype2 n=4097 sink=100667399
unify_datatype2 n=4097 sink=100667399
build_abbrev2 n=4097 sink=100667399
unify_abbrev2 n=4097 sink=234852359
```

An initial bench build tried to read the private forwarding table and failed
with E0616; it was replaced by public setup instantiation. No visibility or
compiler-source change was made. The full compiler suite is left to CI;
only the requested `tc::` slice ran locally.

### 5. Ranked removals to investigate (not implemented)

**Measured charge is not measured saving.** Each number below is the
executed instruction charge of the listed OVERHEAD groups, from the tables
above. It is the gross work a removal targets, not a promise that the
whole operation gets that much cheaper: replacement checks, register
allocation and inlining can offset it. A realized saving requires building
and measuring the proposed source edit; that would violate this task's
no-compiler-source-change constraint. No such figure is invented here.
The ranking is by measured target charge, with risk stated separately.

| Rank | OVERHEAD groups / smallest candidate edit | Ground3 | Ground1 | Vars | Bind ground1 | Datatype2 | Abbrev2 | What could go wrong / gate |
|---|---|---:|---:|---:|---:|---:|---:|---|
| 1 | `unify.rs:1280–1290,1302,1311`: generation/storage check + visited test + mark store. Replace marking for a bounded occurrence probe with an explicit remaining-node budget as in `ctype.ml:1432–1465`; preserve the marked walk for an undecided/cyclic/shared case. No removal of the actual occurrence test. Charges split as **7+6+3** in ground3/datatype2 and **14+14+6** in abbrev2. | 16 | 0 | 0 | 0 | 16 | 34 | Simply deleting marks can loop or revisit a shared DAG exponentially. A budget needs an undecided result, not false. Check `expand_tier_agrees_on_recursive_abbreviations`, `kernel_tier_agrees_on_generated_cases`, `structural_tier_agrees_on_generated_cases`, and deep/wide step bounds; include a cyclic non-occurring graph and heavily shared DAG. Budget tests cost instructions; **net saving unknown**. |
| 2 | `unify.rs:1200`: tagged continuation dispatch. Have the child-pair producer (`push_lists:1116–1122`) hand its first pair directly to `run_frames:1186–1223`, leaving the remaining work in order on the stack; only residual/general continuations use the kind switch. Removing both child dispatches in these flat cases targets the shown 6; forwarding only the first targets a subset, not all 6. | 6 | 0 | 0 | 0 | 6 | 6 | This is representation overhead compared with recursive `unify_list` (`ctype.ml:2347–2350,2440–2445`), but ordinary recursion has its own costs. Do not reorder children or bypass Linked/Recursion/Field frames. Check `unify_of_equal_deep_types_fits_the_stack`, `unify_of_equal_wide_types_is_linear`, `explain_plan_agrees_on_generated_cases`, `explain_reaches_the_reversed_trace_below_a_swapped_unify3`, and `explain_reaches_a_clash_with_the_recursion_repair_pending`. New pair-return plumbing costs instructions; **net saving unknown**. |
| 3 | `graph.rs:154`: repeated `from == to` guard. Factor `link`'s distinct-node body (`:157–167`) into a private helper; keep the public guard, but use the helper where the caller already proves distinctness. Start at the nullary shortcut (`unify.rs:268–278`), then prove the structure/substitution call sites separately. | 3 | 1 | 0 | 0 | 3 | 7 | `ctype.ml:2233` already rejects identical heads before `:2257`; `unify3` and substitution need stronger proofs because originals and expanded heads differ. A self-link never terminates. Check `link_directions`, `representative_chain_cost`, `expansion_is_memorized_per_node_and_per_nullary_type`, expansion/scoped/explain differential plans and the existing same-node case. Ground3's 3 and abbrev2's 7 include sites beyond the simplest nullary edit; **net saving and eligible subset unknown until those proofs and a build**. |

These rows cover **every** group classified OVERHEAD. Their gross sums
are 25, 1, 0, 0, 25 and 47 instructions respectively, not projected whole-
operation savings. In particular, the absence of a line-154 charge for
variables does not prove the guard is absent from assembly: optimized
instructions can be attributed to other lines. No hidden savings are
assigned to those lines.

The larger, explicitly UNSURE opportunities are:

- `unify_expanded`'s representative calls (`graph.rs:234–252`, 25 source-
  attributed instructions in ground3, 76 in abbrev2): some are after a
  potentially mutating expansion, so `ctype.ml:2278–2288` requires them.
  Separate entry calls on already-known representatives from post-mutation
  calls before proposing an edit. Do not remove all of this bucket.
- Out-of-line `expand_once` entry/return and `unify3` call plumbing: source
  line attribution includes spills and return/result work. OCaml also calls
  functions here; neither a blanket overhead label nor an inline attribute
  guarantees a saving. K2's own experiments show inlining can cost more.
- Bounds checks and Vec traffic: preserving safe Rust, frame order and
  linear step bounds is part of the contract. A load charged to a shared
  standard-library line cannot be called a second row load without following
  its instruction addresses and the optimizer's dataflow.

No source under `compiler-rust/src` was edited. These are kernel costs;
no application speedup is inferred, and no optimization is submitted.

### Final application repeatability check

A 3,735-module application was checked with **two copies of the same
release executable**, because this change touches no production compiler
code. This is an output/repeatability sanity check, not independently built
before/after binaries and not evidence of an optimization. Both executable
SHA-256 hashes were
`504d39684aeba51cb754f4b1955ec1a3c95d249d8a850775d759792c231ea3d1`.

```sh
cargo build --release --manifest-path rewatch/Cargo.toml
# Finished `release` profile [optimized] target(s) in 4m 57s
# BASE and CANDIDATE are copies of that executable; APP is outside the checkout.
scripts/bench_project.sh "$APP" "$BASE" "$CANDIDATE" --runtime-from "$PWD"
RESCRIPT_RUNTIME="$PWD/packages/@rescript/runtime" \
  python3 scripts/compare_checker_builds.py "$APP" "$BASE" "$CANDIDATE"
```

Sanitized output (both scripts exited 0):

```text
base: instructions=63919897203 source_lines=656677 instructions_per_line=97338.413
candidate: instructions=63913772174 source_lines=656677 instructions_per_line=97329.086
Outputs identical
Instructions difference: -0.0096%
base: exit code 0, 3735 signatures, 32 diagnostics in 18 files, 3980 generated files
candidate: exit code 0, 3735 signatures, 32 diagnostics in 18 files, 3980 generated files
outcome: both exit with 0
signatures: no difference (3735 compared)
diagnostics: no difference (18 compared)
javascript: no difference (3980 compared)
no differences
```

All 23 PR checks passed at `f270e0b60`, including output parity and instruction
count. This final update only records validation and clarifies the machine
and the fresh-parameter link citation; it changes no benchmark or compiler
code. The source-group totals were independently resummed from the Markdown:
916.953969, 122, 119, 124.000058, 960.954414 and 2826.268888, matching their
operation measurements within 0.0001 instruction.

## K3

Four removals from the hot paths of unification that K3a section 5 ranks,
with no change of behaviour, one commit each; an item is kept when it
saves 5 instructions or more on `unify_ground3`, `unify_datatype2` or
`unify_abbrev2` and makes no operation of the table more than 2 dearer,
and is otherwise reverted in a commit of its own. Same machine kind and
method as "K3a" section 1 (x86-64 Linux, eight virtual CPUs, Valgrind
3.22.0, pinned `rustc 1.102.0-nightly (ac8310ba6 2026-11-09)`, fat LTO,
one codegen unit, line tables, 1,000,000 iterations minus zero,
unification minus its `build_*` twin, the other operations as in "K1").
The reference script ran first and reproduced R1's raw figures (`empty
18`, `unify_ground1 318`, `unify_ground3 746`, `generalize7 672`). No
bench operation changed.

### Per commit

Before: trunk `6a0838552`. Each column is a whole build and run of that
commit: (1) `ac4d94e52`, (2) `e6528bba7`, (3) `fa0c96fbd`, (4)
`e91359ead`. The three reverts `4773a3e0a`, `4b230242c` and `a4c3a5137`
have the trees of the base, of (2) and of (2), so their figures are
those columns. After review, (1) was re-applied on top of (2) (see
"Review" below); the final figures are those of "Merged head".

| Operation | K3a now | Before | (1) | (2) | (3) | (4) |
|---|---:|---:|---:|---:|---:|---:|
| `unify_vars` | 119.00 | 120.00 | 120.00 | 120.00 | 118.00 | 118.00 |
| `unify_ground1` | 122.00 | 121.00 | 121.00 | 121.00 | 119.00 | 122.00 |
| `unify_ground3` | 916.95 | 911.95 | 820.95 | 894.00 | 892.00 | 894.00 |
| `bind_ground1` | 124.00 | 124.00 | 124.00 | 124.00 | 122.00 | 122.00 |
| `unify_vars_local` | 119.00 | 120.00 | 120.00 | 120.00 | 118.00 | 118.00 |
| `unify_ground1_local` | 122.00 | 121.00 | 121.00 | 121.00 | 119.00 | 122.00 |
| `unify_ground3_local` | 916.95 | 911.95 | 820.95 | 894.00 | 892.00 | 894.00 |
| `bind_ground1_local` | 124.00 | 124.00 | 124.00 | 124.00 | 122.00 | 122.00 |
| `unify_datatype2` | 960.95 | 955.95 | 828.95 | 938.00 | 936.00 | 938.00 |
| `unify_abbrev2` | 2826.27 | 2822.27 | 2867.27 | 2788.06 | 2786.06 | 2788.06 |
| `instance1` | 137.06 | 137.06 | 137.06 | 137.06 | 137.06 | 137.06 |
| `instance3` | 217.31 | 217.31 | 217.31 | 217.31 | 217.31 | 217.31 |
| `instance5` | 305.34 | 305.34 | 305.34 | 305.34 | 305.34 | 305.34 |
| `instance7` | 325.27 | 325.27 | 325.27 | 325.27 | 325.27 | 325.27 |
| `generalize7` | 449.00 | 449.00 | 449.00 | 449.00 | 449.00 | 449.00 |
| `lower7` | 422.00 | 422.00 | 422.00 | 422.00 | 422.00 | 422.00 |
| `copy7` | 1709.58 | 1709.58 | 1709.58 | 1709.58 | 1709.58 | 1709.58 |
| `repr` | 9.00 | 9.00 | 9.00 | 9.00 | 9.00 | 9.00 |
| `restore` | 63.00 | 63.00 | 63.00 | 63.00 | 63.00 | 63.00 |
| `keep` | 44.00 | 44.00 | 44.00 | 44.00 | 44.00 | 44.00 |

"K3a now" is K3a's table on `c4e9326eb`. The base reproduces it within
5 instructions on every operation (trunk's R3e frame kinds since: the
largest moves are `unify_ground3` and `unify_datatype2` -5, `unify_abbrev2`
-4, `unify_vars` +1, `unify_ground1` -1).

| Item | `unify_ground3` | `unify_datatype2` | `unify_abbrev2` | Dearest other operation | Kept |
|---|---:|---:|---:|---|---|
| (1) expansion test inline | -91.00 | -127.00 | **+45.00** | none dearer | reverted, then **kept by decision in review** |
| (2) occurrence probe | -17.95 | -17.95 | -34.21 | none dearer | **yes** |
| (3) `link_distinct` | -2.00 | -2.00 | -2.00 | none dearer | no: saves 2 |
| (4) rare frame arms out of line | 0.00 | 0.00 | 0.00 | `unify_ground1` +1 | no: saves 0 |

(1) and (3) are measured against the base and (2) respectively; (4)
against (2).

**(1) An expansion attempt that cannot succeed makes no call. Reverted by the rule, then kept by decision in review.**
`Checker::never_expands` tested, inline in front of the first pair of
`expand_head` calls of `unify_expanded`, the returns of `expand_once`
that have no side effect and need no memo: the representative is not a
constructor, or its type's row (read at the call, one `TypeInfo` load)
has none of `ABBREV`, `ALIAS`, `INHERITS`, for which no public memo entry
can exist (`memorize` runs only in `subst` of a public expansion, which
needs `ABBREV`, and in `expand_alias`, which needs `ALIAS`; the chain
lookup only for `INHERITS`). On the two operations whose heads do not
expand it removes the two calls (`expand_once` 94 and 138 instructions)
for 2 node and row tests. On `unify_abbrev2`, whose heads do expand, the
tests are added work in front of an `expand_once` that loads the node and
the row again, and spills: +45, where the rule allows +2. Any test in
front of an unchanged `expand_once` costs the expanding path at least one
row load and two compares per head, so no form of the item meets the
rule. Three forms were measured:

| Operation | Before | (1) wrapper, four asks | (1) wrapper, first pair | (1) as committed |
|---|---:|---:|---:|---:|
| `unify_vars` | 120.00 | 117.00 | 117.00 | 120.00 |
| `unify_ground1` | 121.00 | 118.00 | 118.00 | 121.00 |
| `unify_ground3` | 911.95 | 818.95 | 825.95 | 820.95 |
| `bind_ground1` | 124.00 | 121.00 | 121.00 | 124.00 |
| `unify_datatype2` | 955.95 | 826.95 | 833.95 | 828.95 |
| `unify_abbrev2` | 2822.27 | 3040.27 | 2917.27 | 2867.27 |

The first two put the test in an inline wrapper around `expand_head`;
LLVM then called `expand_head` out of line (212 instructions in
`unify_abbrev2` for four calls, 106 for two). The committed form tests
the first pair only (the second pair runs only after an expansion), with
`expand_head` called at the original sites, where it stays inline: 45
over the base in `unify_expanded`, all of it the two tests and register
pressure. (The message of the revert commit `4773a3e0a` names the
first two forms' figures the wrong way round: +218 belongs to four asks,
+95 to the first pair. This table is right.)

**(2) The occurrence walk of a small type uses no marks. Kept.**
`Checker::reaches` first runs `Checker::unreached_within_budget`, the
probe of `occur_reaches_budget` (compiler/ml/ctype.ml:1432-1465,
`walk_budget` 256 at :1424): the same edges as the marked walk in the
same mode, on `g.work`, one step a node, no marks; it answers "not
reached" only when it finished within 256 nodes. When it met the node or
ran out of budget the marked walk runs as before and answers. The saving
is all in `reaches`: 214.05 -> 196.00 in `unify_ground3` and
`unify_datatype2`, 434.05 -> 400.00 in `unify_abbrev2` (the generation
setup, the mark test and the mark store a node, and the amortized growth
of `marks`). No step count changed: no step test failed, so none was
lowered.

**(3) A link between two nodes proven distinct makes no identity test.
Reverted.** `Graph::link` kept its guard and called the new
`Graph::link_distinct` (`pub(super)`, since the callers are in
`tc::unify`; `debug_assert_ne!`). Unproven sites kept the guard: the
link of `bind_routed` and `bind_leaf` when reached from `Checker::bind`
(with scoped types a childless target is linked without a walk, so
`var == ty` is not excluded), the structure link of `unify3` (an
expansion through a parameter can make `t1'` the other side's original),
and `repair_recursion`. Proven sites: the nullary shortcut and
`bind_leaf` from `unify_pair` (two distinct representatives), the two
variable cases of `unify3` (`occur` clashes when the other side is the
variable), and `unify_var` (`var == ty` returned at its top). 2 fewer on
every unification operation.

**(4) The loop of `run_frames` tests the common frame kinds first.
Reverted.** The arms of every kind but `Pair` and `Linked` moved,
unchanged, into one out-of-line `Checker::run_rare_frame`. With
`#[inline(never)]` alone the call in the loop made `unify_distinct` keep
more values in callee-saved registers (+9 on its line 0, +4 at the loop
head): dearer everywhere. With `#[cold]` too (committed) it is neutral on
the three operations of the rule:

| Operation | (2) | (4) `#[inline(never)]` | (4) `#[cold] #[inline(never)]`, committed |
|---|---:|---:|---:|
| `unify_vars` | 120.00 | 121.00 | 118.00 |
| `unify_ground1` | 121.00 | 125.00 | 122.00 |
| `unify_ground3` | 894.00 | 900.00 | 894.00 |
| `bind_ground1` | 124.00 | 125.00 | 122.00 |
| `unify_datatype2` | 938.00 | 944.00 | 938.00 |
| `unify_abbrev2` | 2788.06 | 2794.06 | 2788.06 |

In `unify_ground3` the dispatch itself (`unify.rs:1255`) went from 10 to
6 instructions, and the loop and entry gained what it lost. K3a's
"about 18 instructions" of these arms are therefore not in the
dispatch: the rare arms' code is not executed on these operations.

### Review

The keep rule was stated per operation where item (1) is a trade
between operations: 91 and 127 fewer on heads that do not expand
against 45 more (1.6%) on a pair that expands twice, which loses only
if most structure pairs have abbreviation heads. And R3f measured that
new callers elsewhere in the crate made LLVM stop inlining
`expand_head` into `unify_expanded` (about 100 on `unify_ground3`); a
test in front of the call keeps the common path independent of that
decision. So (1) was re-applied as `0022a7a57` ("kept by decision in
review"), with its three figures against the base: `unify_ground3`
-91.00, `unify_datatype2` -127.00, `unify_abbrev2` +45.00.

One attempt then tried to take back the 45 (keep it for 20 or more, with
`unify_ground3` and `unify_datatype2` within 5 of their saving):
`f5bae56ab` made the test one condition over both heads, so that when
the left head may expand the right one's row is not read and both go to
`expand_head`. It took back 6, so it was reverted (`06b497a58`):

| Operation | (2) `e6528bba7` | (1) kept `0022a7a57` | (1) 2 `f5bae56ab` |
|---|---:|---:|---:|
| `unify_vars` | 120.00 | 120.00 | 120.00 |
| `unify_ground1` | 121.00 | 121.00 | 121.00 |
| `unify_ground3` | 894.00 | 803.00 | 805.00 |
| `bind_ground1` | 124.00 | 124.00 | 124.00 |
| `unify_vars_local` | 120.00 | 120.00 | 120.00 |
| `unify_ground1_local` | 121.00 | 121.00 | 121.00 |
| `unify_ground3_local` | 894.00 | 803.00 | 805.00 |
| `bind_ground1_local` | 124.00 | 124.00 | 124.00 |
| `unify_datatype2` | 938.00 | 811.00 | 813.00 |
| `unify_abbrev2` | 2788.06 | 2833.06 | 2827.06 |
| `instance1` | 137.06 | 137.06 | 137.06 |
| `instance3` | 217.31 | 217.31 | 217.31 |
| `instance5` | 305.34 | 305.34 | 305.34 |
| `instance7` | 325.27 | 325.27 | 325.27 |
| `generalize7` | 449.00 | 449.00 | 449.00 |
| `lower7` | 422.00 | 422.00 | 422.00 |
| `copy7` | 1709.58 | 1709.58 | 1709.58 |
| `repr` | 9.00 | 9.00 | 9.00 |
| `restore` | 63.00 | 63.00 | 63.00 |
| `keep` | 44.00 | 44.00 | 44.00 |


### Merged head

`origin/ocaml-to-rust-rewrite` at `d158207a2` (with R3f, #294) merged
without conflict as `06489d7d1`; trunk added no attribute on
`Checker::expand_head`. Base: that trunk. Head: the merge. This is the
final table of K3:

| Operation | Base (trunk `d158207a2`) | Head | Change |
|---|---:|---:|---:|
| `unify_vars` | 117.00 | 117.00 | +0.00 |
| `unify_ground1` | 122.00 | 122.00 | +0.00 |
| `unify_ground3` | 1013.95 | 814.00 | -199.95 |
| `bind_ground1` | 121.00 | 121.00 | +0.00 |
| `unify_vars_local` | 117.00 | 117.00 | +0.00 |
| `unify_ground1_local` | 122.00 | 122.00 | +0.00 |
| `unify_ground3_local` | 1013.95 | 814.00 | -199.95 |
| `bind_ground1_local` | 121.00 | 121.00 | +0.00 |
| `unify_datatype2` | 1013.95 | 822.00 | -191.95 |
| `unify_abbrev2` | 2940.27 | 2968.06 | +27.79 |
| `instance1` | 137.06 | 137.06 | +0.00 |
| `instance3` | 217.31 | 217.31 | +0.00 |
| `instance5` | 305.34 | 305.34 | +0.00 |
| `instance7` | 325.27 | 325.27 | +0.00 |
| `generalize7` | 449.00 | 449.00 | +0.00 |
| `lower7` | 422.00 | 422.00 | +0.00 |
| `copy7` | 1709.58 | 1709.58 | +0.00 |
| `repr` | 9.00 | 9.00 | +0.00 |
| `restore` | 63.00 | 63.00 | +0.00 |
| `keep` | 44.00 | 44.00 | +0.00 |

`unify_ground3` and `unify_datatype2` on trunk carry R3f's loss of the
inlining of `expand_head`; on the head neither head of those operations
reaches it. `unify_abbrev2` pays item (1)'s two tests, as decided.

### Raw output

```text
revision operation zero full raw
before empty 335066 19337324 19.002258
before instance1 335086 156395945 156.060859
before instance3 335120 236644455 236.309335
before instance5 335154 324673170 324.338016
before instance7 335188 344607404 344.272216
before generalize7 335134 793607350 793.272216
before lower7 335084 766607286 766.272202
before copy7 335106 1728916091 1728.580985
before repr 335058 165395931 165.060873
before restore 335114 219396353 219.061239
before keep 335098 200396351 200.061253
before build_vars 335393 78405840 78.070447
before unify_vars 335427 198405874 198.070447
before build_ground1 335456 98413433 98.077977
before unify_ground1 335489 219413466 219.077977
before build_ground3 335522 200776627 200.441105
before unify_ground3 335556 1112730630 1112.395074
before build_vars_local 335320 78405795 78.070475
before unify_vars_local 335354 198405829 198.070475
before build_ground1_local 335382 98413359 98.077977
before unify_ground1_local 335422 219413399 219.077977
before build_ground3_local 335451 200776556 200.441105
before unify_ground3_local 335485 1112730559 1112.395074
before build_bind_ground1 335420 88427658 88.092238
before bind_ground1 335514 212427780 212.092266
before build_bind_ground1_local 335499 88427765 88.092266
before bind_ground1_local 335469 212427707 212.092238
before build_datatype2 323577 186767415 186.443838
before unify_datatype2 323582 1142721834 1142.398252
before build_abbrev2 329106 186770975 186.441869
before unify_abbrev2 329112 3009039869 3008.710757
(1) empty 335312 19337570 19.002258
(1) instance1 335332 156396191 156.060859
(1) instance3 335366 236644701 236.309335
(1) instance5 335400 324673416 324.338016
(1) instance7 335434 344607650 344.272216
(1) generalize7 335380 793607596 793.272216
(1) lower7 335316 766607546 766.272230
(1) copy7 335352 1728916337 1728.580985
(1) repr 335318 165396163 165.060845
(1) restore 335360 219396599 219.061239
(1) keep 335358 200396583 200.061225
(1) build_vars 335629 78406104 78.070475
(1) unify_vars 335662 198406137 198.070475
(1) build_ground1 335698 98413675 98.077977
(1) unify_ground1 335732 219413709 219.077977
(1) build_ground3 335770 200776875 200.441105
(1) unify_ground3 335803 1021730877 1021.395074
(1) build_vars_local 335580 78406027 78.070447
(1) unify_vars_local 335614 198406061 198.070447
(1) build_ground1_local 335634 98413611 98.077977
(1) unify_ground1_local 335663 219413640 219.077977
(1) build_ground3_local 335703 200776808 200.441105
(1) unify_ground3_local 335738 1021730812 1021.395074
(1) build_bind_ground1 335658 88427924 88.092266
(1) bind_ground1 335770 212428008 212.092238
(1) build_bind_ground1_local 335753 88427991 88.092238
(1) bind_ground1_local 335708 212427974 212.092266
(1) build_datatype2 323823 186767661 186.443838
(1) unify_datatype2 323828 1015722080 1015.398252
(1) build_abbrev2 329352 186771221 186.441869
(1) unify_abbrev2 329358 3054040115 3053.710757
(2) empty 335330 19337574 19.002244
(2) instance1 335350 156396165 156.060815
(2) instance3 335384 236644675 236.309291
(2) instance5 335418 324673390 324.337972
(2) instance7 335452 344607624 344.272172
(2) generalize7 335384 793607584 793.272200
(2) lower7 335348 766607534 766.272186
(2) copy7 335370 1728916341 1728.580971
(2) repr 335336 165396195 165.060859
(2) restore 335364 219396587 219.061223
(2) keep 335376 200396615 200.061239
(2) build_vars 335657 78406088 78.070431
(2) unify_vars 335691 198406122 198.070431
(2) build_ground1 335686 98413649 98.077963
(2) unify_ground1 335724 219413687 219.077963
(2) build_ground3 335757 200776848 200.441091
(2) unify_ground3 335790 1094777086 1094.441296
(2) build_vars_local 335568 78406029 78.070461
(2) unify_vars_local 335602 198406063 198.070461
(2) build_ground1_local 335602 98413593 98.077991
(2) unify_ground1_local 335642 219413633 219.077991
(2) build_ground3_local 335677 200776796 200.441119
(2) unify_ground3_local 335706 1094777030 1094.441324
(2) build_bind_ground1 335654 88427906 88.092252
(2) bind_ground1 335762 212428014 212.092252
(2) build_bind_ground1_local 335747 88428027 88.092280
(2) bind_ground1_local 335703 212427955 212.092252
(2) build_datatype2 323797 186767649 186.443852
(2) unify_datatype2 323802 1124768065 1124.444263
(2) build_abbrev2 329340 186771195 186.441855
(2) unify_abbrev2 329346 2974828246 2974.498900
(3) empty 335330 19337574 19.002244
(3) instance1 335350 156396165 156.060815
(3) instance3 335384 236644675 236.309291
(3) instance5 335418 324673390 324.337972
(3) instance7 335452 344607624 344.272172
(3) generalize7 335384 793607584 793.272200
(3) lower7 335348 766607534 766.272186
(3) copy7 335370 1728916341 1728.580971
(3) repr 335336 165396195 165.060859
(3) restore 335364 219396587 219.061223
(3) keep 335376 200396615 200.061239
(3) build_vars 335657 78406088 78.070431
(3) unify_vars 335691 196406122 196.070431
(3) build_ground1 335686 98413649 98.077963
(3) unify_ground1 335724 217413687 217.077963
(3) build_ground3 335757 200776848 200.441091
(3) unify_ground3 335790 1092777086 1092.441296
(3) build_vars_local 335568 78406029 78.070461
(3) unify_vars_local 335602 196406063 196.070461
(3) build_ground1_local 335602 98413593 98.077991
(3) unify_ground1_local 335642 217413633 217.077991
(3) build_ground3_local 335677 200776796 200.441119
(3) unify_ground3_local 335706 1092777030 1092.441324
(3) build_bind_ground1 335654 88427906 88.092252
(3) bind_ground1 335762 210428014 210.092252
(3) build_bind_ground1_local 335747 88428027 88.092280
(3) bind_ground1_local 335703 210427955 210.092252
(3) build_datatype2 323797 186767649 186.443852
(3) unify_datatype2 323802 1122768065 1122.444263
(3) build_abbrev2 329340 186771195 186.441855
(3) unify_abbrev2 329346 2972828246 2972.498900
(4) empty 335318 19337590 19.002272
(4) instance1 335338 156396211 156.060873
(4) instance3 335372 236644721 236.309349
(4) instance5 335406 324673436 324.338030
(4) instance7 335440 344607670 344.272230
(4) generalize7 335400 793607602 793.272202
(4) lower7 335350 766607566 766.272216
(4) copy7 335358 1728916357 1728.580999
(4) repr 335338 165396197 165.060859
(4) restore 335380 219396605 219.061225
(4) keep 335378 200396617 200.061239
(4) build_vars 335659 78406120 78.070461
(4) unify_vars 335697 196406158 196.070461
(4) build_ground1 335708 98413699 98.077991
(4) unify_ground1 335741 220413732 220.077991
(4) build_ground3 335774 200776893 200.441119
(4) unify_ground3 335808 1094777132 1094.441324
(4) build_vars_local 335600 78406061 78.070461
(4) unify_vars_local 335634 196406095 196.070461
(4) build_ground1_local 335648 98413611 98.077963
(4) unify_ground1_local 335688 220413651 220.077963
(4) build_ground3_local 335717 200776808 200.441091
(4) unify_ground3_local 335751 1094777047 1094.441296
(4) build_bind_ground1 335686 88427938 88.092252
(4) bind_ground1 335794 210428046 210.092252
(4) build_bind_ground1_local 335779 88428031 88.092252
(4) bind_ground1_local 335735 210427987 210.092252
(4) build_datatype2 323843 186767667 186.443824
(4) unify_datatype2 323848 1124768083 1124.444235
(4) build_abbrev2 329358 186771241 186.441883
(4) unify_abbrev2 329364 2974828292 2974.498928
(1)-kept empty 333047 19335305 19.002258
(1)-kept instance1 333067 156393926 156.060859
(1)-kept instance3 333101 236642436 236.309335
(1)-kept instance5 333135 324671151 324.338016
(1)-kept instance7 333169 344605385 344.272216
(1)-kept generalize7 333115 793605331 793.272216
(1)-kept lower7 333051 766605281 766.272230
(1)-kept copy7 333087 1728914072 1728.580985
(1)-kept repr 333053 165393898 165.060845
(1)-kept restore 333095 219394334 219.061239
(1)-kept keep 333093 200394318 200.061225
(1)-kept build_vars 333360 78403835 78.070475
(1)-kept unify_vars 333398 198403873 198.070475
(1)-kept build_ground1 333437 98411414 98.077977
(1)-kept unify_ground1 333470 219411447 219.077977
(1)-kept build_ground3 333503 200774608 200.441105
(1)-kept unify_ground3 333537 1003774847 1003.441310
(1)-kept build_vars_local 333315 78403762 78.070447
(1)-kept unify_vars_local 333349 198403796 198.070447
(1)-kept build_ground1_local 333363 98411340 98.077977
(1)-kept unify_ground1_local 333403 219411380 219.077977
(1)-kept build_ground3_local 333432 200774537 200.441105
(1)-kept unify_ground3_local 333466 1003774776 1003.441310
(1)-kept build_bind_ground1 333387 88425653 88.092266
(1)-kept bind_ground1 333509 212425747 212.092238
(1)-kept build_bind_ground1_local 333494 88425732 88.092238
(1)-kept bind_ground1_local 333436 212425702 212.092266
(1)-kept build_datatype2 321558 186765396 186.443838
(1)-kept unify_datatype2 321563 997765812 997.444249
(1)-kept build_abbrev2 327087 186768956 186.441869
(1)-kept unify_abbrev2 327093 3019826007 3019.498914
(1)-2 empty 333016 19335288 19.002272
(1)-2 instance1 333036 156393909 156.060873
(1)-2 instance3 333070 236642419 236.309349
(1)-2 instance5 333104 324671134 324.338030
(1)-2 instance7 333138 344605368 344.272230
(1)-2 generalize7 333098 793605300 793.272202
(1)-2 lower7 333048 766605264 766.272216
(1)-2 copy7 333056 1728914055 1728.580999
(1)-2 repr 333036 165393895 165.060859
(1)-2 restore 333078 219394303 219.061225
(1)-2 keep 333076 200394315 200.061239
(1)-2 build_vars 333357 78403818 78.070461
(1)-2 unify_vars 333395 198403856 198.070461
(1)-2 build_ground1 333406 98411397 98.077991
(1)-2 unify_ground1 333439 219411430 219.077991
(1)-2 build_ground3 333472 200774591 200.441119
(1)-2 unify_ground3 333506 1005774830 1005.441324
(1)-2 build_vars_local 333298 78403759 78.070461
(1)-2 unify_vars_local 333332 198403793 198.070461
(1)-2 build_ground1_local 333346 98411309 98.077963
(1)-2 unify_ground1_local 333386 219411349 219.077963
(1)-2 build_ground3_local 333415 200774506 200.441091
(1)-2 unify_ground3_local 333449 1005774745 1005.441296
(1)-2 build_bind_ground1 333384 88425636 88.092252
(1)-2 bind_ground1 333492 212425744 212.092252
(1)-2 build_bind_ground1_local 333477 88425729 88.092252
(1)-2 bind_ground1_local 333433 212425685 212.092252
(1)-2 build_datatype2 321541 186765365 186.443824
(1)-2 unify_datatype2 321546 999765781 999.444235
(1)-2 build_abbrev2 327056 186768939 186.441883
(1)-2 unify_abbrev2 327062 3013825990 3013.498928
trunk empty 334357 19336601 19.002244
trunk instance1 334377 156395222 156.060845
trunk instance3 334411 236643732 236.309321
trunk instance5 334445 324672447 324.338002
trunk instance7 334479 344606681 344.272202
trunk generalize7 334411 793606641 793.272230
trunk lower7 334375 766606591 766.272216
trunk copy7 334397 1728915368 1728.580971
trunk repr 334363 165395222 165.060859
trunk restore 334391 219395644 219.061253
trunk keep 334403 200395642 200.061239
trunk build_vars 334684 78405145 78.070461
trunk unify_vars 334718 195405179 195.070461
trunk build_ground1 334743 98412706 98.077963
trunk unify_ground1 334777 220412740 220.077963
trunk build_ground3 334811 200775902 200.441091
trunk unify_ground3 334845 1214729905 1214.395060
trunk build_vars_local 334631 78405092 78.070461
trunk unify_vars_local 334660 195405121 195.070461
trunk build_ground1_local 334659 98412650 98.077991
trunk unify_ground1_local 334693 220412684 220.077991
trunk build_ground3_local 334727 200775846 200.441119
trunk unify_ground3_local 334761 1214729849 1214.395088
trunk build_bind_ground1 334711 88426963 88.092252
trunk bind_ground1 334815 209427067 209.092252
trunk build_bind_ground1_local 334798 88427050 88.092252
trunk bind_ground1_local 334760 209427012 209.092252
trunk build_datatype2 322854 186766706 186.443852
trunk unify_datatype2 322859 1200721125 1200.398266
trunk build_abbrev2 328397 186770252 186.441855
trunk unify_abbrev2 328403 3127039145 3126.710742
head empty 334391 19336635 19.002244
head instance1 334411 156395226 156.060815
head instance3 334445 236643736 236.309291
head instance5 334479 324672451 324.337972
head instance7 334513 344606685 344.272172
head generalize7 334445 793606645 793.272200
head lower7 334409 766606595 766.272186
head copy7 334431 1728915402 1728.580971
head repr 334397 165395256 165.060859
head restore 334425 219395648 219.061223
head keep 334437 200395676 200.061239
head build_vars 334718 78405149 78.070431
head unify_vars 334752 195405183 195.070431
head build_ground1 334747 98412710 98.077963
head unify_ground1 334781 220412744 220.077963
head build_ground3 334815 200775906 200.441091
head unify_ground3 334849 1014776145 1014.441296
head build_vars_local 334629 78405090 78.070461
head unify_vars_local 334663 195405124 195.070461
head build_ground1_local 334663 98412654 98.077991
head unify_ground1_local 334697 220412688 220.077991
head build_ground3_local 334731 200775850 200.441119
head unify_ground3_local 334765 1014776089 1014.441324
head build_bind_ground1 334715 88426967 88.092252
head bind_ground1 334819 209427071 209.092252
head build_bind_ground1_local 334802 88427082 88.092280
head bind_ground1_local 334770 209427022 209.092252
head build_datatype2 322858 186766710 186.443852
head unify_datatype2 322863 1008767126 1008.444263
head build_abbrev2 328401 186770256 186.441855
head unify_abbrev2 328407 3154827306 3154.498899
```

### Checks

Every commit, before its push (each run listed separately, debug build):

```text
cargo test --manifest-path compiler-rust/Cargo.toml --lib tc::
(1)       test result: ok. 217 passed; 0 failed; 11 ignored; 0 measured; 2621 filtered out; finished in 294.62s
(2)       test result: ok. 217 passed; 0 failed; 11 ignored; 0 measured; 2621 filtered out; finished in 304.43s
(3)       test result: ok. 217 passed; 0 failed; 11 ignored; 0 measured; 2621 filtered out; finished in 289.57s
(4)       test result: ok. 217 passed; 0 failed; 11 ignored; 0 measured; 2621 filtered out; finished in 292.77s
(1) 2     test result: ok. 217 passed; 0 failed; 11 ignored; 0 measured; 2621 filtered out; finished in 298.10s
head      test result: ok. 231 passed; 0 failed; 1 ignored; 0 measured; 2648 filtered out; finished in 294.14s
```

CI `Instruction count` on `f4f485422` (head = trunk `6a0838552` plus
item (2)): base 4,024,492,488, head 4,023,750,316, within the threshold.

The reverts restore trees that ran these tests (the base's is trunk's;
the head's is (2)'s). No test was added, removed, ignored or edited and
no step count was lowered. The differential plans passed; that their
pinned seed lists are unchanged was checked as
`git diff origin/ocaml-to-rust-rewrite -- compiler-rust/src/tc/differential.rs`,
which is empty on the final head (this branch does not touch the file). `tc` is not on a compiler build's path (the driver's
default checker is the old one), so no application or `tests/tests`
saving is claimed; the CI `Instruction count` check reports the build's
figures.

## K4

The cost of a unification whose heads expand, with no change of
behaviour. `unify_abbrev2` (two parameterised abbreviation heads, each
expands once) cost 2822.27 at `838ccbca7` and 2968.06 on trunk
`5ea10ac75`. Three attempts, one commit each, in a fixed order: an
attempt is kept when `unify_abbrev2` goes down by 20 or more and no other
operation goes up by more than 2, and is otherwise reverted in a commit of
its own. Target: `unify_abbrev2` at or below 2822.27 with `unify_ground3`
at or below 816 and `unify_datatype2` at or below 824.

Same machine kind and method as "K3a" section 1 (x86-64 Linux, eight
virtual CPUs, Valgrind 3.22.0, the pinned nightly of `rust-toolchain.toml`,
fat LTO, one codegen unit, line tables, every operation of
`benches/tc_kernel.rs` at 1,000,000 iterations minus zero; unification and
`bind_ground1` minus their `build_*` twin, `generalize7` and `lower7`
minus `instance7`, `repr`, `restore` and `keep` minus `instance1`, the
other operations minus `empty`; a control row (`empty`, `build_*`) is
shown raw). Function attribution: for every function cachegrind records
(inlined code counts in the function it is inlined into),
`(op.full - op.zero - twin.full + twin.zero) / 1,000,000` summed over its
files and lines.

### Before

| Operation | `838ccbca7` | Before (trunk `5ea10ac75`) |
|---|---:|---:|
| `instance1` | 137.06 | 137.06 |
| `instance3` | 217.31 | 217.31 |
| `instance5` | 305.34 | 305.34 |
| `instance7` | 325.27 | 325.27 |
| `generalize7` | 449.00 | 449.00 |
| `empty` | 19.00 | 19.00 |
| `lower7` | 422.00 | 422.00 |
| `copy7` | 1709.58 | 1709.58 |
| `repr` | 9.00 | 9.00 |
| `restore` | 63.00 | 63.00 |
| `keep` | 44.00 | 44.00 |
| `checker_instance1` | 126.06 | 126.06 |
| `checker_instance3` | 207.31 | 207.31 |
| `checker_instance5` | 294.34 | 294.34 |
| `checker_instance7` | 314.27 | 314.27 |
| `build_vars` | 78.07 | 78.07 |
| `unify_vars` | 120.00 | 117.00 |
| `build_ground1` | 98.08 | 98.08 |
| `unify_ground1` | 121.00 | 122.00 |
| `build_ground3` | 200.44 | 200.44 |
| `unify_ground3` | 911.95 | 814.00 |
| `build_vars_local` | 78.07 | 78.07 |
| `unify_vars_local` | 120.00 | 117.00 |
| `build_ground1_local` | 98.08 | 98.08 |
| `unify_ground1_local` | 121.00 | 122.00 |
| `build_ground3_local` | 200.44 | 200.44 |
| `unify_ground3_local` | 911.95 | 814.00 |
| `binder` | -8.00 | -8.00 |
| `find_local` | 47.00 | 47.00 |
| `find_open` | 224.00 | 224.00 |
| `find_miss2` | 624.00 | 624.00 |
| `bind_leave` | 172.18 | 172.18 |
| `intern` | 160.00 | 160.00 |
| `build_bind_ground1` | 88.09 | 88.09 |
| `bind_ground1` | 124.00 | 121.00 |
| `build_bind_ground1_local` | 88.09 | 88.09 |
| `bind_ground1_local` | 124.00 | 121.00 |
| `build_datatype2` | 186.44 | 186.44 |
| `unify_datatype2` | 955.95 | 822.00 |
| `build_abbrev2` | 186.44 | 186.44 |
| `unify_abbrev2` | 2822.27 | 2968.06 |

`838ccbca7` is the base of K3's table ("Per commit", column "Before"):
its figures reproduce that column exactly. Trunk carries K3 (the
expansion test and the occurrence probe) and R3f.

### Where `unify_abbrev2`'s difference sits

| Function | `838ccbca7` | Trunk `5ea10ac75` | Change |
|---|---:|---:|---:|
| `Checker::expand_once` | 798.00 | 816.00 | +18.00 |
| `Graph::instance` | 458.00 | 458.00 | +0.00 |
| `Checker::reaches` | 434.05 | 400.00 | -34.05 |
| `Graph::compress` | 306.00 | 306.00 | +0.00 |
| `Checker::unify_distinct` | 276.00 | 284.00 | +8.00 |
| `Checker::unify_expanded` | 251.00 | 195.00 | -56.00 |
| `Checker::expand_head` | 0.00 | 212.00 | +212.00 |
| `Checker::unify3` | 192.00 | 190.00 | -2.00 |
| `Checker::memorize` | 82.00 | 82.00 | +0.00 |
| `tc_kernel::main` | 25.00 | 25.00 | +0.00 |
| total | 2822.27 | 2968.06 |

- `Checker::expand_head`, +212: at `838ccbca7` it is inlined into
  `unify_expanded`; on trunk it is a function of its own, called four
  times (two heads, each asked twice, ctype.ml:2278-2283). Its loop lines
  cost what they cost inline (`expand.rs:819` the call of `expand_once`,
  42 inline and 40 out of line; `:831` 16 and 16; `:836` 4 and 4); the
  `repr` at its entry is 48 out of line where 31 left `unify_expanded`.
  What is new is the call itself: the entry line `:813` 28, the return
  line `:841` 32, and 16 + 8 + 8 more on lines 0 and on the slot reads
  (`graph.rs:235`, `mod.rs:1823`), about 23 a call.
- `Checker::unify_expanded`, -56: the loop lines above left it (about
  -100); K3's two tests (`unify.rs:780-781`, 13, with the `Result`
  handling of the two new call sites, `result.rs`, 16) and its own lines
  came in.
- `Checker::expand_once`, +18: the same steps, compiled in a different
  frame (line 0 +20, the node and row loads of the two heads that do
  expand, which K3's test has just loaded: `graph.rs:248` +6,
  `index.rs:238` +4).
- `Checker::reaches`, -34.05: K3's item (2), the occurrence probe.
- `Checker::unify_distinct`, +8, and `unify3`, -2: register allocation
  around the new call.

Together: the out-of-line `expand_head` and the reloads behind K3's test
cost about +174 (`expand_head` + `expand_once` + `unify_expanded`), the
probe takes back 34.

### Attempt (a): the loaded node and row go to the expansion. Reverted.

`013996c36`. `Checker::expand_once` and `Checker::expand_head` became
wrappers, of unchanged signature and behaviour, of a private
`Checker::expand_loaded` and a `pub(super)` `Checker::expand_head_loaded`
that take the head's node and its type's row as loaded
(`Checker::load_head`); K3's test (`never_expands`, as `may_expand`)
returned the pair it loaded and the head that may expand handed it to
`expand_head_loaded`. The loads went, as intended: `expand_loaded` is 42
below `expand_once` (774 against 816). But both pairs of expansions now
make out-of-line calls with the pair as two 16-byte arguments: the first
pair calls `expand_head_loaded` (entry line 52, its call of
`expand_loaded` 56, return line 40, for the four calls), the second pair
calls `expand_head`, now a wrapper of 78 around the same call. Against
trunk: `unify_abbrev2` +145.00, `unify_ground3` -1.00, `unify_datatype2` +1.00
(the whole table is in "Per attempt" below):

| Function | Trunk | (a) | Change |
|---|---:|---:|---:|
| `Checker::expand_once` | 816.00 | 0.00 | -816.00 |
| `Checker::expand_loaded` | 0.00 | 774.00 | +774.00 |
| `Checker::expand_head_loaded` | 0.00 | 292.00 | +292.00 |
| `Checker::expand_head` | 212.00 | 78.00 | -134.00 |
| `Checker::unify_expanded` | 195.00 | 224.00 | +29.00 |
| every other function | 1745.06 | 1745.06 | +0.00 |
| total | 2968.06 | 3113.06 | +145.00 |
