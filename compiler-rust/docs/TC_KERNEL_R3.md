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
