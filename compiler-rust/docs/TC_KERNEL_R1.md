# R1 kernel measurements

Before: `8bf6724487`. After: `3ce75c9b4` (the three changes below).
The checker is not on the driver path. These are kernel costs, not savings
in a compiler build. R1's gate is the measured attribution table with at
most 30 extra generic-bookkeeping instructions for `instance7`, replacing
the original blanket +25% limit against a kernel missing required data.

## Method

Same machine, Valgrind 3.22 cachegrind, pinned Rust toolchain, fat LTO,
one codegen unit, line tables. One million operations, subtract each
program's zero-iteration run. Subtract its own empty loop for instances;
subtract its own `instance7` run for `generalize7` (node-making is then
removed as well). Do not subtract another instance run from `instance7`:
that operation **is** the instance cost. The reference's `scheme7` builds
six distinct nodes; the checker bench reproduces that graph.

Run the actual reference script first:

```sh
CARGO_TARGET_DIR=/tmp/checker-reference cargo build --release \
  --manifest-path compiler-rust/docs/prototypes/checker-kernel/Cargo.toml
bash compiler-rust/docs/prototypes/checker-kernel/measure.sh \
  /tmp/checker-reference/release/checker-kernel
CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 \
CARGO_PROFILE_BENCH_DEBUG=line-tables-only \
  cargo bench --manifest-path compiler-rust/Cargo.toml --bench tc_kernel --no-run
```

For each executable and operation, retain both cachegrind files and annotate
both (substitute the executable printed by Cargo for `BENCH`):

```sh
valgrind --tool=cachegrind --cache-sim=no \
  --cachegrind-out-file=instance7.zero.cg BENCH instance7 0
valgrind --tool=cachegrind --cache-sim=no \
  --cachegrind-out-file=instance7.full.cg BENCH instance7 1000000
cg_annotate --auto=yes --threshold=0 instance7.full.cg
```

The rerun of the reference script reproduces the published figures. Its raw
instructions/iteration, before empty-loop or node-making subtraction:

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

Unification, application and scope operations are R3/R4 operations, not
implemented by R1. The R1 benchmark does not fabricate substitutes for them.

## Results

Instructions per operation after subtraction. The before executable was
rerun on the same setup; differences below one instruction include
amortized pool growth and runtime, not an invented per-node charge.

| Operation | Reference | Before (`8bf6724487`) | After | After minus reference |
|---|---:|---:|---:|---:|
| instance1 | 89.00 | 168.09 | 140.06 | +51.06 |
| instance3 | 169.00 | 246.26 | 220.31 | +51.31 |
| instance5 | 221.00 | 346.46 | 305.34 | +84.34 |
| instance7 | 250.00 | 390.49 | 327.27 | +77.27 |
| generalize7 | 404.00 | 488.00 | 488.00 | +84.00 |

No operation was substituted or removed to improve this table. Generalization
is unchanged by the three instantiation changes and remains within 25% of
its reference. The instance costs are judged by the attribution below.

## The three changes

1. `fdbf557f0`: `Graph::push` and `Graph::instance` do not touch forwarding
   storage. `copy` and `capture` resize it once at entry for existing source
   nodes. Each row is initialized at most once per unit; the sum of that
   initialization is linear in nodes made. A test makes 10,000 instances
   without growing the forwarding array. The shared-positions copy test
   starts with 10,000 source nodes and no forwarding rows.
2. `d41bfabea`: closed and external-bearing instances share one const-generic
   implementation. The closed specialization has no external lookup case
   in its per-reference mapping. Both specializations retain the node and
   slot step bounds, including a 10,000-parameter test for each.
3. `3ce75c9b4`: capture validates tags; instantiation uses a `b`-field addend
   table and rewrites `a` only for arrows. In the actual tag order the table
   is `[0, 0, list_base, list_base, param_base]` (the LINK entry is never
   captured). This removes the four-way match/panic arm from the node loop.
   The table is retained because it reduced every required measured case:

| Operation | After step 2 | After step 3 | Difference |
|---|---:|---:|---:|
| instance3 | 227.31 | 220.31 | -7.00 |
| instance5 | 321.33 | 305.34 | -16.00 |
| instance7 | 352.27 | 327.27 | -25.00 |

The sub-cent rounding difference in `instance5` is from the measured
startup/growth remainder, not a changed operation.

## Instruction attribution

These are disjoint **debug-info attribution buckets**, from both programs'
cachegrind files, not estimates of cycles or independently toggled
counterfactual features. For each bucket: `(full - zero) / 1,000,000`, then
subtract that bucket's empty-loop run. The table shows **after minus
reference**. The buckets sum to the full measured difference.

| Attributed code | instance1 | instance3 | instance5 | instance7 |
|---|---:|---:|---:|---:|
| Descriptor/reference code and template header | +25.00 | +27.00 | +30.00 | +29.00 |
| Slice range/index validation | +2.00 | +2.00 | +6.00 | +6.00 |
| Pool iteration, writes and capacity/length bookkeeping | +23.00 | +21.00 | +48.00 | +41.00 |
| Forwarding zero-fill in instance | 0.00 | 0.00 | 0.00 | 0.00 |
| Caller/dispatch | +1.00 | +1.00 | 0.00 | +1.00 |
| Amortized pool growth and runtime | +0.06 | +0.31 | +0.34 | +0.27 |
| **Total** | **+51.06** | **+51.31** | **+84.34** | **+77.27** |

The classifier is unchanged from the first report: source-attributed
`Graph::instance` instructions in `template.rs` and its inlined `Node`
accessors versus the reference's `main.rs`; `slice/index.rs` separately;
remaining Rust-library instructions attributed to `instance` as pool
iteration/storage; then `memset`, the benchmark caller, and all remaining
runtime/growth instructions. Startup and empty-loop subtractions are
performed independently for each bucket. There is no unreported remainder.

### Required data versus still generic bookkeeping

The split below assigns the operations implementing the extra section 3.2
data to required-data cost. It leaves all other differences, including every
range/index check, root-kind check, handle-limit check, function/loop setup,
tag relocation, caller and allocation/runtime remainder, in generic
bookkeeping. It does **not** call all of `instance` design-required merely
because the function is necessary.

At source revision `3ce75c9b4`, the required-data assignment is reproducible
from these cachegrind source lines and the library bucket:

| Required-data operation | Attribution | instance1 | instance3 | instance5 | instance7 |
|---|---|---:|---:|---:|---:|
| Pool ranges, external-policy dispatch, parameter-pool presence | `template.rs:369,370,432` | 13 | 13 | 13 | 13 |
| Memo-sentinel/reference mapping above the reference's relative mapping | `template.rs:417,422` minus reference `main.rs:126` | 3 | 9 | 11 | 4 |
| Parameter label/location payload construction | `template.rs:435` | 0 | 0 | 4 | 6 |
| Extra slot/parameter iteration and storage, three pools instead of two | Rust-library `instance` bucket, excluding `slice/index.rs` | 23 | 21 | 48 | 41 |
| **Required-data difference** | | **39** | **43** | **76** | **64** |

The extra library work comes from the memo slot and the 12-byte parameter
rows plus a separate parameter pool, all copied with the same exact-size
iterator strategy. It includes reservation/length maintenance for those
additional pools, not a forwarding-array pass or an additional type walk.
The source line attribution is an accounting rule, not proof of a minimum
possible machine-code sequence.

For the gate's `instance7`, the **generic** 13.27 is independently accounted
for rather than chosen as a round residual:

| Generic difference | Instructions | Cachegrind attribution |
|---|---:|---|
| Source control/relocation not assigned to required data | +6 | root-kind test +4 (`template.rs:361`); handle limit +3 (`:402`); slice-range arithmetic -2 (`:426,434,448` vs reference `:128,132`); tag/field relocation +1 (`graph.rs:29`, `template.rs:446,449,456,457` vs reference `:133,136`); function/unknown-line net 0 |
| Range/index checks, all retained conservatively as generic | +6 | `slice/index.rs:90,238` |
| Caller/dispatch | +1 | benchmark `main`, after its own empty loop |
| Amortized growth/runtime | +0.27 | all remaining functions, after startup and empty-loop subtraction |
| **Still generic bookkeeping** | **+13.27** | **Below the 30-instruction gate** |

`hyperfine --warmup 2 --runs 10`, one million `instance7` calls per run:

| Version | Mean ± standard deviation | Min–max |
|---|---|---|
| Before (`8bf6724487`) | 15.2 ± 1.9 ms | 13.7–20.2 ms |
| After | 13.3 ± 1.2 ms | 12.3–16.6 ms |

These short kernel runs are supporting evidence, not an application speedup.

## Expansion memo ownership

The general copy creates a distinct cleared memo slot per copied constructor.
It does not implement `compiler/ml/ctype.ml:779-797`: `proper_abbrevs` then
`find_repr` in the shared simple-abbreviation memo. A nullary copy may need
to link to an already memoized representative; an `Mcons` memo can require
shared invalidation through `Mlink`. That path/declaration and expansion
memo belongs to R3. Its section 5.3 row explicitly assigns the lookup and
invalidation in general copies **and** template instantiation. Clearing a
private slot is not a claim of O11 parity.

## What remains and why

The difference above the kernel splits into **required data / still generic
bookkeeping** instructions as follows: `instance1` **39.00 / 12.06**,
`instance3` **43.00 / 8.31**, `instance5` **76.00 / 8.34**, and `instance7`
**64.00 / 13.27**. The required-data part is the 12-byte parameters with label
and location, constructor memo slot, external-reference support and three
pools instead of two; the generic part retains all other control, checks,
relocation and growth/runtime differences. R1 meets the revised 30-instruction
bookkeeping gate. Whether the measured instance price matters in a complete
checker is judged by R5c: covered units at most 60% of the old cost, including
the bridge, not by assuming an application saving from this kernel.
