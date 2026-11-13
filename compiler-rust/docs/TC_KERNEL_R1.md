# R1 kernel measurements

Measured at `996a0b12a`, after the full-compression and public-API changes.
The checker is not on the driver path. These are kernel costs, not savings
in a compiler build. The figures below are **not** within the original
25% limit for instantiation; they expose the cost of the extra design data
for review rather than claiming that the original gate passed.

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

The reference script's raw instructions/iteration were:

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

All numbers are instructions per operation after subtraction. "Before" is
`17655d0ad`: already the public production API and full compression, before
the iterator changes. Differences of less than one instruction include
amortized arena growth, not an invented per-node charge.

| Operation | Reference | Before | After | After minus reference | Within +25% |
|---|---:|---:|---:|---:|---|
| instance1 | 89.00 | 122.06 | 168.09 | +79.09 | No |
| instance3 | 169.00 | 300.18 | 246.26 | +77.26 | No |
| instance5 | 221.00 | 466.30 | 346.46 | +125.46 | No |
| instance7 | 250.00 | 550.40 | 390.49 | +140.49 | No |
| generalize7 | 404.00 | 841.00 | 488.00 | +84.00 | Yes |

The one-node case regresses: the fixed cost of explicit external/parameter
pool ranges and bulk forwarding initialization is not paid back on one node.
That regression is included, not hidden by reporting only larger schemes.

## Instruction attribution

These are disjoint **debug-info attribution buckets**, from both programs'
cachegrind files, not estimates of CPU cycles or independently toggled
counterfactual features. For each bucket: `(full - zero) / 1,000,000`, then
subtract that bucket's empty-loop run. The table shows **checker minus
reference**. The buckets sum to the measured difference, including the
caller and the fractional allocation/runtime remainder.

| Cause / attributed code | instance1 | instance3 | instance5 | instance7 |
|---|---:|---:|---:|---:|
| Descriptor/reference code and template header | +21.00 | +27.00 | +42.00 | +64.00 |
| Slice range validation, once per pool | +5.00 | +5.00 | +8.00 | +8.00 |
| Pool iteration, writes and capacity/length bookkeeping | +40.00 | +34.00 | +64.00 | +56.00 |
| Dense forwarding zero-fill (`memset`) | +13.00 | +11.00 | +12.00 | +12.00 |
| Caller/dispatch | 0.00 | 0.00 | -1.00 | 0.00 |
| Amortized pool growth and runtime | +0.09 | +0.26 | +0.46 | +0.49 |
| **Total** | **+79.09** | **+77.26** | **+125.46** | **+140.49** |

How to read the buckets against section 3.2:

- **Descriptor/reference/header:** the checker has a non-generic-root case,
  a bounded local-handle space, external-reference ranges and parameter-pool
  ranges. It preserves the constructor memo sentinel, relocates arrows into
  the separate parameter pool, and retains each parameter's label/location.
  The reference has none of those pools and reserves no constructor memo
  slot. Relative-reference arithmetic itself exists in both. These counts
  are the source-attributed `Graph::instance` instructions in `template.rs`
  and its inlined `Node` accessors, versus the reference's `main.rs`.
- **Range checks:** the checker validates slices for the template-range row and the node, list and parameter storage. The checked ranges are outside the
  node/slot iteration, not a bounds check at each indexed source read.
  These are `Graph::instance` instructions attributed to `slice/index.rs`.
- **Pool iteration/storage:** section 3.2 requires 12-byte parameters instead
  of the reference's four-byte arrow slots, and a constructor memo slot;
  section 3.3 requires a dense forwarding array for general copying. Those
  extra pools need reservation, length updates, iteration and stores. This
  bucket is the remaining Rust-library code attributed to `Graph::instance`
  (including exact-size iterator machinery), not an extra arbitrary charge.
- **Zero fill:** the dense forwarding array must have initialized generation
  rows before a future generalization/copy can address those nodes. Its bulk
  initialization now uses `memset`, once per instance; the reference has no
  forwarding array. The row is eight bytes, pinned by a test.
- **Growth/runtime:** the reference preallocates large pools; the checker
  starts with empty pools and grows them. These counts are the fractional
  residual outside `instance`, `main` and `memset`, after the same startup
  and empty-loop subtractions. They are not charged once per visited node.

This attributes emitted instructions to the required storage mechanisms;
it is not proof that every compiler-generated instruction in a bucket is
irreducible. In particular the fixed pool/header overhead warrants review
before accepting an exception to the original limit.

## Costs removed

The first profiles attributed 120 instructions of `instance7` to Vec code,
including repeated `push` capacity checks, and 208 instructions of
`generalize7` to non-inlined representative walks. The changes:

1. Source ranges are slices and destinations use exact-size `extend` calls;
   each node/list/parameter pool reserves once, without a per-node growth
   test. The forwarding rows are initialized in bulk.
2. Capture records external references separately. Instantiation validates
   those references before extending nodes, allowing safe disjoint borrows
   and avoiding a mutable whole-graph accessor inside each copy iteration.
3. Parameter ranges are recorded during capture, not discovered by another
   tree pass. A 16-byte `Template` indexes a cold 20-byte pool-range row;
   counts remain u32, avoiding a 65,535-node limit. This is an explicit
   extension of section 3.2's proposed template/external-range layout.
4. The representative helper is inlineable and the child-enqueue helper is
   inlined. There is no per-node `children` call left. Empty external and
   parameter pools do not run iterator setup.

An intermediate split-borrow version left `instance_ref` uninlined and
cost 653.40 raw instructions for `instance7`; forcing its inline expansion
reduced that to 543.40, but retained per-node destination checks. It was
superseded by the bulk-pool implementation, not kept as a second path.

`hyperfine --warmup 2 --runs 10`, one million `instance7` calls per run:

| Version | Mean ± standard deviation | Min–max |
|---|---|---|
| Before | 16.6 ± 0.3 ms | 16.3–17.2 ms |
| After | 13.7 ± 0.8 ms | 12.8–15.4 ms |

These short kernel runs are supporting evidence, not an application speedup.

## Expansion memo ownership

The general copy currently allocates a distinct memo slot for each copied
constructor and clears it. It does **not** implement
`compiler/ml/ctype.ml:779-797`: `proper_abbrevs`, followed by `find_repr` in
the shared simple-abbreviation memo. In particular a copied nullary
constructor may need to become a link to an already memoized representative,
and an `Mcons` memo can require shared invalidation through `Mlink`.

That lookup requires the path/declaration and expansion memo owned by R3;
it is now explicit in R3's section 5.3 row. R3 must apply it to both general
copies and template instantiation, including memo invalidation. R1 must not
claim O11 parity merely because its source constructor's private memo slot
was cleared. No expansion algorithm or substitute fallback is added here.
