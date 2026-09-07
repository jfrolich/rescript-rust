# Type-graph descriptor copy investigation

## Scope

This investigation covers one boundary: read access to mutable `TypeDesc` nodes during Ctype unification and recursive type-graph walks. It does not change signature ownership, portable internalization, substitution, lazy Env forcing, type-node identity, or Btype backtracking.

## Why this boundary is next

The existing serial sample recorded 146 `TypeDesc::clone` leaves, 281 `TypeDesc` drop leaves, 254 leaves in one `Vec::clone` specialization, and 2,280 `memmove` leaves. The parallel sample recorded 68, 100, and 945 for the corresponding descriptor clone, descriptor drop, and `memmove` leaves. These are sampled events, not elapsed-time budgets.

Caller stacks narrow the descriptor copies to an executed Ctype family. In the serial call graph, `unify_types` directly parents 32 sampled clone events and `deep_occur_rec` directly parents 17. Other Ctype parents include `subst_identity_copy_rec`, `unify_var`, `generalize_rec`, and `link_type`. The parallel call graph again shows `unify_types` and `deep_occur_rec`. This is distinct from the required signature materializations. It occurs while typing expressions and patterns after signatures have entered the local type arena.

The Rust ownership mismatch is concrete:

- `TypeContext::get_desc` at `compiler-rust/src/types/context.rs:1598-1600` deep-clones the descriptor so callers can release the `RefCell` borrow before recursion or mutation.
- `deep_occur` at `compiler-rust/src/types/ctype.rs:957-991` clones a complete descriptor even though its constructor branch reads only `args`. Its fallback then calls `iter_type_expr`.
- `iter_type_expr` at `compiler-rust/src/types/btype.rs:298-368` releases the borrow by materializing owned payloads. It clones argument vectors, tuple vectors, constructor vectors, object-name vectors, polymorphic-variable vectors, package vectors, and a complete `RowDesc`.
- `unify_types` at `compiler-rust/src/types/ctype.rs:5110-5847` needs selected owned fields before recursive mutation, but starts by cloning both complete descriptors. Some branches then clone payloads or the first descriptor again for failure restoration.

The OCaml owner is different. `compiler/ml/btype.ml:255-278` matches the descriptor by reference and visits immediate children in place. `compiler/ml/ctype.ml:2270-2445` reads `t1'.desc` and `t2'.desc` directly, retaining only `d1` for the exact restoration boundary around `unify3`. `compiler/ml/ctype.ml:493-500` generalizes by borrowing the constructor abbreviation and then traversing immediate children. Native code does not construct read-only descriptor snapshots.

A blanket borrowed accessor is not a valid Rust fix. Recursive callbacks can path-compress or mutate nodes, and holding a `RefCell` borrow across those calls can panic on cycles. The proposed mechanism must first copy only the stable handles and scalar fields required by the selected branch, release the borrow, and then recurse. Required fresh type copies and native rollback descriptors stay intact.

## Focused diagnostic design

Before production changes, use one archive-only instrumented source tree and one serial fixed Tella build. Add counters to each compilation-owned `TypeContext`, never global or thread-local state. Register the source revision, binary hashes, Tella revision, compiler/runtime paths, source and config inventories, protected-file hashes and mtimes, exact 3,248-module output count, 107-source runtime bootstrap proof, and the 5,048-file JavaScript digest before launching it.

The counters will separate four kinds of work:

1. `get_desc` snapshots in `unify_types`, `deep_occur_rec`, `generalize_rec`, and `link_type`, with calls and descriptor variant.
2. Payload copied by those snapshots: vector element counts, path component counts, strings, row fields, and row-name arguments. These are logical copied items, not bytes or live heap.
3. Copies required for native-equivalent rollback in `unify_types`, counted separately from read-only inspection.
4. `iter_type_expr` payload materialization, with calls and copied immediate-child handles, row fields, and owned metadata that no callback reads.

Use owner-local `Instant` scopes only around the complete selected operation, plus a no-timer counter lane if the timer perturbs the build materially. Report inclusive operation time separately from copy bookkeeping. Do not extrapolate sample counts or logical items to wall time. Preserve the first run and every setup failure. Run under `/usr/bin/lockf -k /tmp/rescript-tella-heavy.lock`.

## Candidate design gate

Retain a production change only if the diagnostic shows material read-only copy work in this boundary. The first candidate is a Ctype-specific inspection enum and an immediate-child collector:

- Match a borrowed descriptor once.
- Copy only `TypeExprRef`, `AbbrevMemoRef`, flags, and branch-required labels or paths.
- For generic graph walking, append child handles in native order while borrowed, then release the borrow before callbacks.
- Keep the exact `d1` rollback copy where OCaml restores `t1'.desc` after failed unification.
- Keep `CopyCache`, fresh generic-node allocation, row-copy markers, substitution windows, `repr` compression, and allocation order unchanged.

Do not add descriptor interning, `Rc` or `Arc` per type node, unsafe pointers, serializer normalization, path-spelling equivalence, or force suppression. If the measured removable work is small, stop without a production rewrite.

## Validation if the gate passes

Add unit tests for cyclic links, recursive variants, diamonds, failed structural unification restoration, object fields, package arguments, and callback mutation after child collection. Then build release compiler and Rewatch binaries and run typedtree, raw Lambda, optimized Lambda, JavaScript, external JavaScript, and error parity with release artifacts. Existing red syntax and AST0 gates and the external native blocker remain unwaived.

A successful candidate still requires a new sealed paired comparison against the immutable position-index candidate binaries. Parallel and serial cohorts stay separate, with the existing fixed Tella input and output safeguards. No old cohort can be pooled or rerun.
