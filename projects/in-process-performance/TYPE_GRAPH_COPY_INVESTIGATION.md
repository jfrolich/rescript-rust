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

The OCaml owner is different. `compiler/ml/btype.ml:255-278` matches the descriptor by reference and visits immediate children in place. `compiler/ml/ctype.ml:2175-2324` implements `unify3`: it reads `d1` and `d2` at lines 2178-2179, then restores `t1'.desc` in the failure handler at lines 2322-2324. `compiler/ml/ctype.ml:493-500` generalizes by borrowing the constructor abbreviation and then traversing immediate children. Native code does not construct read-only descriptor snapshots.

A blanket borrowed accessor is not a valid Rust fix. Recursive callbacks can path-compress or mutate nodes, and holding a `RefCell` borrow across those calls can panic on cycles. The proposed mechanism must first copy only the stable handles and scalar fields required by the selected branch, release the borrow, and then recurse. Required fresh type copies and native rollback descriptors stay intact.

## Focused diagnostic design

Before production changes, use one archive-only instrumented source tree and one serial fixed Tella build. Add counters to each compilation-owned `TypeContext`, never global or thread-local state. Register the source revision, binary hashes, Tella revision, compiler/runtime paths, source and config inventories, protected-file hashes and mtimes, exact 3,248-module output count, 107-source runtime bootstrap proof, and the 5,048-file JavaScript digest before launching it.

The counters will separate four kinds of work:

1. `get_desc` snapshots in `unify_types`, `deep_occur_rec`, and `generalize_rec`, with calls and descriptor variant.
2. Payload copied by those snapshots: top-level vector elements, row fields, row payload type handles, and row-name argument handles. The probe deliberately excludes nested metadata size: `Path` clones share `Arc` nodes, and it does not traverse strings or longidents solely for accounting. These are logical copied items, not bytes or live heap.
3. Copies required for native-equivalent rollback in `unify_types`, counted separately from read-only inspection.
4. `iter_type_expr` payload materialization, with calls and copied immediate-child handles, row fields, and owned metadata that no callback reads.

Use owner-local `Instant` scopes around descriptor cloning or the existing child-materialization operation. Record calls and time separately by descriptor variant or materialization kind in the same fixed run. Update counters only after each timed region. Report clone/materialization self-time separately from bookkeeping. These timers exclude snapshot destruction and later branch payload clones, so they are neither a full descriptor lifetime cost nor a veto on all copy/drop traffic. Do not extrapolate sample counts or logical items to wall time. Preserve the first run and every setup failure. Run under `/usr/bin/lockf -k /tmp/rescript-tella-heavy.lock`.

## Candidate design gate

Retain a production change only if the diagnostic shows material read-only copy work in this boundary. The first candidate is a Ctype-specific inspection enum and an immediate-child collector:

- Match a borrowed descriptor once.
- Copy only `TypeExprRef`, `AbbrevMemoRef`, flags, and branch-required labels or paths.
- For immutable descriptor lists, copy only child handles in native order, then release the borrow before callbacks. Variant rows must remain staged: resolve each `row_field_repr` after prior callbacks, inspect `repr(row_more)` after all field callbacks, and call `row_more` only after `iter_row`, matching `compiler/ml/btype.ml:237-271`.
- Keep the exact `d1` rollback copy where OCaml restores `t1'.desc` after failed unification.
- Keep `CopyCache`, fresh generic-node allocation, row-copy markers, substitution windows, `repr` compression, and allocation order unchanged.

Do not add descriptor interning, `Rc` or `Arc` per type node, unsafe pointers, serializer normalization, path-spelling equivalence, or force suppression. If the measured removable work is small, stop without a production rewrite.

## Validation if the gate passes

Add unit tests for cyclic links, recursive variants, diamonds, failed structural unification restoration, object fields, package arguments, and callback mutation. Include a discriminator where an earlier row callback mutates a later row field and `row_more`; the later resolution must observe that mutation. Then build release compiler and Rewatch binaries and run typedtree, raw Lambda, optimized Lambda, JavaScript, external JavaScript, and error parity with release artifacts. Existing red syntax and AST0 gates and the external native blocker remain unwaived.

A successful candidate still requires a new sealed paired comparison against the immutable position-index candidate binaries. Parallel and serial cohorts stay separate, with the existing fixed Tella input and output safeguards. No old cohort can be pooled or rerun.

## Completed diagnostic

The registered serial diagnostic completed exactly once. It compiled 3,248 project modules and 107 runtime sources, emitted 5,048 JavaScript files with the required `1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49` digest, and produced 16,775 counter records: five lanes for each of 3,355 compilation contexts. The instrumented build took 19.114471959 seconds. That wall time is perturbed and is not comparable to the earlier uninstrumented release cohort.

The parent independently checked the process count, process-group cleanup, all four inventories, 12 generated metadata paths, the 510-row generated-source ledger, four protected untracked files, 18 protected generated files, all sealed dependencies, all 414 original and 414 probe source files, and the live JavaScript output. The audit passed. The immutable evidence is under the organization-controlled `simplify-and-speed/type-desc-read-copy-diagnostic` artifact, especially `provenance/parent-counter-analysis.json` and `provenance/parent-postrun-audit.json`.

| Lane | Calls | Timed operation self-time | Logical copied payload |
|---|---:|---:|---:|
| `unify_read` | 6,230,958 | 113.765 ms | 4,233,087 vector items; 369,957 row fields |
| `deep_occur_read` | 4,927,592 | 86.791 ms | 2,327,951 vector items; 63,610 row fields |
| `generalize_read` | 545,545 | 10.072 ms | 317,155 vector items; 41,568 row fields |
| `required_rollback` | 158,811 | 3.231 ms | 182,316 vector items; 62,112 row fields |
| `iter_materialize` | 14,826,666 | 250.128 ms | 11,222,109 child handles; 750,128 row fields |

The three descriptor-read lanes total 210.627 ms. Descriptor reads plus child materialization total 460.755 ms, arithmetically 2.41% of this one instrumented wall time. Neither number is a removable-work estimate. Timing every call adds two clock reads around each operation. The recorded intervals include timing overhead but exclude snapshot destruction and payload clones performed later by individual branches.

The kind split makes the limit concrete:

- `iter_materialize` spent 50.507 ms across 3,500,775 `None` visits that copied no payload. Its 192.363 ms across 11,069,760 `Many` visits includes the stable child-handle snapshot needed to release the `RefCell` borrow before callbacks. Arrow traversal already drops labels and copies only `TypeExprRef` handles. Tuple, constructor, package and poly traversal likewise copy only handles.
- Variant child materialization accounted for 6.546 ms across 211,377 visits. Replacing it with an eager flattened collector is invalid: native traversal resolves each row field after earlier callbacks and observes `row_more` after field callbacks.
- `deep_occur_read` constructor snapshots accounted for 76.147 ms across 4,287,590 calls. The lane copied 2,327,951 vector items across those constructor calls and all other descriptor kinds, so at least 1.96 million constructor calls were nullary. The timing does not isolate argument-vector allocation from timer, borrow or `Path` `Arc` increment costs. Snapshot destruction is outside the interval.
- `generalize_read` constructor snapshots accounted for 7.818 ms across 443,467 calls. A narrow implementation could borrow the descriptor, copy only `AbbrevMemoRef`, release the borrow, and then use the existing staged child traversal. This would avoid cloning an unused path and argument vector before `iter_type_expr` snapshots the required child handles, and would also eliminate snapshots of non-constructor descriptors. The full `generalize_read` lane is 10.072 ms, of which 7.818 ms covers constructors. Neither figure measures the associated destruction cost.
- `unify_read` accounted for 113.765 ms across both input descriptors and all branches. A branch-specific inspection enum could avoid unused fields, but unification deliberately owns stable values across recursive mutation and must retain the first descriptor for native-equivalent failure restoration. The separate rollback lane confirms 3.231 ms of measured work that is required, not removable.

## Materiality disposition

The evidence does not justify a production refactor at this boundary.

The measured intervals do not establish enough removable work to justify the broad candidates. Replacing `unify_types` snapshots with a branch inspection enum would restructure the mutation and rollback control flow. Its recorded clone intervals total 113.765 ms including timing overhead, but this is not an upper bound on total copy-and-destruction cost. Replacing `iter_type_expr` ownership would target work that is predominantly required handle stabilization and would risk `RefCell` conflicts or changed row-mutation observation. Neither is a credible route to a material clean-build improvement from this evidence.

The coherent narrow candidate is the `generalize_rec` borrow described above. It would remove the read-only snapshots measured across the full 10.072 ms lane, including the 7.818 ms constructor subset, in a 19.114-second perturbed build. `deep_occur_rec` could similarly copy only constructor arguments, but that retains argument-vector copying, whose cost was not separately attributed; borrowing those arguments across recursive `repr` and traversal would require a new aliasing and mutation proof for cycles. The diagnostic cannot attribute enough removable cost to either change to pass the production gate.

Therefore no compiler code, descriptor representation, traversal API or ownership model is changed. A future investigation may revisit this only with new evidence that separates timer overhead, allocation and destruction and proves a larger owner-local budget. It must still retain stable child handles where callbacks can mutate, the exact unification rollback descriptor, and native staged row behavior.

## Preserved protocol history

The preparation record is intentionally not sanitized. Bytes for one pre-kind-counter runner version were overwritten before sealing; its recorded hash and the surviving source, patch and binary versions remain, with the loss disclosed in `provenance/runner-version-loss.json`. The first sealed runner was rejected before execution because its input and process-lifetime guards were incomplete, and that version is preserved. The first admitted outer wrapper then failed before launching the runner because shell `noclobber` rejected a second redirection to its newly created capture file. Its empty log and exit status 1 are preserved. The parent verified that this was a zero-launch failure, recorded the correction, and used the same still-unconsumed sealed slot once. No diagnostic workload was retried or replaced.
