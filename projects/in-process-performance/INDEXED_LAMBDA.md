# Indexed optimized Lambda migration

## Goal

Replace the recursive owned `lambda::Lambda` tree with compilation-owned indexed storage that remains canonical across optimized-Lambda passes and is consumed directly by JS lowering. This is a storage and ownership migration, not a new optimizer. The OCaml pass order, branch order, source-order child lists, smart-constructor behavior, identifier allocation, metadata updates, diagnostics, CMJ boundaries, dumps, source maps, and JavaScript output remain unchanged.

The current Rust pipeline repeatedly consumes and rebuilds `Box<Lambda>` and `Vec<Lambda>` trees. The target representation allocates optimized-Lambda nodes in a module-local store and addresses them with checked `u32` indices. Rewrites return roots for independently allocated replacement nodes and reuse unchanged immutable node IDs where semantics permit. Old nodes remain valid only while metadata or substitutions intentionally retain them. Each pass must track reachable live nodes versus retained superseded nodes and payload bytes; blindly appending a complete new graph per pass could worsen peak RSS and is not an acceptable endpoint. Reclamation or compaction requires separate evidence and must not change identity or traversal. No per-node `Rc`/`Arc`, `unsafe`, structural deduplication, placeholder nodes, or output-mode behavior is permitted.

## Whole-path ownership

One `IndexedLambda` is owned by a compilation after RawLambda lowering and moves through:

1. `raw_lambda/lower.rs`: ultimately emit indexed nodes directly; during migration, perform one owned `Lambda -> IndexedLambda` conversion at the first migrated boundary.
2. `lam_compile_main.rs`: retain the same sequence of deep flatten, collect, exits, alias, alpha, lets, coercion/export, and hoisted-alias operations while replacing each root with a `NodeId` in the same store.
3. Analysis and rewrite helpers: `lam_analysis`, `lam_beta_reduce`, `lam_subst`, `lam_util`, `lam_hit`, `lam_closure`, `lam_eta_conversion`, `lam_pass_count`, and `lam_pass_eliminate_ref` receive `&IndexedLambda` plus `NodeId` and preserve current traversal and fresh-identifier order.
4. `lam_compile.rs` and its primitive/constant/variant/external helpers: borrow the indexed store and compile from a root `NodeId`. Temporary optimizer expressions are appended to that store or represented by narrowly scoped local indexed stores when they originate from external CMJ Lambda payloads.
5. CMJ and debug compatibility: CMJ export Lambda payloads remain at the serialization boundary until that format is migrated. `-drawlambda`, Lambda sexp capture, playground intermediates, and diagnostics materialize or print by borrowed indexed traversal in the same natural order. Normal production JS compilation must not materialize a recursive tree.
6. `js_ir`: remains the consumer output for this migration. A later JS-indexing project is separate.

`driver::InProcessPreJsCompileResult` will eventually own the indexed store/root instead of a recursive `Lambda`, so the representation survives the in-process signature-ready split.

## Representation

The initial representation consists of:

- `NodeId(u32)`, with checked conversion from `usize` on insertion.
- A dense `Vec<IndexedNode>` containing only a discriminant and compact scalar/index fields.
- Per-kind cold payload vectors for values that enlarge uncommon variants: constants, apply metadata, function metadata/parameters, primitives/locations, switch metadata, and strings.
- Contiguous side arrays for ordered child `NodeId`s, recursive bindings, keyed switch cases, and string-switch cases. Ranges are `(start: u32, len: u32)` and preserve insertion/source order.
- A root `NodeId` and explicit context-paired borrowed APIs (`node`, `children`, `bindings`, switch-case access). M1 does not brand each `NodeId` with an arena: callers must interpret it only through the `IndexedLambda` from which it came. `IndexedLamStats<'arena>` keeps that arena alive and supplies the paired lookup context, but cannot reject a foreign store's numerically valid ID. Callers do not retain payload references while appending nodes.

Children are inserted before parents during the initial conversion, giving postorder locality without changing semantic traversal. Passes must traverse children in the exact order of their OCaml counterparts rather than relying on physical node order. Sharing is explicit: two parent payloads may name the same `NodeId`. Rewrites do not mutate a shared child in place; they return replacement roots, so independent occurrences remain independently rewritable unless a pass deliberately reuses a result.

The compatibility materializer uses the root-directed semantic traversal, not arena order or structural content. Shared indexed nodes become equivalent recursive values at the old boundary because recursive `Lambda` has no observable node identity.

## Migration checkpoints

### M1: storage plus the first real pass

- Add complete lossless owned `Lambda -> IndexedLambda` conversion and compatibility `NodeId -> Lambda` materialization.
- Add semantic round-trip tests covering every node family and preserving switch/case/binding order.
- Add tests that deliberately share one child index between two parents, rewrite one parent path by appending nodes, and prove the other parent and shared child remain unchanged. Assert semantic materialized results, not pointer identity.
- Port `Lam_pass_collect.collect_info` and its arity queries to borrowed indexed access. Its Lambda-bearing identifier metadata stores `NodeId`s paired with the stats lookup arena instead of eagerly materializing function bodies, option payloads, or block elements.
- Differential tests run indexed collect/arity against the existing tree implementation across node variants and metadata outcomes. Separate deterministic model checks cover ordered and deliberately shared child edges.
- Keep the production pipeline unchanged. A tree -> indexed -> tree boundary around one read-only pass would be unamortized conversion overhead and is not a production milestone.

M1 is an inactive, buildable, regression-tested migration foundation. It makes no wall-time claim. Production integration waits until enough contiguous rewriting passes and the consumer use the same store without an intermediate recursive materialization.

### M1 status (implemented, inactive)

Implemented at `f2f755257` / `a299a3f4c`:

- `lambda/indexed.rs` owns the 8-byte hot node tags, checked `u32` payload/range/index insertion, per-kind cold payload tables, source-ordered side tables, full owned conversion, and compatibility materialization.
- `lambda/lam_pass_collect_indexed.rs` directly traverses indexed nodes for collect and arity analysis. `IndexedLamStats<'arena>` owns no recursive Lambda payload: its option/block/function metadata keeps `NodeId`s and a borrowed lookup context. This keeps the arena alive but is not compile-time arena branding for individual IDs. External arity cache/resolver calls preserve the existing order.
- Differential tests compare the actual tree and indexed collectors' metadata, arity results, retained payloads/recursion flags, and external resolver/cache call order. A separate deterministic traversal model checks indexed visited-edge order, including repeated visits through a deliberately shared child; it does not instrument the existing recursive collector. Storage tests cover every Lambda node family, case/binding ordering, compact handle sizes, and independent parent rewrites over a shared immutable child.
- Production `lam_compile_main`, driver ownership, and JS lowering remain unchanged. There is no performance claim and no Tella timing for this inactive foundation.

### M2: exits segment (next handoff)

First introduce an owning `IndexedLambdaContext` (or equivalent split-field design) for the arena and ID-bearing metadata. M1's `IndexedLamStats<'arena>` immutably borrows the arena, so it cannot coexist with `&mut` appends during exits. M2 must support safe split borrows of storage and metadata without `RefCell`, `unsafe`, whole-store cloning, or retaining payload references across append calls. This context is also the boundary for enforcing or checking the same-store `NodeId` contract more strongly.

Then port exit counting, bounded-variable analysis, substitution, and `simplify_exits`. Keep handler roots as `NodeId`s in substitution tables. The first integration candidate must include enough contiguous work to avoid an unamortized round trip: initial deep flatten (or direct indexed lowering at its output), collect, exits, and the following collect should share one store. Before retaining that candidate, count reachable roots plus superseded nodes/payload bytes and determine whether unchanged-node reuse offsets retained rewrite generations. Keep production unchanged if the candidate still materializes before its consumer.

### M2 status (implemented, inactive)

- `IndexedLambdaContext` is the sole public owner-scoped entrypoint for the canonical root, append-only store, and ID-bearing collect metadata. Raw `NodeId`, `IndexedLambda`, node views, and raw-root pass functions are crate-private. The context exposes no pass API accepting a caller-provided ID, so numerically equal IDs from separate stores cannot be mixed at the public boundary. Private recursive helpers have an explicit same-store contract.
- `IndexedLamStats` no longer borrows its arena. Context methods split immutable store access from mutable metadata access for collect, then append through the owned store during rewrites without `RefCell`, `unsafe`, per-node reference counting, or recursive Lambda snapshots.
- `lam_pass_exits_indexed.rs` ports exit counting, bounded-variable analysis, the shared indexed inline-size helper, variable substitution, and `simplify_exits` to `NodeId`. It preserves body-before-value exit-count order, switch-default double counting, handler-before-body decisions, source-order child traversal, negative-label behavior, and independent freshening for repeated/shared raise edges. Rebuilt apply, primitive, switch, string-switch, conditional, and sequence nodes mirror the OCaml `Lam` smart-constructor paths, including cases where the current recursive Rust helpers still carry reference debt; compatibility materialization remains a raw-constructor boundary.
- The existing standalone Rust `lam_subst.rs` rebuilds raw variants and preserves `ap_transformed_jsx`, even though OCaml `compiler/core/lam_subst.ml:30-66` calls smart constructors and invokes `Lam.apply` with its default `ap_transformed_jsx = false`. Indexed exits does not call that helper: it mirrors the OCaml helper over `NodeId`, always traverses even an empty map, and resets JSX only in the substitution path. Direct `simplify_exits` application rebuilding continues to preserve JSX per `compiler/core/lam_pass_exits.ml:204-207`. Focused tests separate these policies, including nested applications; resolve the production helper debt separately before migrating its other callers.
- Differential tests compare tree and indexed exit counts, bounded-variable decisions, materialized optimized Lambda, identifier-generator frontiers, retained collect payloads/arity/recursion flags, external control families, nested catches, and deliberately shared raises. The test path performs collect -> exits -> collect in one store; production remains unchanged.
- `storage_measurements` reports hot-node allocations, semantic edge visits, unique nodes reachable from the current root, unique nodes reachable from metadata roots, their live union, superseded nodes, and shallow occupied/capacity bytes for every side table. Shallow side-payload bytes are partitioned into current-root live, metadata-retained-only, and unreachable superseded storage. Nested heap allocations inside identifiers, constants, primitives, locations, and strings are explicitly excluded rather than mislabeled as a deep total. OCaml always runs the rewrite even when there is no catch, so repeated passes can append superseded generations; tests quantify this rather than claiming no-op reuse.
- Indexed collect follows `compiler/core/lam_pass_collect.ml:34-37,79-89` and retains a `NodeId` for every bound function, including large, `Never`, async, and directive functions. The current recursive Rust collector's conditional tree-payload retention remains production debt; it is not copied into the cheap indexed metadata representation. Tests verify the full payload and metadata-retained-only byte accounting after the root is rewritten.
- Test builds additionally measure the maximum unique reachability of roots present in the temporary exit-substitution table immediately after each mutation. This diagnostic is compiled out of normal builds and is not a claim about total peak compiler live heap or the recursive traversal stack.

### M3: alias/deep-flatten segment

Port `lam_analysis`, closure/hit/util helpers, beta reduction/substitution, alias simplification, and deep flatten. Metadata stores retained `NodeId`s tied to the owning compilation rather than cloned trees. Preserve resolver calls and identifier allocation order. This removes the first major recursive reconstruction cluster.

### M3 status (implemented, inactive)

- Shared indexed smart constructors, source-ordered child rebuilding, `Lam_util.refine_let`, and unconditional general substitution now live in `lam_indexed_helpers.rs`. Indexed exits uses that shared implementation; substitution still resets `ap_transformed_jsx`, while direct pass rebuilding preserves it.
- `lam_analysis_indexed.rs` ports side-effect analysis, hit-variable queries, and closure usage statistics over borrowed `NodeId`s. Weighted inline size is shared with the indexed collector's existing sparse-aware implementation, including omitted logical record/object fields; it is not treated as an allocation metric.
- `lam_beta_reduce_indexed.rs` ports simple beta reduction, capture-avoiding bounded-variable freshening, argument evaluation order, usage-map decisions, and metadata registration. Complex nullable arguments are bound unchanged and substituted through the fresh variable exactly as in `compiler/core/lam_beta_reduce.ml:47-111`; the current tree Rust identity-wrapper compensation is deliberately not inherited. Every rename uses the caller's pipeline-wide `IdGenerator`. Unused-argument sequencing reproduces native `Hash_ident` bucket/fold/resize order with context-local retained capacity instead of randomized Rust map iteration.
- `lam_pass_remove_alias_indexed.rs` ports metadata-driven field and option simplification, boolean folding, local/direct/cross-module beta reduction, closure/recursion guards, JSX-preserve handling, string-switch scrutinee replacement, and explicit CMJ Lambda import at the external resolver boundary.
- `lam_pass_deep_flatten_indexed.rs` ports nullable-option temporary introduction, beta-residue handling, named immutable tuple elimination, recursive extraction stopping at the first dependency, sequence flattening, and source-ordered group reconstruction in the same append-only store.
- Focused tests exercise exact materialized output for boolean/optional/field/string-switch metadata branches, nullable beta reduction, recursion/export/capture and function-attribute guards, JSX preservation, successful and rejected external inlining, application and primitive locations/flags, caller identifier frontiers, native hash-fold collisions/resizing/repeated calls, sparse inline-size boundaries, test-only substitution-root peak reachability, exact storage partitions, OCaml recursive extraction where the current tree Rust pass still has reference debt, and `collect -> exits -> collect -> alias -> deep_flatten` over one context. The indexed optimizer pipeline remains inactive pending M4-M6. The shared primitive-purity helper refactor in `lam_analysis.rs` is active code and is covered by focused purity tests plus optimized-Lambda, JavaScript, and diagnostic parity gates.

### M4: alpha/lets segment

Port arity-driven alpha conversion and eta expansion, occurrence counting, reference elimination, and let DCE. All replacements append to the same store; smart constructors remain behaviorally identical.

### M4 status (implemented, inactive)

- `lam_pass_alpha_conversion_indexed.rs` queries indexed local and external arity metadata before rewriting applications. Exact, partial, and over-application use the M3 indexed smart constructors. Eta expansion allocates every `param` and `partial_arg` through the caller's pipeline-wide `IdGenerator`. It follows the `fold_right` allocation, source-order binding list, and `fold_left` wrapping in `compiler/core/lam_eta_conversion.ml:37-74`. Other alpha branches preserve native OCaml argument and record-field evaluation boundaries, including right-to-left sibling freshening and resolver queries. Direct application rebuilding preserves JSX; generated inner applications use the reference default `false`.
- `lam_pass_count_indexed.rs` ports body-first let counting, alias inheritance, closure and loop capture boundaries, double-counted incomplete switch defaults, the invalid both-full switch assertion, and inlineable-function beta from `compiler/core/lam_pass_count.ml:59-203`. Occurrence cells use compilation-local indices instead of `Rc<RefCell<_>>`. Count and let simplification share the context's retained native `Hash_ident` beta table capacity because OCaml's `Lam_beta_reduce_util.param_hash` is global across both calls.
- `lam_pass_eliminate_ref_indexed.rs` ports field-zero reads, setfield, offset, closure escape, and recursive traversal from `compiler/core/lam_pass_eliminate_ref.ml:14-102`. It preserves native constructor argument order. A failed rewrite can leave previously appended nodes unreachable; ordinary passes do not add a reachability walk to hide that retention.
- `lam_pass_lets_dce_indexed.rs` ports strict, alias, strict-optional, mutable-reference, string folding, direct beta, side-effect, recursive, and control-flow branches from `compiler/core/lam_pass_lets_dce.ml:14-219`. It preserves the reference's explicit `let` sequencing, native constructor argument order, and left-to-right `let ... and ...` switch group. Substitution and string tables are lookup-only, so Rust map iteration cannot affect output. Beta folding reuses the accepted native bucket traversal implementation.
- Tests cover local and external arity; exact, partial, and over-application; JSX, async attributes, application locations, identifier frontiers and flags; effectful eta ID-to-RHS mapping; apply under/equal/over, list-map, letrec, switch-record, and shared sibling order; repeated alpha calls; nested and shared occurrence edges; all switch-default fullness cases; mutable-reference success and escape; alias and strict DCE; string folding; inline rejection; recursive and control-flow traversal; retained beta hash capacity; and `collect -> exits -> collect -> alias -> deep_flatten -> alpha -> lets` in one store with one generator. The combined test asserts the materialized result and concrete allocation, edge, unique-node, occupied/capacity-byte, metadata-only, and unreachable shallow-storage partitions. Nested heap bytes remain excluded.

A temporary linked OCaml core oracle confirmed native sequence freshening. From frontier 1002, the second under-application received `param/1003` and `partial_arg/1004`, then the first received `param/1005` and `partial_arg/1006`. The checked-in test uses relative stamps and does not depend on the oracle process's starting frontier.

Production `lam_compile_main`, driver ownership, and JavaScript lowering still use recursive `Lambda`. M4 has no wall-time claim. M5 and M6 remain required before activation or timing.

### M5: export and in-process ownership

Port export coercion, hoisted aliases, required-module collection, intermediate printers, and the `InProcessPreJsCompileResult` boundary. At this checkpoint no normal optimizer step converts back to recursive Lambda.

### M5 status (implemented, inactive)

- `lam_compile_main_indexed.rs` owns the candidate pre-JS result. One `IndexedLambdaContext` runs the complete M1-M4 optimizer sequence and every reference recollection in `compiler/core/lam_compile_main.ml:291-337`, then ports coercion/grouping, group DCE, hoisted aliases, pre-optimizer required-module capture, effect classification, and CMJ value selection. No normal candidate pass materializes recursive Lambda.
- Coercion keeps the ordered export list, membership set, and export map as separate values, matching `compiler/core/lam_coercion.ml:82-172`. Its `fold_right2` callback allocates renamed exports right-to-left while consing source-order lists. Only the same-name, different-stamp variable branch changes the export set. The final gate accepts any `Pmakeblock`, using the export identifiers supplied at the producer boundary rather than inferring them again from the block tag.
- Group DCE follows `compiler/core/lam_dce.ml:26-73`: initial identifiers are visited head-first, free-variable dependencies follow `Set_ident` stamp/name/flags order, global identifiers are skipped by flag rather than stamp spelling, recursive groups retain only visited bindings, and missing local bindings fail in deterministic reference order.
- Hoisted aliases resolve through indexed group roots and module fields without tree conversion. Alias identifiers are allocated in source order; generated groups and exports retain the native reverse-source fold result, while CMJ hoisted metadata remains in source order. Every misplaced-attribute gate creates the established `Warning::MisplacedAttribute`, applies `WarningConfig`, and delivers active warnings through a lightweight sink immediately in source order. Warning-as-error remains pending on the owning result for M6's post-JS, pre-CMJ fatal gate. Name collisions retain the function target location or fallback attribute location with the reference message.
- CMJ selection runs arity and persistent-Lambda decisions together, preserving both combined omit gates from `compiler/core/lam_stats_export.ml:32-105`. Submodule arity lookup carries the external resolver and its static/dynamic caches in source order. Null, undefined, and boolean payloads survive without cross-module inlining; constructor payloads and closed always-inline/functor functions obey the reference flag. Selected recursive Lambda is materialized only by the explicit CMJ compatibility method.
- `sexp_lambda.rs` directly prints indexed nodes with the same structure as the recursive Lambda sexp printer. A debug-only diagnostics observer materializes through the established recursive printer boundary and receives every `d` pass label plus all `Single`, `Recursive`, and `Nop` groups. This preserves existing drawlambda, diagnostics, and playground formatting instead of inventing another external format; optimizer behavior is identical when the observer is absent.
- The additive Raw-Lambda converter constructor borrows one caller-owned `Arc<IdGenerator>`. It seals output in `IndexedRawLambda`, which can only come from that shared-generator converter; the indexed lowering entrypoint consumes this token rather than accepting an unrelated Raw tree and generator. The same stream passes through real primitive-wrapper conversion, lowering, all optimizer passes, coercion and the owning pre-JS result. Legacy production converter/lowering constructors keep stack-owned generators and production driver/rewatch continue to use recursive Lambda until M6.
- Coercion consumes the optional single-tree optimizer root, including when grouping produces no roots. Group/export roots then become the sole private owner-scoped program roots. `materialize` and the single-root indexed printer reject post-group use instead of treating the first RHS as a whole program. Storage measurements report optimizer-root, grouped-backend, identifier-metadata, and unreachable storage separately.

Focused tests cover exact list/set/map coercion outcomes, right-to-left identifier allocation, generic makeblock coercion, deterministic full-flag `Set_ident` DCE failure and retention order, dynamic/static required modules, dead pre-optimizer module roots, hoisted warning configuration/resolution/order/collision, CMJ omit and retention gates, external arity query/cache order, direct indexed printing, exact identifier flags, grouped-root storage partitions, one generator through Raw conversion/lowering/optimization/later-consumer allocation, and owner moves. Production remains inactive, so this milestone makes no output-parity, Tella, or speed claim.

### M6: JS consumer

Port `LambdaCompiler` and helper APIs to borrowed indexed access. Preserve recursive-binding dependency order, catch/switch label state, loop state, temporary identifier allocation, CMJ external lookup behavior, and source locations. Remove the normal production compatibility materialization. Recursive Lambda remains only at explicit CMJ/debug compatibility boundaries until those formats are separately migrated.

### M6 status (unfinished continuation)

Checkpoints `1aafdbd3a` and `1dc615ca5` implement the owner-private mutable CMJ beta boundary, not the full consumer. `LambdaCompiler` takes a shallow application snapshot, releases the store borrow, queries the existing CMJ Lambda cache, checks the recursive function header, and only then imports an eligible function into the same store. Indexed beta receives the original argument `NodeId`s, context-retained metadata and native beta hash capacity, and the compiler's shared generator. Rejected candidates proceed to the arity query without importing the function.

Focused tests cover same-store argument reuse, shared-generator allocation, successful beta without an arity query, and rejected-function arity fallback. One test materializes the reduced result at a test-only compatibility boundary before invoking the old recursive compiler. This does not prove direct indexed JS consumption and is not M6 acceptance. The common consumer must call `prepare_indexed_external_field_apply`, recursively compile `Reduced(NodeId)` without materialization, and complete every Lambda family before activation.

### M6 shared JS helper checkpoint (not a consumer completion)

The recursive primitive caller now delegates final JS emission to `compile_primitive_js`, which accepts only JS expressions, the already-ordered prelude and primitive metadata. Its hoisted external-field descriptor lookup accepts borrowed recursive/indexed inputs and still runs before argument compilation (`compiler/core/lam_compile.ml:284-302`, `1734-1757`). Eta runtime aliases and identity-module returns also use common borrowed input readers with thin recursive production wrappers. These readers never materialize indexed subtrees. They do not own mutable recursion.

Three direct JS helper tests cover indexed identity-module reads with explicit identifier name/stamp/all-flags and dynamic-import checks, indexed eta guards, and primitive JS emission retaining the prelude and the actual shared dynamic-import generator. The initial inline identity fixture was folded by the existing producer smart constructor before reaching the tested helper; the fixture now constructs that consumer shape explicitly. This is helper coverage, not the required sealed producer-to-JS test.

Validation under the heavy-test lock:
- Debug default compiler tests: 1315 library passed / 108 ignored, 16 comptime passed / 23 ignored, 9 doctests passed / 7 ignored; binaries included.
- Release compiler and rewatch builds passed. Release rewatch tests: 150 passed.
- Release parity: typedtree 610/610, raw Lambda 610/610, optimized Lambda 610/610, focused JS 344/344, JS snapshots 610/610, diagnostics 1431/1431.
- **Release default compiler tests are not green.** `parser::benchmark::tests::benchmark_index` failed its 1.20x threshold at 1.26x, then 1.23x on one full-suite retry. Both attempts had 1314 library tests passing and 108 ignored; the failure stops later targets. No threshold or test suppression was changed. Logs: `/tmp/m6-consumer-release-tests.log` and `/tmp/m6-consumer-release-tests-retry.log`.

Mutable `NodeId` recursion, actual application-site CMJ `Reduced` consumption, all control-flow families and the sealed M5-to-JS boundary remain unimplemented. These results validate the active helper refactor only. There is no M6 acceptance, activation, Tella run or speed claim.

### M6 mutable application owner (continuing)

`lam_compile_indexed.rs` now holds the mutable compiler/context pair and lowers indexed applications directly. Closed operations take explicit child continuations receiving that same owner and a `NodeId`. Actual application lowering invokes the retained CMJ preparation boundary and immediately dispatches `Reduced(NodeId)` through that continuation. Normal calls and rejected CMJ calls compile arguments right-to-left while emitting operands/preludes in source order (`compiler/core/lam_compile.ml:358-389`, `1647-1656`). Nested `App_na` flattening uses indexed `append_rebuilt`, retaining original argument handles, application metadata and the returned smart-constructor root.

The same owner also lowers primitive operands left-to-right through the shared JS emitter (`Ext_list.split_map`, `compiler/ext/ext_list.ml:643-670`), handles short-circuit and dynamic-import branches, and has a NeedValue try/Assign continuation boundary. Short-circuit scalar JS emission is shared with the legacy caller. No indexed subtree is materialized.

Focused check and four indexed-owner tests pass. Tests now compile an actual CMJ `Reduced` original argument and an imported beta-reduced try node to JS through the same indexed continuation, checking physical argument ID reuse, source locations, beta/JS stamps and explicit flags, generator Arc identity, rejection without import, arity-query-before-argument timing, and native call visit order. The fixture continuation is intentionally closed over the moved families; a full general dispatcher, remaining control-flow modes, grouped M5 entrypoint and full acceptance validation are still pending. This is substantive application-path progress, not M6 completion. No release benchmark retry or full release gate cycle was run for this checkpoint.

## Validation at every checkpoint

- Unit tests for semantic output, source-order traversal, shared-child isolation, and exact rewrite decisions.
- Debug and release compiler builds under the shared heavy-work lock.
- Focused pass tests with 5-10 second compiler/test timeouts.
- Before production retention: release compiler and rewatch tests; full typedtree, raw Lambda, optimized Lambda, JavaScript, diagnostics, and focused JS parity; pinned Tella full clean build; exact generated-JS manifest comparison excluding `node_modules`; preservation of the pre-existing generated Tella modifications.
- Instrumented allocation and visited-node counters, if added, count actual store insertion and traversal events and are removed before authoritative timing. Track reachable live nodes, superseded nodes retained by metadata/substitutions, and side-payload bytes before choosing an append/reuse/reclamation policy.
- Performance measurement only after correctness, with separately saved instrumentation-free binaries and fixed-count alternating one-worker/twelve-worker clean builds. Conversion overhead is reported rather than hidden.

## Non-goals and rejected shortcuts

- No `GroupArena` wrapper around existing vectors.
- No tree-to-arena-to-tree conversion for every pass.
- No reuse-only claim based on moving existing `Box`/`Vec` allocations.
- No folded-switch move experiment, RawLambda action DAG, scheduler tuning, signature cache, or typechecker identity/force-order change.
- No use of `lam_analysis::size` as a node/allocation counter.
- No claim that fewer allocations or instructions guarantees a wall-time gain.
