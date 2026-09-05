# Indexed optimized Lambda migration

## Goal

Replace the recursive owned `lambda::Lambda` tree with compilation-owned indexed storage that remains canonical across optimized-Lambda passes and is consumed directly by JS lowering. This is a storage and ownership migration, not a new optimizer. The OCaml pass order, branch order, source-order child lists, smart-constructor behavior, identifier allocation, metadata updates, diagnostics, CMJ boundaries, dumps, source maps, and JavaScript output remain unchanged.

The current Rust pipeline repeatedly consumes and rebuilds `Box<Lambda>` and `Vec<Lambda>` trees. The target representation allocates each optimized-Lambda node once in a module-local store and addresses it with a `u32` index. Rewrites append replacement nodes and return a new root in the same store. Old nodes remain valid for metadata and substitutions that intentionally retain an earlier expression. No per-node `Rc`/`Arc`, `unsafe`, structural deduplication, placeholder nodes, or output-mode behavior is permitted.

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
- A root `NodeId` and explicit borrowed APIs (`node`, `children`, `bindings`, switch-case access). Callers do not retain references while appending nodes.

Children are inserted before parents during the initial conversion, giving postorder locality without changing semantic traversal. Passes must traverse children in the exact order of their OCaml counterparts rather than relying on physical node order. Sharing is explicit: two parent payloads may name the same `NodeId`. Rewrites do not mutate a shared child in place; they return replacement roots, so independent occurrences remain independently rewritable unless a pass deliberately reuses a result.

The compatibility materializer uses the root-directed semantic traversal, not arena order or structural content. Shared indexed nodes become equivalent recursive values at the old boundary because recursive `Lambda` has no observable node identity.

## Migration checkpoints

### M1: storage plus the first real pass

- Add complete lossless owned `Lambda -> IndexedLambda` conversion and compatibility `NodeId -> Lambda` materialization.
- Add semantic round-trip tests covering every node family and preserving switch/case/binding order.
- Add tests that deliberately share one child index between two parents, rewrite one parent path by appending nodes, and prove the other parent and shared child remain unchanged. Assert semantic materialized results, not pointer identity.
- Port `Lam_pass_collect.collect_info` and its arity queries to borrowed indexed access.
- In the production pipeline, convert once after the initial existing deep-flatten, run the first collect over the indexed representation, and materialize once at the next still-recursive pass boundary.

M1 is a buildable regression-tested migration checkpoint. It is not expected to improve wall time because the temporary compatibility materialization remains. No performance claim is valid until production retains indexed storage across multiple rewriting passes and into JS lowering.

### M2: exits segment

Port exit counting, bounded-variable analysis, substitution, and `simplify_exits`. Keep handler roots as `NodeId`s in substitution tables. The same indexed store then survives collect -> exits -> collect without materialization.

### M3: alias/deep-flatten segment

Port `lam_analysis`, closure/hit/util helpers, beta reduction/substitution, alias simplification, and deep flatten. Metadata stores retained `NodeId`s tied to the owning compilation rather than cloned trees. Preserve resolver calls and identifier allocation order. This removes the first major recursive reconstruction cluster.

### M4: alpha/lets segment

Port arity-driven alpha conversion and eta expansion, occurrence counting, reference elimination, and let DCE. All replacements append to the same store; smart constructors remain behaviorally identical.

### M5: export and in-process ownership

Port export coercion, hoisted aliases, required-module collection, intermediate printers, and the `InProcessPreJsCompileResult` boundary. At this checkpoint no normal optimizer step converts back to recursive Lambda.

### M6: JS consumer

Port `LambdaCompiler` and helper APIs to borrowed indexed access. Preserve recursive-binding dependency order, catch/switch label state, loop state, temporary identifier allocation, CMJ external lookup behavior, and source locations. Remove the normal production compatibility materialization. Recursive Lambda remains only at explicit CMJ/debug compatibility boundaries until those formats are separately migrated.

## Validation at every checkpoint

- Unit tests for semantic output, source-order traversal, shared-child isolation, and exact rewrite decisions.
- Debug and release compiler builds under the shared heavy-work lock.
- Focused pass tests with 5-10 second compiler/test timeouts.
- Before production retention: release compiler and rewatch tests; full typedtree, raw Lambda, optimized Lambda, JavaScript, diagnostics, and focused JS parity; pinned Tella full clean build; exact generated-JS manifest comparison excluding `node_modules`; preservation of the pre-existing generated Tella modifications.
- Instrumented allocation and visited-node counters, if added, count actual store insertion and traversal events and are removed before authoritative timing.
- Performance measurement only after correctness, with separately saved instrumentation-free binaries and fixed-count alternating one-worker/twelve-worker clean builds. Conversion overhead is reported rather than hidden.

## Non-goals and rejected shortcuts

- No `GroupArena` wrapper around existing vectors.
- No tree-to-arena-to-tree conversion for every pass.
- No reuse-only claim based on moving existing `Box`/`Vec` allocations.
- No folded-switch move experiment, RawLambda action DAG, scheduler tuning, signature cache, or typechecker identity/force-order change.
- No use of `lam_analysis::size` as a node/allocation counter.
- No claim that fewer allocations or instructions guarantees a wall-time gain.
