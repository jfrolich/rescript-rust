# Env/component ownership experiment

## Selected question

Can one compilation-owned component representation eliminate repeated lookup transport, declaration copying and signature reconstruction while preserving native Env behavior?

This is the first larger hypothesis selected from the architecture round, not an accepted optimization. The fresh profiles place substantial work in Env across typechecking and Raw. They do not separate required graph work from removable ownership overhead. The isolated copy-function diagnostic did not establish a large map-only target. Historical mutation journaling and contiguous internalization have prior small or flat full-build results.

## First checkpoint: prove the boundary

Before changing production code, document the current and proposed owners, identities, lifetimes, mutation points and query/force state transitions. Attribute complete component construction and descriptor-query lifetimes, including setup and destruction outside the inner lookup, repeated same-identity queries, copied declaration/override state and retained roots. Use a bounded separately preregistered archive-only probe if existing evidence cannot answer this. Report the actual cost of `Layout__Types` through this boundary, without treating its typecheck delta as proof of cause.

The diagnostic must not count shared Arc-backed registry maps as deep copies, equate outer calls with unique objects, add overlapping nested durations or infer DRAM/allocator bytes from logical payload. Source review must identify which copies preserve independent mutable graph identities. Parent reviews this checkpoint before implementation activation. If no material removable work is established, close this hypothesis with evidence; do not switch tasks or manufacture a reason to keep a large patch.

## Intended implementation scope

- Own forced component descriptors and lookup state within the compilation context. Build final required substituted component state once at the existing native force boundary.
- Give repeated queries stable handles or short borrows into that state where legal. Release guards before forcing, mutation, recursion or calls that can grow the relevant owner.
- Replace the old redundant transport/reconstruction path when the new path is activated. Do not retain a compatibility facade that secretly repeats the same copies.
- Preserve the raw/canonical signature views that GenType, CMJ and diagnostics actually require. Avoid keeping extra whole graphs alive just to simplify ownership.
- Keep existing shared registry storage and intentional sparse large-record/label representations. A compact index can avoid repeated materialization only if every native-visible allocation, identity and force remains at the correct boundary.

Starting Rust paths include `ctype.rs::resolve_type_item_through_env`, `typecore.rs::lookup_type_in_resolved_path` and signature qualification, `env_lazy.rs::StoredModuleComponents`/`QualifiedModuleComponents`, and `cmi/persistent_env.rs`. These are investigation boundaries, not permission to rewrite unrelated parser, backend or type algorithms.

## Native contract

Read the checked-in code before implementation:

- `compiler/ml/env.ml:781-813`, `865-914`, `1091-1100`: descriptor queries, module forcing, normalization and qualified value lookup are distinct APIs.
- `compiler/ml/env.ml:1415-1585`: alias scraping, prefix substitution and the whole-component construction pass. Iterate in native order, including runtime positions and the evolving captured Env.
- `compiler/ml/subst.ml:130-165`, `303-400`: copy identities, recursive stubs and per-declaration cleanup.
- `compiler/ml/mtype.ml`: alias strengthening and its effect on type versus value descriptions.
- `compiler/ml/datarepr.ml`: constructor/label graph sharing, allocation and metadata. Indexing is not permission to delay visible work or eagerly clone every large JSX label payload.

First parent-component force remains whole-component. Module-declaration substitution thunks, child-component thunks and modtype substitution/cleanup remain distinct. Child thunks capture the Env at their exact signature-item position. Probe queries must not accidentally enter a stronger force path. Preserve identifier allocation, type-node physical identity, row/abbreviation independence, full metadata and all public outputs. Native tuple/constructor syntax is not proof of left-to-right evaluation.

No per-declaration laziness, signature-content/spelling heuristics, force suppression, output-mode semantics, structural type deduplication, serializer normalization, new unsafe code, new per-node Rc/Arc or global mutable instrumentation. Existing context-local interior-mutability mechanisms must model actual ownership, not bypass borrow conflicts.

## Review and acceptance

One fresh owner handles this scope. Preregister diagnostics and the later fixed D/candidate release cohort before observing their outcomes. Keep serial and parallel results separate and compare with the historical optimized control when making a new-best claim. Do not add samples to resolve uncertainty.

Add direct native-contract tests for captured Env, alias shadowing, repeated lookup identity, recursive modules/types, primitive runtime positions, constructor/label duplicate ordering, independent row/abbreviation mutation, separate module/modtype cleanup, lazy child force order and large sparse records. Exercise actual production callers, not only a modeled helper. Full default and release compiler/rewatch tests, release builds, typedtree/raw/optimized/JS/error parity and exact new fixtures precede retention. Use successful-test output for the planned parser benchmark run; no retry-until-green or threshold changes.

Both inherited exact-JS blockers remain visible. Internal passes and unchanged Tella output do not waive them or authorize production acceptance. Preserve the fixed Tella pin and eighteen original modifications, complete manifests, immutable controls, raw failed attempts and durable evidence. Restore only this candidate if rejected, never sibling work. No push, PR operation or merge by the owner. Parent maintains the sole draft PR.
