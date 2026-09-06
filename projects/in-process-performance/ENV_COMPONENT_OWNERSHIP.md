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

Both inherited exact-JS blockers remain visible. Internal passes and unchanged Tella output do not waive them or authorize production acceptance. Preserve the fixed Tella pin and eighteen original modifications, complete manifests, immutable controls, raw failed attempts and durable evidence. Restore only this candidate if rejected, never sibling work. No push, PR operation or merge by the owner. PR19 has merged. The user has asked to continue on the default branch, `ocaml-to-rust-rewrite`; parent handles pushes there.

## Boundary review, first source checkpoint

Owner `bks-9b72b0de-396c-7d5f-a662-e90f9799f817`, examined clean `bb288cbcd53cf27372137617bd28c60fac6ff4b8`. Compiler and rewatch source have no diff from D. Ordinary release hashes still match D (`a5ed9a622e3b787a8dae0cb5228a5eb5717849314d0af40c05f9689c6a6788af` bsc, `5fe8158df5d3201d4cf07fd962cf61b22edf63874b03bfd5328e1fe16f47c3c4` rescript). No production activation, diagnostic build, Tella mutation or new timing occurred during this source checkpoint.

This is **not yet the complete attribution checkpoint**. The source establishes removable transport operations but not their material cost. Existing samples cannot fill the missing same-identity and complete-lifetime accounting. Production approval should wait for that accounting. The diagnostic plan below is registered before any new diagnostic outcomes.

### Current owners and lifetime boundaries

| Owner / identity | Creation and query | Mutation and release |
|---|---|---|
| `PersistentEnv` wrapper in `TypecoreContext`, with another wrapper in `TypeContext` | `driver.rs:15004-15021` creates from the registry and loads implicit opens. `typecore.rs:1326-1327` clones into `TypeContext`. Ctype's `in_process_module_resolution_env` clones that wrapper before lookup, even if the resolved-type cache will hit. Raw receives another clone at `driver.rs:15222-15223`. | Local alias preparation, overrides and hidden-module membership belong to each wrapper. The loaded-structure cache, error and CRC state are shared. A temporary query wrapper drops on every exit from `resolve_type_item_through_env`, including early return. The context wrapper is not the sole owner of the shared persistent cache. `clear_persistent_env_for_park` exists, but a source search found no call; its comment is not evidence that normal teardown invokes it. |
| `Env` snapshots, identified by `Env::id()` | `Env::clone` assigns a new id; `clone_preserve_id` keeps it. `IdTbl` and `TycompTbl` use persistent maps and shared opened layers, not whole copied binding tables. `add_module_with_component_context` captures the seed before inserting the module and bumping the id (`env.rs:1251-1274`). | Binding changes produce new persistent-map state. Snapshot clones still copy `functor_args` and GADT-instance vectors and reset derived alias caches. Captured seeds keep previous binding roots alive. Ordinary Env cloning must not be counted as deep declaration copying. |
| `StoredModuleComponents` | Each binding owns a shared stored thunk. The thunk owns boxed seed Env, access path, owned module declaration, optional parent signature Arc and separate OnceCells for components and functor state (`env_lazy.rs:1686-1700`). | `with_components` reuses a populated cell; otherwise it constructs a temporary image. Real APIs publish the image, probes do not. An unpublished image is destroyed after the callback. The seed/module/parent fields remain present after a successful force; OnceCell publication does not release them. Actual last-owner timing is unmeasured. |
| `QualifiedModuleComponents` | A view shares access path, signature and `StructureComponentTables` through existing Arcs (`env_lazy.rs:351-385`). Local stored thunks and the context's qualified-component cache can retain images. | Name tables and qualified declarations populate through existing interior mutability. Cloning the view does not copy its signature graph or tables. Child thunks can retain the parent signature and earlier Env roots. The context cache's callback borrows its map until the callback returns (`context.rs:947-962`); a new owner cannot carry that guard into insertion or recursive forcing. |
| Resolved type transport | `lookup_type_in_resolved_path_with_cache_mode` first checks `(env.id(), parent path, name)`. Misses clone the selected declaration container into an Arc; hits clone that Arc. `resolve_type_item_through_env` then clones the contained declaration into an owned return value (`ctype.rs:2381-2394`). | Its vectors, record/variant declaration payloads, attributes and inlined-type containers are owned copies. `TypeExprRef` members still address the same type nodes. Optional alias strengthening performs another wrapper clone and can allocate a new manifest. Those necessary manifest mutations are distinct from unmodified transport. |

`PersistentEnv`'s derived clone (`cmi/persistent_env.rs:592-664`) shares its cache, load paths, renamed signatures, registry maps, errors and CRC table. Its owned clone candidates are `compiling_module`, the three override maps, `hidden_modules`, `prepared_cached_alias_rewrites`, and `AliasPrefixRewrites.local`. Portable override values themselves are Arcs; cloning their map does not internalize the portable graph. String lengths, map elements and declaration vector capacities are logical payload measures, not allocator bytes or DRAM traffic.

There are more retained declaration roots than the final component signature alone. Local construction registers declarations by name and stamp, captures working Env snapshots, and passes the qualified parent signature into child thunks (`env_lazy.rs:1577-1675`). Context resolved-type and qualified-module caches retain additional descriptors. Their roots may share type nodes. Counting each root as a separate reachable graph would overstate retained storage.

### Query and construction transitions

1. Ctype's descriptor query creates a resolution wrapper before entering the resolved-type cache. A cache hit therefore avoids graph construction but not that wrapper's creation/drop or the owned result clone. The optional alias-target query creates another wrapper. The caller may consume only a few declaration fields, but that is not permission to revive the rejected five-projection experiment.
2. `ComponentLookupApi` explicitly separates module, descriptor, type, modtype, open and probe calls (`typecore.rs:31291-31343`). Only `ProbeModuleDescr` disables publication and alias-signature forcing. A probe can reuse already-published state; its cold miss can build temporary state. Do not silently memoize those misses or promote their API.
3. Component lookup tries a local stored thunk, then the context component cache, then parent/functor/persistent/general construction (`typecore.rs:31365-31419`). A direct persistent type query has an additional raw-signature scan path (`31595-31650`). This must be included in the diagnostic; measuring only `build_local_module_components` misses it.
4. Local construction resolves a raw signature, copies/qualifies it, applies parent substitution, walks raw/qualified items to build captured child Envs, then constructs tables (`env_lazy.rs:1378-1678`). The persistent alias fast path instead shares `ps_sig` and creates a view. Required alias scraping can force a module declaration or persistent renamed signature. These paths cannot be collapsed merely because their printed access paths match.
5. `lookup_value_for_access` deep-copies and substitutes a value on its first name lookup, then caches it. Constructor and label first-name queries scan the signature and allocate selected buckets (`env_lazy.rs:846-951`). Module declaration forcing has its own local/context/registered-alias reuse path (`1014` onward), separate from child component construction. A new component image must replace these redundant construction routes, not wrap them.

### Native obligations that constrain the proposed change

Line references below describe checked-in code, rather than assuming older comments are exact. Generic qualified value lookup is at `env.ml:1062-1073`; `lookup_value` selects it at `1101`.

- `env.ml:781-813` reads descriptor/type tables. `865-914` separately forces module declarations and normalizes paths. A descriptor lookup may force a parent table and its alias scrape, but must not force the selected child module declaration merely to access its component thunk.
- `components_of_module_maker` performs the whole signature pass. `prefix_idents` computes complete substitution and runtime paths first. Each type invokes `Subst.type_declaration`, row naming, constructor construction and label construction before storing the original declaration into the evolving Env. Each module creates two distinct thunks before adding the original module to that Env. Modtype substitution runs at parent construction, not at the child module-declaration boundary.
- `subst.ml:245-247`, `273-300`, `303-324` clean up per type-expression/declaration/extension operation. `130-165` records temporary physical substitutions and recursive stubs. Rust's `copy_lookup_signature_for_subst` currently creates one map and passes it across signature items (`typecore.rs:25748-25846`, `26011-26023`). A final-image design must not copy that shape blindly into a single native substitution scope. This is a source discrepancy requiring explicit sharing tests, not a measured optimization opportunity by itself.
- `mtype.ml:41-102` leaves values unchanged while strengthening appropriate type manifests and module declarations. A query return that only needs to inspect a cached type must not repeat strengthening; moving strengthening to construction requires proof that the captured alias target and Env match.
- `datarepr.ml:137-188` allocates a shared ordinary constructor result before traversal. The explicit recursive call processes the tail before current constructor payload construction. `254-276` creates one `lbl_all` array and shared label result for the record. Current Rust per-name builders allocate selected results independently (`env_lazy.rs:34-192`). A name-to-index table alone cannot establish native graph sharing. The replacement must allocate native-visible graphs once, preserve duplicate bucket order, and represent large label arrays without duplicating hundreds of payloads per index entry.

### Proposed ownership shape, conditional on attribution

Use one compilation-owned component store with owner-paired component/entry handles. Each entry represents one native thunk, with its captured Env, substitution, raw module input and explicit unforced/forced result. Separate entries represent module-declaration thunks and child-component thunks; modtype substitution retains its own cleanup boundary. Existing shared registry inputs stay shared. Do not introduce another global component cache.

On first real parent force, scrape the alias at the existing API boundary, compute complete prefix substitution, then build final value/type/constructor/label/modtype tables in native order. Module entries retain unforced declaration and child thunk handles. A repeated query obtains a short borrow or a small result containing an owner-paired handle, not a cloned `PersistentEnv` and declaration container. Mutation paths request an explicit owned/native copy only where semantics require independent state. This requires threading the resolution owner through current Ctype/Env callers; borrowing the entire current RefCell across recursion is not a solution.

Export/GenType/CMJ/raw/canonical consumers still need signature views. Before dropping raw inputs after force, inventory every consumer and retained root. Prefer projecting existing entries where valid, but do not recreate full signatures at every lookup or retain a second whole graph merely to simplify the API. Exact release points and recursive forcing/error behavior remain design work; this paragraph is not an approved implementation specification.

### Registered bounded diagnostic, not acceptance timing

Register one archive-only diagnostic experiment on D, with exactly four complete builds in order D w1, probe w1, D w12, probe w12. No A repeat, hyperfine screening, acceptance cohort or profile extension. The adjacent control estimates single-run instrumentation overhead only. Use the existing immutable D executables and a separately built archived D probe with explicit TypeContext-owned accounting. No mutable process-global/thread-local counters or instrumentation calls into stronger lookup APIs.

Instrumentation must cover these observations before running:

- Full resolution scope from before wrapper clone to after its destruction, with a separate child timer for wrapper clone/drop and owned declaration transport. Exclude caller-owned returned declaration lifetime from the scope, then record its known ownership destination separately rather than pretending the resolver drops it.
- Outermost query/construction elapsed union and separately labeled nested scopes. Record wrapper clone/drop, raw resolve, qualification, final table assembly, first-name value/constructor/label work and temporary-image destruction. Do not sum inclusive timers. Report timer overhead through D/probe process metrics rather than subtracting an assumed per-call cost.
- Requests keyed by context identity, Env id, structural Path identity, name and API; resolved component identities keyed by a context-local monotonic token attached to the archived component object. Never use printed path equality or reusable raw addresses as proof of same identity. Separate same-key requests, resolved-cache hits, same-component queries, cold builds, unpublished probe builds and alias/module-declaration forces.
- At actual wrapper clone sites, count owned override/hidden/prepared-alias entries and logical string/container payload. Count shared map handles separately. At actual declaration clone sites, count owned vector/record/variant/inlined/attribute payload and copied handles separately from newly allocated type nodes. No fresh blanket type-descriptor census.
- Record construction input/output node-allocation deltas, raw/qualified signature roots and module/child thunk retention at creation, force, phase exit and context teardown. Assign stable context-local signature/thunk tokens for root accounting without keeping extra owning Arcs in the probe. Shared roots are not unique graphs, endpoint capacities are not peak live heap, and context teardown coverage must be implemented rather than inferred from the unused park helper.
- Attribute contexts by source module at setup, including `Layout__Types`, and report that module's query/construction union alongside whole typecheck and Raw phase elapsed. If it is absent, the diagnostic is incomplete. The historical 324.070ms typecheck gap is not an Env budget.

Run only after probe source review, counter invariants and short fixture checks. Preserve archive originals, patch, separately built executable, raw per-context records, all failures and SHA inventories in organization-controlled durable storage. Build and run through the heavy lock. Notify parent to stop edits before resolved source/runtime/dependency inventory. Apply the existing exact eleven compiler-info plus `.sourcedirs` writer policy, pin/backup/restore all eighteen original Tella files, and require exit 0, 3248 modules and the fixed 5048-JS digest for every full build. No retry to replace failed observations. Keep normal D source and binaries unchanged.

### Tests required before production approval

Direct production-call fixtures must cover repeated returned type-node identity, same spelling with different local Env bindings, captured Env before/after alias shadowing, recursive types/modules, primitive runtime positions, duplicate constructor/label bucket order, shared ordinary constructor result and label-array identity, independent row/abbreviation mutation across declarations, separate module/modtype cleanup, cold/warm/probe/child force traces and sparse large-record access. Export/GenType/raw/canonical tests must show the same required views without hidden whole-signature reconstruction. Syntax, typedtree, raw, optimized, exact standalone nonempty JS, diagnostics and external gates remain required.

Decision at this checkpoint: request parent review of the source boundary and diagnostic plan, **not production activation**. Material removable cost, complete teardown accounting and actual `Layout__Types` attribution remain unknown. The hypothesis is neither accepted nor falsified. No performance claim or source-correctness gate has been earned by this source-only review.


## Parent review: diagnostic continuation approved

Parent reviewed the source checkpoint against Ctype's wrapper/result clones, the persistent Env fields, resolved-type cache and persistent-signature fallback, stored thunk publication, native constructor/label sharing and per-declaration substitution cleanup. The boundary and fixed four-build archive-only diagnostic are approved. Production implementation remains unapproved pending the measured checkpoint.

The user requested continuing on the default branch after PR19 merged. Work now uses `/Users/jake/checkouts/rescript-rust` on `ocaml-to-rust-rewrite`, initially `18d441b29405f81f2357cac5594c52579957e7bf`. Compiler/rewatch source there matches D exactly. The old experimental worktree is preserved. Its release binaries were verified previously; the new checkout is not claimed built. Record the new root, actual runtime and every resolved dependency symlink before the diagnostic. Do not silently inherit the old root's input inventory.

Before full runs, verify that diagnostic identity tokens distinguish a cloned stored thunk with independent cells from a cloned component view sharing its tables. Tokens must not retain graphs. A TypeContext Drop hook runs before automatic field destruction; it cannot alone measure complete teardown or last-owner release. Use an actual enclosing lifetime boundary where available, and report any remaining lifetime gaps explicitly. Keep caller-owned declaration lifetime separate from resolver-local wrapper destruction. Preserve the registered counts and all failed attempts; no diagnostic expansion or extra runs to improve a result.

Owner `bks-9b72b0de-396c-7d5f-a662-e90f9799f817` is reassigned sole compiler/shared-worktree/heavy ownership for this continuation, subject to acknowledging the new checkout. Prepare and check the archived probe, run the registered diagnostic, restore inputs, and return the measured checkpoint. Parent will review the probe source before the four full builds, without requiring another ownership release or idle wait.

## Archived probe prepared for parent review

Continuation uses clean main base `b6fbd703b9e93413f9a469ece8aa0f9054937e90`. Durable probe/evidence root is `/Users/jake/.opensession/artifacts/rescript-performance-20260905/env-ownership`. Normal compiler/rewatch source remains D; no full diagnostic build has run. Review patch `probe-review.patch` SHA256 is `558b2c0308887853b5b1dc451e3f1d580843f88a220e21ba4642f5bd77461b82`; linked probe rescript is `e3b8332d204ec0a9559897288906de21f5b4ca9d536e1eb02740ccb2dd774387`. The archive-only scripts preserve original, intermediate and final patch/source inventories.

Release rewatch and standalone bsc builds passed. Filtered release library tests passed 7/7: six new diagnostic identity/order tests and one existing indexed test whose name matched `probe`. Standalone D/probe comparisons pass exact JS, typedtree and raw Lambda; fresh JS stdout is 671 bytes for each compiler. The small in-process project passes D/probe byte-identical JS and counter invariants, with an actual `Layout__Types` module record and module phase timings. This fixture proves instrumentation binding, not the actual Tella module's attribution; that remains for the four registered builds.

Preserved preparation failures are the initial module-visibility patch assertion, one missing Rust lifetime annotation, a fixture missing `type rec`, and the new checkout's missing runtime source mirror directory. No full attempt was replaced. Runtime setup copied the exact 107 `.res` and 49 `.resi` files from main runtime into its `lib/ocaml`, matching the basename-copy writer at `rewatch/src/build/compile.rs:3897-3928`. Every mirror hash matches both main source and the previous control runtime. No CMI/CMJ build, dependency installation or runtime-path substitution was used. The project retry has a separate artifact directory and log.

### Review interpretation limits

- Scope rows are `[calls, inclusive_ns, exclusive_ns]`; `outer_union` counts only outer scopes. Exclusive totals conserve the union. `wrapper_clone` includes nested payload accounting and the actual clone; `all_persistent_clone` surrounds the actual context-wrapper clone after payload scanning. Payload counts occur once there. Instrumentation traversal is separately timed, not treated as copied data. Resolver-local wrapper destruction is explicit. The returned declaration's caller-owned lifetime remains outside that timer. The self-manifest clone is counted but not part of `decl_transport_clone` timing.
- Construction node deltas are inclusive and non-additive. First-name value, constructor and label build timers distinguish cold work from enclosing query scopes. Module-declaration force has its own scope. Temporary-image timing measures local handle release, not guaranteed final graph destruction.
- Root endpoints follow selected context signature caches, typed Envs, Env module-component bindings, seed Envs, parent signatures, forced images and cached children. They do not enumerate every inline module signature, functor result, persistent-loader cache or returned signature owner. Signature tokens use Weak references to existing signature Arcs: no payload is retained, but allocation headers are retained as probe overhead and prevent address reuse. Tokens only have meaning within one context report. Cloned tables retain their token; independently cloned stored thunks get new tokens even when they share a populated image.
- Context teardown starts after diagnostic records and explicit instrumentation-container cleanup. The last-field sentinel runs after actual context fields drop; tested Rust field order and the actual TypeContext field declaration order agree. Other owners may retain graphs beyond this boundary. Neither endpoint counts nor field teardown measure total live heap or all last-owner releases.
- Declaration counters cover parameter/argument handles, record/variant/inlined containers and attribute string/pair payload. Wrapper counters cover owned map/set entries, key strings and source-override path bytes, while registry/portable/metadata references stay classified as shared. They do not provide allocator capacity/traffic, full nested representation-string bytes or a complete graph-size estimate. No logical count is a DRAM measurement.

The new runner uses main's runtime explicitly, preserves all eighteen Tella originals, verifies immutable controls, and freezes resolved dependency/runtime input hashes, main tracked-source hashes and symlink targets before exactly D1/P1/D12/P12. Existing module timing is enabled equally on all four diagnostic builds. Parent must acknowledge the exact patch and stop edits before the frozen window. The only allowed input differences remain the eleven previously proven compiler-info paths and `.sourcedirs`; source/symlink equality is also required. Full production gates and performance acceptance remain unearned.

## Measured boundary checkpoint

The approved fixed four-build diagnostic completed at main `95323bb48e2e72dd5df53b68b56bda73c406fca4`. Exactly D w1, P w1, D w12, P w12 ran. Every build exited zero, compiled 3248 modules and reproduced 5048 JavaScript files with digest `1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49`. No full attempt failed, repeated or was excluded. These are diagnostic comparisons, not candidate acceptance timing.

### Process cost and instrumentation limits

| Diagnostic | Wall s | User / sys s | Peak RSS bytes | Instructions | Cycles |
|---|---:|---:|---:|---:|---:|
| D w1 |19.276664|17.66 / 0.86|2074394624|253048330434|80164918615|
| P w1 |23.890263|21.68 / 1.90|2088599552|346937612932|101207309038|
| D w12 |4.799025|40.96 / 2.18|3034710016|253693320319|141720308406|
| P w12 |5.738344|45.02 / 3.97|2989752320|348343352870|162200909543|

Single-run probe overhead is +4.613599s serial and +0.939319s parallel, with +93.889B/+94.650B instructions. Root census alone records 2.253487s serial and 9.293125s summed parallel. Its traversal, retained weak allocation headers, diagnostic keys, timers and logging are measurement work. Do not subtract this once from an inclusive compiler timer to predict a saving, fit a confidence interval to four rows, or pool these with earlier cohorts.

All 3511 probe context records satisfy query-request = unique-key + repeat-key, component-request = unique-key + repeat-key, and summed exclusive scope durations = outer scope union. Both modes retain all records. Parallel scope times are sums of worker elapsed time, not wall or CPU time.

### Repetition and actual owned transport

Counts below are serial. Parallel agrees except four additional context-wrapper clones, four additional memory-override entries, eleven prepared-alias entries and 289 key bytes. The scheduling difference remains in raw data.

- 2,228,083 type queries, 368,646 unique context/Env/path/name/API keys and 1,859,437 repeated keys. The existing resolved-type cache hits 1,871,290 times. API-separated keys explain why a cache hit is not identical to a repeated diagnostic key.
- 1,194,232 Ctype resolver calls. The main returned-declaration clone executes 1,184,353 times. Across the selected resolver/cache-insertion sites, 1,540,973 owned declaration clones occur. These copy declaration containers, not the referenced type graph.
- Selected clones request 12,877,206 regular record-label entries, 4,285,804 constructor entries, 1,513,505 constructor argument handles, 2,015,604 parameter handles and the same number of variance elements. Observed attributes include 97,490,064 name bytes and 841,679,308 payload string bytes. This is cumulative logical requested content, not simultaneous memory, capacity or measured traffic. Inline constructor/inlined record attributes and representation strings are not exhaustively byte-accounted.
- 3,708,035 actual `TypeContext::persistent_env_clone` calls. Owned state totals 3,707,114 memory-override entries, 329,516 portable-override entries, 51,820 local alias entries, 11,628,889 prepared-alias set entries and 253,395,881 owned key bytes. Hidden/source override counts are zero. Portable values and module metadata stay shared; three registry fields per wrapper are recorded as shared fields, not copied registry maps.
- 110,998 stored-thunk requests contain 92,982 cached reads, 17,740 real builds and 276 unpublished probe builds. The latter must not be memoized. There are 78,992 table assemblies over 2,675,569 signature items, but these are not proven duplicate constructions of the same native thunk.
- All 65,217 observed selected-value queries are first-name builds. This does **not** establish repeated selected-value reconstruction inside one shared table. Constructor queries have 9,835 first-bucket builds among 38,428 requests; labels have 1,836 among 3,661. Their build time is small.

The first three serial declaration-transport consumers are `TextOverlayLineBackground` 40.065ms, `TextOverlayLineBackground__Test` 32.148ms and `ViewportOverlays` 32.014ms. This concentration neither authorizes file-specific behavior nor identifies a parallel critical path.

### Measured scopes

| Scope | Calls w1 | Inclusive ms w1 | Exclusive ms w1 | Inclusive summed ms w12 |
|---|---:|---:|---:|---:|
| Outermost union |6258432|5790.468|5790.468|12311.392|
| Ctype resolver |1194232|2654.073|781.993|5438.898|
| Actual context-wrapper clone |3708035|321.014|321.014|1155.161|
| Instrumentation wrapper payload scan |3708035|466.193|466.193|796.813|
| Resolver wrapper acquisition |2370209|679.699|186.993|1541.030|
| Resolver-local wrapper release |2370209|94.302|94.302|370.333|
| Main returned-declaration clone |1184353|339.206|339.206|657.398|
| Alias-strengthening query |1184353|527.933|117.992|1198.019|
| Local component construction |18016|374.066|182.171|801.808|
| Signature qualification |15863|101.965|44.868|214.113|
| Signature copy |23178|139.374|139.374|304.362|
| Final table assembly |78992|365.085|365.085|719.382|
| Module-declaration force |10793|74.776|74.776|153.812|
| First selected-value build |65217|120.180|120.180|275.370|
| First constructor bucket |9835|3.657|3.657|7.930|
| First label bucket |1836|0.614|0.614|1.060|

The actual clone timer excludes the explicit wrapper payload walk. The main declaration timer excludes its subsequent payload census. Those two scopes plus the separately timed resolver-local release total 754.522ms serial. They are disjoint observed scopes, **not total ownership cost, an upper bound or a removable budget**. Other copies/releases and caller-owned lifetimes are missing; not all wrapper calls belong to the selected resolver; independent declaration copies can be required; instrumentation changes execution.

Construction node deltas are 2,366,206 for local component construction, 17,650 for table assembly, 372,125 for module-declaration forcing, 345,831 for first value builds, 11,317 for constructor buckets and 2,088 for label buckets. They overlap through nested calls and must not be added. These counts do not justify removing required substitution graphs or treating current per-name allocation boundaries as native semantics.

### Actual Layout__Types coverage

| Scope | D w1 ms | P w1 ms | D w12 ms | P w12 ms |
|---|---:|---:|---:|---:|
| Typecheck |549.708|576.278|1421.286|1018.096|
| Raw/lowering |139.064|141.584|306.246|260.167|
| Module wall |700.182|733.995|1753.444|1326.474|

P's lower parallel module time despite a slower full process demonstrates scheduling perturbation, not a gain. All measured Env scopes in this module total 39.249ms serial across typecheck/Raw, with 20.307ms inclusive in the resolver. The main declaration clone is 7.781ms, all context-wrapper clones 0.480ms, resolver-local wrapper release 0.088ms and local component construction 1.106ms. This weakens the claim that the measured boundary explains the historical 324.070ms A/D typecheck gap. It is not a bound on every operation one might classify as Env; call coverage is explicitly limited.

The module makes 3239 type queries, 2489 repeat-key requests and 2506 cache hits; 4741 resolver entries include early exits before a qualified query. Its root endpoints agree in both modes:

| Endpoint | Envs | Stored thunks | Forced stored thunks | Component tables | Observed signature roots | Signature items |
|---|---:|---:|---:|---:|---:|---:|
| Setup |90|89|0|3|3|156|
| After typecheck |685|118|19|42|47|868|
| Pre-JS exit |706|145|45|70|86|1267|
| Context drop entry |705|145|45|70|86|1267|

### Retention and lifecycle findings

Across all serial context-drop endpoints, the selected census sees 351,426 stored thunks, 16,216 forced stored thunks, 77,172 component tables and 111,324 observed signature roots containing 3,605,674 items. These are sums over separate context endpoints, **not simultaneous heap occupancy**. Tables also come from non-stored-thunk paths. The largest signature-root set is 485 serial and 486 parallel. The three driver endpoints cover 3355 implementation contexts; all 3511 contexts have a drop endpoint, including interface contexts without those driver checkpoints.

The source retains seed Env, owned raw module declaration and parent signature fields after stored-thunk force. Endpoint growth shows continued roots through Raw; it does not prove those inputs are dead. Inline `MtySignature`, functor results, persistent loader contents and external result owners remain outside this census. There is no exhaustive last-owner accounting.

Context-field teardown totals 946.712ms serial and 3783.773ms summed parallel, after explicit probe-container cleanup of 5.132ms/32.958ms. It includes all production TypeContext fields, not just components. Weak-header retention and instrumented allocation history can still affect it. Local unpublished-image handle release is only 0.007ms/0.012ms, not a missing large cost.

### Design decision requested

**The evidence supports continuing the ownership investigation, but does not by itself justify activating the proposed complete-image rewrite.** The demonstrated target is owned transport around cached type queries. Repeated same-identity whole-component reconstruction is not established; neither the 1.54M declaration count nor 841MB logical attribute content establishes that a larger image will be faster. The 23–25% earlier sampled Env family cannot be used as a reclaimable budget.

The source-aligned ownership shape to consider remains:

1. A compilation-owned resolution state separates shared registry/internalized inputs from loader-view overrides, hidden modules and alias preparation. Capture view identity with Env identity. Do not globally merge mutation/alias effects merely to avoid wrapper copying. Thread this owner through actual Ctype/Env/typecore/Raw callers rather than adding another cache before the old cloned wrapper.
2. Env bindings address owner-paired native component thunks. Child-component and module-declaration entries remain distinct. Each holds original input, prefix substitution and the Env captured at the exact item position. Whole parent construction follows `env.ml` with per-declaration `Subst` cleanup and native constructor/label sharing. Probe reads do not publish a real entry.
3. Repeated type lookup returns a selected component/type-entry handle, not an Arc wrapping a copied declaration followed by another owned declaration clone. Read-only consumers take short projections; mutations/strengthening retain native copy and manifest-allocation boundaries. Guards end before forcing, recursion, graph mutation or owner growth. Cross-compilation handles are invalid.
4. Direct final descriptor construction should remove an old reconstruction path only when that path is shown redundant. Export/GenType/CMJ/raw/canonical views keep their required identities and lifetime. Do not discard raw inputs until all readers and captured thunks are independent, recreate full signatures per query, or eagerly duplicate sparse large-label payloads.

There are two unresolved design obligations before production approval: enumerate which owned resolver returns are inspection-only versus subsequently mutated, and define the loader-view transitions so removing wrapper clones does not merge independent override/alias state. They can be resolved from source and direct tests; no additional diagnostic cohort is proposed. Broader whole-image construction must be justified through that native API design, not clone-volume ranking. It can increase immediate allocations compared with today's Rust per-name paths and offset transport savings.

Parent should accept or reject this ownership direction with these limits, then require the exact owner/handle/mutation contract before activation. A facade that still invokes old transport is not completion. The task must not drift into Layout, maps, parser or backend work. Required production tests remain captured Env/alias shadowing, recursion, primitive positions, duplicate buckets, physical repeated-lookup identity, row/abbreviation independence, per-declaration cleanup, separate module/modtype forcing, child/probe traces, sparse labels and export/debug views. Full gates, independent exact-head review and the fixed D/candidate plus historical A comparisons remain necessary. No speedup or one-second feasibility is claimed; inherited external missing-Belt and standalone exact-JS ordering blockers remain unwaived.

### Verification and preservation

Frozen inputs were 42310 before and 42322 after. Exactly the eleven proven compiler-info outputs and `.sourcedirs` were added. All tracked main files and resolved symlink targets were equal. New runtime mirrors were included; no old-root manifest was reused. All eighteen original Tella bytes, backups, pin and modified-file set are restored. Immutable control/probe hashes and unchanged D production source were rechecked before report edits. One supplemental restoration assertion used a mistyped handwritten pin; its failure is documented separately and corrected against the approved runner. It caused no cohort or inventory rerun.

Raw stdout/stderr/process metadata, clean logs, JS manifests, scope/root records, source inventories and exact patch are durable under `env-ownership`. Compiler target caches are excluded from evidence; preserved source/patch/binaries reproduce the probe. No probe/build process remains. The archived source is explicitly instrumented and preserved; normal main compiler/rewatch source stays D. This is the measured checkpoint, not completion of an accepted production optimization. Ownership remains with this session pending parent's decision.

Final evidence check at this checkpoint verifies all 415 reviewed archived compiler/rewatch files and 8893 durable non-target evidence paths. `evidence-hashes.json` includes raw logs and source archive contents. The earlier 122-file snapshot remains byte-verifiable: the initial runner script is restored from its committed `201e0e61f` version under `scripts/`, and reviewed failure-safe scripts are separately preserved under `scripts-reviewed-95323/`. This preserves both versions rather than silently replacing an inventoried file. The compact committed summaries match their durable originals.

## Candidate implementation: resolution-view contract

The first candidate source slice replaces eager copying of the private `PersistentEnv` containers with one coarse `Arc<ResolutionView>` snapshot. This is not per-type-node reference counting and does not change the existing shared registry maps. Every write enters `Arc::make_mut`; clones still observe independent overrides, hidden modules, compiling-unit name, local aliases and prepared-alias membership. Loaded structures, CRC/error state, renamed-signature storage and registry fields retain their original ownership. Source-fallback construction still creates an independent cache with placeholders, increments depth and resets the prepared set; it does not reuse the normal view wholesale.

Mutation inventory in `cmi/persistent_env.rs` covers compiling-unit assignment, portable/disk signature preparation, cached-signature preparation, signature finalization, fallback alias import, in-memory metadata registration, transient signature hiding and namespace registration. A warm prepared-set check now uses `contains` before requesting a mutable view: the old `insert(existing_key)` returned false and changed no state. The cold branch inserts at the same point before registration/alias work. This avoids cloning a snapshot for a no-op without suppressing any lookup or force. Component algorithms remain untouched.

Two direct release tests pass: cloned reads share the snapshot while writes isolate owned overlays and preserve shared loader identities; warm preparation keeps the snapshot shared while cold preparation remains private. This slice is already used by existing Ctype/typecore/Env/Raw `PersistentEnv` clones, not an unused API. Remaining declaration-result integration, full tests/review/parity/timing and acceptance are still pending. No speedup is claimed.

The declaration-result integration now returns `TypeDeclarationRef` through Ctype's internal lookup/expansion path and Raw's typeopt/matching inspections. Its Shared variant carries the existing cached declaration Arc, so repeated inspection no longer executes `(*decl).clone()`. Env/local-constraint results remain borrowed. Alias strengthening, self-manifest replacement and uncached module fallbacks still construct owned declarations at the previous semantic boundary. The owned public compatibility boundary remains explicit for typemod's abbreviation-cycle callback; coherence checks and Raw's immediate/variant inspections use the shared view instead.

Consumer inventory: Ctype contractiveness, level/variance, abbreviation expansion and subtype checks inspect declarations or copy selected parameter/variance vectors before recursive work. They do not mutate the returned declaration container. Raw typeopt/matching and typemod coherence inspect representation/manifest metadata. The resolver itself changes metadata only in the existing alias/self-manifest strengthening branches. `into_owned` isolates container mutation while retaining the previous shallow clone's TypeExprRef sharing. The carrier adds a Box allocation for already-owned fallback/strengthening results to keep the common shared/borrowed carrier small; this added cost remains part of candidate timing/RSS, not hidden as a free transformation.

Direct production-lookup release tests pass for cold/warm cached Arc identity without new type nodes, writable metadata isolation with shared type-node identity, no probe cache publication, and recursive lookup while an earlier result remains live. The existing original-module-signature preservation test also passes. Existing component construction, signature copying, module/child force order and probe APIs remain unchanged. Full candidate gates and independent review are not yet run.

## Fixed candidate acceptance measurement registration

Registered before any candidate full-build timing outcome. Candidate source is under independent review starting `b54d194c1`; later corrections require exact-head re-review. Full correctness gates precede timing eligibility. Use immutable D controls and the accepted candidate release executables, main runtime with verified source mirrors, pinned Tella, explicit BSC/runtime/RAYON settings, warm filesystem and selected clean outside each full-process timer. Preserve 3248 modules, 5048 JS digest, all eighteen originals and resolved input/source/symlink inventories. Parent stops edits before the frozen window. Reuse the failure-safe owned-process-group runner and preserve every attempt.

Run two separate hyperfine screens per D/candidate w1/w12 cell, then exactly eight D/candidate pairs per worker mode. Odd pairs run D then candidate, w1 first; even pairs reverse variant order and use w12 first. If correctness-eligible, also run eight separate historical A/candidate w12 pairs regardless of the D comparison's effect, with alternating order. No extra, excluded, pooled or extended samples. Screens stay separate from paired results. Report wall/user/sys/RSS/instructions/cycles/load/exits/output hashes, mean/SD/median/min/max and paired Student-t 95% intervals. No fresh A/D baseline cohort is authorized.

Acceptance requires demonstrated reduction of actual work/instructions and supported parallel wall improvement without output changes or an unexplained RSS increase. The partial diagnostic scopes are not a gain target. Serial gain without supported parallel improvement is insufficient. Existing external missing-Belt and standalone exact-JS declaration-order failures remain explicit; inherited blockers cannot become a production-acceptance waiver. No benchmark retry, threshold change or parser/dependency/backend detour is permitted.


Independent source reviewer `bks-801b182e-f548-7ef9-902c-47a60ae82d2b` reported no blocking source findings at `57ff05309100737bd034b113668811844f10d8bb`, with moderate-high confidence. The reviewer inspected immutable Git objects because its tool allowlist rejected the main-checkout `cd`; parent separately verified main compiler source equals that exact review target. This is source review, not gate/performance acceptance.

The requested coverage addition exercises actual `typecheck_source_signature` with `Leaf`, `Backing.Child` and `AliasUnit` source files, two sibling loader views and separate TypeContexts. Both fallback caches are independent, preserve cycle placeholders, reset prepared membership and discover real alias state without modifying the original view. A third context exercises the actual fallback-merge path only while the original cache still contains no loaded type nodes; shared-cache publication remains visible as before while aliases stay view-private. The direct release test passes. This is a test-only delta requiring review before timing, not a component algorithm change.

## Candidate gates and capacity blocker

Reviewer `bks-801b182e-f548-7ef9-902c-47a60ae82d2b` closed the test-only finding at `9d6a4a0b72f6f69724bb49816853fe77e3089399`: both fallback caches explicitly retain `Cycle -> None`, increment depth and reset preparation; a short guard proves the original cache contains exactly that placeholder before the third context. Runtime source remains the reviewed implementation. Source review is not gate/performance acceptance.

Release compiler/all-bin and rewatch builds passed. The first full release compiler test attempt at `0e448cb49` remains **failed: 1295 passed, 50 failed, 108 ignored**. It stopped at the library. Bins, comptime, docs and rewatch then ran once each: bins 0/0, comptime 16 passed/23 ignored, docs 9 passed/7 ignored, rewatch 150 passed. No full release library rerun occurred.

The 48 functional failures lacked native runtime and test/dependency artifacts in the new checkout. Actual helpers read `tests/tests/lib/ocaml`, `tests/dependencies/rescript-react/lib/ocaml` and `node_modules/@rescript/runtime`. Native main setup compiled 107 runtime modules; parity setup compiled 619 test/dependency modules. The original failure list registered 48 instances under 45 unique names. One authorized exact release-binary invocation per unique name passed all 48 instances after setup. Duplicate harness names ran together, not as repeated recovery attempts. No parser benchmark was included. Original failures, prerequisite checks, registration and recovery remain separate evidence.

Two actual release parser benchmark failures remain unwaived and were never retried: `Css_Legacy_Core` 12069/9600us, 1.26x; `index` 9550/7655us, 1.25x, against the unchanged 1.20x threshold. These were executed checks, not skips or proof of fixed instability.

Release parity passes typedtree 610/610, raw Lambda 610/610, optimized Lambda 610/610, focused JS 344 fixtures, canonical JS snapshots 610/610 and diagnostics 1431/1431. External parity fails in OCaml at `bs-css/src/Css_AtomicTypes.res:1446`, missing Belt, before Rust comparison. All eighteen Tella originals were restored afterward; old-worktree status remained identical. Internal passes do not waive the external failure.

New `EnvOwnership.res` matches native/candidate syntax sexp with locations at 16454 bytes, typedtree stderr at 25728, raw Lambda stderr at 821, optimized Lambda stderr at 4839, and fresh JS stdout at 671. D agrees. The first fixture script compared both streams in debug modes and reported differences because native also emits JS stdout where Rust only emits IR stderr. Offline exact stderr comparison uses the IR channel without normalization or recompilation. `-dparsetree` is absent in D/candidate and remains an unsupported debug-dump difference; the real parser sexp check supplies syntax coverage. Old TypeArgStorage JS ordering remains native != D == candidate.

Main's target/reference/dependency links and 686 native source hashes are recorded. Native source matches the old reference checkout; binaries are reused native artifacts, not a new native build. There was no installation, dependency upgrade, old-source edit or write through `_build`. Candidate/probe/control and release test executables were preserved outside disposable caches.

Parent authorized the exact 4474-file disposable release-cache inventory, SHA256 `24eef40bca5b6d0c8cec141895c5e2cc3c29d9a397b3a7a69a66fa22c0d74fe9`. Under the heavy lock, paths/types/sizes, idle compiler state and preserved binaries/source were verified. Only listed files were unlinked; no directories were removed. The three retained release executables stayed hash-identical. Available space rose from 1028336 to 2883600 KiB; deletion and before/after records are preserved.

Default profile settings stayed unchanged. The default compiler build passed, then default rewatch failed with **ENOSPC**, including tracing-opentelemetry, serde_ignored, fs2, serde_path_to_error, oxc_parser, rayon and boa output writes. The attempt was preserved and not retried. About 131 MiB remains free; the new debug cache occupies 3.0 GiB. Default tests have not started. No optimization/debug/incremental setting was changed and no gate category is silently omitted. Parent acknowledged the blocker and requested stopping build/test launches while inspecting a separate safe capacity route. No deletion beyond the authorized 4474 files has occurred; exact remaining code-generation space is unknown.

No candidate performance cohort has started or been declared eligible. Release/parser, external and TypeArg failures remain red; default validation is incomplete. The candidate is experimental, not an accepted optimization. This session retains ownership while capacity is resolved.

## Default validation completed after capacity recovery

At source head `02e8f4be1f4719d93da4042ecd42e62b8d3d931d`, the separately registered default rewatch capacity-recovery build passed under the global heavy-work lock. It used `cargo build --locked --manifest-path rewatch/Cargo.toml`, the unchanged default `unoptimized + debuginfo` profile, no `RUSTFLAGS`, the existing Env-ownership target, and the runner's 600-second owned-process-group bound. The original ENOSPC build record remains intact and red; it was not overwritten or reclassified.

The previously unstarted default targets then each ran once with `--show-output` and passed:

- compiler `--lib`: 1345 passed, 108 ignored;
- compiler `--bins`: both binary targets completed with zero tests;
- compiler `--test comptime_tests`: 16 passed, 23 ignored;
- compiler `--doc`: 9 passed, 7 ignored;
- rewatch: 150 library tests passed; main and documentation targets completed with zero tests.

Every process exited zero without timeout. The helper now exposes a dedicated `default-rewatch-recovery` phase so recovery cannot rerun the already-passed compiler build or overwrite the failed rewatch attempt. Durable commands, process metadata, stdout/stderr hashes, counts and preservation checks are in `candidate/default-validation-summary.json`, SHA256 `7cf62e9efae1ff72842e0457f80b6855183be565da46e64ccae80bdf9c681375`.

Post-gate verification found all 156 runtime source mirrors equal to their recorded main sources, all eighteen Tella originals equal to preserved backups at pin `66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa`, and the old worktree status equal to its pre-gate baseline. The Env target links remain scoped to `env-ownership/probe-source/rewatch/target`. Preserved candidate release executables remain `88c8a9338abefba9681cc4f4d7d39228a28b47039ee7928ac2f81f9b26b0f4fe` for bsc and `5e149f9e75826404726fca8e4701f0525fca85c4f77cd17b6110d58df3dd3549` for rewatch. About 20.8 GiB remained available after the gates. No timing process started.

Default validation is now complete and green, but the candidate is not production-accepted or automatically timing-eligible. The original full release-library failure, both release parser threshold failures, external OCaml missing-`Belt` failure and standalone TypeArg JavaScript ordering mismatch remain red and unwaived. Parent must decide whether those known blockers permit the preregistered experimental timing cohort. There is still no measured candidate speedup, production claim or one-second forecast.

## Candidate binary provenance before experimental timing

The preserved `88c8a933…` bsc and `5e149f9e…` rewatch form the coherent candidate release-build pair. Their commands ran from approximately 12:04–12:10 at the `57ff05309` candidate checkpoint with `--locked --release`, default features, unset `RUSTFLAGS`, release LTO and one codegen unit. The files were preserved immediately at their 12:07/12:10 mtimes. Later, the full `cargo test --release` command at test-only head `0e448cb49` rewrote ordinary `compiler-rust/target/release/bsc` at 12:20 to the distinct `7f3e605c…` file. The only compiler/rewatch source delta from `57ff05309` to `0e448cb49`, and then to `9d6a4a0b`, is test code in `persistent_env.rs`; this does not establish binary equivalence, and none is claimed.

The saved internal parity and exact fixture processes used ordinary paths after 12:20, so they evidence `7f3e605c…` bsc with `5e149f9e…` rewatch. They do **not** directly evidence the preserved `88c8a933…` bsc. Both binaries remain untouched. Exact process windows, commands, hashes, sizes, fixture command paths and source deltas are preserved in `candidate/binary-provenance-investigation.json`.

For the approved bounded experiment, the prepared runner freezes the coherent release-build candidate pair `88c8a933…`/`5e149f9e…` as C; immutable architecture controls `a5ed9a62…`/`5fe8158d…` as D; and immutable historical controls `7c39a09c…`/`0187abee…` as A. The ordinary `7f3e605c…` bsc remains correctness-gate evidence and is excluded from timing. This is an explicit artifact choice, not a claim that the two candidate bsc files are equivalent.

`scripts/env_ownership_candidate_measure.py` encodes exactly eight screen builds, 32 alternating D/C paired builds across project workers 1 and 12, and sixteen separate alternating A/C worker-12 builds. Every attempt requires 3248 modules, 5048 JavaScript files and digest `1cacd5cf…`; records wall/user/sys/RSS/instructions/cycles/load; uses 120/600-second clean/build bounds; preserves failures without retry; and restores the eighteen Tella originals. Timed modes require a parent-authored approval record matching the prepared head, plan hash and binary-provenance hash plus the global heavy-lock sentinel. `freeze-inputs` performs one selected D clean and records fresh reachable inputs, tracked source and resolved symlinks before timing. No full build or timing mode has run.

The previously untested preserved `88c8a933…` executable now has one dedicated exact qualification. Without rerunning native, D or ordinary `7f3e605c…`, it compiled a byte-identical copy of `EnvOwnership.res` once in each JS, typedtree, raw-Lambda and optimized-Lambda mode. Its 671-byte JS stdout and 25728/821/4839-byte IR stderr streams exactly match both saved native and ordinary-candidate evidence. The newly emitted JavaScript then passed the existing alias-identity, captured/shadowed value and recursive-variant assertions in Node. Each compiler invocation and the Node check used a unique bounded process record under the global lock. An initial Node launch found no `node` on the restricted PATH before creating a process; that failure is preserved separately, and the one actual Node execution used the existing absolute executable. `candidate/fixtures-88/qualification.json` and its manifest contain all hashes. No parser, suite, full build or performance run occurred.

The final screen-runner revision writes a per-slot started marker before launching a compiler and redirects stdout/stderr directly to durable files. The screen child remains in the bounded Hyperfine driver's process group; a driver timeout therefore kills the wrapper and compiler together while retaining partial streams. Missing child completion metadata is reported as missing, never synthesized. Each slot is validated against D/C, workers 1/12 and repetitions 1/2, requires the frozen baseline, and refuses an existing marker or output. Finalization rejects driver and child failures independently. Setup/launch failures append a screen row, while paired/historical rows still append from `finally`; final validation rejects every recorded error and checks the exact planned tuple sequence and required metrics. A real fake child printed and then hung; the bounded test killed its process group, preserved the partial output and found no remaining child. No full corpus process was used by these tests.

## Fixed cohort closed on candidate output mismatch

The approved experimental cohort is permanently closed after **39 of 56** full builds. All eight separate screens passed. The paired phase recorded 31 builds: the first 30 reproduced 3248 modules, 5048 JavaScript files and digest `1cacd5cf…`; pair 8 position 1, candidate C at project worker 1, compiled and exited zero with complete metrics but produced digest `94f4515a…`. The runner stopped immediately. Pair 8 D/w1, all sixteen historical A/C builds and final verification did not run. There is no replacement, retry, exclusion, extension, complete D/C confidence interval, historical comparison or performance-acceptance result.

Exactly one output differed: `src/frontend/Hooks__Settings.bs.js`, expected SHA256 `7639a4ba…`, actual `3fa8b761…`. The actual 2358-byte file and 1520-byte source were copied before any later clean into `candidate-timing/failure-evidence-paired-8-C-w1`, together with the failed process, streams, clean and 5048-file manifest. No matching `.cmi`, `.cmj`, `.cmt`, `.cmti`, `.ast` or `.iast` artifact existed under the Tella roots to archive. An existing 2367-byte expected file was found in both independent `fuzz-errors` full/static Rust-output caches and copied without recompilation. The byte diff is only:

```diff
-  let updateValue = async (persistOpt, newValue) => {
-    let persist = persistOpt !== undefined ? persistOpt : true;
+  let updateValue = async (match$1, newValue) => {
+    let persist = match$1 !== undefined ? match$1 : true;
```

The source declaration is `async (~persist=true, newValue)`. `typecore.rs:16203-16319`, matching native `typecore.ml:3532-3577`, desugars this to a synthetic `*opt_persist*` parameter and default-value match. `raw_lambda/lower.rs:707-787`, matching `lam_convert.ml:321-365`, recognizes that prefix and renames the parameter from the bound name to `persistOpt`. The observed `match$1` is the generic match identifier shape exposed when that recognition or its expected input shape does not apply. This narrows the source investigation to optional-parameter rename recognition/input shape; it does **not** establish that the Env COW candidate caused the difference rather than exposing preexisting whole-build nondeterminism.

The stop summary SHA256 is `6a9b384a961606d8ed38d640ed73a75a5ddc3e7c7d880dc3304c140e467debd4`. Archived failure manifest SHA256 is `62c9943c0d43aba056b13b538c14c1cfee5ed5bee93f4f45d3b9a4fe38b3ecd0`; expected-byte/diff/root-lead record SHA256 is `406fa0e8331a7fc330f132a6f65a6dff17b015dd869b4c7bd9ed77a38a7cf30c`. Post-failure inventory remained valid with only the exact twelve generated metadata additions, frozen source and symlinks equal, all six binaries unchanged, Tella's eighteen originals restored at the fixed pin and the old worktree unchanged. Every prior release/parser/external/TypeArg failure remains red and unwaived. The candidate remains unaccepted and has no reportable performance result.

### Root-cause lead qualification

The final JavaScript diff alone does not prove that optional-parameter recognition failed. `raw_lambda/lower.rs` runs that recognition before its `alias_tbl`, Lambda simplification runs afterward, and `lam_compile.rs` copies the resulting ordinary function parameters into JS IR. The printer derives its base spelling from `Ident.name`; it does not transform `persistOpt` into `match`. Therefore failed recognition or a changed input shape remains one lead, alongside downstream identifier substitution/aliasing and same-stamp identity collision. No failed-build raw, lowered or optimized Lambda was preserved to distinguish those paths.

A related invariant risk is concrete but not yet tied to this occurrence. Rust `Ident` equality treats equal nonzero stamps as equal regardless of name, while its hash includes the first name character and its ordering includes name and flags. Equal-stamp/different-name identifiers therefore violate `Eq`/`Hash`. Native optional renaming uses ordered `Map_ident` (`Ext_ident.compare`: stamp then name), while native `Hash_ident` also assumes globally fresh stamps. Rust has several separately owned/TLS stamp streams across typechecking, raw conversion, lowering and split JS continuation, with explicit synchronization boundaries intended to retain that invariant. Blindly changing global equality/hashing or fixing a hash seed would hide rather than establish the defect.

The candidate's matching change is reachable from the synthetic `Option` default match: it replaces an owned declaration result with `TypeDeclarationRef`. The inspected matching consumer only reads declaration kind, layout and manifest; this supplies no direct mutation or identifier-allocation evidence that COW caused the name change. The next bounded discriminator, if source execution is authorized, is a single-source pre-JS regression that records raw and lowered function-parameter `(name, stamp)` pairs under two controlled worker TLS starting states, rejects duplicate nonzero stamps with different names, and checks the Ident-keyed map hash contract. It is not a build sweep, timing retry or reopening of the closed cohort. The append-only correction record is `failure-evidence-paired-8-C-w1/rootcause-lead-correction.json` (SHA256 `a3569cef4f117406e4bb9973e7cd5c5723ab8bfa75d6f3880eb533ec958bf9d2`).
