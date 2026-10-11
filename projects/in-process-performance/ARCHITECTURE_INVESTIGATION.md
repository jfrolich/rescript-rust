# Architecture investigation: what it takes to compile Tella in under one second

Date: 2026-09-16. Branch `compiler-performance-overhaul`. Scope: a read-mostly
investigation of every stage of the in-process Rust compiler as driven by
`rewatch build --in-process`, the algorithms and data representations each
stage uses, where the measured time goes, and which architectural changes are
large enough to matter for a `<1s` clean build of the pinned Tella webapp
(3,248 modules, 5,048 generated JS files, 16.6 MB of ReScript source in 3,023
`.res` files, only 55 `.resi` files).

**Implementation audit correction (2026-09-17):** OCaml resets persistent
Env caches and reinitializes identifier stamps for each unit
(`compiler/core/res_compmisc.ml:35,49`). Raw dependency storage can be shared
with local mutation overlays, but forced component binders cannot simply be
retained across units. `link_type` can legitimately reach dependency nodes,
and stamp changes can reorder generated JS through SCC hashing. See the
[corrected store design](THREAD_TYPE_STORE.md#corrected-stamp-policy-for-stages-3-and-4).
The original A/C estimates remain hypotheses, not validated savings.

This document does not claim any speedup. It ranks changes by measured work
affected and by the semantic contract they must preserve. Numbers marked
*(measured 2026-09)* come from the previous campaign's fixed-protocol runs
([MEASUREMENT_REBASELINE.md](MEASUREMENT_REBASELINE.md),
[ARCHITECTURE_BENCHMARKS.md](ARCHITECTURE_BENCHMARKS.md)); numbers marked
*(fresh)* come from the profile run at the end of this document.

## 0. Summary

1. **One second is a three-constraint problem, not a hot-spot problem.** On the
   benchmark machine (Mac16,10: 4 performance + 6 efficiency cores) the build
   currently does ~19–21 s of serial CPU work, sums to ~39–41 s of thread
   time at 12 workers, and has a measured signature-dependency critical path
   of ~1.6 s. The fresh profile shows the 2.4× thread-time inflation is
   *uniform across unrelated phases*, so most of it is efficiency-core
   heterogeneity plus oversubscription (the machine is ~6.5–7 P-core
   equivalents), and only ~1.2–1.3× is real contention. To finish in 1 s
   *all three* must move at once: serial work ≤ ~6 s, contention ≤ ~1.1×,
   and the critical chain < 1 s — the last of which also means keeping chain
   modules off efficiency cores. No scheduling change, no single pass
   rewrite, and no cache can do that alone.

2. **The type checker is not slow because of its algorithm; it is slow because
   of its memory representation.** It is a faithful port of OCaml's
   `ctype`/`typecore`/`typemod`/`env`, but every type node is 112 B + a 96 B
   `RefCell<TypeDesc>` holding heap `Vec`s, `Arc<Path>` chains and `SmolStr`s;
   `get_desc` clones the descriptor (33 M clones/build, ~3.2 GB logical);
   36.9 M nodes are allocated per build, and **47 % of them (17.4 M) are
   re-internalized copies of dependency signatures** that every one of the
   3,248 modules rebuilds from scratch (`Stdlib`, `Pervasives`, `TellaStd`,
   `Belt`, …). OCaml's node is 4 words, its descriptor is pattern-matched in
   place, and its persistent-structure table is shared within a compilation
   (then cleared by `Res_compmisc.init_path`).

3. **The largest real levers, in order:**
   - **A. A frozen, shared, process-wide dependency type store** (Sorbet
     `GlobalState` / rustc crate metadata / Zig `InternPool` model). Publish a
     module's signature once as immutable POD nodes; consumers reference them
     directly through a two-level `TypeExprRef`. Removes 17.4 M allocations,
     0.7 s of internalization, the per-module `register_sig_types_*` walks,
     and some of the 3 GB RSS that drives parallel inflation. This is a Rust
     storage optimization; per-unit mutation and substitution behavior must
     still follow OCaml's compilation lifecycle.
   - **B. POD type nodes** (no heap pointers inside `TypeDesc`: interned
     `PathId`, argument ranges into a side vector, interned labels), so
     `get_desc` is a 16–24 B copy, arena drop is O(1), and `Path.same` is an
     integer compare. Representation-only; identity semantics unchanged.
   - **C. Once-per-package prelude environment and deletion of the Rust-only
     type registries** (`type_decl_store`, `type_decl_by_path`, …) that every
     module rebuilds by walking every dependency signature. OCaml has neither.
   - **D. Finish the indexed backend end to end** (M6 JS consumer, then an
     indexed JS IR and a single-buffer printer). The backend is 5.45 s of
     serial work rebuilding 464 B `Lambda` trees ~14 times.
   - **E. Parallel-inflation and placement fixes**: a process-global atomic
     bumped on every `Env` mutation from 12 threads, `Arc<Path>` refcount
     ping-pong on shared registry data, per-module registry snapshot clones,
     and — most important on this hardware — no core-class affinity for
     critical-path work: the fresh profile shows inflation is *uniform*
     across unrelated phases, i.e. mostly efficiency-core heterogeneity, and
     the chain head `Layout__Types` runs 2.55× slower under parallel load.
   - **F. Pipeline the frontend into the DAG** so parse and typecheck
     overlap and `.resi` signatures unblock dependents first.

4. **Honest trajectory.** A+B+C+E are the only changes with a plausible
   multi-second effect and they compound (B makes A `Sync` and cheap to
   build; A removes the work C would otherwise cache; B and E attack the
   same inflation). The target is a *clean* build: nothing from a previous
   build may be reused, so every second has to come out of the work itself
   or out of the chain. With all of A–F landed, the arithmetic in §1 lands
   around 1.3–1.7 s on this machine; 1 s additionally needs the critical
   chain under 1 s on performance cores, which follows from A–C making the
   chain modules 2–3× faster plus E.5 placement. Anything less than the full
   stack stops at ~2.5–3 s.

## 1. The budget

*(measured 2026-09, fixed protocol, historical fast stack A)*

| Quantity | Value |
|---|---:|
| Clean build wall, 1 worker | 18.3–19.0 s |
| Clean build wall, 12 workers | 4.60–4.65 s |
| CPU (user+sys), 1 / 12 workers | 18.2 s / 41.5 s |
| Retired instructions, 1 / 12 workers | 240 B / 241 B (same work) |
| IPC, 1 / 12 workers | 3.11 / 1.79 |
| Peak RSS, 1 / 12 workers | 2.1 GB / 3.0 GB |
| Signature-DAG longest path at 12 workers | 1.62 s (0.70 s with serial service times) |
| Idle-slot wait at 12 workers | 7–14 ms (workers are never starved) |
| Type nodes allocated per build | 36.9 M (17.4 M from internalizing dependency signatures) |
| `get_desc` clones per build | 33.2 M |
| Whole-signature copies per build | 55.5 K copies, 1.46 M items |

Hardware arithmetic. Apple's efficiency cores deliver roughly 0.4–0.5 of a
performance core on this kind of pointer-chasing code, so 4P+6E ≈ 6.5–7
P-core-equivalents. With zero contention and zero critical-path stalls, 19 s
of serial work bottoms out at ~2.8 s. The observed 4.6–5.3 s is that floor
times ~1.7×: the real contention share (~1.2–1.3×, §5) times the
critical-chain and barrier stalls the scheduler cannot fill.

Therefore, for 1.0 s:

| Constraint | Today | Needed |
|---|---:|---:|
| Serial CPU work | ~19–21 s | ≤ 6 s (3.2× less) |
| Real contention (beyond core heterogeneity) | ~1.2–1.3× | ≤ 1.1× |
| Critical chain (signature DAG, parallel conditions) | 1.62 s | < 0.9 s, on P-cores |

The three are coupled: the same representation changes that cut serial work
(fewer bytes, fewer allocations, no shared refcounts) are the ones that cut
inflation, and faster per-module typechecking is what shortens the chain,
because 98 % of Tella modules have no `.resi` and their signature is only
known after the whole implementation is typechecked.

Reference point: on the 657-file in-repo corpus, OCaml `bsc` processes finish
in 6.2 s total *including ~657 process spawns*, while the Rust compiler needs
26.5 s ([CORPUS_BASELINE.md](../typechecker-performance/CORPUS_BASELINE.md)).
The per-file typecheck+backend work in Rust is therefore roughly 4–7× OCaml's
today. OCaml is the existence proof that this algorithm can run 4× faster
than the current Rust port with the *same* semantics — the gap is data layout
and duplicated work, not the algorithm.

## 2. Pipeline, stage by stage

```
rewatch: discover packages → scan sources → PARSE (rayon par_iter, all files)
   → deps graph → runtime precompile (107 modules) → DAG scheduler
per module (worker):
   registry snapshot clone → TypeContext::new → initial_env → PersistentEnv::from_registry
   → load_pervasives (open Pervasives, Stdlib, -open TellaStd)      [untimed "env_setup"]
   → [.resi] typecheck signature → publish PersStruct → SignatureReady
   → TYPECHECK implementation (typemod.type_structure)             [Typecheck]
   → signature prepare/extract (moregen, compunit, normalize, copy, serialize) [untimed]
   → SignatureReady (no .resi) → dependents unblocked
   → GenType (if annotated)                                         [Gentype]
   → typedtree → RawLambda (translcore/translmod/matching)          [Lambda]
   → RawLambda → Lambda (lam_convert)                               [Lambda]
   → PreJsMsg → wait for dependency JS metadata (cmj purity/arity/constants)
   → JS finish: lambda optimization (14 passes) → JS IR → JS passes → print → write  [LambdaOptimization, Codegen]
   → JsMetadataReady → TypeContext drop                             [untimed]
```

### 2.1 Orchestration (`rewatch/src/build.rs`, `build/compile.rs`)

- **Parse phase**: `parse::generate_asts` runs a `rayon::par_iter` over every
  module. Each file is read, scanned and parsed by the Rust parser into a
  `ParseArena` (positions, locations, strings and rare expression payloads in
  side tables), then the builtin PPXs run in-process (JSX v4, `let?` unwrap,
  and the native Spice port — Tella's `@jfrolich/ppx-spice/ppx` is served by
  `binary_ast/spice_ppx.rs`, so no subprocess is spawned). Dependencies are
  extracted from the AST and the AST is retained in memory as
  `StoredAst(Arc<…>)`. No `.ast` file is written in in-process mode.
- **Barrier**: `deps::get_deps` builds the module graph after *all* parsing.
  Measured parse+deps barrier: 2.0 s serial, 0.30 s at 12 workers.
- **Runtime precompile**: the 107 `@rescript/runtime` modules are parsed and
  compiled from source into the registry on every build (≈50–90 ms).
- **Scheduler**: a `BinaryHeap<WorkUnit>` ordered by critical-path priority
  (`compute_critical_path_priorities` over per-module cost estimates), bounded
  to `rayon::current_num_threads()` in-flight units inside a
  `rayon::in_place_scope`. Work is split in two: *pre-JS* (typecheck + raw
  lowering, publishes the signature as soon as it exists) and *JS finish*
  (runs when the module's backend-visible dependencies have JS metadata).
  Every spawned unit clones a `ModuleRegistry` snapshot (Arc-backed shared
  maps plus small local maps).
- **Publication**: a compiled module's signature is serialized into a
  `PortablePersStruct` (self-contained index graph) and inserted into the
  registry; JS metadata (purity, export arities/constants, hoisted exports) is
  published separately after codegen.

### 2.2 Parser and builtin PPX (`compiler-rust/src/parser`, `binary_ast/ppx.rs`)

Hand-written recursive descent, 1:1 with `res_core.ml`, with arena indices
(`StrIdx`, `LocIdx`, `PosIdx`, `ExprIdx`), sparse side tables for rare
payloads, zero-copy tokens. 1.5 s serial for 16.6 MB (≈11 MB/s including
PPX, dependency extraction and arena construction; the parser alone is
2–5× faster than OCaml's). This stage is not a first-order lever; its cost
is dominated by the JSX and Spice rewrites and it is fully parallel. The only
structural cost is the phase barrier (§4.F).

### 2.3 Per-module environment setup (untimed)

`compile_preprocessed_structure_in_process_until_js` does the following
*before* the `Typecheck` timer starts and *after* it stops:

- `TypeContext::new` — fresh arena plus ~15 side tables including five
  string/stamp/path-keyed `HashMap`s of type declarations.
- `initial_env` — predef types/exceptions.
- `PersistentEnv::from_registry` — per-module loader view.
- `load_pervasives` — `open_module("Pervasives")`, `open_module("Stdlib")`,
  then every `-open` (`TellaStd` for Tella). Each `open_module` calls
  `find_pers_struct`, which **internalizes the whole portable graph of that
  module into this module's arena** (`internalize_pers_struct`), then runs
  `collect_alias_rewrites`, `register_sig_types_recursive` (twice when an
  alias prefix exists), `register_types_by_stamp_in_signature_recursive`,
  builds `QualifiedModuleComponents` (prefix substitution over the full
  signature) and `add_signature_to_env_with_options` which applies
  `substitute_type_paths_in_sig` over every item. `Stdlib` alone is ~100
  submodules; `TellaStd` re-exports much of the app's shared vocabulary.
- After typechecking: `apply_moregen_constraints`/`includemod::compunit`
  (OCaml does this too), `normalize_signature_types`,
  `copy_lookup_signature_for_subst` (a full signature deep copy for the
  GenType raw-signature cache), `register_in_memory_signature`,
  `extract_module_update` → `serialize_pers_struct` (walks the signature
  graph twice: finalized and raw).
- At the end: dropping the `TypeContext` — 36.9 M nodes' destructors across
  the build, each `TypeDesc` owning `Vec`s/`Path`s/`String`s.

This is where the *3.7 s serial "residual"* measured by the phase timer
mostly lives. It is not a serialization phase; it is untimed per-module
work. §5 attributes it with fresh per-module `overhead_ms`.

### 2.4 Type checking (`types/typecore.rs`, `typemod.rs`, `ctype.rs`, `env.rs`, `env_lazy.rs`)

Algorithms (all OCaml's, by design):

- **Inference**: Hindley–Milner with *levels*. `current_level` is bumped on
  entering a `let`, fresh variables get that level, `generalize` turns
  variables above the level into `generic_level`, `instance` copies generic
  schemes. Unification is destructive union-find: `link_type` rewrites a
  node's `desc` to `Tlink(other)`; `repr` follows links. Failed speculative
  unifications roll back through `snapshot_type_state`/`restore_type_state`
  (OCaml `Btype.snapshot`/`backtrack`).
- **Abbreviation expansion**: `expand_head` follows `Tconstr` manifests via
  `Env.find_type` and memoizes expansions in the `abbrev` cell hung off each
  `Tconstr` (`Mcons` chains). Memo hits are semantically visible (they decide
  physical sharing in the typedtree), so they are per-compilation state.
- **Copy/instance**: OCaml marks visited nodes in place with `Tsubst` and
  cleans up afterwards; Rust uses a `CopyCache { HashMap<TypeExprRef,
  TypeExprRef>, row_more_markers }` per instance (9.6 M copy entries, 6 %
  cache hits, ~0.4 s inside the copy function alone).
- **Environment**: OCaml `Env.t` is a functional record of `Ident.tbl`
  (balanced trees) with lazily forced module components
  (`components_of_module_maker`: `prefix_idents` + `Subst` over the
  signature, forced once per `(env, sub, path, mty)`). Rust `Env` is a record
  of `IdTbl<Arc<T>>` backed by `im_rc::HashMap<String, Vec<(Ident, T)>>`
  (HAMT; O(1) clone, path-copy on insert) plus opened layers, and
  `env_lazy::QualifiedModuleComponents` with `OnceCell`-forced substituted
  views. Every `add_*` allocates a `String` key, wraps the description in a
  fresh `Arc`, and bumps a **process-global** `NEXT_ENV_ID` atomic.
- **Module system**: `typemod` types structures/signatures; `includemod`
  does signature inclusion (matching items by name, `moregeneral` on values,
  coercion construction). Applied to every module against its own inferred
  signature (`compunit`) exactly as OCaml does.
- **Cross-module**: `PersistentEnv::find_pers_struct` is OCaml's persistent
  structure table. In-process it reads `PortablePersStruct`s from the shared
  registry and internalizes them into the current arena. There is no
  `.cmi` read in this mode.

Representation, Rust vs OCaml:

| | OCaml | Rust today |
|---|---|---|
| `type_expr` | 3-field record, 32 B | `TypeExpr` 112 B: `RefCell<TypeDesc>` (96 B) + `Cell<i32>` + id |
| `Tconstr` payload | `Path.t * type_expr list * abbrev_memo ref` (shared immutable list) | `{ path: Path (Arc chain + SmolStr), args: Vec<TypeExprRef>, abbrev: AbbrevMemoRef }` |
| `Tarrow` arg | `{lbl; typ}` in a shared list | `Vec<TypeArg>`; `TypeArg` = boxed optional label + ref (was 80 B, now ~16 B after the TypeArg experiment) |
| Reading a descriptor | pattern match on the record, zero copy | `get_desc` clones (33 M/build) or `borrow_desc` (RefCell guard) |
| Node handle | pointer | `TypeExprRef(u32)` into arena (good) |
| Path equality | structural recursion on shared pointers | structural recursion on `Arc` chains + `SmolStr` compares |
| Persistent structures | process-wide table, cleared between compilation units | re-internalized into every module's arena (17.4 M nodes/build) |
| Env tables | `Ident.tbl` AVL over `Ident` | `im_rc::HashMap<String, …>` + `Arc<T>` per binding |
| Marking during traversal | flips `level` sign in place | side maps / snapshots |

Measured *(2026-09)*: Typecheck 7.8–8.9 s serial (≈42 % of serial work,
20–21 s summed thread time at 12 workers). Sample partition of running
worker samples: Env family 23–25 %, other typechecking 28–29 %, memmove leaves
14–16 %, allocator leaves 10–11 %, drop leaves 8 %. Module p50/p90/p99/max
typecheck: 0.9 / 5.2 / 23 / 263 ms serial, and 2.0 / 14 / 64 / 512 ms at 12
workers — **the same module takes ~2× longer when 11 siblings run**, which is
the inflation constraint in the small.

### 2.5 Signature publication and import (`cmi/portable_types.rs`, `persistent_env.rs`)

Producer: `serialize_pers_struct` walks the signature's reachable type graph
(finalized *and* raw) into `PortableTypeGraph { entries: Vec<PortableTypeEntry> }`
with `usize` indices, fingerprints it, stores it in the registry as
`Arc<PortablePersStruct>`. Consumer: `internalize_pers_struct` allocates a
placeholder node per entry then fills descriptors (direct contiguous
allocation was measured as a ~30 ms parallel gain). 58 K internalizations per
build, 0.73 s serial inclusive, 1.66 s summed at 12 workers. In OCaml this
step is `input_value` of a `.cmi` — a C loop at ~10–20 ns/word — and is
memoized until the persistent cache is reset for the next compilation.

### 2.6 Typedtree → RawLambda → Lambda (`raw_lambda/convert.rs`, `matching.rs`, `lower.rs`)

- `convert.rs` ports `translcore`/`translmod`: expression lowering, record and
  variant representation decisions (`typeopt` queries back into `Env` and
  type expansion), FFI externals, module coercions, `let rec` compilation.
- `matching.rs` ports `matching.ml`: pattern-matrix decomposition
  (specialise by constructor/constant/variant/record/array, default matrix,
  jump summaries, `Lstaticcatch`/`Lstaticraise` exits). Actions are shared
  through `Arc<MatchActionData>` while matrices are copied (a needed fix for
  quadratic cloning).
- `lower.rs` ports `Lam_convert.convert`: alias/exit tables, optional-arg
  naming, exception wrapping, dependency collection, smart constructors.

Cost: 2.3–2.6 s serial; its sample union includes substantial Env/type
lookup work (typeopt), so it benefits directly from A–C. `Lambda` is a 464 B
enum of boxed children.

### 2.7 Lambda optimization (`lambda/lam_compile_main.rs`)

Exactly OCaml's `lam_compile_main.ml:148-200` sequence: deep_flatten →
collect → exits → collect → alias → deep_flatten → collect → alias →
deep_flatten → collect → alpha → exits → collect → alias → alpha → lets
(count + DCE + eliminate_ref) → exits → coercion/grouping → hoisted aliases.
~14 whole-tree traversals; each consuming pass rebuilds `Box<Lambda>` trees.
Cost: 1.3 s serial. The indexed store (M1–M5: `lambda/indexed.rs`,
`*_indexed.rs`) implements every pass on `NodeId`s in one append-only
context but is **inactive** because the JS consumer (M6) is unfinished; a
partial activation would pay a tree→arena→tree conversion and was measured
to lose.

### 2.8 JS backend (`lambda/lam_compile*.rs`, `js_ir/`)

`LambdaCompiler` ports `lam_compile.ml`: continuation-passing compilation
with `Js_output` (declare/assign/return/effect modes), tail-call/loop
labels, CMJ cross-module inlining via registry lookups, then JS passes in
OCaml order (`flatten_and_mark_dead`, `tailcall_inline`, `shake`,
`external_shadow`, `record_rest`), then the `js_dump` port (a layout engine
over a `String`), optional source maps. `Expression` is 256 B with `Box`
children and `Option<String>` comments. Cost: 1.6–1.7 s serial plus 0.26 s
file writes.

### 2.9 GenType

Runs on the typed artifact for annotated modules (181 of Tella's files):
0.27–0.29 s serial. Not a lever.

### 2.10 Parallel behaviour

- Scheduled-slot occupancy 96.7 % at 12 workers; idle-slot wait 7–14 ms.
  There is no scheduling slack to recover; wall time is CPU inflation plus
  the critical chain.
- 16 workers beat 12 by only 28 ms (and cost 226 MB more RSS). Twelve is the
  elbow because there are only ten cores.
- Instruction count is flat across worker counts; cycles rise 77 B → 135 B.
  The fresh per-phase breakdown (§5) shows the inflation is uniform across
  phases that share no state, so most of it is efficiency-core heterogeneity
  and oversubscription; the memory/allocator/contention share is ~1.2–1.3×.
  Still real, still worth removing, but not the 2× it looks like.
- Concrete shared-state suspects (all cheap to falsify): `NEXT_ENV_ID`
  fetch_add on every `Env` mutation from all threads; `Arc<Path>` and
  `SmolStr` refcount traffic on paths cloned out of registry-shared
  signatures (3.4 M path-bearing copy actions per build); `ModuleRegistry`
  `RwLock<HashMap>` reads on every `find_pers_struct`; per-unit registry
  snapshot clones; mimalloc cross-thread frees when JS-finish runs on a
  different worker than pre-JS (arena moved across threads).

## 3. Where the time goes (serial)

| Bucket | Fast stack A (2026-09) | This head (fresh) | Notes |
|---|---:|---:|---|
| Typecheck | 8.1 s (42 %) | 8.39 s (41 %) | Env/component forcing, instance/copy, unify, includemod |
| Untimed residual | 3.8 s (20 %) | 4.61 s (22 %) | 3.03 s is per-module setup/teardown (implicit opens + internalization + registries, signature prepare/extract/serialize, context drop); rest is rewatch startup/scan, deps, JS-finish bookkeeping, writes |
| Raw lowering + convert | 2.4 s (13 %) | 2.51 s (12 %) | includes Env/typeopt queries |
| Codegen (JS IR + passes + print) | 1.7 s (9 %) | 1.75 s (8.5 %) | |
| Parse + PPX + deps | 1.5 s (8 %) | 1.53 s (7 %) | fully parallel, barrier 0.3 s |
| Lambda optimization | 1.3 s (7 %) | 1.46 s (7 %) | 14 tree rebuilds |
| GenType | 0.3 s (1.5 %) | 0.33 s (1.6 %) | |
| **Total** | **~19 s** | **20.59 s** | |

Two thirds of the build is type-system data movement: typecheck, the
residual, and the Env-heavy half of raw lowering. Eighty percent of modules
are tiny and pay a fixed ~1 ms of untimed per-module work on top of ~1 ms of
typechecking.

## 4. Proposals

Each proposal states the mechanism, the evidence it targets, the semantic
contract that must hold (this port is a 1:1 OCaml rewrite; representation
may change, algorithms, force order, identity and mutation semantics may
not), the expected effect on each of the three constraints, and the size.

### A. Frozen shared dependency type store (the "global symbol table")

**Borrowed from:** Sorbet's immutable `GlobalState` shared read-only across
typechecking threads; rustc's crate metadata (`TyCtxt` interns types once
and every query reads them by reference); Zig's `InternPool` (one
process-wide, index-addressed, POD type table). All three separate
"published, immutable" from "being built, mutable".

**Mechanism.** Replace `PortablePersStruct → internalize into every consumer`
with `publish once into a process-wide append-only frozen arena`. A
`TypeExprRef` becomes two-level: a high bit (or id range) selects the shared
store vs. the compilation-local arena. `ctx.borrow_desc` / `get_level`
branch on that bit. Shared backing nodes are immutable; the state
OCaml writes into dependency nodes moves to per-compilation overlays
keyed by shared node id:

1. `abbrev` memos on `Tconstr` — already an index into `ctx.abbrevs` in
   Rust; shared nodes get a lazily created local `AbbrevMemoRef` through an
   overlay map (memo hits stay per-compilation, so typedtree sharing is
   unchanged).
2. Levels — use a local scalar overlay for traversal marks **and** ordinary
   level changes; a bitset cannot represent both.
3. Descriptors — `link_type` legitimately reaches dependency declaration
   nodes (`btype.ml:633-651`, `ctype.ml:2118-2127`). Preserve the write and
   physical handle identity in a local descriptor overlay, never suppress it.
4. Row-field cells — isolate their mutable links in the local overlay too.

Publishing a module = the producer's `serialize_pers_struct` walk, but
emitting POD nodes directly into the shared store (the same DFS order and
first-visit ids it emits today) instead of a portable vector that each
consumer re-walks. `find_pers_struct` then returns a `PersStruct` whose
signature items carry shared refs; nothing is allocated in the consumer.

**Required OCaml contract.** `Res_compmisc.init_path` clears persistent
structures between units, and `initial_env` reinitializes stamps. Sharing
immutable raw storage must preserve that per-unit behavior. Component
forcing (`components_of_module_maker`) still happens per
`(env, sub, path, mty)` in the consumer and produces consumer-local
substituted views; force order, binder allocation, and copy depth must not
change. Only their immutable source storage is shared.

**Evidence.** 17.4 M of 36.9 M node allocations (47 %); 58 K internalizations;
0.73 s serial / 1.66 s summed parallel inside internalization alone; plus the
per-module `register_sig_types_recursive`, `register_types_by_stamp_*`,
`substitute_type_paths_in_sig` and `collect_alias_rewrites` walks over the
same graphs (in the residual); plus the RSS those copies retain (3 GB at 12
workers, which is the inflation). Only ~18 dependency modules are touched
per compile on average, but `Stdlib` + `Pervasives` + `TellaStd` are among
them for *every* module.

**Effect.** Serial: −1.5 to −2.5 s (internalization, registry walks, drops,
plus the allocator/memmove share of those nodes). Inflation: significant —
the largest reduction of per-worker resident bytes available. Critical
chain: every chain module stops paying the prelude import.

**Contract to preserve.** Physical identity of shared nodes is *more* OCaml-like,
not less. Must keep: consumer-local component forcing and substitution
copies; per-compilation abbrev memos; identical first-visit node ordering
in the sexp serializer (it indexes by first appearance, not raw id — verify);
no mutation of shared nodes (enforce with a debug assertion in `set_desc`,
`set_level`, `link_type`). `Tsubst`/`CopyCache` must treat shared roots as
ordinary originals.

**Size.** Large but mechanical: `TypeExprRef` bit split, `TypeArena` split
into `LocalArena` + `&'static FrozenStore` (or `Arc<FrozenStore>` grown with
an append-only chunked vector so readers never relocate), `AbbrevMemoRef` /
`RowFieldRef` overlays, and rewriting `internalize_pers_struct` into
`freeze_pers_struct`. Depends on B for `Sync` nodes (a `RefCell<TypeDesc>`
with `Vec`s cannot be shared across threads; a POD node can).

### B. POD type nodes, interned paths and labels, O(1) arena drop

**Borrowed from:** Zig/Roc typed-index "SafeList"/`MultiArrayList` storage;
OXC's 16-byte enum discipline; Carbon's and Sorbet's integer-interned names.

**Mechanism.** `TypeDesc` variants hold no heap pointers:

```
Tconstr { path: PathId, args: ArgRange, abbrev: AbbrevMemoRef }   // 4 × u32
Tarrow  { args: TypeArgRange, ret: TypeExprRef }
Ttuple  (TypeRange)
Tvariant(RowId)            // row payload in a side table, mutable through ctx
Tobject { fields: TypeExprRef, name: ObjNameId }
Tfield  { name: LabelId, kind: FieldKindRef, typ, rest }
Tvar(NameId) / Tunivar(NameId) / Tpoly { body, vars: TypeRange } / Tpackage(PkgId)
```

with `ctx.type_args: Vec<TypeExprRef>` (append-only ranges), `ctx.paths:
PathInterner` (structure-hashed, so `PathId == PathId` ⇔ `Path.same`), and
`ctx.labels/names: StrInterner`. `TypeExpr` becomes `{ desc: Cell<TypeDesc>
(Copy, ≤ 24 B), level: Cell<i32>, id: u32 }`. `get_desc` returns the `Copy`
descriptor; `borrow_desc` disappears; `set_desc` is a `Cell::set`. Dropping
a `TypeContext` frees a handful of `Vec`s.

**Why it is faithful.** Pure representation. Node identity stays the arena
index; `Path.same` is structural in OCaml, and structural interning gives
identical answers (different stamps ⇒ different ids). Row descriptors keep
their mutation points (`row_more`, field cells) via `RowId` side tables with
the same `RowFieldRef` cells that exist today. Snapshot/backtrack becomes a
journal of `(ref, old desc)` `Copy` pairs — cheaper and closer to
`Btype.log_change`. Interning is per `TypeContext` (or per frozen store for
A); no global interner, no `unsafe`.

**Evidence.** 33.2 M descriptor clones (3.2–3.5 GB logical; 0.49 GB nested
requested bytes), 14–16 % memmove and 10–11 % allocator leaves, 8 % drop
leaves, 870 MB of descriptor `Vec` capacity across lifetimes, 84 % of arrow
arguments unlabeled, `TypeExprRefMap::insert` hot. The rejected "five short
borrows" experiment showed that *partial* borrow conversion does not pay;
the whole-representation change is what removes the clone class.

**Effect.** Serial: −2 to −3 s across typecheck, raw lowering and the
residual's drop share. Inflation: the second largest lever (node bytes ÷ 4,
no `Arc` refcount traffic on paths, allocator calls ÷ ~3). Critical chain:
proportional.

**Contract.** Same `TypeDesc` variant set and the same observable
descriptor after every mutation; same `Tlink` chains; same abbrev-memo cells;
`Tsubst` marker behaviour reproduced either in place (now cheap, since desc is
`Copy` — this could finally replace `CopyCache` with OCaml's own in-place
`Tsubst` + `cleanup_types`, removing the per-instance `HashMap`) or through the
existing cache.

**Size.** The largest mechanical refactor in this list: every `match` on
`TypeDesc` in `ctype.rs` (12 K lines), `typecore.rs` (35 K), `typemod.rs`
(26 K), `includemod.rs`, `typeopt`, `sexp_typedtree`, `portable_types`,
`gentype`. Most arms only change `args.iter()` → `ctx.args(range).iter()` and
`path.clone()` → `path` (Copy). A `TypeDescView<'ctx>` shim can carry the old
field shapes during migration. Guarded by the existing 610-file typedtree/
raw/optimized/JS/diagnostic parity suites.

### C. Once-per-package prelude Env; delete the Rust-only type registries

**Borrowed from:** OCaml's functional `Env` shared by extension; rustc's
"prelude" and `Steal` ownership at phase boundaries. Cross-unit storage reuse
is an optimization, not what OCaml's reset-cache lifecycle already does.

**Mechanism.**
1. Build the initial environment (`initial_env` + `open Pervasives` + `open
   Stdlib` + every `-open` from the package's `compiler-flags`) **once per
   package configuration** into a frozen `PreludeEnv` whose tables are the
   same `im_rc` HAMTs; each module extends its immutable layers. This requires
   factoring unit-local forced substitution views from shared templates:
   cached tables must not retain another unit's binders or mutation overlays.
   A plain O(1) clone of today's fully forced Env is not sufficient.
2. Delete `type_decl_store`, `type_decl_by_stamp`, `type_decl_by_path`,
   `type_decl_by_exact_path`, `type_item_by_path`, `missing_type_item_by_path`,
   `resolved_pdot_type_cache` and the `register_sig_types_*` walks that fill
   them from every loaded signature. Route every remaining consumer through
   `Env.find_type`/`lookup_module_descr` and `env_lazy` components, which is
   what OCaml does (`env.ml:781-813`). AGENTS.md already classifies these as
   approximations of `components_of_module_maker` caching.
3. Replace the process-global `NEXT_ENV_ID` with a `TypeContext`-owned
   counter (it exists only to key abbrev-cache checks within one
   compilation).

**Evidence.** `env_setup` and `signature_extract` are outside the phase
timers: fresh per-module `overhead_ms` sums to 3.03 s serial (0.93 ms per
module), and for the 80 % of modules that finish in <5 ms it is ~40 % of
their cost (§5). `register_sig_types_recursive` runs twice for aliased units
and walks nested submodules; `Stdlib` is ~100 submodules. The same
dependency components (`ReactEvent.*`, `Jotai.Atom`, `TellaStd.*`, …) are
re-qualified hundreds of times across modules. Env family is 23–25 % of
samples across typecheck *and* raw lowering. OCaml builds a persistent
unit's components from `Env.empty`/`Subst.identity` (`env.ml:669-678`),
but clears them at the next compilation's `init_path`. That construction
root alone does not establish cross-unit binder or mutation independence.

**Effect.** Serial: −1.5 to −2.5 s (the whole per-module tax plus the
repeated qualification work). Inflation: removes one contended atomic
per Env mutation and a large share of per-module `String` key allocation.
Chain: every module starts typechecking without the prelude tax.

**Contract.** The implicit opens' components must be forced in the same
order and with the same captured env/subst as `res_compmisc.ml:48-63` +
`env.ml:1874-1877`, including per-unit binder identities and stamp
consumption. A frozen template must not skip those effects. Lookup fallbacks
currently served by the string registries must be
proven unreachable or re-expressed as Env/component lookups — this is
parity-debt removal, so it may briefly move parity numbers; per AGENTS.md,
verified OCaml-aligned changes are kept and the fallout is fixed forward.

**Size.** Substantial: separate shared templates from unit-local lazy
substitution views, then remove redundant registries. The original "mostly
deletion plus a cache" estimate understated the ownership work.

### D. Backend on indexed arenas, end to end

**Borrowed from:** OXC/SWC arena-owned IR with `u32` node ids and no
per-pass reconstruction; the campaign's own M1–M5 work.

**Mechanism.** Finish M6 (indexed `LambdaCompiler` consumer, CMJ beta at the
application site into the same store, no final materialization), then:
lower `RawLambda` directly into the indexed store from `convert.rs` (no
recursive `RawLambda` at all — `translcore` output goes straight to node
ids, with `matching.rs` producing action ids); give `js_ir` the same
treatment (`Expression` 256 B → ~24 B hot node, comments/locations in side
tables); print into one pre-sized `String`/`Vec<u8>`. Keep every OCaml pass,
order, smart constructor and identifier allocation as the indexed passes
already do.

**Evidence.** 5.45 s serial (raw 2.4 + opt 1.3 + codegen 1.7), 464 B
`Lambda` / 256 B `Expression`, backend memmove and allocation samples, 14
tree rebuilds. Retention data for the indexed store (reachable vs
superseded generations) is measured by the existing `storage_measurements`
and must gate activation — appending a new generation per pass can retain
more than the recursive tree it replaces.

**Effect.** Serial: −1.5 to −2.5 s if the whole backend runs in one store
(halving it is the realistic scenario). Inflation: fewer bytes, fewer
allocations. Chain: none directly (backend is off the signature chain), but
it frees cores for chain work.

**Size.** M6 is the remaining large piece (general dispatcher, control-flow
families, grouped entry, fatal-warning gate, source locations), then two
further arena migrations. It should be sequenced *after* A/B/C because those
change the `typeopt` and Env costs that raw lowering currently pays, and
because the same team cannot land two 30K-line refactors at once.

### E. Parallel-inflation fixes and heterogeneous-core placement

**Borrowed from:** rustc's parallel-compiler guidance (worker-local
allocation, avoid shared atomics/locks in hot paths); Apple's QoS-based
core placement.

**Mechanisms (each independently measurable):**
1. `NEXT_ENV_ID` → per-context counter (see C.3). Falsify with `perf`/
   `sample` before/after: contended `fetch_add` on one cache line from 12
   threads is a textbook scaling bug.
2. Interned `PathId` (B) removes `Arc<Path>` refcount traffic on registry-
   shared paths; until B lands, measure how many `Path::clone`s touch
   registry-owned `Arc`s.
3. Registry snapshots: pass `&ModuleRegistry` behind an `Arc` snapshot taken
   once per scheduling wave instead of cloning per work unit; the local
   provisional maps can be a tiny overlay struct.
4. Keep pre-JS and JS-finish of the same module on the same worker when the
   queue allows (thread-affine steal), so mimalloc frees stay thread-local
   and the moved `Lambda`/arena stays cache-warm.
5. **Critical-path QoS.** On 4P+6E hardware the OS decides core class by
   thread QoS. Run the top-priority (critical-path) units on
   `QOS_CLASS_USER_INITIATED` threads and background/JS-finish units on
   `QOS_CLASS_UTILITY`, via `pthread_set_qos_class_self_np` at unit start
   (or two rayon pools with different QoS). The measured chain is 1.62 s
   under parallel conditions vs 0.70 s with serial service times, the fresh
   profile shows phase inflation is uniform (hardware heterogeneity, §5), and
   the chain head `Layout__Types` goes from 574 ms to 1,463 ms under load.
   This is the cheapest experiment in the document and directly targets the
   third constraint. Pair it with a chain-aware JS-finish priority (§5,
   scheduler counters) rather than the previously rejected JS/typecheck flip.
6. Allocator: profile mimalloc's cross-thread free counts and page reuse
   (`MIMALLOC_SHOW_STATS`); consider per-worker arenas for `TypeContext`
   (B makes contexts a few large `Vec`s, which any allocator handles well).

**Effect.** Inflation 2.1× → ~1.4× is plausible with 1–4 plus B; item 5
attacks the chain directly. None of these change compiler semantics.

### F. Frontend pipelining

1. **Pipeline parse → typecheck.** Enqueue a module's pre-JS unit as soon as
   its own file and all its dependencies are parsed (dependency names are
   known from the AST). Removes most of the 0.3 s parallel barrier; with a
   1 s budget that is 20–30 %. PPX behaviour, dependency discovery and
   diagnostics order must be preserved (`rewatch/src/build.rs:409-450`).
2. **Interface-first.** For the 55 `.resi` modules the signature is
   published before the implementation is typechecked (already); make sure
   the scheduler prioritises `.resi` typecheck units above everything, since
   each unblocks dependents at near-zero cost.
3. **Not in scope: a persisted store.** The benchmark is a clean build, so
   reusing a previous build's frozen store, mmap-ed signatures, or cached
   JS is not a valid lever here. The runtime (107 modules) and the 225
   dependency modules must be compiled inside the 1 s like everything else;
   they are cheap only because A/C make them cheap, not because they are
   remembered.

### G. Measurement as a feature

- Emit a Chrome trace (`tracing-chrome`) from the existing `tracing` spans
  behind `RESCRIPT_TRACE=path.json`, so the critical path, per-unit
  `env_setup`/`signature_extract`/`drop` durations and worker idle gaps are
  visible in Perfetto without Jaeger.
- Split the untimed residual into named buckets (`EnvSetup`,
  `SignaturePrepare`, `SignatureExtract`, `ContextDrop`, `RegistryUpdate`)
  in `timing::Phase`.
- Add allocation counters per phase (mimalloc heap stats delta per unit).
- Keep the fixed-protocol paired runs (`scripts/measurement_rebaseline.py`)
  as the acceptance gate.

## 5. Fresh profile (2026-09-16, this branch head)

Release build of `d98b8b943` (bsc `f7c693e9…218c11`, rewatch
`eab60143…53d3d`), Tella pin `66a5edab…`, runtime = this worktree's
`packages/@rescript/runtime`, `RESCRIPT_RUNTIME`/`RESCRIPT_BSC_EXE` explicit,
`rescript clean` before every build, heavy-work lock held. Every build
compiled 3,248 modules. These are single instrumented runs plus a 3-run
screen, **not** the paired acceptance protocol; the historical fast stack A
is 4.60–4.65 s on the same corpus. Raw logs: `/tmp/perf-inv-*.{out,err}`,
analysis script `/tmp/perf-inv-analyze.py` (not committed).

**Headline.** `hyperfine`, 12 workers, 3 runs: **5.287 ± 0.090 s**
(5.197–5.376; user 38.3 s, sys 2.5 s). One worker, instrumented: **20.59 s**.

**Serial phases (w1).** total 20.59 s = recorded 15.98 s + **untimed 4.61 s
(22.4 %)**. Parse 1.53 s, typecheck 8.39 s (40.8 %), raw lowering 2.51 s,
Lambda optimization 1.46 s, GenType 0.33 s, codegen 1.75 s. Runtime
precompile: 107 modules in 94 ms.

**Where the untimed 4.6 s is.** Per-module `overhead_ms` (wall of the pre-JS
unit minus its timed phases: `TypeContext::new`, `initial_env`,
`PersistentEnv::from_registry`, implicit opens with their internalization and
registry walks, `includemod::compunit`, `normalize_signature_types`, the
GenType raw-signature copy, `serialize_pers_struct`, context drop) sums to
**3.03 s** across 3,248 modules: mean 0.93 ms, median 0.62 ms, p90 1.6 ms,
p99 5.0 ms, max 20.5 ms (`Net-NodeJs`, `Http-NodeJs`, `Css` — large binding
modules whose signatures are big). The other ~1.6 s is rewatch startup and
source scan (≈0.11 s), dependency analysis, JS-finish untimed work (registry
updates, path resolution, 0.26 s of file writes), channel/scheduler work and
payload drops.

**The fixed per-module tax dominates the typical module.** 2,590 of 3,248
modules (80 %) finish their pre-JS unit in under 5 ms serial. Together they
spend 2.40 s in typecheck and **1.63 s in untimed setup/teardown** — for the
typical Tella module, roughly 40 % of its cost is the fixed per-module
prelude/registry/drop work, plus the
warm-up part of typechecking (first lookups into freshly internalized
`Stdlib`/`TellaStd` components). This is the quantitative case for §4.C.

**Distribution and the chain head.** Typecheck per module p50 0.95 ms, p90
5.5 ms, p99 22 ms, **max 574 ms** (`Layout__Types`). Top pre-JS units
(serial wall / typecheck / raw lowering, ms): `Layout__Types` 729 / 574 /
143, `Service__PublicClip` 178 / 116 / 36, `UI__LayoutPickerStructured` 153 /
102 / 40, `Service__PublicClipLegacy` 124 / 82 / 26, `Schema__EditorEvents`
109 / 71 / 28, `LayoutDetail` 96 / 66 / 22, then a cluster of
`Editor__Timeline__*` at 60–70. `Layout__Types.res` is 12,875 lines / 456 KB
with **366 `@spice` annotations** and ~2,900 constructor lines — a
Spice-generated codec schema — and 25 other modules' JS units wait on its
metadata. Tella overall: 1,941 `@react.component`s and 4,548 `@spice`
annotations; JSX and Spice-generated code are the two dominant typing
workloads.

**Parallel (w12, instrumented).** Wall 4.80 s (4.69 s inside rewatch's own
timer). Summed thread time by phase, with inflation over serial: parse 3.16 s
(2.06×), typecheck 20.12 s (2.40×), raw lowering 6.12 s (2.44×), Lambda
optimization 4.33 s (2.95×), codegen 4.25 s (2.42×), GenType 0.84 s (2.56×),
per-module untimed 7.53 s (2.49×). `Layout__Types` typecheck: 574 ms serial
→ **1,463 ms** at 12 workers (2.55×); its pre-JS unit 1,694 ms.

**Correction to the inflation narrative.** Inflation is *uniform* across
phases that share nothing (the parser touches no compiler shared state, the
typechecker touches a lot), so the dominant cause is not phase-specific
contention. Twelve threads on 4 performance + 6 efficiency cores, with
efficiency cores running this pointer-heavy code at roughly 0.4–0.5× a
performance core, predicts ≈1.8–2.0× summed-thread inflation by themselves;
the residual ≈1.2–1.3× is the actual memory/allocator/contention share.
Two consequences: (1) "CPU seconds at 12 workers" must never be read as
work; the machine has ~6.5–7 P-core-equivalents; (2) a critical-path module
scheduled onto an efficiency core runs 2–2.5× slower, which is exactly the
`Layout__Types` observation and is the cheapest chain lever available
(§4.E.5).

**Scheduler counters (w12).** `scheduled_typecheck 3249`, `scheduled_js
3248`, `signature_ready 3248`, `max_ready_typecheck 885`,
`js_scheduled_while_typecheck_ready 3223` (99 % of JS units). The dispatch
loop pops a ready JS-finish unit before consulting the typecheck priority
heap, so with hundreds of signature-producing units ready, JS work always
takes the next free slot. SCRATCHPAD records that a naive flip (all typecheck
first) and a fixed `capacity/4` JS cap both *regressed* wall time — deferring
JS retains pre-JS payloads and delays JS metadata that other modules' JS
units wait on (`pending_js_dep`: `Layout__Types` 25, `EditorEvents` 17,
`Color` 14, …). The right policy is chain-aware, not a flip: give a JS unit
the priority of the highest-priority module waiting on its metadata, and
make critical-path *typecheck* units pre-empt only lower-priority JS.
Measure with the fixed paired protocol.

**Compiler counters (w12).** Lazy lookups: module 1.53 M hits, type 230 K,
value 65 K, constructor 28.6 K hits / 9.8 K scans (204 K items scanned),
child-component 36.6 K hits / 23.5 K scans (203 K items). Qualified
components 2.30 M hits / 121 K misses / 71 K registered; stored components
93 K cached, 17.7 K published. **Signature copies: 55,493 calls / 1.46 M
items** — `persistent_env.rs:3508` (identifier-freshening copy of a resolved
signature) 32,324 calls / 1.07 M items; `typecore.rs:31885` (component
qualification `prefix_idents`/`Subst` copy) 15,863 / 163 K;
`typecore.rs:32221` (persistent-root lookup copy) 3,495 / 171 K;
`driver.rs:15166` (GenType raw-signature copy) **3,199 / 40 K — one full
signature copy per module whether or not GenType is used**. Signature
qualification of persistent roots: 11,005 calls / 133 K items, dominated by
the *same* dependency components re-qualified in module after module
(`Jotai.Atom` 438×, `ReactEvent.Mouse` 319×, `BaseUI.Tooltip` 301×,
`ReactEvent.Pointer` 267×, `TellaStd.Response` 171×, …). In OCaml, a
persistent unit's components are built from `Env.empty` and `Subst.identity`
(`env.ml:669-678`, `1707`), but `Res_compmisc.init_path` resets that cache
between units. §4.A/C must therefore preserve per-unit substitution and
force effects while sharing context-independent storage. Sparse records: 10,421
large records, 4.74 M logical labels vs 35 K populated fields (already
active).

## 6. Sequencing

1. **E.1, E.5, G** (days): remove the global atomic, add QoS placement,
   add the trace exporter and residual buckets. These are small, measurable
   and de-risk everything after by making the chain and the residual visible.
2. **B** (weeks, one owner): POD nodes + interners + `Copy` descriptors.
   Land behind the full parity suites. This is the prerequisite for A's
   `Sync` store and the single largest serial-work reduction.
3. **A + C** (weeks): frozen shared store, prelude env, delete string
   registries. A and C are the same boundary (`find_pers_struct` →
   component forcing) and should be one design.
4. **D** (weeks): finish M6, then direct indexed lowering, then indexed JS IR.
5. **F** (days): pipelining, `.resi` priority.
6. Re-measure after each retained step with the fixed protocol; re-derive the
   §1 table. Stop and re-plan if serial work is not below ~10 s after 2–3.

Re-sequencing after step 1 (2026-09-16): a call-graph sample of the serial
build attributes ~23 % of the worker window to per-module teardown of
dependency state (`Env`, component caches, `TypeContext`), ~13 % to `Arc`
refcount traffic inside those drops, ~8 % to `find_pers_struct` and ~6 % to
the prelude `open_module`, against ~3 % for `TypeDesc` clone/drop. A is
therefore taken before B, scoped per worker thread so it needs no `Sync`
nodes; see [THREAD_TYPE_STORE.md](THREAD_TYPE_STORE.md).

Expected trajectory (serial work → parallel wall on this machine, with
inflation improving from 2.1× toward 1.3×): 19 s / 4.6 s → after 1–2: ~13 s /
~2.9 s → after 3: ~9 s / ~1.9 s → after 4: ~6.5 s / ~1.4 s → after 5:
~5.5 s / ~1.1–1.3 s. One second requires all of it plus a sub-second
critical chain on performance cores; it is a full-stack representation
change, not a tuning exercise, and nothing may be carried over from a
previous build.

## 7. What not to do (from the rejected experiments)

- Partial borrow/clone reductions inside the current representation
  (rejected: −102 ms serial, inconclusive parallel). Clone *counts* do not
  predict wall time while the representation stays pointer-heavy.
- Within-pass allocation reuse on recursive trees (rejected deep-flatten
  reuse: +90 ms).
- Scheduler policy tweaks: slots are 97 % occupied; there is nothing to
  reorder.
- More worker threads: +28 ms at 16 workers for +226 MB.
- Any lazy/force-suppression/path-spelling shortcut in the typechecker
  (AGENTS.md); every proposal above is a representation or ownership change
  with OCaml's algorithm, force order and identity semantics intact.
