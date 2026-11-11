# The shared world and the type checker core: design and staged plan

Status: design, nothing here is implemented. This document is the spec for the
stages in section F.

## 0. Summary

### The problem

A 3,735-module application (619,000 lines) builds at 455,000 lines per second
on a 10-core machine: about 123,000 retired instructions per source line, 76 G
instructions in total, so 1% of the build is about 0.76 G instructions. The
target is two million lines per second, about 28,000 instructions per line.
Type checking is 40% of the build (49,000 per line) and has to come down to
about 12,000.

The checker does not do more work than OCaml's. Its call counts of `unify`,
`instance`, `copy` and `expand_head` are within 20% of the OCaml compiler's.
The gap is the cost of each call and the fixed cost of each module.

### The rules

1. The generated JavaScript is the program the OCaml compiler emits.
2. The same programs are accepted and rejected, with the same diagnostics
   (text and location).
3. No intermediate representation is compared with OCaml: the typed tree,
   Lambda and identifier stamps may differ.
4. Compilations may share one world.
5. New code is built beside the old, with the old as the oracle, and switched
   over gradually. Trunk passes all tests and ships after every stage.
6. No new `unsafe`.

### The design in one page

**The world** is one store per build, readable from every thread without
locks:

- Names and paths are already interned process-wide (`name.rs`,
  `types/path.rs`). They stay.
- Variable-free types are interned in a **ground tier**: equal types have
  equal handles.
- Each module's exported, non-ground types live in **segments**: immutable
  pages published once through `OnceLock`, the mechanism `types/shared_store.rs`
  already uses.
- Exported types name other modules' items by absolute path, so a reference
  into another module needs no substitution copy. Substitution remains for
  module aliases (needed for diagnostics, see B.6), `include`, functor
  application and module-type instantiation, one item at a time, memoised in
  the world.

**The checker core** keeps the handle type (`TypeExprRef`) and the read API
(`TypeDesc`), so the backend, genType, the printer and the editor analysis do
not change. It changes what is underneath:

- A handle's two tag bits name its tier: scratch node, variable, ground,
  segment. Only variables (and row-field and mutability cells) are mutable.
  `repr` of a non-variable is a bit test, not a memory read.
- Every node carries flags computed at construction. A ground type is
  returned by `instance`, skipped by generalisation, level updates and the
  occur check, and compared by handle.
- Levels stay, on scratch nodes and variables only. They are not replaced by
  variable ranks: OCaml reports an escaping type constructor when it lowers
  the level of a *structure* node, and that decides which of two errors a
  program gets (C.4).
- A generalised type is a frozen term. Instantiation copies only the spine
  that holds quantified variables.
- An expected type that is a fresh variable is not created: the checker
  infers and lowers levels instead (C.9).
- An environment is a scope and a position in one append-only binding log.

Two refinements of the direction this design started from, both forced by the
code:

- **`typecore.rs` and `typemod.rs` (52,000 lines) are not rewritten.** They
  reach the type representation through a narrow waist: `typecore.rs` calls
  `set_desc` 6 times, `set_level` 3 times and `link_type` 4 times; everything
  else goes through about 60 `ctype` operations and the `TypeContext` read
  API. The new core is implemented behind that waist, selected per
  compilation. Their own cost (walking expressions is 25% of checking) is
  reduced in place, guided by profiles.
- **Publishing is not copy-free, and does not need to be.** Scratch nodes are
  single-threaded `Cell` storage interleaved with dead inference nodes. The
  exported non-ground nodes are copied once into a segment. That one copy
  replaces today's four (saving copy, portable encoding, decoding,
  internalisation) and the per-lookup copies. Ground nodes, 78% of the total,
  are never copied.

Also: the typed tree is already stored in flat per-module pools
(`types/tast_arena.rs`). Only its environment snapshots change.

### The stages

| # | Stage | Saving (share of today's build instructions, estimated) |
|---|---|---|
| P0 | Differential tooling and counters | 0 |
| P1 | Ground flag and fast paths on today's representation | 4-6% |
| P2 | Infer instead of unifying with a fresh variable | 1.5-2.5% |
| P3 | Publish straight into the shared pool; encode off the critical path | 2.5-3.5% |
| P4 | Process-wide component views; delete stamp replay | 2.5-3.5% |
| P5 | Absolute paths in exports; no lookup copies | 3-4% |
| P6 | Environment as a binding log | 3-4% |
| P7 | Term store and core switch (no behaviour change) | 0 |
| P8 | The new core operations | 4-6% when switched on |
| P9 | Switch on per package, then by default | 0 |
| P10 | Segments, export tables, one checker per worker | 2-3% |
| P11 | `typecore`/`typemod` walk cost, profile-driven | 4-6% |
| P12 | Delete the old core | 0 (code size) |

The estimates sum to 27-39% of the build against a needed 30% (37,000 of
123,000 instructions per line). They are estimates with a wide error; section
F says how each was derived.

## A. Survey of today's code

All paths are relative to `compiler-rust/src/`.

### A.1 How a type node is stored and mutated

A type is a `TypeExprRef(u32)` (`types/type_expr.rs`). Two tag bits select a
storage tier:

| Tag | Tier | Storage | Writes |
|---|---|---|---|
| top bit clear | compilation-local | `TypeContext::types` (`TypeNodes`) | in place |
| `STORE_REF_TAG` | worker store | `thread_store::ThreadTypeStore` | in place during a store build, else to overlays |
| `SHARED_REF_BITS` | shared pool | `shared_store::SharedGraph` pages | to overlays only |

A node is `TypeNode { desc: Cell<TypeDesc>, level: Cell<i32>, id: Cell<i32> }`
(`types/context.rs`), 32 bytes, in chunks that double in size and never move.
`TypeDesc` is a 24-byte `Copy` enum (a test asserts the size). Its payloads
are handles: `TypeRefList` and `TypeArgList` (ranges of an append-only list
pool), `RowDescRef`, `PackageLidsRef`, `AbbrevMemoRef`, `MutabilityRef`, and
`Path` (a pointer to a process-wide interned node).

Mutation, as in OCaml:

- `link_type` and `set_desc` overwrite a descriptor with `Tlink(target)`.
  Unification links variables, and also links one *structure* node to the
  other before it unifies their children (`unify_types` in `types/ctype.rs`),
  restoring the descriptor if the children fail.
- `set_level` lowers or raises a node's level.
- `repr` follows `Tlink` chains and compresses them. It reads the descriptor
  of every node it is called on.
- Row fields (`RowFieldRef`), object-field mutability cells (`MutabilityRef`)
  and abbreviation memos (`AbbrevMemoRef`) are separate mutable cells.

A write to a worker-store or shared node goes to a per-compilation overlay
(`store_desc_overlay`, `store_level_overlay`, `store_abbrev_overlay`,
`store_row_field_overlay`, and the `shared_*` equivalents, all
`thread_store::PagedOverlay`). Every read of such a node first consults the
overlay. `TypeContext` has about 100 fields; roughly a third exist for the
store tiers, their overlays and the replay records of A.5.

Backtracking uses `TypeMutationJournal` (`types/context.rs`): a trail of
`TypeMutation` entries (descriptor, compression, level, row field,
mutability, level counters). Logging is off unless a snapshot is live
(`TrailLogging`). `snapshot_type_state` and `restore_type_state` are the
entry points; C.6 lists the callers.

### A.2 Levels, generalisation and instantiation

`TypeContext` holds `current_level`, `nongen_level`, `global_level` and a
stack of saved levels. `begin_def`/`end_def` raise and lower the current
level; `typecore.rs` calls `begin_def` 42 times and `typemod.rs` 10 times.

Levels and identifier stamps share one number line. `init_def(stamp)` sets
the current level to the current identifier stamp, and `set_current_time`
sets the stamp counter from a level (`typecore.rs`, around local modules,
first-class module unpacking and locally abstract types, which also add 1000
to the level). `get_level_in_env` (`ctype.rs`) answers "at which level was
this type constructor bound" with the declaration's `type_newtype_level` or,
failing that, the binding time (stamp) of the path's head identifier. This is
how OCaml detects a type escaping its scope, and it is the one place where
stamp *order* is part of the type system. Stamp *values* are not.

- `generalize` / `generalize_rec` walk a type and set every node above the
  current level to `GENERIC_LEVEL`, including the nodes held by a
  constructor's abbreviation memo. `generalize_structure`,
  `generalize_expansive` and the `lower_nongen_*` family are variants.
- `update_level` lowers the level of every node above a target.
  `update_level_checked` is the environment-aware form: for a `Tconstr` whose
  constructor is bound above the target level it tries to expand the
  abbreviation, and fails with the escaping constructor otherwise. It runs
  under a snapshot and retries with expansion of parameterised constructors.
- `instance` builds a `CopyCache` and calls `copy_type_cached`: a node at
  `GENERIC_LEVEL` is copied, any other node is returned as is. There is no
  fast path for a type without variables: `instance` of `int => string`
  allocates three nodes and a parameter list.
- `binding_facts` (in `ctype.rs`) is an existing small-budget walk that
  answers "is the variable absent" and "is the type free of universal
  variables" before a variable is linked. It is the closest thing today to a
  flag, recomputed on every binding.

### A.3 The copy paths and who calls them

| Copier | What it does | Nodes per build | Main callers |
|---|---|---|---|
| `copy_type_cached` (`ctype.rs`) | instantiation: copies generic nodes | 4.95 M | `instance`, `instance_list`, `instance_parameterized_type`, `instance_constructor`, `instance_label`, `instance_poly` |
| `copy_lookup_type_expr_with_paths` (`typecore.rs`) | `Subst.type_expr`: copies every non-variable node, rewriting paths | 2.55 M | `copy_lookup_value_description_for_subst`, `copy_lookup_signature_for_subst`, `copy_lookup_module_type_for_subst`, `copy_type_expr_mapping_paths`; called from `env_lazy.rs` (`lookup_value_for_access_inner`, the component builders), `typecore.rs` module resolution, `typemod.rs`, `cmi/persistent_env.rs`, and `driver.rs` when a signature is saved |
| `subst_identity_copy` (`ctype.rs`) | `Subst.type_expr Subst.identity` | 0.60 M | `typecore.rs` (function bodies, coercions, results), `includemod.rs`, `moregeneral` |
| direct construction | `new_constr`, `new_arrow`, ... | 0.90 M | everywhere |
| fresh variables | `new_var` | 2.49 M | `typecore.rs` (84 call sites), `ctype.rs` (61) |

`copy_lookup_type_expr_with_paths` allocates a placeholder variable for
every node it copies, builds the copy, then links the placeholder to it. It
runs when a value of another module is first looked up through a component
view, because the stored signature names the module's own types by local
identifier and the view must name them by path (OCaml's `prefix_idents` and
`Subst`).

`type_application` (`typecore.rs`) creates two variables per application: one
as the expected type of the function expression, one that is unified with the
function's type only to lower its level. These are 0.71 M of the 2.49 M.

### A.4 Environments

`Env` (`types/env.rs`) is `{ id, scope_id, data: Rc<EnvData> }`. `EnvData`
holds one table per namespace: `IdTbl` for values, types, modules, module
components and module types, `TycompTbl` for constructors and labels, plus
functor arguments, local constraints, label families and flags.

- `IdTbl` is a persistent hash map (`im_rc::HashMap<Name, IdBucket>`), a
  linked list of the most recent bindings (`Recent`, moved into the map every
  16 additions) and a chain of opened layers (`IdOpened`).
- An `open` adds an `IdOpened` layer per table. The layer tables of one
  opened signature are built once (`OpenedLayers::build`) and attached with
  `add_prebuilt_open_layers`.
- Every extension clones the `Env` and gets a new `id`; `scope_id` changes
  only when module-level bindings change, and keys the resolution caches.
- A lookup reads the recent list, then the map, then each opened layer.
- The typed tree stores an `EnvRef(u32)` per node; `TypeContext::typed_envs`
  is a `Vec<Rc<Env>>` de-duplicated by `id` (`store_typed_env`). These
  snapshots keep every version of the persistent maps alive until the module
  is torn down. Dropping them is 0.98% of the build
  (`docs/DEPENDENCY_COMPONENTS.md`).

### A.5 How a dependency's signature becomes visible

1. **Save.** After type checking, `driver.rs`
   (`compile_preprocessed_structure_in_process_until_js`) copies the
   signature twice with `copy_lookup_signature_for_subst` (one copy as the raw
   signature genType reads, one to finalise paths), and registers it with
   `PersistentEnv::register_in_memory_signature`.
2. **Encode.** `extract_module_update` calls
   `portable_types::serialize_pers_struct`: it walks the signature into a
   `PortableTypeGraph`, computes a stamp-independent fingerprint
   (`compute_type_graph_fingerprint`) and encodes the result
   (`binser::Encoded`). The decoded form is kept once for the first dependent
   (`ReservedSignature`).
3. **Publish.** The signature-ready hook hands the `PortablePersStruct` to
   the build system (`apply_signature_ready` in `rewatch/src/build/compile.rs`),
   which registers it in the `ModuleRegistry` and unblocks dependents.
4. **Internalise.** The first compilation that needs the unit calls
   `internalize_pers_struct`: once per build into the shared pool
   (`SharedTypePool::pers_struct` and `publish`), or into the worker store or
   the compilation when the graph is not shareable.
5. **Component views.** A lookup `M.x` builds a `QualifiedModuleComponents`
   (`types/env_lazy.rs`) for the access path, lazily, per name
   (`force_entry`). Views of persistent-rooted paths are built as *store
   builds* (`TypeContext::build_in_store`) into the worker store and shared by
   later compilations on that worker.
6. **Replay.** A store build records a `StorePiece`: the identifier stamps it
   consumed and the registrations it made (`StoreEffect`). A compilation that
   reuses the view replays the piece (`touch_store_piece`) so that its own
   stamp counter advances as OCaml's would. `StoreStampOrigins` maps store
   stamps back to local ones when a signature is saved.
7. **Lookup copy.** `lookup_value_for_access_inner` copies the value's type
   with `copy_lookup_value_description_for_subst` and applies the component
   substitution (`build_value_subst_maps`).

Measured: lookups in other modules 4.9% of the build, publishing 4.6%.
`docs/DEPENDENCY_COMPONENTS.md` measured each view being built about 4.2
times (once per worker that needs it), `build_in_store` at 3.5% and replay at
1.2-2.1%.

Steps 5 and 6 exist to reproduce OCaml's stamps. Under rule 3 they are no
longer required.

### A.6 Per-module setup and teardown

Setup (1.1% of the build): `fresh_type_context` (a new `TypeContext` and
`IdGenerator`, a store lease from `thread_store::current`),
`in_process_type_check_context` (`TypeCheckContext::new`, `initial_env`,
`PersistentEnv::from_registry`, load paths, `load_pervasives`), and
`ModuleRegistry::for_worker_snapshot`.

Teardown (about 2.5%): dropping `typed_envs` (0.98%), the `TypedArena`
(0.45%), the type node chunks, the overlays and about 40 hash maps.
`docs/DEPENDENCY_COMPONENTS.md` found that reusing the containers alone does
not pay, because the cost is their contents. This design removes the
contents (persistent-map nodes, per-node allocations) first and reuses the
containers second.

### A.7 What reads the checker's results

| Reader | Reads |
|---|---|
| Lambda lowering (`raw_lambda/convert.rs`, `matching.rs`, `typeopt.rs`) | the typed tree; `exp_type`/`pat_type` through `TypeContext`; `exp_env`/`pat_env` to expand types and find declarations (36 uses); `typeopt_answers` memo |
| Pattern analysis (`types/parmatch.rs`) | typed patterns, declarations, `instance`, `expand_head` |
| Diagnostics (`types/printtyp.rs`, `driver.rs`, `driver/type_clash.rs`) | types by structure and by variable identity; levels of variables; environments for path printing |
| genType (`gentype/`) | the typed tree, the saved signature and the raw signature (`gentype_raw_module_sigs`), one environment use |
| Editor analysis (`analysis/`, `rewatch/src/build/tooling.rs`) | `ToolingTypedModule`: the `TypeContext`, the typed tree and its arena, type-checked on demand in a watch session. Builds write no `.cmt` files |
| Incremental build (`cmi/item_deps.rs`, `rewatch/src/build/state_db.rs`, `incremental.rs`) | the fingerprint; `SignatureSummary` (per-item digests and references); `UnitRead`s collected from the typed tree; the encoded `PortablePersStruct` in the state store |
| Dependents | the signature, through A.5 |
| Typed-tree and Lambda dumps (`types/sexp_typedtree.rs`) | everything, including node ids; diagnostics only |

All of them read types through `TypeContext` accessors (`repr`, `get_desc`,
`get_level`, `type_list`, `type_args`, `row_desc`). None mutates a type
except diagnostics, which marks and names nodes in its own tables.

## B. The world

### B.1 What is shared and what is not

| Data | Lifetime | Written by | Read by |
|---|---|---|---|
| Names, paths | process | any thread, under a shard lock | any thread, lock-free |
| Ground types | build (watch: session) | any thread, under a shard lock | any thread, lock-free |
| Segments (a unit's non-ground exported types, declarations, layouts, locations) | until the unit is recompiled | the unit's checker, published once | any thread, lock-free |
| Unit export tables | same | published with the segment | any thread, lock-free |
| View items (substituted items) | build | first thread to need one | any thread, lock-free |
| Scratch (inference nodes, variables, trail, binding log, typed tree) | one module | one worker | that worker, and the backend for that module |

### B.2 Handles

`TypeExprRef` stays a `u32`. In the new core the two top bits are the tier:

| Bits 31..30 | Tier | Payload (30 bits) | Mutable |
|---|---|---|---|
| `00` | scratch node | index into the compilation's node array | no |
| `01` | variable | index into the compilation's variable table | yes |
| `10` | ground | index into the world's ground tier | no |
| `11` | segment | page number (20 bits) and offset (10 bits) | no |

The old core uses the same bits for its own tiers. A `TypeContext` is in one
mode for its whole life (E.1), so the meanings never mix.

Limits: 2^30 nodes per tier. The benchmark allocates 11.5 M nodes in total
across all modules; the ground tier holds about 60,000.

### B.3 The ground tier

```rust
/// One interned variable-free type.
struct GroundNode {
    desc: TypeDesc,   // children are ground handles; lists live in `lists`
    hash: u32,        // structural hash, fixed seeds
    flags: TypeFlags, // see C.2
}

pub struct GroundTier {
    /// Chunk k holds 1 << (10 + k) slots; chunks never move.
    chunks: [OnceLock<Box<[OnceLock<GroundNode>]>>; 20],
    /// Children lists and arrow parameter lists, same layout.
    lists: ChunkedOnce<Box<[TypeExprRef]>>,
    args: ChunkedOnce<Box<[TypeArg]>>,
    next: AtomicU32,
    /// 64 shards; each maps a structural hash to candidate indices.
    shards: Box<[Mutex<hashbrown::HashTable<u32>>]>,
}
```

Interning `desc`:

1. Compute the structural hash from the constructor, the path's
   `same_hash`, labels and the children's handles (children are already
   interned, so the hash is shallow).
2. Probe a per-worker direct-mapped cache (`[Cell<(u32 hash, u32 index)>;
   8192]`), as `types/path.rs` does. On a hit, compare the descriptor
   shallowly and return.
3. On a miss, lock the shard. If an equal node exists, return it. Otherwise
   take the next index, write the slot with `OnceLock::set`, insert the index
   in the shard table, unlock.

Why this is safe without `unsafe`: a slot is written through `OnceLock`
before its index is visible. An index becomes visible either through the
shard table (the reader took the same mutex after the writer) or through a
published segment or export table (published after the writer finished). A
reader therefore never sees an unwritten slot, and `OnceLock::get` returns a
plain shared reference.

Cost, stated: `OnceLock<GroundNode>` adds its state word to each slot (4 or 8
bytes depending on the platform) and one atomic load per read. With 60,000
nodes the memory is under 3 MB. The benchmark constructs 3.83 M ground nodes
for 60,000 distinct types, so about 98% of constructions end at step 2
without a lock. A lock-free append-only pool with plain slots cannot be
written safely; this is the structure chosen instead.

What is *not* interned: a type that contains a variable, a universal
variable or `Tpoly`, a row or object with a row variable, a recursive type
(it is built through a variable, see C.5), or a constructor bound inside an
expression (C.2, `SCOPED`).

A ground type may name a type of the module being compiled by its local
identifier (`Pident t`). Two modules can intern the same such node (same
name, same stamp). That is harmless: a node carries no declaration, and
every table keyed by ground handle that depends on declarations is per
compilation (C.7).

### B.4 Segments and publication

```rust
/// Immutable exported data of one unit. Built by one checker, then frozen.
pub struct Segment {
    unit: UnitId,
    pages: Box<[u32]>,               // global page numbers, in order
    nodes: Box<[SegNode]>,           // desc + level (generic or not) + flags
    lists: Box<[TypeExprRef]>,
    args: Box<[TypeArg]>,
    rows: Box<[RowDesc]>,            // row fields resolved, no cells
    lids: Box<[Vec<Longident>]>,
    layouts: Box<[Layout]>,
    locations: DeclLocTable,
}

pub struct World {
    generation: u64,
    ground: GroundTier,
    /// Page number -> the segment that owns the page (as `SharedPages` today).
    pages: Box<[OnceLock<Arc<Segment>>]>,
    next_page: AtomicU32,
    /// Dense unit id (assigned by the build plan) -> exports.
    units: Box<[OnceLock<Arc<UnitExports>>]>,
    unit_ids: Mutex<AHashMap<Name, UnitId>>,   // only for units the plan did not know
    views: ViewTable,                          // B.6
}
```

A segment handle is a global index: `page << 10 | offset`. A reader resolves
it with one `OnceLock` load and two array reads, as `shared_store::page_node`
does today.

Publication of unit `M`, after its structure is type-checked and its
signature is final:

1. **Export copy.** Walk the signature. A ground type is kept (after step
   2). Any other node is copied into a `Vec<SegNode>` owned by the checker:
   variables are resolved, generic variables become generic `Tvar` nodes of
   the segment, row-field cells are resolved into the row. Sharing is kept
   with a map from scratch handle to segment handle. Pages are reserved from
   `next_page` as the vector grows.
2. **Absolute paths.** While copying, an identifier of one of `M`'s own
   items becomes `Pdot(Pident M, name)`; nested modules give longer paths.
   Ground types that mention such identifiers are re-interned with the
   rewritten paths, memoised per ground handle for the publication.
3. **Export table.** Build `UnitExports` (B.5).
4. **Digests.** Compute the interface fingerprint and the per-item digests by
   hashing the export table. Ground types contribute their stored structural
   hash; segment nodes are hashed by structure. Neither reads a handle value
   or a stamp.
5. **Freeze.** Wrap the vectors in `Arc<Segment>`, set every reserved page
   slot, set the unit's slot in `units`. From here the data is never written.
6. **Signal.** Send the fingerprint and digests to the build system, which
   unblocks dependents.
7. **Encode, later.** The digest thread (`DigestPrep` in
   `rewatch/src/build/compile.rs`) produces the portable encoding for the
   incremental store from the frozen segment. No dependent waits for it.

The export copy is the only copy. It visits the non-ground part of the
signature once. Today the same nodes are copied by the two saving copies,
the portable encoding, the decode or the reserved decoded form, the
internalisation, and again on each first lookup per worker.

How many nodes the export copy visits is not measured. An upper bound is the
0.60 M identity-substitution copies plus the share of the 2.55 M lookup
copies that are not ground (22% by the overall ratio, 0.56 M). At about 60
instructions per node that is under 0.1% of the build.

Segments are self-contained: a segment node refers only to its own segment
and to the ground tier. If an exported type reaches a non-ground node of
another unit's segment (a re-exported value whose type holds a row), the
export copy copies it. This is what makes a segment retirable (B.7) and
encodable on its own.

### B.5 Export tables and item identity

```rust
pub struct UnitExports {
    unit: UnitId,
    name: Name,
    segment: Arc<Segment>,
    root: ModuleExports,
    fingerprint: u64,
    item_digests: Box<[(Kind, Name, u64)]>,
    deprecated: Option<Box<str>>,
}

/// One structure signature: the unit itself or a nested module.
pub struct ModuleExports {
    path: Path,                         // absolute
    items: Box<[SignatureItem]>,        // in signature order, absolute paths
    values: NameIndex,                  // name -> (item index, runtime position)
    types: NameIndex,
    constructors: NameMultiIndex,       // name -> descriptions, newest first
    labels: NameMultiIndex,
    modules: NameIndex,                 // -> nested ModuleExports or alias target
    modtypes: NameIndex,
    children: Box<[ModuleExports]>,
}
```

`NameIndex` is an immutable hash table keyed by `Name` (pointer equality,
content hash), built once at publication. This is what `SignatureIndex` and
the lazily forced tables of `StructureComponentTables` compute today, per
worker and per name.

The identity of an exported item is its absolute path. `Path` is already
interned with a precomputed `same` class, so comparing two type constructors
is a pointer comparison. Finding the declaration of `M.N.t` is: unit table
read for `M`, then one `NameIndex` probe per path component. A per-worker
direct-mapped cache from path to declaration removes the probes on repeated
lookups.

Constructor and label descriptions are built at publication, not on first
lookup: they are a function of the declarations.

### B.6 Where substitution remains

Reading `M.x` where `M` is the unit's own name needs no substitution: the
stored type already says `M.t`.

| Case | Why a substitution is needed | Granularity | Memo |
|---|---|---|---|
| Module alias `module A = B`, including the alias modules of a namespace | OCaml prints and compares the types of `A.x` as `A.t` (the components of `A` are prefixed with `A`, and `A.t` has the manifest `B.t`). Diagnostics would otherwise print `B.t` | one item on first use | `ViewTable`, world |
| `include M` | the included items get new local identifiers; types keep naming `M.t` through manifests | one signature, in the including compilation | scratch |
| Functor application `F(X)` | parameter replaced by argument, generative types renamed | one item on first use | `ViewTable` when `F` and `X` are both absolute paths, else scratch |
| Module type instantiation (`module N: S`, `S with type t = ...`) | fresh identifiers per use | one signature | scratch |
| First-class module unpacking | fresh scoped identifiers | one signature | scratch |

```rust
struct ViewKey { root: Path /* same-class */, source: ItemId, kind: ViewKind }

pub struct ViewTable {
    shards: Box<[Mutex<AHashMap<ViewKey, Arc<OnceLock<ViewItem>>>>]>,
}
```

The first thread to need a view item computes it, copies its non-ground
nodes into a small segment and publishes it; other threads asking for the
same key wait on the `OnceLock` and then read it. The result is a function
of the key alone. A view build that would have to read compilation-local
state (a local alias of a local module) is not a world view: it stays in
scratch.

This replaces the per-worker view tables, `build_in_store` and the replay of
`StorePiece` (A.5 steps 5 and 6).

### B.7 Memory lifetime

One-shot build: the world lives until the process exits. The process may
exit without tearing it down (`enable_cli_cleanup_skip` already exists in
`driver.rs`).

Watch mode: the world persists across builds behind an `RwLock`. Builds and
editor queries hold it for reading. Between builds, with the write lock, the
driver retires the units it is about to recompile: it takes their page slots
and unit slots (`OnceLock::take` needs `&mut`, which the write lock gives)
and returns the pages to a free list. A unit that is not recompiled keeps
its segment and its page numbers, so nothing is internalised again. Today
every build re-internalises every unit it touches (`begin_build` bumps the
generation and discards the stores).

Why retiring is sound: a segment refers only to itself and the ground tier
(B.4), and a dependent holds no handle into another unit's segment after its
own publication. A dependent that is not recompiled can therefore not hold a
handle to a retired page.

The ground tier and the view table grow monotonically within a session, as
names and paths already do. Bound: when the ground tier exceeds a threshold
(say four times its size after the first full build), the next build starts
a new world and re-internalises units from their encoded form. View items
are dropped whenever one of the units in their key is retired.

### B.8 Determinism

Claim: the JavaScript, the diagnostics and the stored artefacts do not depend
on the number of workers or on which worker checked which module.

1. What a checker reads from the world is a function of content, not of
   timing. A unit's exports are a function of its source, its options and
   the exports of its dependencies (induction over the dependency order). A
   view item is a function of its key. A ground node is a function of its
   structure.
2. What varies with scheduling is handle *values*: ground indices, page
   numbers, view segment pages. So handle values must never reach output.
   The rules that enforce this:
   - No ordering by handle. `TypeExprRef` has no `Ord` today; it stays that
     way.
   - A table keyed by handle is used for lookup only. Any iteration that can
     reach output iterates a `Vec` in insertion order or sorts by a
     structural key. Names and paths already follow this rule (their hashes
     use content, never addresses).
   - Digests and encodings use structural hashes and positions within the
     encoded unit, never handles.
   - Printing names variables by traversal order (D.1), never by handle.
3. Identifier stamps of the compilation are allocated by its own counter and
   depend only on its own source and on nothing in the world (P4 removes the
   replay that tied them to shared data).
4. A debug mode (`RESCRIPT_WORLD_SHUFFLE=<seed>`) permutes ground index
   allocation and page numbers. CI runs the parity suites once with it. The
   existing rule "output must not depend on thread count" is checked by
   building the benchmark with 1 and with 10 workers and comparing outputs.

## C. The checker core

### C.1 The waist

The new core is not a new type checker. It is a new implementation of two
interfaces that the rest of the compiler already uses:

- **Storage**, on `TypeContext`: `repr`, `get_desc`/`borrow_desc`/`with_desc`,
  `get_level`, `type_list`, `type_args`, `row_desc`, `package_lids`,
  `row_field`, `mutability_repr`, the constructors (`new_var`, `new_constr`,
  `new_arrow`, `new_tuple`, `new_poly`, ...), `begin_def`/`end_def`/`init_def`,
  `snapshot_type_state`/`restore_type_state`.
- **Operations**, in `ctype`: `unify` and its modes, `instance*`,
  `generalize*`, `update_level*`, `expand_head*`, `try_expand_head`,
  `full_expand`, `occur*`, `moregeneral`, `equal`, `matches`, `subtype`,
  `enlarge_type`, `nondep_type`, `filter_arrow`-style helpers, the `subst_*`
  copies.

`typecore.rs`, `typemod.rs`, `includemod.rs`, `includecore.rs`, `parmatch.rs`,
`printtyp.rs`, the backend and the tools sit above the waist and are shared
by both cores. The few places above the waist that write a descriptor or a
level directly (6 `set_desc`, 3 `set_level` and 4 `link_type` calls in
`typecore.rs`; 9, 1 and 1 in `typemod.rs`; 2 `set_desc` in `includemod.rs`; 1
in `printtyp.rs`; 12 in `cmi/persistent_env.rs`) are first turned into named
`ctype` operations (stage P7), so that the waist is closed.

Why not rewrite the layers above: they hold the behaviour that makes
diagnostics match (each function cites the OCaml code it reproduces), they
are five times the size of the core, and nothing in the measurements says
their *algorithm* is the problem. Their cost is in how they call the core
and in clones, reference counts and temporary vectors, which stage P11
removes in place.

### C.2 Terms and flags

Tiers are in B.2. A scratch node:

```rust
struct ScratchNode {      // 32 bytes
    desc: TypeDesc,       // 24 bytes; never Tvar, never Tlink
    level: Cell<u32>,     // see C.4
    flags: TypeFlags,     // u8, fixed at construction
}

struct VarSlot {          // 8 bytes
    binding: Cell<TypeExprRef>,   // 0 = unbound
    level: Cell<u32>,
}
```

Variable names (`Tvar(Some(name))`) are sparse: a side vector of `(var index,
Name)`, sorted by construction. `get_desc` of an unbound variable handle
returns `TypeDesc::Tvar(name)`, so readers see what they see today.

Flags, computed when a node is constructed, as the union of the children's
flags plus the node's own:

| Flag | Set when the type contains | Used by |
|---|---|---|
| `HAS_VAR` | a variable handle (bound or not), or a row or object tail that is a variable | everything: a node without it is *ground* |
| `HAS_UNIVAR` | `Tunivar` or `Tpoly` | `occur_univar`, `instance_poly`, the univar-escape checks |
| `HAS_SCOPED` | a constructor, row name or package path bound inside an expression (see below) | `update_level`, escape checks |
| `HAS_ROW` | `Tvariant`, `Tobject`, `Tfield` | printing (D.2), the row unifier |
| `HAS_LOCAL_IDENT` | a path whose head is a local (stamped) identifier | publication (B.4 step 2), expansion memo scope (C.7) |

"May need expansion" is deliberately not a node flag. Whether `p<args>`
expands depends on the declaration of `p`, which for a local identifier
depends on the compilation and, during a recursive type definition, on the
moment. It is a memoised per-path fact (C.7).

`HAS_VAR` is conservative and monotone. A node built over a variable that
is later bound to a ground type keeps the flag. That costs a slow path, not
correctness. Generalisation and the export copy rebuild such types, and the
rebuilt node is ground.

**`HAS_SCOPED`.** A ground type skips level updates (C.4). That is only sound
if lowering its level could never have failed or expanded anything. OCaml
fails or expands when a `Tconstr` path's binding level is above the target
level. For a path rooted in another unit the binding level is 0. For a type
declared by a structure item of the module being compiled, the binding time
is below every level in use afterwards, because `type_structure` calls
`init_def` with the current stamp at each item (`typemod.rs`). The remaining
paths are those bound *inside an expression*: local modules, locally
abstract types, unpacked first-class modules, existential types of GADT
constructors. The rule:

> A `Tconstr`, a row name or a `Tpackage` sets `HAS_SCOPED` when the binding
> time of its path's head identifier is greater than the *item floor*: the
> level `init_def` set at the start of the current structure item.

A type with `HAS_SCOPED` is never ground-interned and never skipped.

This rule is the single most delicate invariant of the design. It is
protected by a debug check: in debug builds, and in the differential mode of
E.2, every skipped `update_level` runs the full walk on the side and asserts
that it would neither fail nor expand.

### C.3 Variables and the trail

A variable is an index into `vars: Vec<VarSlot>` of the compilation. Binding
is `vars[v].binding.set(t)`. `repr`:

```rust
fn repr(&self, mut t: TypeExprRef) -> TypeExprRef {
    while t.is_var() {                       // tag test, no memory read
        let b = self.vars[t.var_index()].binding.get();
        if b.is_null() { return t; }
        t = b;
    }
    t
}
```

Today `repr` loads the descriptor of every node to test for `Tlink`. Most
calls are on structure nodes, for which the new `repr` touches no memory.

Structure nodes are never linked. OCaml links two structure nodes when it
unifies them; C.5 covers what that was for.

Universal variables (`Tunivar`) are scratch or segment nodes, not variable
slots: they are never bound, and their identity is their handle.

The trail keeps the shape of `TypeMutationJournal`, with fewer entry kinds:

```rust
enum Trail {
    Bind(u32),                       // variable index; undo = unbind
    VarLevel(u32, u32),              // variable, old level
    NodeLevel(u32, u32),             // scratch node, old level
    RowField(RowFieldRef, Option<RowField>),
    Mutability(MutabilityRef, FieldMutability),
    Levels { current: u32, nongen: u32, global: u32 },
}
```

Entries are pushed only while a snapshot is live. Path compression of
variable chains is done only when no snapshot is live, so it needs no trail
entry (OCaml logs compressions for the same reason: a compressed chain would
survive the undo of the binding it skipped).

The dense table makes one more thing cheap: a snapshot is the trail length
plus the lengths of the node and variable arrays, and restoring truncates
them.

### C.4 Levels

Levels stay, with OCaml's meaning, on scratch nodes and variables. Ground
and segment nodes have no level cell:

| Tier | `get_level` returns | `set_level` |
|---|---|---|
| ground | `GENERIC_LEVEL` | not called (asserted) |
| segment | the frozen level (`GENERIC_LEVEL` for an exported scheme) | not called |
| scratch, variable | the cell | writes, trailed |

Why not variable ranks only. With ranks, a structure node has no level, and
the scope-escape check moves to the moment a variable is bound. OCaml checks
earlier: `unify` lowers both sides to the lower of their two levels before
it compares their structure (`update_level_checked` in `unify_types`), and
that can raise the escape error on a *structure* node. Unifying `(int, int)`
at an outer level with `(M.t, int)` built inside the scope of a local module
`M` reports "the type constructor `M.t` would escape its scope" in OCaml; a
rank-based checker would report a mismatch between `int` and `M.t`. Both
reject, but the diagnostic differs, which breaks rule 2. Keeping node levels
on the scratch tier reproduces OCaml exactly and costs four bytes per
scratch node. The saving comes from the ground skip, not from removing
levels.

Why skipping ground types is unobservable. A ground type holds no variable,
so no generalisation decision depends on its level. It holds no scoped
constructor, so lowering it cannot fail or expand (C.2). What remains is
whether `instance` copies it or shares it, which only changes node identity;
C.5 and D.2 cover identity.

The rules, for a type `t` with `repr` applied:

- `generalize(t)`: return if `t` is ground or segment; else as today.
- `update_level(l, t)` and `update_level_checked`: return if `t` is ground
  or segment; else as today, including the snapshot and retry.
- `instance(t)`: return `t` if it is ground, or if it is a scratch node
  below `GENERIC_LEVEL` (as today); copy otherwise, and stop at any ground
  child.
- Abbreviation memos attached to constructor nodes are replaced by C.7, so
  `generalize` has no memo chain to walk.

### C.5 Unification

`unify(t1, t2)` after `repr`, in this order:

1. Same handle: done. For two ground types this is the common success
   (0.88 M of 3.09 M top-level unifications are structurally identical ground
   types).
2. Both ground, different handles: they are equal only up to abbreviation
   expansion. Call `ground_equal(env, t1, t2)` (C.7). It mutates nothing. If
   it fails, build the error trace by running the general structural walk of
   step 5 on the two types, which mutates nothing either because neither
   side has a variable.
3. One side an unbound variable `v`, the other ground (1.16 M of 3.09 M):
   bind. No occur check (a ground type cannot contain `v`), no level update,
   no univar check (`HAS_UNIVAR` is clear). If the other side is not ground,
   the checks run as today, each skipping ground subtrees and each skipped
   outright when the flag it looks for is clear.
4. Both unbound variables: as today (levels merged, one bound to the other).
5. Two structure nodes, at least one not ground: lower both to the lower
   level (`update_level_checked`, skipping ground), expand if the heads
   differ, then unify children in OCaml's order: arrow parameters left to
   right, then the result; tuple elements left to right; constructor
   arguments left to right, with the variance-aware handling in
   `unify_same_path_constructor_args` kept as is.

**No structure links.** OCaml links `t1` to `t2` before unifying their
children and restores `t1` if they fail. The link does three things:

- It terminates unification of recursive types. The Rust port already has a
  pair table for this (`UnifyState::already_unified`, `mark_unified`). The
  new core consults it only when both sides have `HAS_ROW`, since a
  recursive type must pass through an object or a variant.
- It shares structure for later speed. Interning does that better.
- It makes the two nodes one node. That is visible only through node
  identity, which the checker reads in one place that reaches output: the
  printer's loop detection, covered in D.2.

**Abbreviations, private types.** Unchanged in behaviour: when the heads
differ, expand the side OCaml expands first (`expand_head_unif`), honouring
private abbreviations (`generic_private_abbrev`, `expand_head_opt`), and
retry. Expansion results come from C.7.

**Records and variants, inline records.** Nominal: a `Tconstr`. Their
unification is path equality plus arguments. Inline records are declarations
attached to a constructor (`TypeInlinedType` in `types/decl.rs`); their types
are ordinary `Tconstr` nodes with a synthetic path. Nothing changes.

**Objects and polymorphic variants: a mutable tier, not row binders.** Rows
keep OCaml's representation: an immutable `RowDesc` whose `row_more` is a
variable, `Reither` fields that hold a mutable link cell (`RowFieldRef`), and
object fields as a `Tfield` list ending in a variable or `Tnil`, with
`MutabilityRef` cells. The cells are dense per-compilation tables with trail
entries, as they are today. `unify_rows`, `unify_row_field`,
`unify_object_fields` and `unify_mutability` are ported onto the new storage
with their logic unchanged.

The alternative, immutable rows with explicit row binders and substitution,
would be cleaner, but OCaml's semantics for conjunctive `Reither` fields,
`row_fixed`, `row_name` and the `[> ]`/`[< ]` bounds are defined by the order
of in-place updates, and the printed form of a row depends on them. The
benchmark's types are 78% ground; rows are a small part of the rest. Choosing
the mutable tier gives up nothing measurable and keeps the highest-risk
diagnostics untouched.

A closed, static row with ground field types and no row variable is ground
and is interned. An object type with no row variable (`Tnil` tail) and
ground fields is ground.

**Recursive types (`as 'a`).** A recursive type is built by creating a
variable, building the body over it and binding the variable to the body.
The body therefore has `HAS_VAR` and stays in scratch for its whole life,
even when it is closed. On export it is copied into the segment as a cyclic
set of segment nodes (the copy map handles the cycle). It is never
ground-interned: interning cyclic terms needs a canonical form for regular
trees, and the benchmark does not justify it. `deep_occur` and `occur` keep
their rule (a cycle is allowed only through an object or a variant).

**Polymorphic fields, `Tpoly`, universal variables.** Unchanged:
`enter_poly`, `unify_univar` and the `univar_pairs` stack in `UnifyState`.
A `Tpoly` in a declaration is a segment or scratch node; `instance_poly`
copies its body, replacing the bound universal variables, and stops at
subtrees without `HAS_UNIVAR`.

**First-class modules.** `Tpackage { path, lids, args }` is a structure node.
Two ground packages with the same handle are equal. Otherwise the existing
comparison through module-type equivalence runs (`package_longident_same_label`
and the inclusion check hook), which needs the environment and is unchanged.

**GADT-style local constraints.** ReScript reaches them: `add_gadt_equation`,
`reify`, `Env::local_constraints`, `trace_gadt_instances` and existential
constructors are all live code. An equation can only be added for a type
that is locally abstract or existential, and such a path always sets
`HAS_SCOPED` (C.2), so a type that mentions it is never ground and never
takes a fast path. In pattern mode (`UnifyMode::Pattern`) the general
algorithm runs as today. The expansion memo of C.7 is bypassed for any path
that has a local constraint in the current environment.

### C.6 Backtracking

Where the checker snapshots and restores today, all of which stay:

| Site | File and function | Why |
|---|---|---|
| Globalising used type variables | `typecore.rs`, `transl_type_globalized` | unify a global variable with a used one, skip on failure |
| Patterns | `typecore.rs`, `save_pattern_backtrack_state` / `restore_pattern_backtrack_state` | or-patterns and constructor disambiguation retries |
| Private abbreviations | `typecore.rs`, `unify_through_private` | retry through the expansion, report the first error |
| `for ... of` | `typecore.rs`, `type_for_of` | try `iterable<'a>`, then the array fallback |
| Coercion | `typecore.rs`, `type_coerce` | try unification with the enlarged type, then subtyping |
| Exhaustiveness | `typecore.rs`, `partial_pred` | type a candidate pattern with passive variants, always undone |
| Constructor arguments | `ctype.rs`, `unify_same_path_constructor_args` | retry after expansion |
| Level lowering | `ctype.rs`, `update_level_checked` | first pass without expansion, then with |
| Enlarging | `ctype.rs`, `safe_abbrev` | probe an abbreviation |
| Matching | `ctype.rs`, `matches` | always undone |
| Failed top-level unification | `ctype.rs`, `unify` | `undo_compress` before the trace is expanded |

The last one disappears: there are no compressions to undo while a snapshot
is live (C.3). `rigidify` and `moregeneral` do not snapshot; they are
unchanged.

There are places that try a unification and ignore a failure without a
snapshot (for example the tag-conflict probes in `typecore.rs` that match on
`Err(_) => {}`). OCaml keeps the partial bindings in those cases, and so
does the new core: the order of child unification is the same (C.5), so the
partial bindings are the same.

### C.7 Abbreviation expansion

Today a `Tconstr` node carries an `AbbrevMemoRef`, a linked list of memoised
expansions that `generalize` walks and `cleanup_abbrev` forgets, plus three
context caches keyed by environment scope (`pdot_expansions`,
`resolved_type_item_cache`, `normalized_path_*_cache`).

The new core has one table per compilation:

```rust
enum PathFacts {                 // per (scope_id, path), direct-mapped cache
    Datatype,                    // record, variant, extensible: never expands
    Abstract,                    // no manifest
    Abbrev { decl: DeclRef, private: bool, nullary: bool },
    Unknown,                     // not found: treated as abstract
}

struct Expansions {
    /// (constructor node handle) -> expansion, for ground nodes.
    ground: FxHashMap<u32, TypeExprRef>,
    /// (path, argument handles) -> expansion, for nodes with variables.
    applied: FxHashMap<(Path, SmallVec<[TypeExprRef; 2]>), TypeExprRef>,
    /// Unordered pair of ground handles -> equal up to expansion.
    equal: FxHashMap<(u32, u32), bool>,
}
```

- Expanding `p<args>` is `instance_parameterized_type` of the manifest
  against `args`, as today. For a ground node the result is ground and is
  memoised by handle. For a node with variables it is memoised by path and
  argument handles; the entry stays valid because handles are immutable and
  variables only become more defined.
- The table is per compilation because a local identifier means different
  declarations in different compilations (B.3).
- It is cleared at the points where `cleanup_abbrev` runs today and where
  declarations change under a path: entering and leaving a recursive type
  definition group in `typemod.rs`/typedecl code, and whenever
  `check_abbrev_env` detects a new environment for a local path
  (`previous_env_id`). Paths with `HAS_SCOPED` and paths with a local
  constraint are never memoised.
- `ground_equal(env, a, b)`: if both are `Datatype`/`Abstract` heads with
  the same path, compare arguments recursively (each a handle comparison
  first); if either head is `Abbrev`, expand and retry; memoise the answer in
  `equal`.

An optional later step shares expansions between compilations for types
whose paths are all absolute (`HAS_LOCAL_IDENT` clear), in a world table.
It is not in the plan; measure first.

### C.8 Schemes and instantiation

A generalised type is not a new kind of value. It is a type handle whose
flags and level say what `instance` must do:

| Handle | `instance` |
|---|---|
| ground | returns it |
| segment node | copies it and its non-ground children, stopping at ground children. Every segment node has `HAS_VAR`: it holds a quantified variable, or it is part of a recursive type, which keeps the flag (C.5) |
| scratch node below `GENERIC_LEVEL` | returns it |
| scratch node at `GENERIC_LEVEL` | copies it, stopping at ground children and at children below `GENERIC_LEVEL` |

So a scheme of another unit is "a frozen term with numbered quantified
variables": the generic `Tvar` nodes of its segment. The numbering is their
order in the segment, and the copy maps them through a small inline vector
(most schemes have at most three variables), as `CopyCache` does with
`TypeExprRefMap` today.

`instance` of a value from another unit therefore allocates only the spine
that holds quantified variables, and reads the frozen segment directly. No
overlay is consulted, because nothing ever writes to a segment.

Inside a module, generalisation is today's marking walk restricted to
non-ground nodes. A let-bound value whose type is ground (the common case)
costs one flag test to generalise and one to instantiate.

### C.9 Expected types

OCaml's `type_expect` already pushes known expected types down: to function
arguments from the parameter types, to record fields from the label types,
to annotated bindings, to JSX props (which are record fields or labelled
arguments by the time they are type-checked). The port does the same. What
remains is the opposite case: an expected type that is a *fresh variable*,
created only so that the expression's type can be unified into it.

```rust
enum Expected {
    /// The caller knows the type.
    Known(TypeExprRef),
    /// The caller would have passed a fresh variable created at this level.
    Infer { level: u32 },
}
```

The meaning of `Infer` is exactly "OCaml passes `newvar ()` here". What
OCaml does with that variable decides what the port may do:

1. **The construct only unifies its computed type with the expected type at
   the end** (`rue`, `unify_exp`). Unifying a type `ty` with a fresh variable
   `v` at level `l` has these effects: `occur` (cannot fail), `occur_univar`
   on `ty`, `update_level(l, ty)`, and the link. With `Infer` the port runs
   `occur_univar` (skipped when `HAS_UNIVAR` is clear) and
   `update_level_checked(l, ty)` (skipped when `ty` is ground), and returns
   `ty`. The errors those two can raise are raised from the same call with
   the same arguments, so the diagnostics are identical.
2. **The construct inspects the expected type for a hint** (record and
   constructor disambiguation, arity of an expected function). A fresh
   variable gives no hint, and `Infer` gives none.
3. **The construct passes the expected type to exactly one child in tail
   position** (`let ... in body`, a sequence's last expression, a constraint's
   inner expression where OCaml passes it through, `open`, a local module's
   body). It passes `Infer` on.
4. **The construct threads the expected type to several children**
   (branches of `if`, `switch` and `try`, array elements, the default of an
   optional argument). The first child is typed with `Infer`, and the others
   with `Known` of the first child's result. This is equivalent because
   nothing else can see the variable while the first child is typed.
5. **The variable is visible to someone else while the expression is typed**
   (a `let rec` binding, a function parameter, the result of applying an
   expression whose type is not yet an arrow). The variable is semantically
   needed. The port materialises it: `Expected::Infer` is turned into
   `Known(new_var())` at that point.

Per construct:

| Construct | Case | Notes |
|---|---|---|
| identifier, constant, field access, constructor without expected hint | 1 | the bulk of `Infer` uses |
| application | 1 for the function position | the function is typed one level deeper and then lowered; today's second variable exists only to do that lowering and becomes a direct `update_level_checked` |
| `let p = e` with a variable pattern and no annotation, not recursive | 1 for `e` | the pattern variable's type is `e`'s type; OCaml types the pattern first, but a variable pattern can neither fail nor warn at that point |
| `let` body, sequence, `open`, local module body | 3 | |
| `if`, `switch`, `try`, array literal | 4 | |
| function literal with unknown expected type | 5 for parameters without annotation; 3 for the body | the arrow is built directly instead of by `filter_arrow` on a variable |
| `let rec`, labelled-argument defaults that mention earlier parameters | 5 | |
| anything not listed | 5 | the default is to materialise, which is always correct |

Where it is not sound, and why the table above avoids it: if a construct
could observe, before it returns, that the expected type is a variable
shared with its caller (case 5), inferring would change which unification
fails first and so which diagnostic is printed. The default for an
unconverted construct is to materialise, so converting constructs one at a
time is safe, and each conversion is checked by the error-output parity
suite.

Level bookkeeping: `Infer` carries the level at which OCaml would have
created the variable. When no `begin_def` has run between that point and the
return, the lowering is a no-op and is skipped by comparing levels.

Of the 2.49 M fresh variables per build, 0.71 M are the two per application.
How many of the rest fall under cases 1 to 4 is not measured; P0 adds the
counter.

### C.10 Environments

```rust
#[derive(Clone, Copy)]
pub struct Env { scope: ScopeId, pos: u32 }      // 8 bytes

struct Binding {                  // one entry of the log
    name: Name,
    id: Ident,
    kind: BindingKind,            // namespace
    item: ItemRef,                // index into a per-kind payload vector
    scope: ScopeId,
    prev_same_name: u32,          // previous entry with this name and namespace
}

struct Scope {
    parent: ScopeId,
    first: u32,                   // log position when the scope was opened
    last_descendant: Cell<ScopeId>,   // set when the scope is closed
    opens: Vec<Open>,             // opens made directly in this scope
    flags: EnvFlags,
}

struct Open { pos: u32, target: OpenTarget, slot: u32 }
enum OpenTarget { World(UnitId, /* nested */ u32), Local(ItemRef) }

pub struct EnvLog {
    bindings: Vec<Binding>,
    scopes: Vec<Scope>,
    heads: FxHashMap<(BindingKind, Name), u32>,   // newest entry per name
    values: Vec<ValueDescription>,                // payloads, one vector per kind
    /* types, modules, modtypes, constructors, labels, local constraints */
}
```

Scopes form a tree, numbered in the order they are opened. An entry `e` is
visible from `Env { scope: s, pos: p }` when `e`'s position is at most `p`
and `e.scope` is `s` or an ancestor of `s`. Because scope ids are assigned
in preorder, "ancestor" is `a <= s <= a.last_descendant` (or `a <= s` while
`a` is still open).

- **Extend.** Push a binding, set `prev_same_name` from `heads`, update
  `heads`, return `Env { scope, pos: new_len }`. No allocation beyond the
  vector push. Entering a scope (a function body, a `let` body, a module
  body, a branch) pushes a `Scope`.
- **Look up `name`.** Start at `heads[name]` and follow `prev_same_name`
  until an entry is visible. For the environment at the frontier of
  checking, which is where almost every lookup happens, the first or second
  entry is the answer. Then check the opens of `s` and its ancestors with a
  position greater than the found entry's, newest first: the first whose
  target table has the name wins, as an open shadows what was bound before
  it. A module has a handful of visible opens; each check is one probe of a
  frozen `NameIndex`.
- **Look up through an old environment** (the backend expanding a type with
  `exp_env`, genType, the editor): the same walk, starting from the newest
  entry of the name. It may pass over later entries that are not visible.
  These lookups are few.
- **Constructors and labels** need all candidates of a name in order
  (`TycompTbl`); the same chain walk yields them.
- **`open M`** adds one `Open` entry pointing at `M`'s frozen export table
  (or at a local module's signature). Nothing is copied or re-indexed. The
  usage slot for the unused-open and shadowing warnings is the entry's
  `slot`, as `OpenSlotState` is today.
- **Identity.** `Env::id` and `scope_id` are used as cache keys. `pos` and
  `scope` replace them: two environments with the same scope and position
  are the same environment.
- **Local constraints, functor arguments, flags** are entries or scope
  fields.
- **The typed tree** stores the 8-byte `Env` where it stores an `EnvRef`
  today, or keeps `EnvRef` as an index into a `Vec<Env>`. `typed_envs` and
  its persistent-map snapshots go away; teardown of environments becomes
  dropping a few vectors.

The log must be reachable from an `Env`. In stage P6 the `Env` type keeps
its public API and carries an `Rc<EnvLog>` next to the two integers (16
bytes, one reference-count update per clone). When the remaining callers
take the log from the checker context, the `Rc` is dropped.

Initial environment: the bindings of the predefined types and the opens of
the standard library are the first entries of every log. They are built once
per worker and copied in as a prefix (a `Vec` clone of a few hundred
entries), or kept as a shared frozen prefix that scope 0 points at.

### C.11 The typed tree

The typed tree is already stored in flat pools owned by the compilation
(`types/tast_arena.rs`: `TypedArena`, `u32` handles, list pools), and its
readers already take the arena next to the root. This design changes two
things in it:

- `exp_type`, `pat_type` and the other `TypeExprRef` fields hold handles of
  the new tiers. Readers go through `TypeContext`, so they do not change.
- `EnvRef` resolves to an `Env` of C.10.

The typed tree is not canonical across the two cores: node sharing and
identifier stamps differ. That is allowed (rule 3). The backend reads types
by structure through `repr`, `get_desc` and `expand_head`, so it sees the
same types.

What the backend can observe of identifiers is their names and the
*relative order* of their stamps within the module (stamps break ties
between equal names and order some maps). The new core creates identifiers
at the same points in the same traversal order as today, so relative order
is unchanged; absolute values change when stage P4 stops replaying the
stamps of shared data.

## D. Diagnostics parity

Every way the printed diagnostics depend on something this design changes,
and what keeps each the same.

### D.1 Names of type variables

`printtyp.rs` names variables at print time (`name_of_type`, `new_name`): a
named variable keeps its name (with a numeric suffix on a clash), an unnamed
one gets the next unused letter in the order the printer first meets it.
The table is keyed by variable identity and reset per report
(`reset_names`, `reset_and_mark_loops`).

Dependencies: (a) variable identity: two occurrences are the same variable;
(b) traversal order of the printed type; (c) which variables carry a name.

- (a) holds: a variable is a slot, `repr` resolves bound ones.
- (b) holds: types are the same structure and the printer is unchanged.
- (c) Names are attached at creation and travel with instantiation exactly
  as today (`copy_type_cached` creates anonymous variables for generic
  ones; annotations create named ones). The export copy keeps names.

One case to test: after `'a` is unified with `'b`, which name survives
depends on which variable was bound to which. The new core binds in the same
direction as `unify_var`/`unify_types` do today (C.5 step 4).

### D.2 `as 'a` and loop detection

`mark_loops_rec` (`printtyp.rs`) adds an alias in two situations:

1. The node's proxy is among its own ancestors in the walk: a recursive
   type.
2. The node is an object or a polymorphic variant whose proxy was already
   visited anywhere in the report, and it is structurally open (not a static
   row, not a closed object).

The proxy of an object or variant is its row variable (`btype::proxy`); for
any other node it is the node itself.

- Case 2 is keyed by the row variable, not by the node, and only for open
  rows, which are never ground. Interning cannot merge two of them, and not
  linking structure nodes cannot split one: two unified open objects share
  their row variable in both cores.
- Case 1 needs a cycle. Ground-interned types are acyclic, so interning
  never creates or removes an alias. A recursive type keeps its own nodes
  (C.5). The remaining difference is the *shape* of a cycle after two
  recursive types are unified: OCaml's links merge the two cycles node by
  node; without links each keeps its own nodes, bound together only at the
  variables. The printed type could then show the alias at a different depth
  (`[#A('a)] as 'a` against `[#A([#A('a)] as 'a)]`).

  Answer: when both sides of a unification have `HAS_ROW` and the pair table
  shows a cycle, the new core records the pair in a per-compilation
  equivalence table (`unified_structure`), and `btype::proxy` in the new
  core maps a node through it. This is the structure link, kept as a side
  table for the only nodes where it is observable. Fixtures: add recursive
  polymorphic variant and recursive object mismatches to
  `tests/build_tests/super_errors`.

### D.3 Unification traces

A type clash prints the outermost pair and, depending on the shape of the
trace, the innermost mismatching pair, with "(defined as ...)" expansions
(`report_unification_error`, `trace_expansions`, `full_expand`, and
`driver/type_clash.rs` for the ReScript-specific messages).

Dependencies: the sequence of pairs, the state of every variable at the
moment of failure, and which pairs are expanded.

- The sequence of pairs is the recursion path. It is the same because
  children are unified in the same order and the same side is expanded first
  (C.5). The ground fast path changes nothing on success; on failure it
  re-runs the general walk to build the trace (C.5 step 2).
- Variable state at failure is the same: the same bindings were made in the
  same order before the failure. Restoring a linked structure node on
  failure, which OCaml does, has no counterpart because nothing was linked.
- `trace_expansions` is keyed by handle and filled by `full_expand` on the
  trace's types; it works on handles of any tier.

Risk: a trace pair in which one side is a variable that OCaml would show as
an already-linked structure. Covered by the differential mode (E.2), which
compares the full text of every diagnostic.

### D.4 Escape errors

"The type constructor `t` would escape its scope" and the universal-variable
escape come from `update_level_checked` and `occur_univar`. Both are called
at the same points with the same levels (C.4, C.9 case 1). The scoped paths
that can make them fail are excluded from every fast path by `HAS_SCOPED`
and `HAS_UNIVAR`, and the debug check of C.2 verifies the exclusion.

Levels and stamps share a number line (A.2). The new core keeps that:
`init_def`, `set_current_time` and the `+ 1000` offsets for locally abstract
types are above the waist and unchanged. Only the *order* of stamps and
levels matters to these checks, and the order is unchanged.

### D.5 Weak (non-generalised) variables

`is_non_gen` prints a variable as `_weak1` when it is not at
`GENERIC_LEVEL`; the counter and the map persist across reports of one
compilation (`weak_counter`, `weak_var_map`). The "contains type variables
that cannot be generalized" error walks the final signature
(`closed_schema`, the `lower_nongen_*` family).

Variables keep their levels and identities, so both are unchanged. The
export copy runs after this check, so a signature with a weak variable is
rejected before it could be published.

### D.6 Value restriction and generalisation

Which variables are generalised depends on levels at `end_def`, on
`is_nonexpansive_node`, and on `generalize_expansive` (variance). All three
are unchanged; ground types have no variables to generalise.

### D.7 Unused-variable, unused-open and related warnings

Usage is recorded by lookups (`UsageTables` in `types/usage.rs`, the
`open_slots` and `open_slot_events` of `TypeContext`, `LookupEvent`), and the
warnings are emitted when delayed checks are forced
(`delayed_unused_checks`, `delayed_warnings` in `TypeCheckContext`).

Dependencies: every lookup must mark the same binding as used, opens must
report the same "first candidate hidden" information for the shadowing
warnings, and delayed checks must run in registration order.

- The binding log (C.10) finds the same binding (same shadowing rule). Its
  lookups call the same marking hooks; an `Open` entry carries the slot.
- A type-directed disambiguation that looks up all candidates
  (`TycompTbl`-style) gets them in the same order.
- Stage P2 changes *when* some sub-expressions are typed relative to their
  pattern (a variable pattern typed after its expression). That does not
  reorder lookups in the expression, and a variable pattern performs none.

### D.8 Deprecation and other lookup-time warnings

Deprecation warnings are emitted at lookup from the item's attributes
(`ModuleDeprecation`, `deprecated_used`). Export tables keep the attributes.
Looking an item up through a view (B.6) must report the deprecation of the
alias and of the target as today; view items copy the attributes of their
source and the alias declaration keeps its own.

Risk: today some declarations are forced lazily, and forcing can emit a
warning the first time (for example a deprecated module alias reached while
building a component view). In the world, a view item is built once per
build by whichever compilation needs it first, so a warning emitted *during
the build of the view* would be reported in only one of the modules that use
it. Rule: building world data never emits a diagnostic. Diagnostics are
emitted by the lookup in the consuming compilation, from data stored on the
item. P4 audits `env_lazy.rs` and `cmi/persistent_env.rs` for warnings
raised inside `build_in_store`.

### D.9 Order of reported diagnostics

Warnings are reported in the order they are pushed to
`TypeCheckContext::warnings`, with delayed ones in registration order, and
the first error stops the module. The order follows the traversal of the
source. Nothing in the world can reorder a module's own traversal. P2 is the
only stage that changes traversal, in the bounded way described in D.7.

Across modules the build system orders output; that is unchanged.

### D.10 Paths in messages

Types print with the path stored in the node (`tree_of_path`), after
`best_type_path`. Absolute paths in exports (B.4) are the paths a dependent
sees today after the component substitution, and alias views (B.6) keep the
alias's name. Inside the module being compiled its own types keep their
local identifiers, so a message says `t`, not `M.t`.

Risk: today's component substitution and the export-time rewrite must
produce the same path for nested modules, for items shadowed within one
signature (the same name declared twice), and for positions in `Pdot`
(`pdot_pos`, used as runtime field positions by the backend). The export
rewrite takes the positions from the same `SignatureIndex` computation that
the views use today.

### D.11 Things that depend on node identity and are not output

For completeness, uses of `TypeExprRef` identity that do not reach rule 1 or
rule 2 and may change freely: de-duplication in the typed-tree dump
(`arity_aliases`, node ids), `TypeExprRefMap` copy caches, `typeopt_answers`.

## E. The differential harness

### E.1 Two cores in one binary

`TypeContext` gets a mode fixed at creation:

```rust
pub enum CoreMode { Legacy, Terms }
```

The storage accessors and the `ctype` operations dispatch on it once at
their entry. The dispatch is a predictable branch; when the old core is
deleted it disappears. Everything above the waist is shared.

Selection:

- `RESCRIPT_CHECKER=legacy|terms|both` for a whole run (default `legacy`
  until P9).
- `RESCRIPT_CHECKER_PACKAGES=a,b,c`: packages checked with `terms`; others
  with `legacy`. This is the per-package switch. It is an environment
  variable, not a `rescript.json` field, so that it is not a product surface.

### E.2 `both` mode

For each module the driver type-checks twice from the same parsed tree and
options, each time from a fresh identifier counter: first `legacy`, then
`terms`. A dependency's signature is read by each run from its own core's
publication (both are kept in `both` mode), so a difference cannot hide
behind a shared input.

Compared, in this order:

1. **Outcome.** Accepted or rejected.
2. **Diagnostics.** The ordered list of `(kind, location, rendered text)`
   for the error, if any, and every warning. Text is compared after the
   normal rendering, so variable names, aliases and paths are covered.
3. **Exported signature in canonical form.** Each signature item printed
   through `printtyp` (the outcome tree, which names variables by traversal
   and is independent of handles and stamps), followed by what the printer
   omits and dependents can read: runtime representation of each type
   (`TypeRepresentation`, variant layouts, record representations), variance,
   `Pdot` positions, attributes that affect code generation, deprecation.
   The stamp-independent fingerprint and the per-item digests are compared
   too, as a cheap first check.
4. **JavaScript.** The module is lowered and printed from both typed trees;
   the bytes are compared. So is the `.cmj`-equivalent metadata dependents
   read (purity, arities, inlinable constants).
5. **Debug invariants.** The skipped-walk assertions of C.2 run in this
   mode.

Reporting: the first difference of each kind is written to
`<build dir>/checker-diff/<Module>.<kind>.diff` as a unified diff of the two
renderings, with the module, the kind and the two fingerprints on stderr.
The build fails at the end with a count per kind;
`RESCRIPT_CHECKER_DIFF=continue` reports and goes on using the `legacy`
result, which is how the benchmark is first brought to zero differences.

Where it runs:

- Unit level (P8): random and corpus type pairs are built in both cores and
  `unify`, `instance`, `generalize`, `expand_head`, `moregeneral` and `equal`
  are compared for outcome and for the printed result. A converter from
  legacy nodes to term nodes makes the corpus (every type in the signatures
  of the standard library and the test suite) available to both.
- Module level: `both` mode over `tests/tests`, the `super_errors` and
  `super_errors_multi` fixtures, the standard library, and the benchmark.
- CI: one job runs the parity suites with `RESCRIPT_CHECKER=both` from P8
  on.

### E.3 The oracle for in-place stages

P1 to P6 and P11 change shared code, so there is no second core to compare
with. Their oracle is the OCaml compiler and the previous commit:

- `scripts/test_js_output_parity.sh`, `scripts/test_stdlib_output_parity.sh`,
  `scripts/test_gentype_output_parity.sh`, `scripts/test_error_output_parity.sh`
  and the `super_errors` build tests gate every stage, as today.
- P0 adds a script that builds the benchmark with two `rescript` binaries
  (base and candidate) and compares, per module, the fingerprint, the item
  digests, the diagnostics and the JavaScript. It reuses the layout of
  `scripts/compare_build_instructions.py`, which already builds both.
- The dump flags (`-dtypedtree`, `-drawlambda`) are debugging aids for
  locating where a difference starts. The typed tree and Lambda are expected
  to change in P1, P4 and P5 (sharing and stamps); that is accepted when the
  gates above hold.

### E.4 Switching over and deleting

1. P8 lands with `terms` available and unused by default.
2. P9: zero differences in `both` mode on the test suites, then on the
   benchmark. The instruction-count workflow gains a second, non-blocking
   measurement with `terms`.
3. `terms` becomes the default for the standard library and the test
   packages, then for everything. `legacy` stays selectable for two releases
   of soak.
4. P12 deletes: the legacy tiers and overlays in `types/context.rs`,
   `types/thread_store.rs`, the legacy operations in `types/ctype.rs`, the
   `AbbrevMemo` machinery, `internalize_pers_struct` and its helpers, the
   mode dispatch, and `both` mode. The unit-level differential tests are
   kept as ordinary tests with recorded expectations.

## F. Staged plan

### F.1 Overview

Every stage is one pull request (P11 is a series) that leaves trunk passing
all tests and shipping. "Saving" is a share of today's whole-build
instructions (76 G on the benchmark), estimated as described per stage.
"Gate" always includes: `cargo build` and `cargo test` for `compiler-rust`
and `rewatch`, the four output parity scripts and the `super_errors` tests of
E.3, and the instruction-count workflow (no increase above 0.1% without a
stated reason). Only additions are listed per stage.

| # | Stage | Depends on | Size (lines changed) | Saving | Hand to a less capable model |
|---|---|---|---|---|---|
| P0 | Differential tooling and counters | - | 600 | 0 | yes |
| P1 | Ground flag and fast paths | P0 | 900 | 4-6% | yes |
| P2 | Infer instead of unifying with a fresh variable | P0 | 700 | 1.5-2.5% | application: yes; other constructs: one at a time, yes |
| P3 | Publish into the shared pool; encode later | P0 | 1,200 | 2.5-3.5% | after a call-site inventory (see P3) |
| P4 | Process-wide views; delete stamp replay | P3 | 2,500, mostly deletions | 2.5-3.5% | no |
| P5 | Absolute paths in exports; no lookup copies | P4 | 2,000 | 3-4% | no |
| P6 | Environment as a binding log | P0 | 2,500 | 3-4% | after an API inventory (see P6) |
| P7 | Term store, closed waist, core switch | P1 | 2,000 | 0 | yes |
| P8 | New core operations | P7 | 7,000 | 4-6% once on | split: simple types yes; rows, univars, GADT no |
| P9 | Switch on | P8 | 500 plus fixes | 0 | no (triage) |
| P10 | Segments, export tables, checker per worker | P5, P6, P9 | 3,000 | 2-3% | no |
| P11 | Walk cost in `typecore`/`typemod` | P2; conflicts with nothing else if kept small | 200-600 each | 4-6% total | yes, each |
| P12 | Delete the old core | P10, soak | -10,000 | 0 | yes |

Parallel tracks:

```
A: P0 -> P1 -> P7 -> P8 -> P9 ----------\
B: P0 -> P3 -> P4 -> P5 -----------------+-> P10 -> P12
C: P0 -> P6 ----------------------------/
D: P0 -> P2 -> P11 (continuous)
```

A, B, C and D touch different files except: P1 and P2 both edit `ctype.rs`
entry points lightly (land P1 first); P2 and P11 both edit `typecore.rs`
(one owner at a time); P5 and P6 both touch `env_lazy.rs` call sites of
`Env` (land P6 first if both are ready).

Stages P1 to P6 pay for themselves on today's representation. If the work
stopped after them, the estimated saving is about 17-23% of the build, with no
long-lived branch.

### F.2 P0: differential tooling and counters

- **Changes.** A script that builds a project with a base and a candidate
  `rescript` and compares per-module fingerprint, item digests, diagnostics
  and JavaScript (E.3). Counters behind `RESCRIPT_COMPILER_COUNTERS`
  (`perf_counters.rs`): nodes allocated by cause, ground share of
  `instance`/`generalize`/`update_level` visits, unifications by shape,
  fresh variables by call site and by the case of C.9, lookup copies,
  exported non-ground nodes per unit. A canonical signature printer (E.2
  item 3) as a library function with tests.
- **Files.** `scripts/`, `perf_counters.rs`, a new
  `types/canonical_sig.rs`, `driver.rs` (a dump flag).
- **Invariant introduced.** The canonical form is independent of node
  identity and stamps: printing a signature, re-internalising it and
  printing again gives the same text.
- **Gate.** Base against base reports no difference on the benchmark; the
  counters reproduce the measured facts in section 0 within 2%.
- **Saving.** None. It answers the unknowns listed in G.

### F.3 P1: ground flag and fast paths on today's representation

- **Changes.** A flags byte per node, in a `Cell<u8>` array parallel to the
  chunks of `TypeNodes` (the 32-byte node has no spare byte; a parallel
  array keeps it at 32). Set by the constructors in `context.rs` from the
  children's flags: `HAS_VAR`, `HAS_UNIVAR`, `HAS_SCOPED`, `HAS_ROW` (C.2).
  Nodes of the worker store and shared pool get their flags when they are
  internalised (`cmi/portable_types.rs`). A node that is written after
  construction (placeholder variables linked by the copiers, `set_desc`)
  is flagged `HAS_VAR` at creation and stays so.
  Fast paths: `instance` and `copy_type_cached` return a ground node;
  `generalize_rec`, `update_level`, `update_level_pass`,
  `generalize_structure_rec` return on one; `binding_facts`, `occurs`,
  `deep_occur`, `occur_univar` stop at one; `unify_types` binds a variable
  to a ground type without the three walks.
- **Files.** `types/context.rs`, `types/ctype.rs`, `types/btype.rs`,
  `cmi/portable_types.rs`, `types/shared_store.rs`.
- **Invariants.** (1) A ground node's reachable graph contains no unbound
  variable and never will. (2) No path in it is scoped. (3) No code decides
  anything from the level of a ground node. To find violations of (3), grep
  the 100-odd `get_level` callers (`ctype.rs` 73, `typecore.rs` 22,
  `printtyp.rs` 9): each either looks at a variable or must treat ground as
  generic.
  One interaction to handle: today unification *links* a structure node to
  another. A ground node may be linked to a non-ground node that is equal
  after the unification; its parents stay ground (invariant 1 holds because
  the two are equal), and `repr` then lands on a node without the flag,
  which only takes the slow path.
- **Gate.** The debug cross-check of C.2 in debug builds and in one CI job.
  The `-dtypedtree` dump will change (shared instead of copied nodes); on a
  sample, confirm the differences are sharing only.
- **Saving, 4-6%.** Instantiation, generalisation and level work is 20% of
  checking, 8% of the build. Ground types are 66% of `instance` calls, 78%
  of copied nodes, 69% of level-update visits and 80% of generalisation
  visits, and half of the occur and univar walks in `unify` (1.16 M
  variable-against-ground bindings). Taking 60-70% of that 8%, plus the
  allocator and copy share of 3.3 M nodes no longer allocated.

### F.4 P2: infer instead of unifying with a fresh variable

- **Changes.** `Expected` (C.9) in `type_expect_full` and its callers. First
  PR: `type_application` only (the function position is typed with `Infer`;
  the second variable becomes `update_level_checked`). Following PRs convert
  one row of the table in C.9 each.
- **Files.** `types/typecore.rs`.
- **Invariant.** A construct handles `Infer` only as its row of C.9 says;
  every other construct materialises the variable on entry.
- **Gate.** Error-output parity is the gate that matters. Add fixtures for
  an escape error and a universal-variable escape through an application
  result, and for a mismatch in the second branch of an `if` and of a
  `switch`.
- **Saving, 1.5-2.5%.** 0.71 M of 2.49 M variables are certain; P0's counter
  says how many more. A variable costs an allocation, a unification, a
  link, and a `repr` hop on every later read of the expression's type.

### F.5 P3: publish into the shared pool; encode off the critical path

- **Changes.** `extract_module_update` builds the `SharedGraph` for the
  unit directly from the `TypeContext` (one walk, as
  `internalize_signature_into_shared` builds it from the portable form) and
  registers the resulting `PersStruct` in the shared pool under the unit's
  name. The fingerprint and `SignatureSummary` item digests are computed by
  hashing that graph. The portable encoding is produced from the frozen
  graph on the digest thread, and only when the incremental store or a
  non-shareable consumer asks. The two saving copies in `driver.rs` are
  reduced to the one genType needs (and that one is skipped when genType is
  off).
- **Files.** `driver.rs`, `cmi/persistent_env.rs`, `cmi/portable_types.rs`,
  `cmi/item_deps.rs`, `types/shared_store.rs`,
  `rewatch/src/build/compile.rs`, `rewatch/src/build/state_db.rs`.
- **Invariants.** The fingerprint and digests computed from the graph equal
  those computed from the portable form (test both on the corpus before
  switching). A dependent never waits for an encoding.
- **Gate.** Incremental-build tests of `rewatch` (`make test-rewatch`); a
  watch-mode edit that changes and one that does not change an interface
  recompile the same dependents as before.
- **Saving, 2.5-3.5%** of the 4.6% publishing cost. What remains is the
  graph walk and the digests.
- **Hand-off.** Needs an inventory of every reader of `PortablePersStruct`
  (`signature()`, `signature_for_dependent()`, `raw_signature()`,
  `summary()`), with which of them run before dependents are unblocked. With
  that list it is mechanical.

### F.6 P4: process-wide component views; delete stamp replay

- **Changes.** Views of persistent-rooted paths (`QualifiedModuleComponents`
  and its forcing tables) become process-wide: an immutable core plus
  per-entry `OnceLock`s, their nodes allocated into shared graphs. Binders
  created while building them take stamps from the process-wide range
  (`next_store_stamp`), and the consuming compilation's own counter is no
  longer advanced: `StoreEffect::Stamps`, `StoreStampOrigins`, reserved
  rename stamps and `touch_store_piece`'s stamp replay are deleted. The
  registrations a view needs in a compilation (`RegisterComponents`,
  `RegisterAliasSource`) become lookups in the world table.
- **Files.** `types/env_lazy.rs`, `types/context.rs`, `types/thread_store.rs`,
  `cmi/persistent_env.rs`, `ident.rs`.
- **Invariants.** Building world data reads no compilation state and emits
  no diagnostic (D.8). A compilation's identifier stamps depend only on its
  own source.
- **Gate.** JavaScript and error parity. The `-dtypedtree` and `-drawlambda`
  dumps will show stamp differences everywhere; verify on a sample that they
  are stamps only. The 1-worker against 10-worker output comparison of B.8.
- **Saving, 2.5-3.5%.** `build_in_store` 3.5% and replay 1.2-2.1% were
  measured (`docs/DEPENDENCY_COMPONENTS.md`); views are built about 4.2
  times each today.
- **Hand-off.** No. It needs the judgement of G.3 (which stamps the backend
  can observe) and an audit for diagnostics raised inside store builds.

### F.7 P5: absolute paths in exports; no lookup copies

- **Changes.** When a unit is published (P3's walk), its own identifiers
  are rewritten to absolute paths (B.4 step 2) and its constructor and label
  descriptions and name indexes are built once. A lookup of `M.x` through
  the unit's own name returns the shared nodes with no copy:
  `lookup_value_for_access_inner` and the type, constructor and label
  lookups stop calling `copy_lookup_*`. Alias views substitute one item on
  first use into the world view table (B.6). The raw signature genType reads
  keeps local identifiers; it is produced by the inverse mapping on demand.
- **Files.** `types/env_lazy.rs`, `types/typecore.rs` (the `copy_lookup_*`
  family and module resolution), `cmi/persistent_env.rs`
  (`build_value_subst_maps`, the re-rooting helpers), `driver.rs`.
- **Invariants.** A shared node is never written (already true: writes go to
  overlays). The path printed for an item reached through any access path is
  the one printed today (D.10).
- **Gate.** Add `super_errors_multi` fixtures that print a type through a
  namespace alias, a local alias of another unit, a nested module, and an
  `include`. genType parity.
- **Saving, 3-4%** of the 4.9% spent on lookups in other modules, plus the
  allocation of 2.55 M nodes (22% of all nodes).
- **Hand-off.** No.

### F.8 P6: environment as a binding log

- **Changes.** C.10 behind the existing `Env` API. `IdTbl`, `TycompTbl`,
  `LayerMap`, `Recent`, `IdOpened` and the `im-rc` dependency go.
  `typed_envs` stores 16-byte values.
- **Files.** `types/env.rs`, `types/context.rs`, `types/typedtree.rs`
  (`EnvRef`), call sites of `Env::clone`.
- **Invariants.** Visibility as defined in C.10. A lookup returns the
  binding today's tables return, including candidate order for constructors
  and labels and the "hidden by an open" information.
- **Gate.** A property test: random sequences of scope entry and exit,
  binding, open and lookup run against the old tables and the log, kept in
  the test suite with the old tables moved under `#[cfg(test)]` until P12.
  The warning fixtures for unused opens and shadowing.
- **Saving, 3-4%.** Environment lookups are 9% of checking (3.6% of the
  build), dropping environment snapshots 0.98%, persistent maps 1.5%
  build-wide.
- **Hand-off.** Yes, after a mechanical inventory of the public methods of
  `Env` and their callers, each tagged extend, look up or other.

### F.9 P7: term store, closed waist, core switch

- **Changes.** `CoreMode` (E.1). The term store of B.2, B.3 and C.2 to C.3
  with constructors and the read API implemented for `Terms`. The direct
  descriptor and level writes above the waist (C.1) become named `ctype`
  operations with a `Legacy` implementation. A converter from legacy nodes
  to term nodes for tests. No operation is implemented for `Terms` yet; the
  mode is unreachable outside tests.
- **Files.** New `types/terms.rs`, `types/world.rs`; `types/context.rs`,
  `types/ctype.rs`, the listed call sites.
- **Invariants.** Those of B.3 and C.2. Size assertions: `ScratchNode` 32
  bytes, `VarSlot` 8 bytes, `TypeDesc` 24 bytes.
- **Gate.** Unit tests: interning from several threads gives one handle per
  type and every thread reads every node; converting a legacy signature and
  printing it gives the same text. Instruction count unchanged in `Legacy`.
- **Saving.** None.

### F.10 P8: the new core operations

Three pull requests, in order:

1. **P8a, simple types.** Variables, the trail, levels, `unify` for
   variables, constructors, tuples and arrows, `instance`, `generalize` and
   its variants, `update_level*`, expansion (C.7), `occur*`, `equal`,
   `moregeneral`, `matches`. Types with `HAS_ROW` or `HAS_UNIVAR` abort with
   a clear internal error. Hand-off: yes.
2. **P8b, rows, objects, `Tpoly`, universal variables, packages.** A port of
   the existing functions onto the new storage (C.5). Hand-off: no; the
   logic is subtle even when unchanged.
3. **P8c, subtyping, coercion, `nondep_type`, pattern mode and GADT
   equations, the `subst_*` copies.** Hand-off: no.

- **Files.** New `types/ctype_terms/` (several files); `types/ctype.rs`
  (dispatch).
- **Gate.** The unit-level differential tests of E.2 for each operation as it
  lands; from P8b, `both` mode over the standard library; from P8c, over
  everything.
- **Saving, 4-6% once switched on,** on top of P1: `repr` without a memory
  read, no structure links, unification of two ground types by handle
  (0.88 M of 3.09 M), expansion by table (5% of checking), no overlays on
  reads of dependency types, scheme instantiation that stops at ground
  children.

### F.11 P9: switch on

Bring `both` mode to zero differences (E.4 steps 2 and 3), package by
package. Each difference is either a bug in the new core or an undocumented
dependency on sharing or order; the second kind is added to section D with
its fix. Hand-off: no; this is triage.

### F.12 P10: segments, export tables, one checker per worker

- **Changes.** For `Terms`: publication as in B.4 (replacing P3's graph
  build), `UnitExports` (replacing the component views of P4 and P5 for
  direct access), the view table for the substitution cases, the world
  lifetime rules of B.7. One `TypeContext` per worker: scratch vectors
  (nodes, variables, trail, binding log, typed-tree pools, expansion tables)
  are cleared, not dropped, between modules, and the initial environment is
  a shared prefix.
- **Files.** `types/world.rs`, `types/env_lazy.rs`, `cmi/persistent_env.rs`,
  `driver.rs`, `rewatch/src/build/compile.rs`, `rewatch/src/build/tooling.rs`.
- **Invariants.** Segments are self-contained (B.4). After a reset, no
  scratch handle of the previous module is reachable: every table keyed by a
  scratch handle is in the reset list, and a debug build poisons the old
  ranges.
- **Gate.** Watch-mode tests (edit, rebuild, edit an interface, rebuild);
  peak memory on the benchmark not above today's; the shuffle mode of B.8.
- **Saving, 2-3%** of the 3.6% setup and teardown, plus what remains of
  publication.

### F.13 P11: walk cost in `typecore` and `typemod`

Walking expressions is 25% of checking (10% of the build), and library code
is 40% of all samples (allocator 8.5%, memory copies 8.3%, hash tables 5.9%,
collecting into vectors 5.6%, drops 3.7%, clones 2.4%). The types module has
1,515 `.clone()` calls and 277 `Arc<`.

This stage is a series of small pull requests, each chosen from a profile:
pick the top self-time function in `typecore.rs` or `typemod.rs`, remove its
temporary vectors (iterate pools in place), its clones of declarations and
descriptions (borrow from the world or the log), its `String` keys (use
`Name`), its per-call hash maps (small inline vectors). Each is gated by
parity and by the instruction count, which must go down.

- **Saving, 4-6% in total,** assumed as half of the walking share. This is
  the least certain estimate in the plan: the split of that 10% between
  necessary work and overhead is not measured (G.9).
- **Hand-off.** Yes, each; the change is local and the gate is objective.

### F.14 P12: delete the old core

E.4 step 4. About 10,000 lines removed. Hand-off: yes.

### F.15 Does it reach the target?

Type checking must go from 49,000 to about 12,000 instructions per line: a
cut of 37,000, which is 30% of today's build. The low and high estimates sum
to 27% and 39%. The stages overlap in what they remove (P1 and P8 both act
on instantiation; P4, P5 and P10 all act on cross-module lookups), and the
ranges above already count each instruction once, but the estimates are
derived from shares of samples, not from prototypes.

The honest reading: P1 to P6 are well supported by measurements and should
deliver 17-23%. Reaching 30% depends on P8 and P11 delivering the upper half
of their ranges. If they do not, the next lever is the one this document
declines for now: restructuring `typecore.rs` itself around the binding log
and expected types, instead of trimming it.

## G. Risks and open questions

Each with a recommended answer.

**G.1 Is the `HAS_SCOPED` rule complete?** The claim is that a type
constructor bound by a structure item never fails a level check afterwards
(C.2). It rests on `init_def` being called at each item and on levels never
dropping below an earlier item's stamps. Functor bodies, recursive modules
and first-class module signatures have not been traced in full.
*Recommendation:* P1 ships with the debug cross-check always on in debug
builds and in one CI job over all suites and the benchmark. If the check
ever fires, widen the flag (the safe direction) instead of adding a special
case.

**G.2 Keeping levels instead of ranks.** This design keeps OCaml's node
levels on scratch nodes (C.4) to keep the escape diagnostics exact. It
gives up a simpler generalisation. *Recommendation:* keep them. Revisit only
if P8's profile shows level maintenance on non-ground nodes above 3% of
checking; even then, prefer a rule that reports the escape error from the
variable binding and verify it against every escape fixture first.

**G.3 Which identifier stamps can the backend observe?** P4 stops advancing
a compilation's stamp counter for shared data, so absolute stamps change and
relative order within a module does not. The JavaScript is believed to
depend only on names and relative order. This was not verified by reading
the whole backend. *Recommendation:* before P4, run the benchmark with a
debug switch that adds a constant gap to the stamp counter after each
dependency load. Identical JavaScript confirms it; a difference names the
place to fix.

**G.4 Does anything outside the printer read structure-node identity in a
way that reaches output?** Found: only `mark_loops_rec` (D.2). Not found by
exhaustive proof. *Recommendation:* P1 already changes sharing (ground types
are shared instead of copied) on today's core, so it is the cheap probe: if
P1 passes error parity and the benchmark comparison, the remaining risk in
P8 is confined to non-ground nodes, where D.2's side table applies.

**G.5 Recursive ground types are not interned.** A closed recursive
polymorphic variant is rebuilt in scratch by each instantiation and copied
into each segment that exports it. *Recommendation:* accept. Count them in
P0; intern them only if they exceed 1% of nodes.

**G.6 How many nodes does the export copy visit?** Unknown; bounded above by
about 1.2 M per build (B.4). *Recommendation:* P0 measures it. If it is
above 0.5% of the build, allocate top-level schemes directly in the unit's
segment pages when a structure-level binding is generalised and closed, and
copy at publication only those that were still open.

**G.7 Watch-mode memory.** The ground tier, the view table, names and paths
grow for the life of a watch session. *Recommendation:* the rollover of B.7.
Report the ground tier size in the watch log at debug level so that the
threshold can be set from real sessions.

**G.8 Lock contention in the ground interner.** A miss in the per-worker
cache takes a shard mutex. With 10 workers, 64 shards and about 60,000
insertions plus a few hundred thousand cache misses per build, contention
should be negligible, but it is not measured. *Recommendation:* P7's
multi-thread test records lock acquisitions; if contended, size the
per-worker cache up before changing the structure.

**G.9 What is inside "walking expressions"?** 25% of checking is self time
in the expression walker; how much is overhead is unknown.
*Recommendation:* P0 adds a profile with allocation and clone sites
attributed to `typecore.rs` functions. Size P11 from it, and decide then
whether trimming is enough.

**G.10 Two cores for several months.** Shared code above the waist must
work with both. A change there can break one core without the author
noticing. *Recommendation:* from P8 on, CI runs the parity suites in `both`
mode, so every pull request is checked against both. Keep the dual period
short: P12 is scheduled, not optional.

**G.11 Editor tooling holds a `TypeContext`.** `ToolingTypedModule` keeps
the context of a module type-checked on demand. With one checker per worker
(P10) the scratch state is reused. *Recommendation:* tooling queries take
their own `TypeContext` from a small pool and return it when the query's
result is dropped; they hold the world's read lock for that time.

**G.12 genType reads the raw signature with local identifiers.** P5 stores
exports with absolute paths. *Recommendation:* keep genType reading the
compilation's own signature (still local, still in scratch) for the unit
being compiled, which is its main input; for dependencies, map absolute
paths of the unit's own items back to bare names when the raw form is
requested. genType output parity is the gate.

**G.13 `Path` and `Name` are pointers.** `TypeDesc` is 24 bytes because a
path is an 8-byte pointer. A 32-bit path id would make it 16 bytes and a
ground node 24. *Recommendation:* not in this plan. Paths are compared and
hashed without a table read today, which an id would cost. Measure after
P8.

**G.14 The estimates.** Every saving is derived from sample shares, not
from a prototype. *Recommendation:* P1 is the calibration. It is small, it
is predicted at 4-6%, and its result should rescale the others before P7
and P8 are staffed.
