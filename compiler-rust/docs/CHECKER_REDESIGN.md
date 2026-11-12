# The shared world and the type checker core: design and staged plan

Status: design. This document is the spec for the stages in section F. Stage
P0 has landed and the sound part of P1 is in pull request #124.

**Amended after stage P1.** P1 found that the premise of the new checker core
is false: sharing variable-free types between uses is observable, down to the
generated JavaScript. Section I states what is observable, chooses the design
answer and re-derives the savings. Every passage below that section I
changes carries a note that starts with "**Amended (I.n)**"; replaced numbers
are struck through. Where a note and the text under it disagree, the note
holds.

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

> **Amended (I.3).** The ground tier and every checker fast path that rests
> on it are withdrawn: the struck-through items below. The checker core
> stays today's representation, one node per occurrence with structure links
> and a level on every node (I.3.3). The world keeps names, paths, segments,
> absolute paths and the view table.

**The world** is one store per build, readable from every thread without
locks:

- Names and paths are already interned process-wide (`name.rs`,
  `types/path.rs`). They stay.
- ~~Variable-free types are interned in a **ground tier**: equal types have
  equal handles.~~
- Each module's exported ~~, non-ground~~ types live in **segments**: immutable
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

- ~~A handle's two tag bits name its tier: scratch node, variable, ground,
  segment. Only variables (and row-field and mutability cells) are mutable.
  `repr` of a non-variable is a bit test, not a memory read.~~
- ~~Every node carries flags computed at construction. A ground type is
  returned by `instance`, skipped by generalisation, level updates and the
  occur check, and compared by handle.~~
- Levels stay, on ~~scratch nodes and variables only~~ every node (I.4). They
  are not replaced by variable ranks: OCaml reports an escaping type
  constructor when it lowers the level of a *structure* node, and that
  decides which of two errors a program gets (C.4).
- ~~A generalised type is a frozen term. Instantiation copies only the spine
  that holds quantified variables.~~ Instantiation copies every generic node
  (I.3.3, rule 3).
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
  reduced in place, guided by profiles. *Amended (I.6): there is no new
  core. The waist remains a useful description of how the layers above reach
  the representation.*
- **Publishing is not copy-free, and does not need to be.** Scratch nodes are
  single-threaded `Cell` storage interleaved with dead inference nodes. The
  exported ~~non-ground~~ nodes are copied once into a segment. That one copy
  replaces today's four (saving copy, portable encoding, decoding,
  internalisation) and the per-lookup copies. ~~Ground nodes, 78% of the
  total, are never copied.~~ *Amended (I.3.3, rule 5): every exported node is
  copied, with its sharing; 368,428 nodes on the application (measured).*

Also: the typed tree is already stored in flat per-module pools
(`types/tast_arena.rs`). Only its environment snapshots change.

### The stages

> **Amended (I.5, I.6).** The table has a second column of savings. "Measured"
> means instructions counted with the change built; everything else is an
> estimate. I.5 gives the basis of each number.

| # | Stage | Saving, original estimate | Saving after P1's findings |
|---|---|---|---|
| P0 | Differential tooling and counters | 0 | 0 (landed) |
| P1 | ~~Ground flag and fast paths~~ Level updates of plain types without a snapshot | ~~4-6%~~ | 1.4% measured (0.7-0.8% on `tests/tests`) |
| P1b | `instance` returns a non-generic root at once (new) | | 0.9% measured (0.65% on `tests/tests`) |
| P2 | Infer instead of unifying with a fresh variable | 1.5-2.5% | 1.5-2.5% |
| P3 | Publish straight into the shared pool; encode off the critical path | 2.5-3.5% | 2.5-3.5% |
| P4 | Process-wide component views; delete stamp replay | 2.5-3.5% | 2.5-3.5% |
| P5 | Absolute paths in exports; no lookup copies | 3-4% | 3-4% |
| P6 | Environment as a binding log | 3-4% | 3-4% |
| P7 | Term store and core switch (no behaviour change) | 0 | dropped |
| P8 | The new core operations | ~~4-6% when switched on~~ | 0, dropped |
| P9 | Switch on per package, then by default | 0 | dropped |
| P10 | Segments, export tables, one checker per worker | 2-3% | 2-3%, on today's `TypeContext` |
| P11 | `typecore`/`typemod` walk cost, profile-driven | 4-6% | 4-6% |
| P12 | Delete the old core | 0 (code size) | dropped |

~~The estimates sum to 27-39% of the build against a needed 30% (37,000 of
123,000 instructions per line).~~ The estimates now sum to 21-29% of the
build against a needed 30% (37,000 of 123,000 instructions per line); 2.3
points of that are measured. The plan no longer reaches the target on its
own estimates (I.5). They are estimates with a wide error; section F says how
each was derived. Section H holds the call-site inventory for P3 and the API
inventory for P6, with the corrections they make to both stages. Section I
holds what stage P1 found and what it changes.

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

> **Amended (I.3.3, rules 5 and 6).** The ground tier is withdrawn. Merging
> equal ground types in a published interface changes which positions of an
> exported type are one node, and a dependent can observe that (I.2.3,
> fixture 7b). A segment holds every exported node of its unit, ground or
> not, with the exporter's sharing. Read "non-ground" in this section as
> "exported", and ignore the ground rows and clauses. B.5 to B.8 stand.

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

> **Amended (I.3.3).** The tiers are today's (A.1). The `variable` and
> `ground` tiers are not built; a segment is a tier of frozen nodes like
> today's shared pool.

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

> **Amended (I.3.3, rule 5).** Withdrawn. Kept for the record.

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

> **Amended (I.3.3, rules 5 and 8).** Step 1 copies every node, not only the
> non-ground ones, and keeps sharing for all of them with one map over the
> whole signature. Step 2 rewrites paths in the copied nodes; nothing is
> re-interned. Step 4 hashes every node by structure. The copy visits 368,428
> nodes on the application (measured, P0 counters), of which 49,712 are not
> ground; at about 60 instructions per node that is still under 0.1% of the
> build. `SegNode` needs no flags.

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

> **Amended (I.3).** The new core is not built. C.2, C.3, C.5, C.7 and C.8
> are withdrawn as a design; they stay as the record of what was tried. C.4
> stands for its argument against ranks and is otherwise replaced by I.4.
> C.6 is a description of today's code and stands. C.9 stands with one
> correction. C.10 and C.11 stand (with H.2 for C.10).

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

> **Amended (I.1 findings 3 and 4, I.3.3 rule 1).** Withdrawn. No flags byte:
> set at construction it cost +3.4% of instructions on today's
> representation (#124), and no sound fast path reads it. "A ground type
> skips level updates" is unsound (I.2). The `HAS_SCOPED` rule below is
> unsound for a weak variable of an earlier structure item
> (`weak_variable_escapes_later_type.res`): the rule in use is
> `path_is_scoped` of #124, which treats every path of the unit being
> compiled as scoped.

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

> **Amended (I.2.1, I.3.3 rule 2).** Withdrawn. "Structure nodes are never
> linked" is wrong: the link is what makes an occurrence print with the
> other side's abbreviation name. `repr` must read structure nodes.

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

> **Amended (I.4).** Every node keeps a level cell, ground or not, and every
> level write is made. The table of tiers, the paragraph "Why skipping ground
> types is unobservable" and the three rules that return on a ground type
> are withdrawn: whether `instance` copies or shares a ground node is
> observable (I.2.3, fixtures 2 to 5). The argument against variable ranks
> stands.

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

> **Amended (I.2.1, I.3.3 rules 1 and 2).** Steps 1 to 3 and the paragraph
> "No structure links" are withdrawn. Step 2 ("it mutates nothing") and step
> 3 ("no level update") change identity and levels that later output reads.
> The third thing a structure link does is not only loop detection: it
> decides the printed name, the stored interface and, through immediacy, the
> JavaScript (I.2.4). Unification is `unify_types` and
> `unify_after_expansion` as they are. The paragraphs on rows, recursive
> types, `Tpoly`, packages and GADT constraints describe today's behaviour
> and stand, without their references to flags and interning.

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

> **Amended (I.5, P8).** Withdrawn. A table keyed by handle shares expansion
> nodes between occurrences, and an expansion node is a node that
> unification links (I.2.1, last two rows of the table). The per-node memo
> (`AbbrevMemoRef`) stays.

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

> **Amended (I.3.3 rule 3).** Withdrawn. `instance` copies every generic
> node, ground or not, once per copy session, and returns every other node.
> The one sound shortcut found is to return at once when the root is not
> generic (P1b, I.5).

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
   `occur_univar` ~~(skipped when `HAS_UNIVAR` is clear)~~ and
   `update_level_checked(l, ty)` ~~(skipped when `ty` is ground)~~, and
   returns `ty`. *Amended (I.3.3 rule 4): both always run. The level update
   of a ground type must be made; with #124 it is the cheap path.* The errors those two can raise are raised from the same call with
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

H.2.6 lists where today's `Env` API contradicts this section, and H.2.7
gives the corrected structure. Read them together with what follows.

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

- ~~`exp_type`, `pat_type` and the other `TypeExprRef` fields hold handles of
  the new tiers. Readers go through `TypeContext`, so they do not change.~~
  *Amended (I.3): the tiers do not change.*
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

> **Amended (I.2).** This section missed the main dependency: the name a
> type is printed with follows node identity, for every type, through
> structure links and through copy-or-share at `instance`. With today's core
> kept (I.3), D.1 to D.10 describe behaviour that does not change. Their
> references to the new core, to flags and to the export copy of non-ground
> nodes no longer apply.

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

> **Amended (I.3.3 rule 2).** Structure links stay, so the
> `unified_structure` side table is not needed. Loop detection is not the
> only reader of structure-node identity; see I.2.

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

> **Amended (I.2).** Incomplete. Node identity of structure nodes *is*
> output: it decides abbreviation names in diagnostics, in the stored
> interface and in genType output, and it decides the JavaScript of
> comparisons through immediacy (I.2.4). The three uses listed below are
> still free to change.

For completeness, uses of `TypeExprRef` identity that do not reach rule 1 or
rule 2 and may change freely: de-duplication in the typed-tree dump
(`arity_aliases`, node ids), `TypeExprRefMap` copy caches, `typeopt_answers`.

## E. The differential harness

> **Amended (I.6).** There is one core. E.1, E.2 and E.4 are not built. E.3
> is the oracle for every remaining stage; I.3.5 says what its build
> comparison catches and what it does not.

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

> **Amended (I.5, I.6).** Savings, dependencies and the hand-off column are
> updated in place. Struck-through text is the original.

| # | Stage | Depends on | Size (lines changed) | Saving | Hand to a less capable model |
|---|---|---|---|---|---|
| P0 | Differential tooling and counters | - | 600 | 0 | ~~yes~~ landed (#122) |
| P1 | ~~Ground flag and fast paths~~ Level updates of plain types without a snapshot | P0 | ~~900~~ 400 | ~~4-6%~~ 1.4% measured | ~~yes~~ done in #124; the rest of the original stage is withdrawn. Do not hand out any "skip ground types" task |
| P1b | `instance` returns a non-generic root at once (new, I.5) | P1; the fixtures of I.2.3 | 30 plus tests | 0.9% measured | yes: one function. Add the fixtures first; gate is no difference in `compare_checker_builds.py` on both projects |
| P2 | Infer instead of unifying with a fresh variable | P0 | 700 | 1.5-2.5% | application: yes; other constructs: one at a time, yes. The level update is never skipped (C.9, amended) |
| P3 | Publish into the shared pool; encode later | P0 | 1,200 | 2.5-3.5% | P3a (encode and summarise after dependents are released): yes, from H.1. P3b (build the graph and the digests without the portable form): yes, once the equality test of H.1.7 is in CI |
| P4 | Process-wide views; delete stamp replay | P3 | 2,500, mostly deletions | 2.5-3.5% | no |
| P5 | Absolute paths in exports; no lookup copies | P4 | 2,000 | 3-4% | no |
| P6 | Environment as a binding log | P0 | 2,500 | 3-4% | steps 1 to 5 of H.2.8: yes. The switch (step 6 on): yes with the corrected design of H.2.7, not with C.10 as written; first confirm the cost of path moves on the benchmark |
| P7 | Term store, closed waist, core switch | P1 | 2,000 | 0 | ~~yes~~ dropped: do not build |
| P8 | New core operations | P7 | 7,000 | ~~4-6% once on~~ 0 | ~~split: simple types yes; rows, univars, GADT no~~ dropped: do not build |
| P9 | Switch on | P8 | 500 plus fixes | 0 | ~~no (triage)~~ dropped |
| P10 | Segments, export tables, checker per worker | P5, P6 ~~, P9~~ | 3,000 | 2-3% | no. Re-scoped onto today's `TypeContext` (I.6): harder than as written |
| P11 | Walk cost in `typecore`/`typemod` | P2; conflicts with nothing else if kept small | 200-600 each | 4-6% total | yes, each |
| P12 | Delete the old core | P10, soak | -10,000 | 0 | ~~yes~~ dropped: there is no old core |

Parallel tracks (amended; the original had `P1 -> P7 -> P8 -> P9` on track A
and `P12` after P10):

```
A: P0 -> P1 -> P1b
B: P0 -> P3 -> P4 -> P5 ---\
C: P0 -> P6 ----------------+-> P10
D: P0 -> P2 -> P11 (continuous)
```

A, B, C and D touch different files except: P1 and P2 both edit `ctype.rs`
entry points lightly (land P1 first); P2 and P11 both edit `typecore.rs`
(one owner at a time); P5 and P6 both touch `env_lazy.rs` call sites of
`Env` (land P6 first if both are ready).

Stages P1 to P6 pay for themselves on today's representation. If the work
stopped after them, the estimated saving is about ~~17-23%~~ 15-20% of the
build (I.5), with no long-lived branch.

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

> **Amended (I.1, I.5).** Built in #124 as far as it is sound. Kept: the level
> update of a plain type without a snapshot, a declaration lookup or a retry
> (`lower_plain_levels`), writing the same levels. Withdrawn: the flags byte;
> the fast paths in `instance`, `copy_type_cached`, `generalize_rec`,
> `generalize_structure_rec`, `occurs`, `deep_occur`, `occur_univar` and
> `binding_facts`; binding a variable to a ground type without the walks.
> Invariant (3) is false: the level of a ground node decides copy or share
> (I.4). The interaction paragraph is wrong too: a ground node can be linked
> to `phantom<'a>` and reach an unbound variable (#124, concern (a)). Saving:
> ~~4-6%~~ 1.4% on the application, 0.7-0.8% on `tests/tests`, measured. The
> follow-up that is sound is P1b (I.5).

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
- **Hand-off.** The inventory is H.1. It corrects this stage in four
  places (H.1.4): the raw-signature copy stays whether or not genType is on;
  the portable encoding is always produced, because the next build of a
  watch session and the editor load units from it; the pool stays keyed by
  the registry's `Arc`; and store binders need their stamp mapping. The
  stage is split into P3a and P3b (H.1.5), with the order of operations in
  H.1.6 and the invariants in H.1.7.

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
  build-wide. *Amended (H.2.10): measured on the log built in step 4,
  binding and cloning are five times cheaper but a lookup is not cheaper
  than today's. Count on the snapshots and the persistent maps, at most
  2.5%, not on the lookups.*
- **Hand-off.** The inventory is H.2. It found that the scope tree of C.10
  cannot be built behind the existing API: environments are extended
  without any scope entry or exit, old environments are extended (1.3% of
  extensions on the test project), and environments cross compilations on
  a worker (H.2.6). H.2.7 replaces the scope tree by a tree of versions
  with one current path; H.2.8 gives the migration order and H.2.9 the
  invariants. `im-rc` stays, because `typemod.rs` uses it elsewhere, and
  `typed_envs` holds 16-byte values, not 8-byte ones, until P10.

### F.9 P7: term store, closed waist, core switch

> **Amended (I.6).** Dropped. It existed to carry P8.

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

> **Amended (I.5, I.6).** Dropped. None of the listed savings is both sound
> and specific to a new core; I.5 goes through them one by one. New estimate:
> 0.

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

> **Amended (I.6).** Dropped.

Bring `both` mode to zero differences (E.4 steps 2 and 3), package by
package. Each difference is either a bug in the new core or an undocumented
dependency on sharing or order; the second kind is added to section D with
its fix. Hand-off: no; this is triage.

### F.12 P10: segments, export tables, one checker per worker

> **Amended (I.3.3 rule 5, I.6).** Kept, on today's `TypeContext` and
> without `Terms`: one context per worker whose containers are cleared
> between modules, a shared initial-environment prefix, export tables in
> place of per-worker component views, and segments that hold every exported
> node with its sharing. Depends on P4, P5 and P6, not on P9. The reset list
> is today's context (about 100 fields, the overlays, about 40 hash maps),
> and type marking needs a visited set for frozen nodes before the level
> overlay can go (I.4). Saving 2-3%, estimated, not re-measured.

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

> **Amended (I.6).** Dropped. The deletions that remain are P4's (stamp
> replay) and whatever P10 makes dead.

E.4 step 4. About 10,000 lines removed. Hand-off: yes.

### F.15 Does it reach the target?

> **Amended (I.5).** No, not on these estimates. The stages now sum to 21-29%
> against the needed 30%, with 2.3 points measured. P1 delivered 1.4% of its
> 4-6%, P8's 4-6% is gone, and P1b adds a measured 0.9%. P1 to P6 with P1b
> give 15-20%. The paragraphs below are the original reading.

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

**G.1 Is the `HAS_SCOPED` rule complete?** *Amended (I.4): answered, no. A
weak variable of an earlier item keeps a level below a later item's types.
#124 widened the rule to every path of the unit being compiled
(`path_is_scoped`), with the debug cross-check.* The claim is that a type
constructor bound by a structure item never fails a level check afterwards
(C.2). It rests on `init_def` being called at each item and on levels never
dropping below an earlier item's stamps. Functor bodies, recursive modules
and first-class module signatures have not been traced in full.
*Recommendation:* P1 ships with the debug cross-check always on in debug
builds and in one CI job over all suites and the benchmark. If the check
ever fires, widen the flag (the safe direction) instead of adding a special
case.

**G.2 Keeping levels instead of ranks.** *Amended (I.4): settled. Levels
stay on every node, because the level of a structure node also decides copy
or share, which is observable.* This design keeps OCaml's node
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
way that reaches output?** *Amended (I.2): yes. P1 was the probe this
paragraph proposed, and it failed: identity decides the abbreviation name
of every type, in diagnostics, in the stored interface, in genType output
and, through immediacy, in the JavaScript.* Found: only `mark_loops_rec` (D.2). Not found by
exhaustive proof. *Recommendation:* P1 already changes sharing (ground types
are shared instead of copied) on today's core, so it is the cheap probe: if
P1 passes error parity and the benchmark comparison, the remaining risk in
P8 is confined to non-ground nodes, where D.2's side table applies.

**G.5 Recursive ground types are not interned.** *Amended (I.3.3 rule 5):
moot, nothing is interned.* A closed recursive
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

**G.8 Lock contention in the ground interner.** *Amended (I.3.3 rule 5):
moot, there is no interner.* A miss in the per-worker
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

**G.10 Two cores for several months.** *Amended (I.6): moot, there is one
core.* Shared code above the waist must
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

**G.14 The estimates.** *Amended (I.5): P1 was predicted at 4-6% and
delivered 1.4%. The share it started from was right (instantiation,
generalisation and level updates are 9.0% of the application's build,
against the assumed 8%); the fraction that can be removed was wrong, because
the ground part has to be done. So the other estimates are not rescaled by
one factor, but each one's "removable fraction" is unverified until the
stage is built.* Every saving is derived from sample shares, not
from a prototype. *Recommendation:* P1 is the calibration. It is small, it
is predicted at 4-6%, and its result should rescale the others before P7
and P8 are staffed.

## H. Inventories for P3 and P6

These two inventories are what F.5 and F.8 ask for before the stages are
handed over. Each lists what the code does today, what the stage does with
each piece, where the code contradicts the design above, and the correction.
Paths are relative to `compiler-rust/src/` unless they start with `rewatch/`.
Functions are named, not line-numbered.

What is measured, estimated and unknown is said where it matters. Nothing in
this section was measured on the 3,735-module application; the two
measurements in H.2 were taken on this repository's `tests/tests` project
(711 modules).

### H.1 P3: call-site inventory

#### H.1.1 Types that carry a signature between compilations

| Type | File | What it is |
|---|---|---|
| `Signature` | `types/decl.rs` | The items. Their `TypeExprRef`s are handles of whichever tier holds the nodes |
| `PersStruct` | `cmi/persistent_env.rs` | A unit as a compilation reads it: name, `ps_sig: Arc<Signature>`, file name, deprecation, CRCs |
| `PortableSignature` | `cmi/portable_types.rs` | A signature whose handles are indices into its own `PortableTypeGraph`, with a location table and the file names of its locations |
| `PortableRawSignature` | same | The same for the raw signature (H.1.3) |
| `PortablePersStruct` | same | What the registry holds: both signatures as `binser::Encoded` bytes, the fingerprint, `shareable`, a lazily computed `SignatureSummary`, and a `ReservedSignature` (the decoded signature, kept for the first dependent) |
| `SignatureSummary` | `cmi/item_deps.rs` | Per-item declaration digests (`item_hashes`) and per-item references (`refs`), computed from a `PortableSignature` |
| `ModuleRegistry` | `cmi/persistent_env.rs` | Name to `Arc<PortablePersStruct>` and to `InMemoryModuleInfo` (the `.cmj`-equivalent data). One shared map plus per-worker local maps (`for_worker_snapshot`) |
| `SharedGraph`, `SharedTypePool` | `types/shared_store.rs` | The immutable pages. The pool belongs to one build generation and maps the *address* of an `Arc<PortablePersStruct>` to the `PersStruct` built from it (`pers_struct`) |
| `ThreadTypeStore` | `types/thread_store.rs` | Per worker: the same address-keyed map (`pers_struct`, `insert_pers_struct`), signature indexes, component views |

Three facts about these types decide what P3 can and cannot do:

1. **The pool dies with the build.** `thread_store::begin_build` bumps the
   generation and `shared_store::pool_for` then returns a new pool. A unit
   that is not recompiled in the next build of a watch session is loaded
   again from its `PortablePersStruct`. The portable form is therefore needed
   for every published unit, not only when the incremental store asks.
2. **The pool is keyed by the address of the `Arc<PortablePersStruct>`** that
   the registry holds. Whoever pre-fills the pool must use that same `Arc`.
3. **The saved signature already names the unit's own items by absolute
   path.** `PersistentEnv::finalize_loaded_signature` rewrites `t` to `M.t`
   in place (`substitute_type_paths_in_sig`,
   `qualify_unit_sig_decl_paths_in_place`, `substitute_submodule_paths`)
   before the signature is serialised. B.4 step 2 and F.7 describe this as
   new work. It is not: what P5 removes is the copy made at lookup, which
   happens although the paths are already absolute.

#### H.1.2 The path today, in order

For a module without an interface file. `W` is the worker thread that
compiles the module, `S` the scheduler thread of `rewatch/src/build/compile.rs`,
`X` a worker that compiles a dependent, `D` the `digest-prep` thread.
"Blocks" says whether a dependent cannot start type checking until the step
is done.

| # | Step | Function (file) | Reads | Writes | Thread | Blocks |
|---|---|---|---|---|---|---|
| 1 | Simplify, check and normalise the inferred signature | `simplify_signature`, `coerce_to_inferred_signature`, `check_nongen_schemes`, `normalize_signature` in `compile_preprocessed_structure_in_process_until_js` (`driver.rs`) | typed structure | `published_signature` | W | yes |
| 2 | Take the stamps `Env.save_signature` would take | `saved_signature_copy` (`driver.rs`), `freshened_signature_bound_idents_from_kind` (`cmi/persistent_env.rs`) | signature | identifier counter only; the copy is dropped | W | yes |
| 3 | Collect what the typed tree read of other units | `unit_reads::structure_reads` | typed tree | `unit_reads` | W | yes |
| 4 | Copy A: the raw signature | `copy_lookup_signature_for_subst` (`types/typecore.rs`), first call | signature | new local nodes, `current_raw_sig` | W | yes |
| 5 | Copy B: the signature to finalise | `copy_lookup_signature_for_subst`, second call | signature | new local nodes | W | yes |
| 6 | Finalise copy B in place and install it | `PersistentEnv::register_in_memory_signature`, `finalize_loaded_signature`, `collect_alias_rewrites` | copy B | descriptors of copy B (`M.t` paths), the worker's `cache`, alias rewrites | W | yes |
| 7 | Register copy A as the raw signature | `TypeContext::register_gentype_raw_module_sig`, `register_raw_module_sig` | copy A | two maps of the `TypeContext` | W | yes |
| 8 | Walk copy B into a portable graph | `extract_module_update`, `serialize_pers_struct`, `serialize_signature`, `TypeGraphSerializer` (`cmi/portable_types.rs`) | copy B through `TypeContext` | `PortableSignature` | W | yes |
| 9 | Walk copy A into a second portable graph | same, for `find_raw_module_sig` | copy A | `PortableRawSignature` | W | yes |
| 10 | Fingerprint | `compute_type_graph_fingerprint`, `hash_signature` | portable graph | `u64` | W | yes |
| 11 | Item digests and references | `SignatureSummary::of`, `signature_refs` (`cmi/item_deps.rs`), called from `PortablePersStruct::encode` | portable signature | `summary` | W | yes |
| 12 | Encode both signatures | `binser::Encoded::encode` in `PortablePersStruct::encode` | portable signatures | bytes | W | yes |
| 13 | Encode again when the signature mentions a store binder | `ident::saving_store_stamps` with `TypeContext::saved_store_stamps` | same | bytes, stamps mapped to local ones | W | yes (rare) |
| 14 | Keep the decoded signature | `reserve_signature` | - | `for_dependent` | W | yes |
| 15 | Hand over | the `InProcessSignatureReadyHook` closure in `compile_module_in_process_to_js_boundary` (`rewatch/src/build/compile.rs`): `Arc::new`, channel send | - | `SignatureReadyMsg` | W | yes |
| 16 | Register and unblock | `apply_signature_ready`, `apply_pending_registry_updates`, `ModuleRegistry::register_module_arc`, `register_in_memory_interface`, `unblock_dependents` | fingerprint | registry, interface generation, ready heap | S | yes |
| 17 | Load in the first dependent | `find_pers_struct_unrecorded`, `portable_types::internalize_pers_struct` | registry entry | - | X | it is the dependent |
| 18 | Take or decode the signature | `signature_for_dependent` (takes the reserved one; later callers decode) | `for_dependent` or bytes | - | X | other workers needing the same unit wait on the pool's `OnceLock` |
| 19 | Build the shared graph | `internalize_signature_into_shared`, `SharedTypePool::publish`, `SharedSink`, `remap_signature_refs`, `import_signature_locations`, `ShapeImport` | portable signature | pages, a `Signature` with shared handles | X | same |
| 20 | Remember it | `SharedTypePool::pers_struct`, `ThreadTypeStore::insert_pers_struct`, `cache_insert`, `record_alias_rewrites`, `register_raw_module_sig` | - | pool slot, worker map, worker cache | X | - |
| 21 | Raw signature on demand | `register_gentype_portable_raw_module_sig`; later `get_gentype_raw_module_sig`, `internalize_raw_signature` | raw bytes **and a full decode of the main signature** (for its file names) | local nodes | X | no |
| 22 | Component view, lookup copy | A.5 steps 5 to 7 | shared signature | P4 and P5 | X | - |
| 23 | Record the dependent's reads | `ModuleRegistry::resolve_signature_reads`, `RegistryUnitSource::refs` | `summary().refs` of every unit read | read sets | X, after its own type check | no |
| 24 | Digests and stored form | `DigestPrep` (`registry.item_digests`, `encode_stored_module_parts`) | `summary().item_hashes`, the encoded bytes, `InMemoryModuleInfo` | `published_item_digests`, `prepared_interfaces` | D, after the module completes | no |

Variations:

- **Interface file.** `typecheck_preprocessed_signature_in_process`
  (`driver.rs`) does steps 2, 4 (one copy, the raw signature the
  implementation is later checked against), 6, 7, 8 to 14 and returns. The
  caller sends `SignatureReady` itself. `resolve_signature_reads` for the
  interface runs on W *before* that send; it reads only dependencies'
  summaries.
- **Location-free first attempt.** When the parse arena stores no locations
  the hook is not called at step 15 but after Lambda lowering, because a
  diagnostic may force a retry with locations. Steps 4 to 14 still run
  before lowering.
- **Unchanged interface in a build without cut-off rounds**
  (`defer_clean_signatures`). A module whose fingerprint equals the previous
  one does not release its dependents at step 16. They wait until its JS
  metadata is final, and then `BuildCommandState::record_published_digest`
  computes `item_digests` **on S**. This is the only place where a digest is
  on the path of a dependent.
- **Not shareable.** `graph_is_shareable` is false only for a graph that
  holds a `Tsubst`. Such a unit, or one published when the pool is full, is
  loaded per worker (`internalize_signature_into_store`) or per compilation
  (`internalize_signature`), each of which decodes.

Other writers of the registry, unchanged by P3: `register_namespace_for_package`
(alias-only signature, empty graph), `LazyStoredModules::materialize_with`
(decodes a stored unit on first lookup), `register_stored_static` (the
embedded runtime), `register_disk_module`, the runtime precompile in
`rewatch/src/build/compile.rs`, `cli/bsc.rs`, and the playground through
`extract_all_cached_modules`.

#### H.1.3 Readers, and what each needs

| Reader | Function | Needs | When |
|---|---|---|---|
| Dependents' type checking | `internalize_pers_struct` | the signature as shared nodes | before the dependent starts |
| Scheduler | `apply_signature_ready` | `fingerprint` | before dependents are released |
| Scheduler, unchanged interface only | `record_published_digest` | `summary().item_hashes` and the JS metadata | when the metadata is final |
| The module itself, during lowering | `find_pers_struct` of its own name (`Typeopt` expansions, optional-pattern lowering) | the finalised `PersStruct` in the worker's `cache` | until `unregister_in_memory_signature` in `finish_preprocessed_structure_in_process_from_js_boundary_with_metadata_hook` |
| The module itself | `flat_make_paths_of_signature`, with `get_gentype_raw_module_sig` | the raw signature (local identifiers) | after lowering, **with or without genType** |
| The implementation of a module with an interface | `check_compunit_inclusion_for_errors`, `implementation_interface_signature`, `read_raw_sig_shared` | the interface's raw signature | inclusion check |
| Local-module alias resolution | `self_alias_raw_parent_module_item` (`types/env_lazy.rs`), `find_raw_module_sig` | the raw signature of a loaded unit | lookups |
| genType | `persistent_alias_module_type` (`gentype/translate_structure.rs`) | the raw signature of the unit and of dependencies | after type checking |
| Read sets | `resolve_signature_reads`, `lambda_reads` | `summary().refs` of dependencies | after each dependent's type check; at the end of the build |
| Incremental store, writer | `DigestPrep`, `UnitDigests` and `encode_stored_module_parts` (`rewatch/src/build/incremental.rs`), `state_db.rs` | `item_digests`, the whole `PortablePersStruct` encoded with the module info and genType declarations (`cmi/stored_module.rs`) | after the module completes; at the end of the build |
| Incremental store, reader | `register_stored_parts`, `decode_stored`, `materialize_with` | bytes to `PortablePersStruct` | start of the next process |
| Watch mode, next build | step 17 again for every unit that was not recompiled | the encoded signature | next build |
| Editor tooling | `WatchProject::registry`, `typecheck_structure_for_tooling` (`rewatch/src/build/tooling.rs`, `driver.rs`) | a registry snapshot; loads units like a dependent | on demand, possibly between builds |
| Playground | `extract_all_cached_modules` | `serialize_pers_struct` of every cached unit | after a compile |

The methods of `PortablePersStruct` and their callers:

| Method | Callers | Before dependents are released |
|---|---|---|
| `fingerprint` (field) | signature hook, interface path, `RegistryUnitSource::refs` (cache key) | yes |
| `signature_for_dependent()` | `internalize_pers_struct` (three branches) | no: it is the dependent |
| `signature()` | `summary()` on first use; `internalize_raw_signature` (file names only); `RegistryUnitSource::refs` when a unit is registered under another name | no |
| `raw_signature()`, `has_raw_signature()` | `internalize_raw_signature`, `internalize_pers_struct` | no |
| `summary()` | `item_deps::item_digests`, `RegistryUnitSource::refs` | only in the unchanged-interface case above |
| `release_signature_for_dependent()` | `apply_pending_registry_updates` (a unit without dependents) | on S |
| `shareable` (field) | `internalize_pers_struct` | - |

#### H.1.4 Where the code contradicts F.5

1. **"The two saving copies are reduced to the one genType needs (and that
   one is skipped when genType is off)."** Copy A is not genType's alone. It
   is the raw signature that `flat_make_paths_of_signature` reads for every
   module, that an implementation is checked against when the copy is of an
   interface, that `env_lazy.rs` reads to resolve aliases, and that is
   shipped to dependents as `PortableRawSignature`. It cannot be skipped
   when genType is off. Copy B exists because step 6 rewrites paths in
   place; it goes away when the rewrite happens during the walk of step 8.
   *Correction:* P3 removes copy B, keeps copy A. Whether copy A can be the
   uncopied `published_signature` once nothing rewrites it in place is a
   separate change, gated by genType parity and by the fixtures that check
   an implementation against its interface.
2. **"The portable encoding is produced ... only when the incremental store
   or a non-shareable consumer asks."** By fact 1 of H.1.1 it is needed for
   every unit that a later build of the same process, or the editor, may
   load. *Correction:* always produce it, off the path of dependents.
3. **"Registers the resulting `PersStruct` in the shared pool under the
   unit's name."** The pool is keyed by the address of the registry's `Arc`
   (fact 2). *Correction:* keep the key; the publishing worker creates the
   `Arc<PortablePersStruct>` and fills the pool slot for it before it sends
   `SignatureReady`.
4. **Digests "computed by hashing that graph".** The hashing code
   (`hash_sig_item` and its helpers, `RefWalker`) reads
   `PortableTypeEntry`. Only the fingerprint is needed before dependents are
   released (plus `item_hashes` in the unchanged-interface case). Hashing a
   `SharedGraph` instead needs a second reader for the same functions and a
   proof that both give the same digests.
5. **Not mentioned: store binders.** A signature can mention an identifier
   created in a worker's store (a functor application's result). Step 13
   saves it with the local stamp it stands for, so that the saved form does
   not depend on which worker built the store data. A shared graph built
   straight from the `TypeContext` must apply the same mapping to the
   identifiers of signature items and to the paths in type nodes.
6. **Not mentioned: `internalize_raw_signature` decodes the whole main
   signature** to read `cmi_longident_names`. That is a decode per unit and
   per compilation that asks for a raw signature.
7. **Not mentioned: the second graph.** Step 9 walks and step 12 encodes the
   raw signature for every unit, although most dependents never ask for it.

#### H.1.5 What P3 does with each step

P3 is split in two. P3a moves work without changing any data structure that
is read. P3b removes the portable form from the path altogether.

**P3a (hand-off: yes).**

| Step | Disposition |
|---|---|
| 1 to 7 | keep |
| 8, 10 | keep on W |
| 9 | keep on W (it needs the `TypeContext`) |
| 11 | **move**: `summary` stays a `OnceLock`, filled by its first reader. Readers are X after its type check, D, and S in the unchanged-interface case; for that case W fills it before it sends `JsMetadataReady`, so S only reads |
| 12 | **move**: `PortablePersStruct` holds the decoded `PortableSignature` and `PortableRawSignature` in a mutex-guarded slot and the bytes in a `OnceLock`. `signature()`, `raw_signature()` and serialisation (a hand-written `Serialize`, since `cmi/stored_module.rs` encodes the struct by reference) fill the `OnceLock` from the slot and empty the slot. D is the first to ask, after the module completes. Drivers without a digest thread (`cli/bsc.rs`, the runtime precompile, tooling, the playground) encode on first use |
| 13 | **replace**: when `saved_store_stamps` is not empty, W applies it to the decoded signatures in place before step 10: a walk over the identifiers of the items and the paths of the graph entries. The graph W builds and the bytes D encodes are then what today's decode returns. The second encode goes away |
| 14 | **replace** with step 19 on W: after step 10, W wraps the struct in its `Arc`, builds the shared graph from the decoded signature it still holds (`internalize_signature_into_shared`, unchanged) and fills the pool slot (`SharedTypePool::pers_struct`) and its own worker map. `ReservedSignature`, `signature_for_dependent` and `release_signature_for_dependent` are **deleted** |
| 15, 16 | keep. The hook and the result structs of `driver.rs` (`InProcessSignatureReady`, `InProcessPreJsCompileResult`, `InProcessJsMetadataReady`, `InProcessInterfaceResult`, `InProcessCompileResult`) carry `Arc<PortablePersStruct>` so that the address W used is the one the registry stores |
| 17 | keep. In the same build the pool slot is filled, so the closure passed to `pers_struct` does not run |
| 18, 19 | run only for a unit that this build did not publish (stored, or published by an earlier build of a watch session), for the non-shareable fallback and when the pool is full; then they decode as today |
| 20, 22, 23, 24 | keep |
| 21 | **fix**: store `cmi_longident_names` in `PortableRawSignature` (or beside the encoded signature) so that no main signature is decoded for it |

What P3a saves is the encoding and the summary on W (they move to D or to
their first reader), the decode or the retained copy on X, and the build of
the graph on X while other workers wait for it. Shares of the 4.6% are not
measured; P0's counters should split publishing into walk, fingerprint,
summary, encode, and load.

What P3a costs: the decoded signatures live from publication until D has
encoded them, where today only the first dependent's copy does.
`PortablePersStruct`'s documentation says the decoded form was once the
largest part of a large build's memory, so peak memory on the benchmark is
part of the gate.

**P3b (hand-off: after its equality test is green).**

| Step | Disposition |
|---|---|
| 5, 6 | **replace**: no copy B. The path rewrite of `finalize_loaded_signature` becomes a map applied while walking (`build_subst_maps_for_module` already computes it). The module's own `cache` entry (the reader "the module itself, during lowering") gets the shared `PersStruct` |
| 8, 19 | **replace** with one walk: `TypeGraphSerializer` gets a sink trait with two implementations, the portable graph and `SharedGraphParts`. The walk must also do what `internalize_signature_into_shared` does besides nodes: locations (`DeclLocTable`, `DeclLocKind::Shared`), file names (`SharedTypePool::intern_longident_name`), variant layouts and shapes (`ShapeImport`), object-field mutability cells, the level of `Tlink` entries, and the store-binder mapping of contradiction 5 |
| 10, 11 | **replace**: the hash functions read through a trait implemented for `HashGraph` and for a shared graph. The portable implementation stays, for stored units |
| 12 | D serialises the frozen graph into the portable form: the inverse of `internalize_desc`, reading `SharedPages` without a `TypeContext` |

P3b is where a mistake changes what dependents see, so it lands only with
the test of H.1.7 invariant 5 running in CI.

#### H.1.6 Order of operations after P3

After P3a, for a module without an interface:

1. W: type check; steps 1 to 7.
2. W: walk the signature and the raw signature into portable graphs.
3. W: fingerprint.
4. W: create `Arc<PortablePersStruct>` holding the decoded signatures (no
   bytes, no summary).
5. W: build the `SharedGraph`, publish its pages, fill the pool slot for the
   `Arc` and the worker's own map.
6. W: send `SignatureReady` with the `Arc` and the fingerprint (after
   lowering instead, for a location-free attempt).
7. S: register the `Arc`, compare fingerprints, release dependents.
8. X: `internalize_pers_struct` finds the pool slot filled; no decode, no
   graph build.
9. W, in parallel with 7 and 8: lowering, JS. Before `JsMetadataReady` in a
   build without cut-off rounds: fill `summary`.
10. D, after `Completed`: fill `summary` if empty, encode both signatures,
    compute `item_digests`, encode the stored module.
11. End of build: `DigestPrep::finish`; the incremental store is written.
12. Next build in the same process: `begin_build` drops the pool. A unit
    that is not recompiled is loaded from its bytes (steps 17 to 20 of
    H.1.2), which D produced.

After P3b, steps 2 and 5 are one walk, step 3 hashes the graph, and step 10
serialises from the frozen graph.

#### H.1.7 Invariants a reviewer can check

1. **No encoding before release.** Between the end of type checking and the
   `SignatureReady` send, W calls neither `binser::Encoded::encode` nor
   `SignatureSummary::of`. Check with a debug-only thread-local flag set
   around that interval and asserted in both functions.
2. **No decode in the publishing build.** In a clean build of any project,
   `binser::Encoded::decode` of a signature runs only for stored units and
   non-shareable units. Add a counter to `perf_counters.rs`; a clean build
   of `tests/tests` must report zero for units compiled in that build.
3. **One `Arc` per publication.** The address W fills the pool with is the
   address in the registry: `SharedTypePool::pers_struct` called by X for a
   unit published in this build never runs its closure (same counter).
4. **Bytes are always produced.** After `DigestPrep::finish`, every
   registered unit of the build has its bytes; an edit-free second build in
   a watch session loads every unit without compiling it. The `rewatch`
   watch and incremental tests cover this.
5. **Same data (P3b).** For every unit of the standard library and of
   `tests/tests`: the fingerprint and every `item_hashes` entry computed
   from the shared graph equal those computed from the portable form, and
   serialising the frozen graph gives bytes equal to the bytes P3a encodes.
   Keep both paths behind a debug switch until this holds in CI.
6. **Raw signature unchanged.** `flat_make_paths_of_signature`, the
   interface inclusion check and genType read the same raw signature as
   before: genType output parity and the `super_errors` interface-mismatch
   fixtures.
7. **Determinism.** The bytes written to the incremental store for a unit do
   not depend on the worker count (build `tests/tests` with 1 and with 8
   workers and compare the stored interfaces).
8. **Scheduling unchanged.** A watch-mode edit that changes an interface and
   one that does not recompile the same dependents as before (the gate of
   F.5).

Unknown: whether any published graph is ever non-shareable in practice
(`Tsubst` in a saved signature); how many compilations have a non-empty
`saved_store_stamps` table, and of those how many signatures mention a
store binder; how the 4.6% splits between the steps.

### H.2 P6: API inventory

#### H.2.1 What an `Env` is today

`Env { id: u64, scope_id: u64, data: Rc<EnvData> }` (`types/env.rs`).
`EnvData` holds seven tables and six small fields:

| Field | Type | Meaning |
|---|---|---|
| `values`, `types`, `modules`, `module_components`, `modtypes` | `IdTbl<T>` | local bindings (a persistent map plus a list of the last 16), under a chain of opened layers |
| `constrs`, `labels` | `TycompTbl<T>` | the same, keeping every binding of a name |
| `functor_args` | `HashSet<Ident>` | modules bound by `add_module_arg` |
| `local_constraints` | persistent map `Path -> TypeDeclaration` | GADT equations |
| `type_label_families` | persistent map `Ident -> LabelArrayRef` | the label array of each local record type |
| `implicit_open_roots` | persistent set of names | `Pervasives`, `Stdlib` |
| `flags` | `EnvFlags` | `in_signature`, `implicit_coercion` |
| `pending_open_slot` | `Option<u32>` | armed before an open, cleared after it |
| `scope_caches` | `Rc<ScopeCaches>` | memo tables, replaced when `scope_id` changes |

The API is a mutable value: callers clone an `Env` and call `add_*` on the
clone. There is no call that enters or leaves a scope. `Clone` gives the
copy a new `id`; `clone_preserve_id` keeps it. Every `add_*` gives a new
`id`; those that change what module-path resolution reads also give a new
`scope_id` (`bump_scope`).

*Amended (H.2.10): steps 1 to 3 of H.2.8 are merged. `Clone` keeps the
`id`, `clone_preserve_id` and `pending_open_slot` no longer exist, and the
methods H.2.2 lists as having no callers are deleted, except the five
`fold_*_names` beside `fold_modtype_names`, which are still there and still
unused.*

#### H.2.2 Operations

"Sites" counts textual call sites outside `types/env.rs`, tests included.
Hot callers are named where the code shows them; how often each runs per
build is not measured, except for the totals in H.2.5.

**Extend.**

| Operation | Returns | Scope change | Sites | Callers | Notes for the log |
|---|---|---|---|---|---|
| `add_value(id, desc)` | - | no | 11 | `typecore.rs`: `add_pattern_variable_value`, `type_let_bindings`, `type_for`, `type_for_of`; `typemod.rs`: `type_structure_item`, `add_signature_items_to_env`; `includemod.rs`: `add_sig_item_to_env`; `cmi/persistent_env.rs`: `add_signature_to_env_with_options_inner` | one entry |
| `add_type(id, decl)` | - | yes | 17 | `typemod.rs`: `type_structure_item`, `transl_sig_type_declarations_with_ids_and_originals`; `typecore.rs`: `type_newtype`, `peel`; `ctype.rs`: `create_reified_constr`; `env_lazy.rs` | one entry; also *removes* the type's label family |
| `store_type(ctx, id, decl)` | - | yes | 18 | `typemod.rs` (14): `check_type_decl`, `transl_sig_type_declarations_with_ids_and_originals`, `compute_type_variance_fixpoint`, `add_signature_items_to_env`, `transl_signature`; `includemod.rs`; `variant_layout.rs`: `resolve_shapes`; `raw_lambda/convert.rs`: `init_shape_struct` | `add_type`, then a label family and one label entry per field, last field first |
| `update_type_variance(id, variance)` | new declaration | yes | 3 | `typemod.rs` | a new entry for the same identifier; keeps the label family |
| `add_type_label_family(id, array)`, `type_label_family(id)` | - / array | no | 2 / 7 | `typemod.rs`; `typecore.rs`: `find_type_label_family` | an entry keyed by the type's identifier |
| `add_constructor(id, desc)` | - | no | 7 | `typemod.rs`: `type_structure_item`, `transl_type_extension`; `typecore.rs`: `type_letexception` | one entry |
| `add_label(id, desc)` | - | no | 3 | `typemod.rs`, `cmi/persistent_env.rs` | one entry |
| `add_module(id, decl)` and `add_module_with_component_context(..)` | - | yes | 47 / 2 | `typemod.rs` (19): `type_structure_item`, `transl_recmodule_modtypes`, `approx_signature`, `decl_module_type_from_typed_module_type`; `typecore.rs`: `type_letmodule`; `ctype.rs`: `strengthen_signature_for_module_access_path`; `raw_lambda/convert.rs`: `init_shape_struct`; `env_lazy.rs` | two entries (declaration and component thunk). **Captures the environment before the binding** as the thunk's `seed_env` |
| `add_module_arg(id, decl)`, `is_functor_arg_path(path)` | - / bool | yes | 7 / 3 | `typemod.rs`; `raw_lambda/typeopt.rs`: `abstractness` | `add_module` plus a marker entry |
| `add_modtype(id, decl)` | - | yes | 16 | `typemod.rs`, `includemod.rs`, `ctype.rs`, `env_lazy.rs` | one entry |
| `add_prebuilt_open_layers(root, layers)` | - | yes | 2 | `cmi/persistent_env.rs`: `open_components_into_env`, `add_signature_to_env_with_options_inner` | one open entry holding `Rc<OpenedLayers>`, the root path and the slot. This is the only way anything is opened |
| `set_pending_open_slot(slot)` | - | no | 7 | `typecore.rs`: `type_open`; `typemod.rs`: `transl_signature`, `type_structure_item` | not an entry: make it an argument of the open (H.2.8 step 1) |
| `add_local_constraint(path, decl)` | - | yes | 3 | `ctype.rs`: `add_gadt_equation`; `typecore.rs`: `add_missing_local_constraints` | one entry keyed by path; called on the unify state's own `Env` |
| `add_gadt_instance_level()` | - | yes | 2 | `typecore.rs` | an entry with no payload |
| `mark_implicit_open_root(name)` | - | yes | 2 | `driver.rs`: `load_pervasives` | one entry |
| `implicit_coercion()`, `in_signature(b)` | new `Env` | no | 1 / 0 | `typemod.rs` | a flags entry |
| `update_value_type_by_name(name, ty)` | bool | no | 1 | `typecore.rs`: `duplicate_ident_types_for_gadt_cases` | **replaces** the innermost binding of `name`, also when it comes from an open (H.2.4) |

**Look up.**

| Operation | Returns | Sites | Hot callers | Relies on |
|---|---|---|---|---|
| `find_value_arc_with_path(name)` | path and description | 1 | `typecore.rs`: `lookup_value_by_lid` (every unqualified identifier) | innermost binding; `Pident` for a local binding, `Pdot(root, name, pos)` through an open |
| `find_value`, `find_value_with_id` | description | 4 | `typecore.rs`: `ensure_string_idx`, `lookup_value_for_arity_suggestion`, `duplicate_ident_types_for_gadt_cases` | same |
| `lookup_value(path)` | description | 4 | `typemod.rs`: `push_sig_values_from_env_pattern`; `env_lazy.rs` | `Pident`: exact identifier; `Pdot`: by last name |
| `find_type_arc_with_path`, `find_type_with_path`, `find_type` | declaration | 10 | `typecore.rs`: `resolve_type_constructor_path`; `ctype.rs`: `unify_types`, `is_instantiable`, `add_gadt_equation`; `printtyp.rs`: `non_shadowed_pervasive_or_stdlib` | innermost binding |
| `find_type_by_ident`, `find_type_arc_by_ident` | declaration | 9 | `ctype.rs`: `try_expand_head_with_mode`, `get_level_in_env`, `lookup_type_decl_for_path`; `typemod.rs` | **exact identifier, never through an open**; a stamp-0 identifier matches a persistent one of the same name |
| `lookup_type(path)`, `lookup_type_arc_by_ident` | declaration | 22 | `typecore.rs` (10): `lookup_raw_type_decl_from_module_path`, `resolve_type_constructor_path`; `ctype.rs`: `try_expand_head_with_mode`, `nondep_type_rec`; `raw_lambda/typeopt.rs`: `find_type_decl`; `raw_lambda/matching.rs`: `build_descriptions` | exact identifier, **then by name** (a documented recovery); `Pdot` goes through `lookup_module` |
| `find_all_constructors_marking(name)`, `find_all_constructors(name)` | candidates, newest first; with marking, each candidate's open slot and the first candidate that open hides | 4 | `typecore.rs`: `disambiguate_constructor`, `with_record_labels`, `pattern_contains_generalized_constructor` | candidate order; the hidden candidate |
| `find_all_labels_marking(name)`, `find_all_labels(name)` | same | 13 | `typecore.rs`: `disambiguate_label`, `type_pattern_record`, `type_record`, `use_in_scope_label_of_type`, `lookup_label_by_expected_type` | same |
| `find_constructor`, `find_label` | innermost | 4 | `typemod.rs`, `typecore.rs` | innermost |
| `find_module_with_path`, `find_module_with_id`, `find_module` | declaration | 30 | `typecore.rs`: `resolve_module_access_path_for_lid`, `resolve_module_lid_impl`, `with_resolved_module_components_for_lid_inner`, `open_module_lid_components_into_env`; `typemod.rs`: `lookup_module_path_for_module_expr`, `lookup_module_paths_by_lid` | innermost; path as for values |
| `find_module_same`, `lookup_module_ident_exact`, `has_module_ident` | declaration / bool | 12 | `ctype.rs`: `normalize_path_full_inner`; `typecore.rs`: `module_alias_target_for_path` | exact identifier, never through an open |
| `lookup_module(path)`, `lookup_modtype(path)`, `find_modtype*` | declaration | 56 | `typemod.rs` (23), `typecore.rs`, `includemod.rs`, `raw_lambda/convert.rs` (7) | built on the above |
| `with_local_module_components`, `local_module_components_shared` | the component thunk of a local module | 5 | `typecore.rs`: `with_resolved_module_components_for_lid_inner`; `env_lazy.rs` | exact identifier; the thunk is shared, not copied |
| `open_slot_use(kind, name)` | slot of the open a name resolves through, and whether that open hides an earlier binding | 1 | `typecore.rs`: `mark_open_name_use` | D.7 |
| `path_starts_with_opened_component`, `path_starts_with_implicit_opened_component` | bool | 4 | `ctype.rs`, `env_lazy.rs` | `find_module_with_path` and the implicit roots |
| `find_local_constraint(path)`, `has_local_constraints()`, `iter_local_constraints()` | declaration / bool / all | 10 / 6 / 1 | `ctype.rs`: `unify_types`, `try_expand_head_with_mode`; `typecore.rs` | `has_local_constraints` must stay a field read: it is tested on every `unify` |
| `normalize_path`, `normalize_path_prefix` | path | 15 | `ctype.rs`, `includemod.rs`: `strict_normalized_alias_path`; `typecore.rs` | `lookup_module` |
| `is_in_signature`, `is_implicit_coercion` | bool | 13 | `includemod.rs`, `typecore.rs`, `typemod.rs` | flags |

**Iterate.** Only three iterations have callers:

| Operation | Caller | Order matters |
|---|---|---|
| `iter_values()` | `typecore.rs`: `apply_letmodule_local_path_cleanup` (every visible value, opened ones included) | no |
| `iter_local_constraints()` | `typecore.rs`: `add_missing_local_constraints` | no |
| `fold_modtype_names()` | `typemod.rs`: `unbound_modtype_alternatives` (the spelling suggestion for an unbound module type) | **yes**: it reproduces the visit order of OCaml's `Ident.fold_name` per layer (`ident_tbl_fold_name_order`), and the order reaches a diagnostic |

No callers (delete before the migration): `in_signature`,
`find_value_with_path`, `find_type_with_id`, `find_modtype_with_id`,
`find_constructor_with_origin`, `find_label_with_origin`, `iter_types`,
`iter_constructors`, `iter_labels`, `iter_modules`, `iter_modtypes`,
`fold_type_names`, `fold_value_names`, `fold_module_names`,
`fold_constructor_names`, `fold_label_names`, and with them
`IdTbl::visible_local_entries` outside `with_current_local_module_aliases`.
`IdTbl` and `TycompTbl` are re-exported by `types/mod.rs` and used nowhere
else.

**Identity.**

| Operation | Sites | Used as |
|---|---|---|
| `id()` | 24 | `TypeContext::store_typed_env` (de-duplication of snapshots); `TypeContext::check_abbrev_env` (clears the abbreviation memos when the id differs from the previous call's); `UnifyState::set_env` (skip when equal); `raw_lambda/typeopt.rs` (`typeopt_answer` cache key); `typecore.rs`: `pattern_env_ref` and the argument-typing code compare the unify state's environment with the current one |
| `scope_id()` | 18 | cache keys in `TypeContext`: `find_type_newtype_level` (`get_level_in_env`), `find_normalized_path_full`, `find_resolved_module_type`, and the component cache keys built by `module_components_cache_key` and `scope_local_module_cache_key` in `typecore.rs` |
| `clone()` | about 150 lines mention an environment clone in `typecore.rs` (52), `typemod.rs` (77), `includemod.rs` (12), `ctype.rs` (6), `cmi/persistent_env.rs` (5) | a new value to extend, or a snapshot |
| `clone_preserve_id()` | 23 | a snapshot of the same environment |

There is no summary (OCaml's `Env.summary`) in the Rust `Env`.

#### H.2.3 Environments that outlive the scope that made them

| Holder | File | Lifetime | Read or extended later | "A position" is enough |
|---|---|---|---|---|
| `TypeContext::typed_envs` (`Vec<Rc<Env>>`), behind every `EnvRef` of the typed tree: `pat_env`, `exp_env`, `ctyp_env`, `mod_env`, `mty_env`, `sig_env`, `str_env`, `str_final_env`, `Texp_open`, `Tcoerce_alias` | `types/context.rs`, `types/typedtree.rs` | the module | read by lowering (`raw_lambda/convert.rs` 6 uses of `get_typed_env`, `matching.rs` 5), by diagnostics (`driver.rs`), by genType (`translate_structure.rs`, one use), by `typecore.rs` (3). **Extended** by lowering: `convert.rs` clones one and calls `add_module`, `add_modtype`, `store_type` (`init_shape_struct`) | yes, if an old position can be extended |
| `StoredModuleComponents::seed_env` | `types/env_lazy.rs` | as long as the binding's thunk; **across compilations** for thunks built in a store build (they sit in `OpenedLayers::module_components` and in the worker store's views) | read and **extended** when the thunk is forced (`build_local_module_components`), long after the binding | only if environments of other compilations stay valid |
| `ChildScanCursor::working_env` | `types/env_lazy.rs` | the component table; across compilations for store-built tables | **extended incrementally** each time a later lookup scans further | same |
| The initial environment | `ThreadTypeStore::initial_env`, `env::initial_env` | the worker's store (a build) | cloned and extended by every compilation on the worker | same |
| `UnifyState::env`, `UnifyStateSnapshot::env` | `types/ctype.rs` | a unification, or a backtracking snapshot | **extended in place** with GADT equations through `env_mut` | yes |
| `DelayedUnusedCheck::env` | `types/typecore.rs` | until delayed checks are forced at the end of the module | read by `parmatch` | yes |
| `PendingMatchCase::case_env`, `PendingSequentialMatchCase::case_env` | `types/typecore.rs` | until the case bodies are typed | read and extended | yes |
| The `envs` of the signature `Scope` | `types/typemod.rs` | one traversal | read | yes |
| `RecModuleTypes` | `types/typemod.rs` | typing a recursive module group | read and extended | yes |
| `Printtyp::printing_env` | `types/printtyp.rs` | one diagnostic | read | yes |
| Error reports | `driver.rs`: `format_wrong_name_report` takes an `Rc<Env>` from `get_typed_env` | one diagnostic | read | yes |

The editor analysis (`analysis/`) and `rewatch` do not call `get_typed_env`
or any `Env` method: they read the typed tree and `TypeContext`. `gentype/emit_js.rs`
has its own unrelated `Env` type.

Three consequences:

1. An old environment is not only read, it is extended, by the checker and
   by the backend.
2. Environments cross compilations on a worker (the initial environment and
   everything reachable from store-built views).
3. "Captured in a closure" does not occur: delayed work stores an `Env`
   value in a struct.

#### H.2.4 Behaviour of the persistent tables that callers rely on

1. **A snapshot never changes.** Every holder in H.2.3 relies on it.
2. **Shadowing.** The innermost binding of a name wins; an open shadows
   everything bound before it and is shadowed by everything bound after it.
3. **Lookup by identifier ignores opens** (`IdTbl::find_by_ident`, OCaml's
   `IdTbl.find_same`), and matches a stamp-0 identifier against a persistent
   one by name.
4. **The path of a result** is `Pident(id)` for a local binding and
   `Pdot(root, name, pos)` for one found through an open, with the position
   stored in the open's table.
5. **Constructors and labels return all candidates**: the bindings of the
   current layer newest first, then the opened table's entries in their
   stored order, then the layers below. With marking, a candidate from an
   open carries the open's slot and the first candidate that the open hides
   (the candidate that follows the open's block).
6. **`include`** adds each item of the signature as a local binding
   (`add_signature_to_env_with_options_inner` with `as_opened` false);
   **`open`** adds one layer per table, built once per opened signature and
   shared (`OpenedLayers`). An empty table adds no layer.
7. **Replacement in place.** `update_value_type_by_name` replaces the
   description of the innermost binding and leaves its identifier, its
   position and, for a binding that comes from an open, its `Pdot` path and
   its slot as they were. Snapshots taken before keep the old description.
   This is OCaml's `Env.copy_types`, used for GADT matches.
8. **Removal.** `add_type` removes the label family of the identifier it
   binds; `update_type_variance` does not.
9. **`scope_id` is stable across value, constructor and label bindings**, so
   that caches of resolved paths survive ordinary `let` bindings.
10. **`id` changes on every clone** (*until step 3 of H.2.8; a clone now
    keeps it*)**.** `check_abbrev_env` therefore clears the
    abbreviation memos when it is called with a clone of the previous
    environment. Whether any output depends on those extra clears is not
    known.
11. **Iteration order** matters in one place (`fold_modtype_names`).
12. **`has_local_constraints` and `find_local_constraint` are on the path of
    every unification** and are a field test in the common case.

#### H.2.5 Measured: how environments are extended and read

A temporary counter (not committed) recorded, for a build of `tests/tests`
(711 modules), the tree formed by environment versions: each `add_*` makes a
new version whose parent is the version it extended; a clone is the same
version. The "current path" is the path from the root to the newest
version.

| Quantity | Value |
|---|---|
| Extensions | about 52,000 |
| Lookups through the `find_*`, `lookup_*` and `iter_*` methods of `Env` | about 559,000 |
| Extensions of a version that is not on the current path, counting extensions only | 678 (1.3%) |
| Lookups at the newest version | 413,600 (74%) |
| Lookups at an older version on the current path | 140,000 (25%) |
| Lookups at a version off the current path | 5,200 (0.9%) |
| Deepest chain of versions | 1,268 |
| Entries undone or redone if the current path is moved to each version that is read or extended off it | 116,000 in total, 0.19 per operation; 1,228 for the longest move |

The off-path extensions come from `type_let_bindings`,
`type_structure_unscoped`, `includemod::add_sig_item_to_env`,
`add_pattern_variable_value`, `build_local_module_components`,
`ctype::add_gadt_equation`, `variant_layout::resolve_shapes`,
`type_function_nary`, `typemod::closed_modtype` and `load_pervasives`, among
others: it is not one construct that can be special-cased.

Not measured: ~~the same on the 3,735-module application, whose modules are
larger;~~ instructions per lookup before and after. *The application is
measured in H.2.10.*

#### H.2.6 Where the code contradicts C.10 and F.8

1. **Scopes are not entered or left.** C.10 assigns scope ids in preorder
   and tests "ancestor" with `a <= s <= a.last_descendant`. The `Env` API
   has no scope entry or exit, so "behind the existing `Env` API" (F.8)
   gives the log nothing to number. Deriving scopes from use does not
   rescue the rule: after `switch x { | A(y) => e1 | B(z) => e2 }` the
   second case extends the environment that the first case already
   extended. If both extensions go into the same scope, the position test
   lets the second case see `y`. If the second starts a new scope, the test
   needs the position at which that scope forked, not the global one, and a
   module with 2,000 structure items gets a chain of 2,000 scopes.
2. **Old environments are extended** (H.2.3, 1.3% of extensions in H.2.5).
   A preorder numbering cannot place a child under a node whose subtree is
   closed.
3. **Environments cross compilations** on a worker. "One append-only log"
   per compilation has no place for the initial environment's bindings as
   another compilation's entries, nor for a store-built `seed_env`. C.10's
   "shared frozen prefix" covers only the initial environment.
4. **Replacement and removal exist** (H.2.4 items 7 and 8). An append-only
   log needs a rule for both.
5. **Identity.** "Two environments with the same scope and position are the
   same environment" changes when `check_abbrev_env` clears memos (H.2.4
   item 10). It has to be a step of its own with its own gate.
6. **The `im-rc` dependency does not go with P6.** `typemod.rs` uses
   `im_rc::HashMap` and `im_rc::HashSet` for the well-foundedness check of
   recursive types, independent of `Env`.
7. **`typed_envs` cannot hold 8-byte values in P6**, and "16-byte" needs
   the log to be reference-counted: correct as C.10's last paragraph says,
   but the count is then touched on every clone, as today.

#### H.2.7 Correction: a version tree with a current path

> **Amended (H.2.10).** Step 4 built this and changed it in six places:
> payloads live in address-stable pools, so results stay borrowed; a module
> thunk's seed does not own its log; a local module and its components are
> one entry; an open is one entry with a mask of its non-empty tables, and
> opens are chained among themselves; `Override` records what it stands in
> for; `base` always names a frozen log that binds no modules. H.2.10 holds
> where the two disagree.

The log is kept; the scope tree is replaced by the tree of versions, and
the position test by a table that always describes one path of that tree.

```rust
#[derive(Clone)]
pub struct Env { log: Rc<EnvLog>, ver: u32 }      // 16 bytes

struct Entry {
    parent: u32,       // the version this entry extends
    kind: Kind,        // Value, Type, Module, Components, Modtype,
                       // Constructor, Label, LabelFamily, FunctorArg,
                       // LocalConstraint, ImplicitRoot, Open, Flags,
                       // GadtLevel, Override
    key: Key,          // (kind, Name), or a Path for LocalConstraint
    id: Ident,
    item: u32,         // index into the payload vector of `kind`
    shadows: u32,      // the entry `visible[key]` held in `parent`, or NONE
    prev_open: u32,    // nearest Open entry at or above `parent`
    scope_ver: u32,    // nearest scope-changing entry at or above this one
    flags: EnvFlags,   // inherited from `parent`; changed by a Flags entry
    constraints: bool, // a LocalConstraint entry is at or above this one
}

struct EnvLog {
    entries: Vec<Entry>,
    /// For the current path only: the innermost entry of each key.
    visible: FxHashMap<Key, u32>,
    on_path: Vec<bool>,          // one bit per entry
    tip: u32,                    // the newest entry of the current path
    base: Option<Env>,           // an environment of a frozen log, see below
    frozen: Cell<bool>,
    /* payload vectors: values, types, modules, components, ... */
}
```

A version is an entry index; version 0 is the empty environment of the log.
An `Env` sees the entries on the path from its version to the root, then
what `base` sees.

- **Clone.** Copy. Same version, same identity.
- **Move the path to `v`** (`make_tip`). If `v` is the tip, nothing. Walk
  from `v` up to the first entry `a` that is on the path, remembering the
  entries passed. Undo from the tip up to `a`: for each entry set
  `visible[key]` back to its `shadows` (or remove the key) and clear its
  bit. Redo the remembered entries from `a` downwards: set `visible[key]`
  and the bit. Everything needed is in the entries; there is no separate
  trail. Extending the tip's parent, which is what leaving a nested
  expression amounts to, undoes exactly the nested bindings.
- **Extend `env` with an entry.** `make_tip(env.ver)`; set `shadows` from
  `visible`; copy `prev_open`, `scope_ver`, `flags` and `constraints` from
  the parent and adjust them for the entry's kind; push; update `visible`;
  the new index is the new tip and the new `env.ver`. If the log is frozen,
  first start a new log whose `base` is `env`.
- **Look up `(kind, name)` in `env`.**
  1. If `env.ver` is on the path: start at `visible[key]` and follow
     `shadows` while the entry's index is greater than `env.ver`. On the
     path, index order is depth order, so the first entry at or below
     `env.ver` is the innermost binding `env` sees. For the tip this is one
     probe. If `env.ver` is off the path: `make_tip(env.ver)`, then one
     probe.
  2. Opens: start at the nearest Open entry at or above `env.ver` and
     follow `prev_open` while the open's index is greater than the binding
     found in step 1 (or to the end if none was found). The first open
     whose table (`OpenedLayers`, unchanged) has the name wins and gives
     the `Pdot` path and the slot; "hides an earlier binding" is whether
     step 1 or a later open in the walk finds the name.
  3. If nothing is found and the log has a `base`, look up in `base`.
- **Look up by identifier.** Step 1 only, following `shadows` until the
  identifier matches (H.2.4 item 3).
- **All candidates of a constructor or label.** Merge the `shadows` chain
  and the `prev_open` chain by index, newest first; an open contributes its
  bucket in stored order. This is the layer walk of
  `TycompTbl::find_all_marking`, because a layer boundary is an open.
- **Replacement** (`update_value_type_by_name`). An Override entry keyed by
  the name, holding the new description. A value lookup that resolves to a
  binding or an open older than a visible Override of the same name returns
  the Override's description with the path, identifier and slot of what it
  found. A log that has no Override entry skips the check (one flag).
- **Removal** (label families). `add_type` pushes a LabelFamily entry with
  no array when a family is visible for the identifier.
  `type_label_family` returns the innermost LabelFamily entry of the
  identifier.
- **`scope_id()`** is `(log, entries[ver].scope_ver)`. The scope-changing
  kinds are those that call `bump_scope` today. `ScopeCaches` move to a map
  keyed by `scope_ver` in the log.
- **`id()`** is `(log, ver)`.
- **Iteration** (`iter_values`, `iter_local_constraints`,
  `fold_modtype_names`). Walk the path from the version to the root and
  through `base`; `fold_modtype_names` groups the entries between opens and
  feeds each group to `ident_tbl_fold_name_order` as today.
- **Other logs.** `Env::empty()` is version 0 of one frozen empty log per
  thread. The worker store freezes the log of the initial environment when
  it publishes it (`publish_initial_env`); each compilation's first
  extension starts that compilation's log with the initial environment as
  `base`. A frozen log is never extended, so the compilations of a worker
  can read it one after the other; its path may still be moved by a lookup
  at one of its older versions. An environment held by store-built data (`seed_env`, `working_env`) keeps
  its log alive through its `Rc`, as it keeps its persistent maps alive
  today.

What this costs, from H.2.5: a lookup at the tip is one hash probe plus the
opens that are newer than the result; a lookup at an older version on the
path follows `shadows` past the newer bindings of the same name, usually
none; 0.9% of lookups and 1.3% of extensions move the path, 0.19 entries
per operation on average. A move is bounded by the distance between the
two versions, 1,228 entries at worst in the measurement.

What it does not need: scope entry and exit calls, a rule for
out-of-order extension, or any change to a caller.

Unknown, and the reason the hand-off is conditional: the cost of moves on
large modules, and whether lowering, which reads snapshots in typed-tree
order after checking, keeps moves short there. If the property test and
the instruction count of H.2.9 hold, the design stands; if moves dominate
somewhere, that reader keeps a private `visible` table for its own
traversal instead of moving the checker's.

#### H.2.8 Migration order

Each step compiles, passes the gates of F.1 and is its own pull request.

1. **Shrink the API.** Delete the methods without callers (H.2.2) and the
   `IdTbl` and `TycompTbl` re-exports. Replace `set_pending_open_slot` by a
   `slot` argument of `add_prebuilt_open_layers` and of the functions that
   reach it (`open_components_into_env`,
   `add_signature_to_env_with_options_inner`, their callers in
   `typecore.rs` and `typemod.rs`). No behaviour change.
2. **Opaque identity.** `id()` and `scope_id()` return `EnvId` and
   `ScopeId` newtypes with equality and hashing only; the caches in
   `TypeContext` and the keys built in `typecore.rs` take them. No
   behaviour change.
3. **Clone keeps identity.** `Clone` for `Env` stops assigning a new `id`;
   `clone_preserve_id` becomes `clone` at its 23 sites. This is the one
   intended behaviour change before the switch: fewer clears in
   `check_abbrev_env`, more hits in `typeopt_answer` and
   `store_typed_env`. Gate: error-output parity, JavaScript parity, and the
   benchmark comparison of E.3. If a difference appears, it names a place
   that depended on the clear (H.2.4 item 10) and is fixed there, not by
   restoring the id.
4. **The log beside the tables.** *Done; H.2.10 records what it decided
   and what steps 5 and 6 do with it.* New `types/env_log.rs` with H.2.7,
   exposing the same methods as `Env`, unused by the compiler. The property
   test of F.8, extended with what H.2.3 and H.2.4 found: sequences of
   bind, open, clone, **extend an old clone**, replace, re-bind a type,
   lookup by name, by identifier and by path, all candidates with marking,
   `open_slot_use`, `scope_id` equality, and `fold_modtype_names`, run
   against both and compared after every operation and again for every
   retained clone at the end.
5. **Shadow mode.** A debug switch makes `Env` carry both representations
   and compare every lookup result. Run the test suites and the standard
   library with it. Not shipped enabled.
6. **Switch.** `Env` becomes the log. `IdTbl`, `TycompTbl`, `LayerMap`,
   `Recent`, `IdOpened`, `TycompOpened` and `EnvData` move under
   `#[cfg(test)]` for the property test. `OpenedLayers` stays.
7. **Typed-tree snapshots.** `typed_envs` becomes `Vec<Env>` de-duplicated
   by version; `get_typed_env` returns `&Env` or a clone instead of
   `Rc<Env>` (17 call sites).
8. **Initial environment as a base log**; remove the store replay that only
   existed to clone it (`cached_initial_env` keeps its `StorePiece` until
   P4 removes pieces).
9. **Drop the `Rc`** when C.10's last paragraph applies: after P10 has one
   checker per worker, the log is reachable from the context and `Env` is
   two integers. Not part of P6.

`im-rc` stays in `Cargo.toml` until `typemod.rs` stops using it
(contradiction 6).

#### H.2.9 Invariants a reviewer can check

1. **A clone is frozen.** Any sequence of operations on other environments
   leaves every lookup through a retained `Env` unchanged (property test,
   step 4).
2. **`visible` describes the path.** After every `make_tip`, for every key,
   `visible[key]` is the newest entry of that key on the path from `tip` to
   the root, and `on_path[e]` is true exactly for the entries on that path.
   A debug assertion recomputes this from parent pointers for small logs.
3. **`shadows` is immutable** after an entry is pushed, and always names an
   older entry of the same key that is an ancestor.
4. **Indices grow along a path**: `entries[e].parent < e`.
5. **Same results as the tables** for every operation of H.2.2, including
   candidate order, the hidden candidate, `Pdot` positions and
   `OpenSlotUse` (steps 4 and 5).
6. **`scope_id` equality** between two environments holds exactly when it
   holds today (property test), and `id` equality exactly when both are the
   same version (step 3 already made this true for the tables).
7. **No entry is written after it is pushed**, except the payload of a
   lazily forced component thunk, which is a `OnceCell` today and stays one.
8. **A frozen log is never extended**: an extension of one of its
   environments starts a new log.
9. **Warnings.** The unused-open, unused-value and shadowing fixtures give
   the same output (D.7).
10. **Cost.** The instruction count of a clean `tests/tests` build goes
    down at step 6 and does not go up at steps 1 to 5 and 7 to 8. A counter
    in `perf_counters.rs` reports path moves and entries moved; on the
    benchmark, entries moved per lookup should stay below one.

#### H.2.10 Step 4: decisions, corrections and measurements

Step 4 of H.2.8 built the log beside the tables (`types/env_log.rs`,
compiled for tests only) and compared it with them. H.2.7 left three
things open. This section decides them, lists where H.2.7 did not hold,
and gives the numbers. Where it disagrees with H.2.7 or H.2.8, it holds.

**Decision 1: results stay borrowed, from address-stable pools.**

Today every lookup returns a reference that borrows the `Env`
(`&ValueDescription`, `&Arc<TypeDeclaration>`, `&Ident`). Outside `env.rs`
there are 203 call sites of the lookup methods (`typecore.rs` 72,
`typemod.rs` 50, `ctype.rs` 34, `env_lazy.rs` 6, 41 elsewhere). Of the 162
in those four files, 21 copy or test the result within the same expression;
141 bind the reference and use it in later statements, across calls that
extend other environments.

H.2.7's `Rc<EnvLog>` with `Vec` payloads cannot give that: pushing to a
shared vector while a reference into it is alive is exactly what Rust
forbids, and a `RefCell` cannot return a reference past its guard. Three
ways out were weighed:

| Option | What the 203 lookup sites become | Cost of a lookup |
|---|---|---|
| The log owned exclusively (`add_value(&mut log, &mut tip, ..)`, lookups borrow the log) | every site takes the log; every site that holds a result while any environment is extended has to copy the result first. Not a receiver for steps 5 and 6 | none added |
| Handles (`ValueRef(u32)`) with accessors on the owner | every site changes to fetch through the owner, and the owner has to be in reach of `includemod`, `printtyp`, lowering and genType, which have no context argument for it | none added, but the accessor needs the same stable storage as below, or the owner behind a `RefCell` and results copied out |
| Payloads returned by value (`Arc` clone) | the 141 borrowing sites compile unchanged only where deref coercion applies; signatures change | one atomic reference-count update per lookup, 15 million per build of the application |
| **Address-stable pools** (chosen) | **nothing: same methods, same signatures** | one `RefCell` flag test around the index probe; no allocation, no reference count |

A pool (`Pool<T>`) is append-only and never moves an element: chunk `c`
holds `64 << c` slots, each a `OnceCell` written once, so `push` takes
`&self` and is safe Rust. Entries and payloads live in pools; only the
movable path index (`visible`, the path bits, the tip) is in a `RefCell`,
and no reference into it is returned. A reference returned by a lookup
borrows the `LogEnv` it was asked through and stays valid while any other
handle of the same log is extended.

The API has two layers. `EnvLog` works on `Tip`s (a `u32`, `Copy`) with
`&self` methods. `LogEnv { log: Rc<EnvLog>, tip }` (16 bytes) wraps it with
`Env`'s method names and signatures: it is the receiver for steps 5 and 6.
Cloning a `LogEnv` copies the version and updates one reference count, as
cloning an `Env` does today; step 9 removes that count by taking the log
from the checker context, without touching `EnvLog`.

Two signatures differ, by necessity: `with_local_module_components` and
`local_module_components_shared` hand out the log's thunk type
(`LogComponents`) until `StoredModuleComponents` carries a seed (decision
2); and `id()` and `scope_id()` return the log's own identity types.

**Decision 2: a module thunk's seed is a version that does not own its
log.**

`StoredModuleComponents` captures the environment before the binding
(`seed_env`), and forcing reads and extends it. In a log, the log owns the
thunk (payload pool) and the forced table is cached in the thunk, so a seed
that owns its log is a reference cycle: the log would never be freed. This
holds for every variant with a strong reference, including a base log
owned by the forced table, because the base is the seed's log. So:

- The seed is `EnvSeed { log: Weak<EnvLog>, tip }` (16 bytes, where
  `Box<Env>` is 8 plus a 24-byte allocation). `add_module` makes it from
  the version being extended: no allocation, no traversal.
  `seed.env()` upgrades it at force time, once per forced thunk. "A tip
  plus the owner supplied at force time" was rejected because a thunk is
  shared out of its log into `OpenedLayers` and child tables, where no
  owner is at hand, and forced there.
- What keeps a log alive: the `LogEnv` handles of its compilation (the
  typed tree's snapshots, the checker's own environments), and for a log
  started while a component table is built, that table.
  `LogEnv::component_working_env(seed)` returns the environment the table
  extends and, exactly when extending the seed starts a new log (the seed's
  log is frozen), that log for the table to own. When the seed's log is not
  frozen the table forks inside it and owns nothing.
- A frozen log binds no modules (`freeze` asserts it). The initial
  environment binds none, and the empty environment binds nothing. Without
  this rule a table forced from a frozen seed would own a log whose base
  owns the table's thunk.
- Step 6 changes three places in `env_lazy.rs`: `seed_env: Box<Env>`
  becomes `seed: EnvSeed`; `build_local_module_components` starts with
  `stored.seed.env()` and `component_working_env`, and stores the owned
  log in the table it returns; `ChildComponentScanState::Complete` keeps
  the cursor's `working_env` instead of dropping it (its children's seeds
  point into that log). In shadow mode (step 5) the seed carries both: the
  table `Env` and the `EnvSeed`.
- Open question for step 5: a thunk built in a store build and forced by a
  later compilation must have its seed in a log that outlives the first
  compilation. Its seeds start from `Env::empty()` (`persistent_env.rs`,
  `ChildScanCursor`), so they live in table-owned logs; shadow mode has to
  confirm that no such thunk is seeded from a compilation's own
  environment (`seed.env()` returning `None` is the signal).

**Decision 3: corrections to H.2.7.**

- *Entry.* `{ parent, shadows, prev_open, scope_ver, item: u32, kind: u8,
  bits: u8, id: Ident }`, 40 bytes. `key` is not stored: it is the kind's
  name space and the identifier's name, or the path in the constraint
  payload. Flags and "has constraints" are bits inherited from the parent.
- *Opens.* One entry per open, whatever the number of names; opened names
  never enter `visible`, so binding an open is O(1) and moving the path
  across one is one step. The entry's record holds the shared
  `OpenedLayers`, the root, the slot, a mask of its non-empty tables and
  the next older open. The mask matters: today an open is a layer of a
  table only when its table is not empty, and `fold_modtype_names` and the
  candidate walk depend on where the layers are. A lookup probes the opens
  that are newer than the local binding it found and have the table:
  O(1) for a name bound after the last open, one probe per such open
  otherwise, which is today's layer walk.
- *Modules.* A local module and its component thunk are one entry with two
  parallel payloads, not two entries; the component table of an open is a
  separate table, so the two name spaces differ only through opens.
- *Replacement.* An `Override` entry records what it stands in for: the
  log and the local entry, or the open. Looked up by name it gives the
  replaced description with the identifier, path, slot and "hides an
  earlier binding" of the original; by identifier it matches when the
  original was local and is skipped when the original came through an
  open; iteration yields it once. A replacement of a replacement stands in
  for the original. "A log without Override skips the check" is not
  needed: the check is one kind test on the entry that was found.
- *Re-binding and removal.* `add_type` looks up the label family of the
  identifier (one probe) and appends a removal entry when there is one;
  `update_type_variance` appends a type entry and leaves the family.
- *`scope_id`* is `(log, scope_ver)`, and for a version with no
  scope-changing entry in its log, the base's. The scope-changing kinds
  are type, module, module type, open, local constraint, GADT level and
  implicit root; values, constructors, labels, label families, flags and
  replacements are not. An open with every table empty adds no entry and
  changes nothing, as today. `mark_implicit_open_root` gives a new `id`
  (H.2.2 said it kept it).
- *Marking.* `open_slot_use` is the lookup by name, then, for a name found
  through an open with a slot, a second lookup at the version before the
  open. "All candidates with marking" merges the `shadows` chain and the
  open chain by index; the hidden candidate of an open's block is the
  item after it, also when that item comes from the base log.
- *Base logs.* `base` is strong and always names a frozen log. Lookups,
  candidates, iteration, folds and identity fall through to it. The memo
  tables of `ScopeCaches` are a map keyed by `scope_ver` in the log.
- *Not in H.2.2 but in the API:* `with_current_local_module_aliases` and
  `module_path_requires_env_scoped_cache`; both are provided.

**Measured: the traffic on the application.** A temporary counter (not
committed) simulated the version tree on today's `Env` during a clean build
of the 3,735-module application: each extension makes a version whose
parent is the version extended, a log is frozen where `publish_initial_env`
publishes it, and an extension of a frozen log starts a new log.

| Quantity | Value |
|---|---|
| Extensions | 526,953 |
| ... at the newest version | 396,974 (75.3%) |
| ... at an older version on the current path (leaving a nested scope) | 121,403 (23.0%) |
| ... at a version off the path | 2,004 (0.38%) |
| ... starting a new log | 6,572 (1.2%) |
| Lookups (nested calls counted) | 15,149,564 |
| ... at the newest version | 10,819,444 (71.4%) |
| ... at an older version on the path | 4,200,561 (27.7%) |
| ... at a version off the path | 129,559 (0.86%) |
| Path moves | 252,966: 123,407 by extensions, 129,559 by lookups |
| Entries undone or redone | 1,229,794: 0.078 per operation, 4.9 per move |
| Longest move | 1,247 entries; deepest path 1,286 |

Distance of a move through the common ancestor, in entries:

| Distance | 1 | 2-3 | 4-7 | 8-15 | 16-31 | 32-63 | 64-127 | 128-255 | 256-511 | 512 and more |
|---|---|---|---|---|---|---|---|---|---|---|
| Moves by an extension | 67,925 | 22,657 | 20,906 | 8,089 | 2,383 | 928 | 397 | 80 | 19 | 23 |
| Moves by a lookup | 17,357 | 66,657 | 22,070 | 13,878 | 6,752 | 2,070 | 619 | 125 | 22 | 9 |

So old versions are extended often (23.4% of extensions), but almost
always by going back up the current path a few entries, which is what
leaving a scope is; 99.9% of moves are shorter than 128 entries, and the
whole build moves 1.2 million entries against 15.7 million operations. The
version tree keeps its advantage. A lookup at a version off the path has to
move the path: a variant that walked up from the version instead of moving
left the path in the wrong place, and 4.4 million lookups then walked 72.6
million entries.

**Measured: the log against the tables** (`env_log_tests.rs`, one workload
in the shape of a module: 10,000 value bindings in 1,000 nested bodies, 100
types, three opens of 1,200-name modules, 50 retained versions, 100,000
lookups with the shares above):

| Part (optimised build, best of 25, one x86-64 machine) | Tables | Log | Tables / log |
|---|---|---|---|
| The whole workload | 7.98 ms | 4.83 ms | 1.65 |
| Its 10,000 bindings and 1,000 clones alone | 3.35 ms | 0.63 ms | 5.3 |
| 100,000 lookups at the newest version, the four kinds below in turn | 2.78 ms | 2.66 ms | 1.05 |
| A local value bound after the opens, per lookup | 18 ns | 24 ns | 0.76 |
| A name bound nowhere, past three opens | 24 ns | 22 ns | 1.08 |
| A value of an opened module | 22 ns | 23 ns | 0.93 |
| A local type | 5.7 ns | 10.3 ns | 0.55 |

Both representations return the same 100,000 answers. Counted on the log:
10,103 entries, 110,200 index probes, 2,920 path moves of 35,540 entries in
all (0.32 per operation).

What this says about F.8's estimate: binding and cloning is where the log
wins, five times over. A lookup is not cheaper than today's: a hit at the
newest version reads the index, the entry and the payload, where a table
hit is one persistent-map probe, and it executes about a third more
instructions (counted with callgrind on this workload). The log has no
worse case with a long list of recent bindings, but no better common case
either. Of F.8's 3-4%, the
part that came from "environment lookups are 9% of checking" should not be
counted on; what remains is the persistent maps (1.5% build-wide) and the
snapshots (0.98%). Step 6 is worth doing for those, at most 2.5%, and for
removing `IdTbl`, `TycompTbl` and the per-version allocations; not for
3-4%. These are estimates from a workload in a test, not a build: step 5
can count the instructions of both representations on the application
before step 6 is committed to.

**Costs.** Stated on each operation in `env_log.rs` and pinned by a
step-count test:

| Operation | Cost |
|---|---|
| Bind (value, type, module, module type, constructor, label, family, constraint, flag, GADT level, implicit root) | one index probe and one push at the newest version; a type also looks up its label family (one probe) |
| Open of a module with `k` names | one push, independent of `k` |
| Clone | no step; one reference-count update |
| Lookup by name at the newest version | one probe, plus one probe per open that is newer than the binding found and has the table |
| Lookup by name at an older version on the path | the same, plus one link per newer binding of the same name |
| Lookup at a version off the path | a path move, then as above |
| Path move | the distance through the common ancestor; one step per entry, an open included |
| Lookup by identifier | one probe, then one link per local binding of the name examined |
| All candidates | one probe, one step per candidate and per open with the table |
| `open_slot_use` | one lookup; a second one when the name comes through an open with a slot |
| `scope_id`, `id`, flags, `has_local_constraints` | a field read |
| `find_local_constraint` | the bit test; one probe when the environment has constraints |
| `iter_values`, `fold_modtype_names`, local module aliases | the length of the path, plus the opened names visited |
| Replace (`update_value_type_by_name`) | one lookup and one push |

**What steps 5 and 6 do with this.** Step 5: `Env` gets a `LogEnv` field
behind the debug switch; every `add_*` calls both; every lookup compares
(the comparison functions of the property test are the model); the seed
carries both forms. Step 6: `Env` becomes `LogEnv`, renamed; the three
changes of decision 2 in `env_lazy.rs`; `EnvId` and `ScopeId` become the
log's identity types; `publish_initial_env` freezes the log; the step
counters and the fault switch of the tests go behind `cfg(test)`.

**Invariants added to H.2.9.**

11. A reference returned by a lookup stays valid and unchanged while any
    environment of the same log is extended (pools never move an element).
12. Nothing stored in a log owns that log: dropping every `LogEnv` of a log
    frees it, with modules bound (`a_component_seed_..._owns_nothing`).
13. A frozen log binds no modules, and a base is always frozen.

## I. P1 findings and their consequences

Stage P1 was implemented in pull request #124. It found that the premise of
the new core is false. This section says what is observable, chooses a design
answer, and re-derives the savings. Every other section that is now wrong
carries a note that starts with "**Amended (I.n)**" and points here.

Short version:

- Which type nodes are one node, and which are generic, decides the name a
  type is printed with. That reaches diagnostics, the stored interface,
  genType output and the generated JavaScript.
- No sound way was found to share variable-free types between uses that
  saves more than about 1% of the build.
- The checker core therefore keeps today's representation: one node per
  occurrence, structure links, a level on every node. The term store, the
  new core and its switch (P7, P8, P9, P12) are dropped.
- The plan's estimates now sum to 21-29% of the build, against a needed 30%.
  They summed to 27-39%.

### I.1 What P1 found, and what this section adds

From #124:

1. Sharing a variable-free ("ground") type between uses, or leaving its
   level alone, changes the abbreviation name an inferred type is printed
   with.
2. Many callers decide something from the level of a structure node.
   Invariant (3) of F.3 does not hold.
3. `HAS_SCOPED` as C.2 defines it is unsound for weak variables of earlier
   structure items.
4. A flags byte set at construction cost +3.4% of instructions on today's
   representation. The sound part of P1 saves 0.7% on `tests/tests` and 1.4%
   on the application, against the 4-6% of F.3.

Added here, each shown below with a program that both compilers were run on:

5. The generated JavaScript depends on it too, not only printed text (I.2.4).
6. It crosses module boundaries through the stored interface (I.2.5,
   fixture 8).
7. Sharing inside one exported type is observable in a dependent: whether
   two positions of `(int, int)` are one node or two (fixture 7). The ground
   tier of B.3 would merge them, so it is unsound as well.
8. The canonical signature of P0 does not record that sharing (I.3.5).

### I.2 What is observable

#### I.2.1 The three facts

A type is a graph of nodes. `repr` maps a handle to its representative. Three
facts about that graph decide every later output:

- **Name.** The path stored in a representative `Tconstr` node.
- **Identity.** Which handles have the same representative: which positions
  in the types of expressions, of bindings in the environment and of one
  scheme are the same node.
- **Generic or not.** Whether a node's level is the generic level.

For a ground type the design assumed that only the first matters. All three
do, because of how the three interact.

**The printer reads the name of the representative and expands nothing.**
OCaml: `Printtyp.tree_of_typexp` (`compiler/ml/printtyp.ml`) takes `repr ty`
and prints a `Tconstr (p, tyl, _)` with `best_type_path p`. Rust:
`Printtyp::tree_of_typexp` (`types/printtyp.rs`) does the same. genType reads
the same path (`translateTypeExprFromTypes_` in
`gentype/translate_type_expr_from_types.rs`). The stored interface stores it
(`serialize_type` in `cmi/portable_types.rs`).

**Unification changes identity, and through identity the name.** OCaml,
`compiler/ml/ctype.ml`; Rust, `types/ctype.rs`:

| Case | OCaml | Rust | Effect |
|---|---|---|---|
| A variable against anything | `unify1_var`: `link_type t1 t2` | `unify_types`, `unify1_var_link` | the variable becomes the other node |
| The same constructor without arguments on both sides, no cached expansion | `unify`: `link_type t1 t2` | `unify_types`, the `same_nullary_no_cached_expansion` branch | two nodes become one |
| Two structure nodes, neither an abbreviation | `unify2`, `unify3`: `link_type t1' t2`, then the children pairwise | `unify_types` (arrow, tuple and constructor arms call `link_type` before the children) | two nodes become one, at every depth |
| Exactly one side is an abbreviation | `unify2` picks the sides so that `unify3` links the plain node to the *unexpanded* abbreviation node | `unify_after_expansion` (`swap`, `relink_target`) | the plain node now prints with the abbreviation's name |
| Both sides are abbreviations | `unify3` links the expansion of side 1 to side 2 | `unify_after_expansion` | both visible nodes keep their own name |

A link never rewrites a path. It changes which node a handle resolves to. So
"this occurrence is now called `myint`" is not a fact about a binding or an
expression. It is a fact about a node, and it holds for every handle that
resolves to that node.

**Only copying separates two handles again, and whether a node is copied is
its level.** OCaml `Ctype.copy`: `if ty.level <> generic_level && partial =
None then ty`, otherwise a fresh node, with a `Tsubst` mark so that a generic
node reached twice in one copy session is copied once. Rust
`copy_type_cached`: `CopyAction::ReturnSelf` for a non-generic node,
`CopyCache::nodes` for the once-per-session rule. `Subst.typexp_rec`
(`compiler/ml/subst.ml`), which copies a signature when an interface is
written and read, keeps sharing the same way. So:

- a generic node gives every `instance` its own copy: a later link on one
  copy does not touch the others;
- a non-generic node is returned as is: every use is the same node;
- two positions of one scheme that are the same generic node are the same
  node in every instance of it.

Which nodes are generic is decided by `generalize` (every node above the
current level, `generalize_rec` in Rust) and `generalize_structure`
(structure nodes become generic, variables are only lowered). The second is
called for every type annotation (`type_pat`, `Ppat_constraint`, in
`compiler/ml/typecore.ml`: the annotation is generalised and instantiated
twice), for parameters and cases whose pattern is not a plain variable
(`type_function`: `propagate`, then `generalize` of every pattern type).
`propagate` itself reads whether the parameter type's node is generic.

#### I.2.2 When two occurrences of an equal ground type must stay distinguishable

Exactly when OCaml keeps them as two nodes and a later link can land on one
of them. Leaving them distinct is always correct. Merging them is observable
when the link's target is *spelled differently*, at that node or below it:

- an abbreviation that expands to the type: `type myint = int`;
- an abbreviation applied to it: `type id<'a> = 'a`, then `id<color>`;
- an abbreviation with a phantom parameter: `type phantom<'a> = int`, which
  also turns the ground occurrence into a type with a variable;
- an abbreviation of an arrow or a tuple: `type cb = int => unit`,
  `type pair = (int, int)`;
- a type reached through a module alias, which is an abbreviation by its
  manifest (and, in Rust, the `normalize_path_full` branches of
  `unify_types`).

No ground type is exempt. `type id<'a> = 'a` can respell any type, and the
abbreviation can be declared later in the file or in any dependency. The
standard library is full of them (`Array.t<'a>`, `String.t`, `Dict.t<'a>`).

The converse matters as much: two occurrences that OCaml holds as *one* node
must stay one node. Copying a node OCaml shares is as wrong as sharing a node
OCaml copies.

There is no shorter rule than the algorithm itself. Whether two uses are one
node depends on levels, and levels depend on where `typecore` calls
`begin_def`, `end_def`, `generalize` and `generalize_structure`. The shapes
that occur most:

| Two uses are one node | Two uses are distinct nodes |
|---|---|
| uses of a function parameter bound by a plain variable pattern, no annotation | uses of an annotated parameter |
| uses of a `let`-bound value whose type nodes were below the level of the `let` (it is the type of an outer parameter, or the content of a weak variable) | uses of a generalised `let`-bound value, including every top-level constant |
| positions of one scheme that were one node when it was generalised | two reads of a record field, two uses of a constructor: each instantiates the declaration |
| | two schemes |

#### I.2.3 Fixtures in prose

All were compiled with the OCaml compiler and the Rust compiler of commit
8a19c272c. Both print the same in every case. Common prelude:

```rescript
type myint = int
let takesMyInt = (x: myint) => ignore(x)
```

The inferred type is read from a type clash forced at the end
(`let _: string = ...`).

| # | Shape | Program | Inferred | Why |
|---|---|---|---|---|
| 1 | function argument, plain | `let g = a => { ignore(a + 1); takesMyInt(a); a }` | `myint => myint` | every use of `a` is the node that `+` gave it; the call links that node to `myint` |
| 2 | function argument, annotated | `let f = (a: int) => { takesMyInt(a); a }` | `int => int` | the annotation is generalised in structure; each use of `a` is a copy |
| 3 | `let`, generalised | `let x = 1` then `takesMyInt(x)` twice, then `(x, x)` | `(int, int)` | `x` is generic; each use is a copy |
| 4 | `let`, not generalised, in a function | `let f = a => { let b = a; ignore(b + 1); takesMyInt(b); a }` | `myint => myint` | `b` is `a`'s node, below the level of the `let` |
| 5 | `let`, not generalised, weak | `let r = ref(None)`; `let x = 1`; `r := Some(x)`; `let y = switch r.contents { \| Some(v) => v \| None => 0 }`; `takesMyInt(y)` | `r: ref<option<myint>>`, `x: int`, `y: myint` | the weak variable holds one copy of `x`'s type; `y` is that node |
| 6 | record field | `type r = {n: int, m: int}`; `let f = (v: r) => { let k1 = v.n; let k2 = v.n; takesMyInt(k1); (k1, k2) }` | `r => (int, int)` | each read instantiates the label; `k1` is generalised |
| 6b | record field, built | `let mk = a => { let v = {n: a, m: 0}; takesMyInt(a); v }` | `myint => r` | `a` is the node of one label instance |
| 7 | inside a tuple | `let pairConst = (1, 2)`; `let h = q => { ignore(q == pairConst); let (a, _) = q; takesMyInt(a); q }` | `h: ((myint, int)) => (myint, int)`, `pairConst: (int, int)` | the link lands on a node *inside* `q`'s type. A name kept per binding (`a`) would miss `q` |
| 7b | one node at two positions | `let dup = a => { ignore(a + 1); (a, a) }` and `let two = (1, 2)`; then `h` as in 7 with `dup(1)`, and with `two` | with `dup(1)`: `(myint, myint)`; with `two`: `(myint, int)` | `dup: int => (int, int)` and `two: (int, int)` print the same, but `dup`'s two components are one node |
| 8 | cross-module | `A` has the prelude, `let x = 1`, `dup` and `two`. `B`: `let g = a => { ignore(a == A.x); A.takesMyInt(a); a }` and 7b with `A.dup(1)`, `A.two` | `B.g: A.myint => A.myint`; `(A.myint, A.myint)` and `(A.myint, int)` | the names and the sharing of 7b pass through the stored interface |
| 9 | phantom parameter | `type phantom<'a> = int`; `let takesP = (x: phantom<'a>, y: 'a) => ...`; `let h = (a, w) => { ignore(a == x); takesP(a, w); a }` | `(phantom<'a>, 'a) => phantom<'a>` | a ground occurrence gains a variable |
| 9b | phantom, weak | `let cell = ref(None)`; `cell := Some(1)`; `takesP(Option.getOr(cell.contents, 0), [])` with `y: array<'a>` | accepted; `cell: ref<option<phantom<'a>>>` | `closed_schema_rec` (`ctype.ml`) expands a constructor before it reports a weak variable |
| 10 | two abbreviations | `type a = int`, `type b = int`; `let g = v => { takesA(v); takesB(v); v }` and the calls swapped | `a => a`; swapped: `b => b` | the first link names the node; the second links only the expansion |
| 11 | arrow and tuple abbreviations | `type cb = int => unit`; `let g = f => { plainF(f); takesCb(f); f }` | `cb => cb` | a non-constructor node is linked to the abbreviation |

Fixture 1 is the one #124 adds (`alias_name_follows_unification.res`); its
second fixture, `weak_variable_escapes_later_type.res`, is about finding 3.
The others are not in the test suite yet. They should
be added before any further change to instantiation, generalisation or
levels: 1 to 7b, 9 to 11 as `super_errors` fixtures, 8 as a
`super_errors_multi` fixture and a genType test, I.2.4 as a JavaScript test.

#### I.2.4 The generated JavaScript depends on it

`Ctype.maybe_pointer_type` (`compiler/ml/ctype.ml`) reads the declaration of
the node's own path and expands nothing. `compute_immediacy`
(`compiler/ml/typedecl.ml`) gives an abbreviation the immediacy of the head
of its manifest only, so `type id<'a> = 'a` is not immediate while
`type color = Red | Green` is. `Translcore.specialize_comparison` and
`translate_unified_ops` (`compiler/ml/translcore.ml`) choose the integer
comparison when the type is immediate. Rust:
`RawLambdaConverter::is_immediate_type_with_env` (`raw_lambda/convert.rs`).

```rescript
type color = Red | Green
type id<'a> = 'a
let takesId = (x: id<color>) => ignore(x)
let x = Red
let g = a => { ignore(a == x); takesId(a); a > Green }
let h = a => { ignore(a == x); a > Green }
```

Both compilers emit, for `g`, `Primitive_object.equal(a, "Red")` and
`return Primitive_object.greaterthan(a, "Green")`, with warning 102
(polymorphic comparison) at both comparisons. For `h` they emit
`return a > "Green"` and no warning. The only difference is the call that
links `a`'s node to `id<color>`. The comparison on line 5 is *before* that
call in the source: the name is read when the module is lowered, after all
unification.

The same holds across modules. With `B.k` inferred as
`A.id<A.color> => A.id<A.color>`, a third module that passes `p` through
`B.k` compiles `p > A.Green` to `Primitive_object.greaterthan(p, "Green")`
and `q > A.Green` for a plain `q` to `q > "Green"`.

So this is under rule 1 (identical JavaScript), not only rule 2.

#### I.2.5 Which outputs

| Output | Depends on name, identity and generic-ness of ground nodes | Shown by |
|---|---|---|
| Diagnostic text (type clashes, and which warnings are raised) | yes | fixtures 1 to 11; warning 102 in I.2.4 |
| Signature printing (`--dump sig`, interface files) | yes | fixture 8: `let g: A.myint => A.myint` |
| The stored interface, and through it dependents | yes: names, and which positions are one node | fixtures 7b and 8 |
| genType | yes | fixture 8: `export const g: (a:A_myint) => A_myint` |
| Generated JavaScript | yes, through immediacy | I.2.4, in the module and in a dependent |
| Accepting or rejecting a program | not found. Fixture 9b is accepted because the check expands abbreviations. Not proven for every check that reads a declaration without expanding |

How often: a temporary counter on every structure link (`link_type` and the
two direct links in `unify_after_expansion`) counted the links whose source
and target have different head constructors. On the application: 94,819
such links, in 2,634 of 3,735 modules (71%). On `tests/tests`: 1,592, in 138
of 711 modules (19%). The count includes links of expansion nodes that no
handle outside the memo holds (the "both abbreviations" row), so it is an
upper bound on visible renamings. In total the application makes 1,587,265
structure links and 2,769,294 variable links.

### I.3 The design answer

#### I.3.1 Options

**Option 1: keep sharing of ground terms, carry the "printed as" name
separately.**

- *A name per binding or per expression* is unsound. Fixture 7: the link
  lands on a node inside the type of `q`, reached through `a`. An annotation
  on `a` does not rename `q`. Fixture 7b: whether two positions rename
  together is a property of the scheme's graph, not of any binding.
- *A name per occurrence* needs an identity per occurrence at every depth,
  with the rules of the table in I.2.1 applied to it. That is a node. The
  only saving left is to create the node late: an occurrence is one cell that
  points at the shared term, and it is copied one level at a time when
  something takes its children. Every reader above the waist that keeps a
  child handle (`typecore.rs` and `typemod.rs` do, throughout) must force
  that copy, and the unifier must handle both forms.

  What it could save, measured with a temporary counter in the instance
  census (application): 3,716,320 ground instantiations; 2,358,093 of them
  copy nothing because the root is not generic; the others copy 2,985,418
  nodes, of which 2,515,804 are the root or a child of the root, which the
  application of a function or the unification of a constructor opens at
  once. That leaves 469,614 deeper nodes, plus at most 354,746 ground nodes
  below non-ground schemes: at most 824,360 nodes, 16.7% of the nodes
  `instance` copies and 7.1% of all type nodes. All instantiation is 5.7% of
  the build (callgrind, I.7). If its cost were proportional to nodes copied,
  the bound is 0.9% of the build, before the cost of the extra indirection
  on every read. On `tests/tests` the same bound is 0.6% (31,888 of 246,275
  copied nodes, instantiation at 4.7%).

**Option 2: share only ground terms that contain no abbreviation-capable
constructor.** There is no such class: I.2.2. A dynamic variant (share until
the first renaming link, then stop) cannot work either, because at that
moment the checker has to rename exactly the occurrences OCaml holds as one
node, and sharing has erased which those are. A variant that recompiles the
module with the old core when a renaming link occurs would recompile 71% of
the application's modules and keep two cores for good.

**Option 3: keep occurrence identity for all types and take the savings
elsewhere.** Today's representation. Nothing to prove: it is the
representation the parity suites already check. It gives up every fast path
of the new core that rested on sharing (I.5).

#### I.3.2 Decision

Option 3.

Reasons:

1. Identity is needed at every node of every type, and it reaches the
   JavaScript. A design that is right "except in rare shapes" is not
   available under rules 1 and 2, and the shapes are not rare (71% of the
   application's modules).
2. The sound form of option 1 saves at most 0.9% and touches every reader of
   a type's children. Two measured changes on today's representation already
   save more: 1.4% (#124) and 0.9% (I.5, P1b).
3. With identity kept, the new core has nothing left that today's core
   cannot do in place (I.5, P8).

#### I.3.3 Rules

The checker core is today's `types/ctype.rs` on today's `TypeContext`
storage. The rules below are what any later change to it must keep.

1. **One node per occurrence.** Every type the checker can unify is a node
   with its own descriptor cell and level cell (`TypeNode`). Equal types are
   never merged because they are equal. There is no flags byte.
2. **Links.** Unification links as the table in I.2.1 says, in that
   direction, before the children are unified, and restores the descriptor
   when the children fail with a unification error (`unify_types`,
   `unify_after_expansion`). The direction is part of the specification: it
   decides the name.
3. **Copy or share is the level.** `instance` and its variants copy a node
   if and only if it is at the generic level, once per copy session, and
   return any other node as it is (`copy_type_cached`). Whether a type is
   ground is never consulted.
4. **Levels are written on every node.** `generalize`, `generalize_structure`
   and the level updates write the level of ground nodes as of any other.
   A fast path may skip *work* (a snapshot, a declaration lookup, a retry) but
   not a write. `lower_plain_levels` of #124 is the model.
5. **Published nodes are frozen, not interned.** The nodes of a published
   interface are immutable and are shared between compilations, as the
   shared pool does today. Each exported node is one stored node. Two equal
   ground types that were two nodes in the exporter are two stored nodes; one
   node at two positions is one stored node (fixture 7b). The export copy
   keeps this with one map from the exporter's handle to the stored handle,
   over the whole signature (`serialize_type` does this today with its
   `cache`).
6. **A frozen node never meets an abbreviation.** A checker reaches a frozen
   node through `instance`, which copies it when it is generic, and the copy
   is what unification links. (A node under a weak variable that fixture 9b's
   check lets through is stored with its own level. Whether such a node
   reaches a dependent's unifier was not determined; if it does, the next
   sentence covers it.) Where code unifies a frozen node directly, the
   write goes to the compilation's overlay (`TypeContext::write_desc_raw`,
   `set_shared_desc`) and no other compilation sees it. Measured on the
   application: 2,789 links written to shared-pool nodes, 2,784 of them
   restored; the ones sampled came from `matches` in `check_constraints_rec`
   (`types/typemod.rs`), which always undoes its unification. The other 5,
   and 123 links written to worker-store nodes, were not traced.
7. **What the printer reads.** `repr`, then the path in that node, through
   `best_type_path`. No expansion and no side table.
8. **What is exported.** For each node reachable from the signature: the
   descriptor of its representative as it stands when the module has been
   checked (so names acquired through links are exported), whether it is
   generic, and its identity (rule 5).

#### I.3.4 Invariants a reviewer can check

1. No function in `types/` reads "is ground" (or any stored summary of a
   subtree) to decide whether to copy, link, write a level or allocate.
2. A change that claims no behaviour change passes fixtures 1 to 11 and
   I.2.4, as tests, with expectations written by the OCaml compiler.
3. `scripts/compare_checker_builds.py` reports no difference between the
   base and the candidate on `tests/tests` and on the application.
4. A stored interface has as many nodes for a type as the exporter had, and
   fixture 7b passes across two modules.
5. A node of the shared pool is written only through an overlay.
6. In a debug build, a fast path asserts on entry that the general path
   would do the same writes (as `level_update_is_plain` does in #124).

#### I.3.5 What the P0 tooling catches

`scripts/compare_checker_builds.py` builds a project with two executables and
compares, per module, the canonical signature, the diagnostics and every
generated file.

It catches, for the programs in the compared project:

- a wrong name anywhere in an exported type: the canonical signature prints
  every type by structure with its paths (`write_type` in
  `types/canonical_sig.rs`);
- a wrong name in a diagnostic the project emits;
- a difference in the JavaScript or in genType output, so the immediacy case
  of I.2.4.

On the application 71% of the modules make at least one renaming link, so a
comparison there exercises this heavily.

It does not catch:

- the name of a type that is not exported, is in no diagnostic and does not
  change the JavaScript (the type of a local binding);
- a difference in *which positions are one node* inside an exported type:
  the canonical text of `dup: int => (int, int)` and of a version with three
  separate `int` nodes is the same. It shows only if a dependent in the same
  project happens to rename one position (fixture 7b). The canonical form
  should number shared structure nodes as it numbers variables; until then,
  invariant 4 needs its own test;
- a difference in generic-ness of a structure node that no later
  instantiation in the project exposes;
- diagnostics of programs that do not compile: the application compiles
  without errors. Those are covered by `super_errors` and
  `scripts/test_error_output_parity.sh` only.

### I.4 Levels

Nothing replaces the level of a structure node. Every node keeps a level
cell with OCaml's meaning. C.4 kept levels on scratch nodes for the escape
errors; the reason is now wider (rule 3 of I.3.3), and it covers ground
nodes.

By caller group of the table in #124. The groups and their members are
#124's. Re-read for this section: `copy_type_cached`, `generalize_rec`,
`generalize_structure_rec`, `link_type`, `unify_types`, the `typecore.rs`
callers named below, `is_non_gen`, `mark_type_node` and `serialize_type`. The
other members were not re-read.

| Group | What the level decides | In the amended design |
|---|---|---|
| `ctype.rs`, level machinery (`update_level*`, `generalize*`, `lower_nongen*`, `link_type`, `unify_types`) | the walks themselves; `unify_types` lowers both sides to the lower of the two structure levels | stays. The only shortcut is one that writes the same levels (rule 4) |
| `ctype.rs`, copiers (`copy_type_cached`, `copy_sep_inner`, `subst_identity_copy_rec`, `record_label_param_subst`, `remap_label_type_to_params`) | copy or share, per node | stays, exactly. This is the observable one (fixtures 2, 3, 4) |
| `ctype.rs`, abbreviations (`try_expand_head_with_mode`, `generic_abbrev`, `generic_private_abbrev`, `subst_with_memo`, `unroll_abbrev`) | the level an expansion is instantiated at; whether a manifest counts as generic | stays. The expansion memo stays per node (C.7 is withdrawn): an expansion node is a node that gets linked (I.2.1, last two rows) |
| `ctype.rs`, rows, objects, subtyping | the level of new nodes | stays; unchanged by this section |
| `ctype.rs`, `moregen*`, `closed_schema_rec`, `occur` | variables only | stays |
| `typecore.rs`: `instance_if_generic`; `propagate` in `type_match_cases_batch_non_gadt` and `type_function_nary`; the unused-argument warning in `type_application`; `generalizable_at_level` in `type_coerce`; the generic-manifest test in `transl_type_inner`; `set_current_time` from a type's level in `type_newtype` and `type_letmodule` | is this structure node generic; is the function's node above the result's; at which level was this type made | stays. `propagate` decides whether pattern types are generalised, which is fixture 2 against fixture 1 |
| `printtyp.rs` | weak-variable naming and the escape hint read variables; the object and row printers copy a node's level to nodes they rebuild | stays |
| `typemod.rs`, `btype.rs` | rebuilt nodes take the original's level; type marking (`mark_type_node`) stores its mark in the level of every node | stays. On a frozen node the mark goes to the level overlay, as today. A stage that removes overlays (P10) must give marking a visited set for frozen handles first |
| `driver.rs`, `cmi/portable_types.rs` | a variable; and every node's level is written to the stored interface | stays; the stored level is what makes a dependent's `instance` copy (rule 8) |

No decision disappears. The decisions that the design removed were exactly
the ones that turned out to be observable.

`HAS_SCOPED` (finding 3) is not a stored flag any more. Its rule is the
function `path_is_scoped` of #124: every path of the unit being compiled is
scoped; only paths rooted in another unit and predefined types are not. This
is the widening G.1 recommended.

### I.5 Savings, re-derived

Base for the shares below: trunk commit 8a19c272c, the application (82.0 G
instructions under callgrind with one worker) and `tests/tests` (4.64 G).
I.7 says how each number was taken.

What the old estimates assumed, against what was measured:

| Quantity | Assumed in F | `tests/tests` | Application | Source |
|---|---|---|---|---|
| Instantiation, generalisation and level updates, share of the build | 8% | 6.8% | 9.0% | callgrind, inclusive: `copy_type_cached`, `generalize_rec` and `generalize_expansive`, `update_level_checked_above` |
| of which instantiation | | 4.7% | 5.7% | same |
| of which level updates | | 1.7% | 2.7% | same |
| of which generalisation | | 0.4% | 0.6% | same |
| Ground share of `instance` calls | 66% | 57.5% | 64.1% | P0 counters |
| Ground share of nodes `instance` copies | 78% | 59.9% | 67.6% | P0 counters |
| Ground share of generalisation visits | 80% | 78.3% | 87.5% | P0 counters |
| Ground share of level-update visits | 69% | 57.2% | 62.7% | P0 counters |
| Top-level unifications of two identical ground types | 0.88 M of 3.09 M | 47,245 of 213,970 | 882,780 of 4,323,174 | P0 counters |
| Top-level unifications of a variable with a ground type | 1.16 M | 55,344 | 1,167,904 | P0 counters |
| Fresh variables made only to be an expected type | 0.71 M of 2.49 M | 36,842 of 124,293 | 745,558 of 2,253,969 | P0 counters |
| Exported nodes, and the non-ground part | not measured | 32,146; 10,645 | 368,428; 49,712 | P0 counters |
| All of type checking (`type_structure`) | 40% | 34.5% | 42.5% | callgrind, inclusive |
| `unify`, inclusive | | 9.1% | 13.3% | callgrind |
| `expand_head_with_mode`, inclusive | 5% of checking | 2.3% | 4.4% | callgrind |
| `repr_chain`, self | | 0.9% | 1.2% | callgrind |
| `TypeContext::store_desc`, self (reads of store and shared nodes) | | 1.0% | 0.8% | callgrind |

The shares the plan started from were about right. What was wrong is how
much of them can be removed: the 60-70% that P1 and P8 took from the first
row was the ground part, and the ground part has to be done.

Stage by stage. "Saving" is a share of the application's build instructions.

| # | Old estimate | New estimate | What it rests on |
|---|---|---|---|
| P0 | 0 | 0 | landed (#122) |
| P1 | 4-6% | **1.4%** (0.7-0.8% on `tests/tests`) | measured, #124: cachegrind, one worker, 81.72 G to 80.56 G on the application; CI instruction count -0.79% on `tests/tests`. The fast paths for `instance`, `generalize` and the occur checks, and the flags byte, are withdrawn |
| P1b (new) | | **0.9%** (0.65% on `tests/tests`) | measured with a temporary patch, not committed: `instance` returns the representative at once when it is not generic, before it builds a `CopyCache`. This is `Ctype.copy`'s own first test, so rules 1 to 4 hold. Application: 78.12 G to 77.43 G (`perf stat`, user instructions, one worker, smallest of three). `tests/tests`: 4.643 G to 4.613 G (cachegrind, smallest of four runs a side). `compare_checker_builds.py`: no difference on either project |
| P2 | 1.5-2.5% | 1.5-2.5% | estimated; the count it rests on is now measured (745,558 variables, 33.1% of fresh variables, 710,674 of them the two per application). It did not assume sharing, with one exception: C.9 case 1 skipped the level update for a ground type. It must run (rule 4); with #124 it is the cheap path |
| P3 | 2.5-3.5% | 2.5-3.5% | estimated, not re-measured. Does not assume sharing in the checker |
| P4 | 2.5-3.5% | 2.5-3.5% | estimated, not re-measured. Same |
| P5 | 3-4% | 3-4% | estimated; lookup copies measured at 2,699,388 nodes (23.2% of all nodes) and `copy_lookup_type_expr_with_paths` at 2.4% of the build. Sound under rule 6: a lookup returns frozen generic nodes and `instance` copies them |
| P6 | 3-4% | 3-4% | estimated, not re-measured. Independent of type representation |
| P7 | 0 | dropped | it existed to carry P8 |
| P8 | 4-6% once on | **0, dropped** | see below |
| P9 | 0 | dropped | nothing to switch on |
| P10 | 2-3% | 2-3%, on today's `TypeContext` | estimated, not re-measured: setup 1.1% and teardown 2.5% (A.6). It did not rest on sharing: type nodes have no destructor, and the export copy visits 368,428 nodes instead of 49,712, which is under 0.1% of the build either way. What changes is its base: see I.6 |
| P11 | 4-6% | 4-6% | estimated, the least certain number in the plan (G.9). Independent of sharing |
| P12 | 0 (code size) | dropped | there is no old core to delete |

**P8, item by item.** F.10 listed what the new core would save on top of P1:

| Claim in F.10 | Under I.3.3 | Bound |
|---|---|---|
| `repr` without a memory read | gone. A structure node can be linked (rule 2), so `repr` has to read it | `repr_chain` is 1.2% of the build (self) |
| no structure links | gone. The links are the mechanism of I.2.1 | `link_type` is 1.4% inclusive |
| unification of two ground types by handle (882,780 top-level) | gone. Each occurrence is its own node; the pairwise links are needed because a child may be held elsewhere (fixture 7) | part of `unify`'s 13.3%; the split is unknown |
| expansion by table | gone as designed. A table keyed by handles shares expansion nodes between occurrences, and expansion nodes are linked (I.2.1). A per-path cache of "is this an abbreviation" exists today (`resolved_type_item_cache`) | `expand_head_with_mode` is 4.4% inclusive; how much is lookup and how much is the copy of the manifest is unknown |
| no overlays on reads of dependency types | does not need a new core. It needs published nodes that are never written, which is rule 6 plus a replacement for the `matches` probe and for type marking on frozen nodes | `store_desc` is 0.8% (self); how much of that is the overlay test is unknown |
| scheme instantiation that stops at ground children | gone (rule 3) | counted under option 1 in I.3.1: at most 0.9% |

Nothing in the list is both sound and specific to a new core. The honest new
estimate for P8 is zero, for 7,000 lines and months of two cores.

**Totals.**

| | Old | New |
|---|---|---|
| Sum of the stages | 27-39% | 21-29% |
| of which measured | 0 | 2.3% (P1 and P1b) |
| P1 to P6 (with P1b) | 17-23% | 15-20% |
| Needed (F.15) | 30% | 30% |

The plan no longer reaches the target on its own estimates, even at the top
of every range. The gap is 1 to 9 points. P11, the least certain stage,
carries 4-6 of the 21-29.

### I.6 What to build

P7, P8, P9 and P12 are not worth building. P7 and P9 have no purpose without
P8; P8 saves nothing that is sound; P12 has nothing to delete. This removes
the largest and riskiest part of the plan (about 9,500 lines and the
two-core period) and, with it, 4-6 points of estimated saving that were
never real.

P10 and P11 are worth building.

- **P10** is re-scoped onto today's `TypeContext`: one checker context per
  worker whose containers are cleared between modules, a shared prefix for
  the initial environment, and export tables built at publication (B.5) in
  place of per-worker component views. It keeps B.4's segments in the form
  of rule 5 (every exported node, sharing kept, no ground tier). It depends
  on P4, P5 and P6, not on P9. It is harder than the version in F.12, because
  the reset list is today's context (about 100 fields, overlays, about 40
  hash maps) instead of a few dense vectors, so it stays "no" for hand-off.
- **P11** is unchanged.

Order:

```
A: P0 -> P1 (#124) -> P1b
B: P0 -> P3 -> P4 -> P5 ---\
C: P0 -> P6 ----------------+-> P10
D: P0 -> P2 -> P11 (continuous)
```

1. Land #124 (P1).
2. P1b: one function, measured, hand-off yes. Gate: the fixtures of I.2.3
   added first, then `compare_checker_builds.py` on both projects.
3. Tracks B, C and D as before.
4. P10 after P5 and P6.

Before any of it: add the fixtures of I.2.3 and I.2.4 to the test suite, and
make the canonical signature record shared structure nodes (I.3.5). They are
the only protection against the next change that assumes what P1 assumed.

If the target of 30% stands, the missing points have to come from outside
this plan's stages: from restructuring `typecore.rs` (the lever F.15
declines), or from the parts of the build that are not type checking
(57.5% of the application's instructions). This document does not estimate
either.

### I.7 How the numbers were measured

- Machine: x86-64 Linux, 8 cores. `rescript` built from commit 8a19c272c
  with `CARGO_PROFILE_RELEASE_LTO=thin` (not the fat-LTO or profile-guided
  build that ships, so absolute counts are a few percent above CI's).
- The OCaml compiler is the dune build of the same commit.
- P0 counters: `RESCRIPT_COMPILER_COUNTERS=1 rescript build` after
  `rescript clean`, on `tests/tests` (711 modules) and on a 3,735-module
  application.
- Shares of the build: `valgrind --tool=callgrind`, `RAYON_NUM_THREADS=1`,
  inclusive cost of the named function unless "self" is said. Functions that
  the compiler inlined are counted in their callers, so a share is a lower
  bound for the named operation.
- Temporary counters (not committed), added in a second checkout: in
  `link_type` and at the two direct `Tlink` writes of
  `unify_after_expansion`, the kind of each link and the module; in the
  instance census, per ground instantiation, the nodes copied and how many of
  them are the root or a child of the root; in
  `TypeContext::write_desc_raw`, writes to shared-pool and worker-store
  nodes, with a backtrace for a sample.
- P1b: the temporary patch is five lines at the top of `ctype::instance`.
  Instructions with `valgrind --tool=cachegrind --cache-sim=no` on
  `tests/tests` and `perf stat -e instructions:u` on the application, one
  worker, smallest run of each side; outputs compared with
  `scripts/compare_checker_builds.py`.
- Fixtures: each program compiled with both compilers
  (`bsc -w +A -bs-jsx 4 -color never`); the cross-module ones with
  `rescript build --dump sig` and with the OCaml reference build
  (`rescript build-reference`), comparing the generated JavaScript and
  genType files of the two.
- Not measured: anything on the profile-guided build; the split of `unify`
  and of `expand_head` into their parts; memory.
