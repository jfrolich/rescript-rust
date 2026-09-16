# Per-thread persistent type store

Implementation design for proposal A of
[ARCHITECTURE_INVESTIGATION.md](ARCHITECTURE_INVESTIGATION.md), re-scoped
so it does not depend on proposal B. Clean-build target only: nothing is
persisted between builds; the store lives for the lifetime of one worker
thread inside one `rescript build` process.

## Why this first

A 12 s `sample` window of the single-worker Tella clean build on this head
(`/tmp/perf-sample-w1.txt`, worker thread, 7.2 K samples), restricted to the
call-graph section and counting each family at its outermost frame:

| family | share | what it is |
|---|---|---|
| `drop_in_place` | 23.3 % | 477 samples at the end of `compile_preprocessed_structure_in_process_until_js`; `Env` 182; `RefCell<Vec<Arc<Env>>>` 142; HAMT entries 87; `QualifiedModuleComponents` 51; component/decl `AHashMap`s 84; `TypeContext` 34; `PersistentEnv` 30 |
| `Arc` refcount traffic | 12.7 % | mostly inside those drops (`Env` 310, `TypeContext` 213) |
| `find_pers_struct` | 8.4 % | `internalize_signature` 4.0, `register_sig_types_*` 2.8, freshen/subst 1.3 |
| `open_module` (prelude) | 6.3 % | overlaps the row above for `Pervasives`/`Stdlib` |
| `hashbrown` | 8.1 % | `insert_module_stamp_subst` 64, component construction 41, subst maps 30, … |
| `TypeDesc` clone + drop | ~3 % | the class proposal B removes |

Per-module import and teardown of *dependency* state is the largest
addressable block (roughly a third of the window; `env_setup` 1.19 s +
residual 2.47 s of the 19.8 s serial build sit outside typecheck, and the
`Env`/component drops inside typecheck add to that). Type-node
representation is a distant second. A per-thread store removes the import
and the teardown for every dependency module after the first module on a
thread that needs it, without requiring `Sync` type nodes.

The earlier worker-local `TypeContext` reuse experiment
(`projects/shared-interfaces/PROGRESS.md`) is *not* what this is: that
reused the whole mutable context, including stamp-keyed declaration
registries whose keys collide when stamps reset per unit. Here only
immutable, generic-level dependency graphs and their once-per-process
component tables are shared; every mutable per-unit table stays per module.

## OCaml reference semantics

- `compiler/ml/env.ml:669-678`: `read_pers_struct` builds `ps_comps` once,
  from `Env.empty` and `Subst.identity`, and stores it in the process-wide
  `persistent_structures` table. Every unit compiled by that process shares
  those nodes and that component table.
- `compiler/ml/env.ml:1874-1877`: `open_signature` adds opened components
  from that shared table; it does not copy the signature.
- `compiler/ml/subst.ml:358-364` (`Subst.signature`) and
  `compiler/ml/env.ml:1516-1585` (`components_of_module_maker`): the
  consumer-visible substituted copies are made when a component table is
  forced. They are per `(path, mty, sub)`, not per unit.
- `compiler/ml/ctype.ml:100-131` (`copy`/`instance`): generic-level nodes
  are always copied before unification, so persistent nodes are never
  linked. `Tsubst` markers are the one in-place write OCaml makes on them,
  and Rust already keeps that state in `CopyCache` instead.
- `compiler/ml/subst.ml:80-86`: abbreviation memos are reset to `Mnil` when
  a signature is saved, so a fresh process starts with empty memos. Memo
  state must therefore stay per module for one-process-per-file parity.

Today's per-module internalization corresponds to one `bsc` process per
file. Sharing forced dependency state across the modules compiled on one
thread is closer to the reference process model, not further from it.

## Ownership model

```
worker thread
└── ThreadTypeStore (thread_local, lives for the thread)
    ├── types:       TypeArena           append-only, generic-level nodes only
    ├── abbrevs:     Vec<AbbrevMemo>     initial (Mnil) values only
    ├── row_fields / field_kinds / variant_layouts   initial values only
    ├── id_gen:      per-thread node ids, disjoint from module-local ids
    ├── stamps:      per-thread ident stamp range, disjoint from unit stamps
    ├── pers:        portable-struct identity -> Arc<PersStruct> (store refs)
    └── comps:       (module path, alias source) -> QualifiedModuleComponents
module compile (TypeContext, dropped at the pre-JS boundary)
    ├── types:       TypeArena           local nodes, as today
    ├── store:       Rc<ThreadTypeStore> handle (one Rc per context, not per node)
    ├── overlays:    store abbrev / row-field / field-kind cells written by
    │                this module, indexed by store cell index
    └── every existing per-unit table, unchanged
```

`TypeExprRef`, `AbbrevMemoRef`, `RowFieldRef`, `FieldKindRef` and
`LayoutRef` reserve their top bit as the store tag. Accessors on
`TypeContext` branch on the tag; index arithmetic (`index()`,
`from_usize`) stays local-only and asserts the tag is clear.

Nothing in `InProcessPreJsCompileResult` references type nodes, so the
handle never crosses threads; the store is `!Send` by construction.

## Invariants

1. Store nodes are generic-level and never `set_desc`/`link_type`ed. A
   `debug_assert!` in `TypeContext::set_desc` and the link path enforces
   it; the debug typedtree/lambda suites are the check.
2. `set_level` on a store node is allowed only for the mark/unmark
   traversal pairs that already restore the level before returning.
3. Abbrev memos, row-field cells and field-kind cells of store nodes are
   read through the module overlay: unset means the store's initial value.
   Writes go to the overlay only. `clear_abbrev_memos`/snapshot-backtrack
   operate on the overlay plus local cells.
4. `TypeExprRefMap` keys are either all-store or all-local in the dense
   path; mixed key sets use the sparse path. `snapshot_type_state` covers
   local nodes and overlays only.
5. Store ident stamps come from a range that no per-unit counter reaches
   (`LOCAL_IDENT_COUNTER` is swapped in while the store builds components
   and restored afterwards). Stamp-keyed per-unit registries
   (`type_decl_by_stamp` and friends) are never shared.
6. Store entries are keyed by portable-struct identity (`Arc::as_ptr`),
   so a module republished in watch mode never aliases a stale graph.
7. Component tables are stored only when their construction did not read
   the module's `Env` (persistent roots, `env.ml:669-678`); local
   components keep today's per-module path.

## Stages

Each stage lands only with `./scripts/test_js_output_parity.sh --release`
610/610 and `./scripts/test_error_output_parity.sh --release` 1431/1431,
plus the debug `./scripts/test_typedtree_parity.sh --quick` and
`./scripts/test_lambda_parity.sh --quick` so the invariant assertions run.

1. **Tagged references and store skeleton, no behaviour change.** Top-bit
   tags on the five reference types; `ThreadTypeStore` with an empty arena;
   `TypeContext` accessors branch on the tag; overlays and assertions in
   place. Paired hyperfine must show no regression from the extra branch.
2. **Store-backed `find_pers_struct`.** Portable persistent structs are
   internalized once per thread into the store; the module's
   `PersistentEnv` cache maps names to the shared `Arc<PersStruct>`.
   `register_sig_types_*` and alias-rewrite collection still run per module
   on the shared signature (they fill per-unit tables). Measure: expect
   `internalize` and the `TypeContext` node drops to fall out of the
   serial profile.
3. **Shared component tables and the prelude.** `QualifiedModuleComponents`
   for persistent roots move to the store; `open_module` for `Pervasives`,
   `Stdlib` and `-open` roots reuses them, and the opened prelude `Env` is
   cached per thread and per open-configuration. Measure: `open_module`,
   `freshen`, `insert_module_stamp_subst`, and the `Env`/component drops.
4. **Per-unit registries** (`type_decl_store`, `type_decl_by_stamp`,
   `type_decl_by_path`, …) are the remaining per-module walk over shared
   signatures. Route consumers through `Env`/component lookup
   (proposal C.2) or make the registration incremental per store entry.

Proposal B (POD nodes) remains the follow-up for the remaining clone and
memmove share; with the store in place its `Sync` requirement disappears.
