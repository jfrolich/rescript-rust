# JS Output Simplify Performance Plan

## ⚠️ AGENT STATUS AND MANDATORY NEXT STEPS (2026-04-21)

Phase 4 ports are done (pass_count, pass_lets_dce, pass_eliminate_ref, pass_exits,
lam_hit, lam_util). But the agent went off-plan: instead of continuing to decompose
the monolith, it added 30+ parity-fix commits to the OLD monolithic `simplify_with_env`.
**This is the opposite of what this plan requires.**

### What MUST happen next — in this order, no exceptions:

1. **DELETE `simplify_with_env` and the entire `SimplifyEnv` machinery.**
   The monolithic function, all 114 helper functions that feed it, the SimplifyEnv
   struct, the save/restore mechanism — all of it goes. Do not keep it "alongside"
   the new passes. Do not try to preserve the 615/657 parity score. Rip it out.

2. **Wire up the OCaml pipeline from `lam_compile_main.ml:148-200`.**
   The entry point should call the ported passes in the exact same order as OCaml.
   The passes that still need porting (collect_info, remove_alias, alpha_conversion,
   deep_flatten) should be stubbed as identity functions until ported.

3. **Port the remaining passes** (Phases 2, 3, 6 from below). Each one replaces
   a stub with a real port.

4. **Do NOT add parity fixes that aren't direct OCaml ports.** If parity regresses
   after deleting the monolith, that's expected. Fix it by porting more OCaml code
   faithfully, not by inventing workarounds.

### Issues to fix in existing ports:

All five items have now been addressed (commits 0382c4696 + 87cc26424):

- ✅ `pass_exits.rs`: threaded `meta.id_gen` through `simplify_exits` so
  every `Ident.rename` share's OCaml's global-counter semantics.
- ✅ `pass_lets_dce.rs`: swapped raw `Lambda::Lsequence` for the smart
  constructor `Lambda::seq`, matching `Lam.seq`.
- ✅ `pass_lets_dce.rs`: dropped the unreachable catch-all `Llet` arm.
- ✅ `pass_count.rs`: dropped the dead `lookup` free function. The sole
  caller was already the `count_var` method on `LetsState`.
- ✅ `lam_util.rs`: dropped the dead `let_variable` helper.

---

## Problem

`simplify.rs` is the main post-lowering lambda simplification pass and is currently
the performance bottleneck. It combines ~6 OCaml passes into one monolithic
function, making it **O(n²)** where OCaml's equivalent pipeline is **O(n) per pass**.

## OCaml's actual pipeline

OCaml does NOT have one simplify pass. It has **distinct, focused passes** run in
sequence, each doing one thing well with pre-computed metadata. From
`lam_compile_main.ml` (lines 148-200):

```
deep_flatten
  → collect_info → simplify_exits → collect_info → remove_alias → deep_flatten
  → collect_info → remove_alias → deep_flatten
  → collect_info → alpha_conversion → simplify_exits
  → collect_info → remove_alias → alpha_conversion
  → simplify_lets (uses collect_occurs)
  → simplify_exits
```

### The passes and what they do

| OCaml pass | What it does | Pre-computed data |
|------------|-------------|-------------------|
| `Lam_pass_deep_flatten` | Flatten nested lets into sequences | None (structural) |
| `Lam_pass_collect.collect_info` | Single traversal builds `ident_tbl`: maps each ident → value shape (Constant, ImmutableBlock, FunctionId, Module, OptionalBlock, Parameter, etc.) | None (produces data) |
| `Lam_pass_remove_alias` | Field folding (block.field → constant), optional unwrapping, boolean const folding, cross-module function inlining | `Lam_stats.ident_tbl` from collect_info |
| `Lam_pass_exits` | Inline/eliminate static exits (catch/raise) | None (local analysis) |
| `Lam_pass_alpha_conversion` | Rename variables to avoid capture after inlining | `Lam_stats` |
| `Lam_pass_lets_dce` | Dead code elimination + alias inlining | `collect_occurs` occ table |
| `Lam_pass_count.collect_occurs` | Single traversal builds `{times, captured}` per ident | None (produces data) |

**Key insight:** Each pass is O(n) because it either:
- Does structural work with no per-binding analysis (flatten, exits)
- Consumes pre-computed O(1)-lookup tables (remove_alias uses ident_tbl, simplify_lets uses occ table)
- Produces data tables in a single traversal (collect_info, collect_occurs)

### What Rust `simplify.rs` does wrong

The Rust code mashes ALL of these into one `simplify_with_env` function:
- Block field folding (= `remove_alias`)
- Optional block unwrapping (= `remove_alias`)
- Function inlining / beta reduction (= `remove_alias`)
- Alias substitution (= `simplify_lets`)
- Dead code elimination (= `simplify_lets`)
- Export handling (= parts of `coerce_and_group`)
- Eta reduction (not in OCaml pipeline at this stage)
- Static exit simplification (= `simplify_exits`) — was separate, got merged

Because it doesn't have the pre-computed tables, it re-derives the information
per binding by walking the body, making it O(n²).

## Plan

### Phase 1: Split into separate passes aligned with OCaml

Refactor `simplify.rs` into distinct passes that mirror OCaml's pipeline:

```rust
// The pipeline
fn simplify_lambda_pipeline(lam: Lambda) -> Lambda {
    let lam = deep_flatten(lam);

    let meta = collect_info(&lam);              // → ident_tbl
    let lam = simplify_exits(lam);
    let meta = collect_info(&lam);
    let lam = remove_alias(&lam, &meta);        // field folding, optional, fn inline
    let lam = deep_flatten(lam);

    let meta = collect_info(&lam);
    let lam = remove_alias(&lam, &meta);
    let lam = deep_flatten(lam);

    let meta = collect_info(&lam);
    let lam = alpha_conversion(&lam, &meta);
    let lam = simplify_exits(lam);

    let meta = collect_info(&lam);
    let lam = remove_alias(&lam, &meta);
    let lam = alpha_conversion(&lam, &meta);

    let occ = collect_occurs(&lam);             // → {times, captured} per ident
    let lam = simplify_lets(&lam, &occ);        // DCE + alias inlining

    simplify_exits(lam)
}
```

Each pass is a simple recursive traversal — O(n) with O(1) lookups into
pre-computed tables.

### Phase 2: Port `collect_info` (= `Lam_pass_collect`)

Single traversal that builds `ident_tbl: HashMap<Ident, IdentInfo>`:

```rust
enum IdentInfo {
    Constant(Constant),
    ImmutableBlock { tag: i32, elements: Vec<Lambda> },
    MutableBlock { tag: i32 },
    FunctionId { arity: Arity, lambda: Option<(LFunction, RecFlag)> },
    Module(Ident),
    OptionalBlock(Lambda, NullableKind),
    NormalOptional(Lambda),
    Parameter,
    Exception,
    NA,
}
```

This replaces the current per-binding `immutable_block_elements()`,
`optional_block_info()`, `inlineable_local_function()`, etc. that populate
`SimplifyEnv` incrementally.

### Phase 3: Port `remove_alias` (= `Lam_pass_remove_alias`)

Simple recursive traversal consuming `ident_tbl`:
- `Pfield(i, _)` on `Lvar(v)` → look up `v` in ident_tbl, if ImmutableBlock
  return element `i` directly
- `Pval_from_option` on `Lvar(v)` → look up, if OptionalBlock return inner value
- `Pis_not_none` on `Lvar(v)` → look up, if Constant/ImmutableBlock return true
- `Lapply(Lvar(v), args)` → look up, if FunctionId with inlineable lambda, beta reduce
- `Lstringswitch(Lvar(v))` → look up, if Constant string, fold

No per-binding body walks. All lookups are O(1) into pre-computed table.

### Phase 4: Port `collect_occurs` + `simplify_lets` (= `Lam_pass_count` + `Lam_pass_lets_dce`)

**`collect_occurs`:** Single traversal with local scope tracking:

```rust
fn collect_occurs(lam: &Lambda) -> HashMap<Ident, UsedInfo> {
    // Track local scope (bv) — cleared at lambda/loop boundaries
    // For each Lvar(v): if v in bv, increment times; else mark captured
    // For Llet(_, v, ...): add v to bv before counting body
    // For Lfunction: count body with empty bv (captures)
    // For Lwhile/Lfor: count body with empty bv (loop captures)
}
```

**`simplify_lets`:** Single traversal consuming occ table + mutable subst table:

```rust
fn simplify_lets(lam: &Lambda, occ: &HashMap<Ident, UsedInfo>) -> Lambda {
    let subst: HashMap<Ident, Lambda> = HashMap::new();
    // For Lvar(v): look up in subst, return substitution or original
    // For Llet(Alias, v, value, body):
    //   if occ[v].times == 0: skip value, return simplify(body)
    //   if occ[v].times == 1 && !captured: subst.insert(v, simplify(value)); simplify(body)
    //   if value is unconditionally substitutable: subst.insert(v, simplify(value)); simplify(body)
    //   else: Llet(Alias, v, simplify(value), simplify(body))
}
```

No `free_variables()` calls. No `alias_use_info()` calls. No per-binding body walks.
All decisions are O(1) lookups.

### Phase 5: Port `simplify_exits` (= `Lam_pass_exits`)

Already partially exists. Ensure it's a clean separate pass:
- Count static raises per exit label
- Inline zero-arg exits where handler is simple
- Eliminate unused catch handlers

### Phase 6: Port `alpha_conversion` (= `Lam_pass_alpha_conversion`)

Rename idents that appear multiple times (after inlining can create duplicates).
Simple traversal with rename map.

### Phase 7: Retire monolithic `simplify_with_env`

Once all passes are ported and parity-verified, remove the old monolithic
`simplify_with_env` and its helper functions:
- `alias_use_info`, `free_variables` calls during simplification
- `lambda_exports_ident` per-binding calls
- `substitution_hits_assigned_free_variable` per-binding calls
- `SimplifyEnv` with its save/restore mechanism
- All the `collect_*` pre-passes that fed into the monolithic function

## Incremental migration strategy

The passes can be introduced one at a time. For each:

1. Add the new pass to the pipeline (before or after the monolithic simplifier)
2. Remove the corresponding logic from `simplify_with_env`
3. Verify parity: `./scripts/test_js_output_parity.sh`
4. Repeat

Start with `collect_occurs` + `simplify_lets` (Phase 4) since that eliminates
the worst O(n²) behavior. Then `collect_info` + `remove_alias` (Phases 2-3)
since that's the next biggest chunk of logic in the monolith.

## Constraints

- **CRITICAL: Every line of Rust must trace to a specific line in OCaml source.**
  Never add logic that cannot be directly attributed to a concrete location in the
  OCaml codebase. If you cannot point to the exact OCaml function and line number
  that justifies a piece of Rust code, do not write it. No "this seems like it
  might be needed", no "this helps with parity", no invented workarounds. If OCaml
  doesn't do it, we don't do it.
- **Direct port of OCaml.** Every pass must correspond 1:1 to an OCaml pass. If
  code doesn't exist in OCaml, delete it.
- **Regressions are fine** as long as we're getting closer to the OCaml
  implementation. Parity will come from architectural correctness, not hacks.
- **Match OCaml's efficiency.** Each pass is O(n). No quadratic algorithms,
  no unnecessary allocations, no per-binding body walks.
- Run `./scripts/test_js_output_parity.sh` after each phase to track progress
  (not as a gate — regressions are acceptable).

## Complexity targets

| Operation | Current | Target |
|-----------|---------|--------|
| Full pipeline | O(n²) in one pass | O(n) × ~12 passes = O(n) |
| Per-binding decision in simplify_lets | O(body) × 5 walks | O(1) lookup |
| Per-binding decision in remove_alias | O(body) via env | O(1) lookup |
| Env scope enter/exit | 7 HashMap remove+insert | Not needed |
| Pre-computed tables | 6 separate pre-passes | 1 collect_info + 1 collect_occurs |

## This is a direct port — delete everything not in OCaml

`simplify.rs` contains ~114 functions. Most have no OCaml equivalent — they were
added across 360 parity commits trying to match OCaml's JS output without matching
its architecture. **All of this Rust-specific logic should be deleted.** The new
implementation is a direct port of the OCaml passes, nothing more.

Functions to delete (non-exhaustive):
- All `collect_exported_*` functions (~30 functions for export tail ordering)
- All `preserve_local_module_*` / `collect_local_module_*` functions
- `inlineable_direct_wrapper_function`, `reduce_direct_wrapper_application_once`
- `inline_recursive_component_internal_wrapper`, `sync_component_wrapper_params_like_ocaml`
- `eta_reduce_function_value`
- `alias_use_info`, `alias_occurs_as_apply_callee`, `alias_occurs_as_apply_argument`
- `single_use_switch_scrutinee_alias_from_mutated_source`
- `collect_mutated_idents`
- `preserve_exported_eta_alias_binding`, `preserve_exported_simplified_var_alias_binding`
- `export_only_single_use_allocating_constant_candidate`
- `refine_let_binding` (OCaml uses `Lam_util.refine_let` — port that instead)
- The entire `SimplifyEnv` struct and its save/restore mechanism
- Everything in `simplify_with_env` that doesn't map to an OCaml pass

If it's not in OCaml, it's not needed. Parity regressions from deleting this
code are expected and acceptable — once the OCaml pipeline is faithfully ported,
parity will come from architectural correctness rather than per-file workarounds.

## Reference files

| OCaml file | Rust target | Role |
|-----------|-------------|------|
| `compiler/core/lam_pass_collect.ml` | New `collect_info.rs` | Build ident_tbl (value shapes, arities, function bodies) |
| `compiler/core/lam_pass_remove_alias.ml` | New `remove_alias.rs` | Field folding, optional unwrap, fn inline (uses ident_tbl) |
| `compiler/core/lam_pass_count.ml` | New `pass_count.rs` | Build occ table ({times, captured} per ident) |
| `compiler/core/lam_pass_lets_dce.ml` | New `lets_dce.rs` | DCE + alias inlining (uses occ table) |
| `compiler/core/lam_pass_exits.ml` | New or existing `simplify_exits.rs` | Static exit inline/eliminate |
| `compiler/core/lam_pass_alpha_conversion.ml` | New `alpha_conversion.rs` | Rename duplicated idents |
| `compiler/core/lam_pass_deep_flatten.ml` | Existing `deep_flatten` in simplify.rs | Flatten nested lets |
| `compiler/core/lam_compile_main.ml:148-200` | Pipeline orchestration in `simplify.rs` or `driver.rs` | Pass ordering |
| `compiler-rust/src/lambda/simplify.rs` | To be decomposed | Current monolithic implementation |
