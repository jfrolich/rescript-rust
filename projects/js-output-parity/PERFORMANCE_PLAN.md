# JS Output Simplify Performance Plan

## Problem

`simplify.rs` is the main post-lowering lambda simplification pass and is currently
the performance bottleneck. The Rust implementation is **O(n²)** where OCaml's
equivalent (`lam_pass_lets_dce.ml`) is **O(n)**.

### Root cause: per-binding body traversals

For every `Llet(id, value, body)`, the Rust `simplify_with_env` currently does
multiple full traversals of `body`:

1. `lambda_exports_ident(body, id)` — O(body)
2. `substitution_hits_assigned_free_variable(&sub, body)` — O(body)
3. `alias_use_info(id, &body)` — O(body) (after simplifying body)
4. `free_variables(&body)` — O(body), allocates HashSet
5. `export_only_single_use_allocating_constant_candidate(id, &value, &body)` — O(body)

For N nested let-bindings, this is 4-5 × O(N) per binding = **O(N²)** total.

### Secondary cost: HashMap save/restore per scope

The demo2 save/restore refactor (`shadow_ident`/`restore_ident`) avoids full
HashMap clones but still does 7 HashMap remove+insert operations per let-binding
scope entry/exit. For deeply nested programs this adds up. OCaml's approach
avoids this entirely.

### OCaml's O(n) design

OCaml splits the work into two passes (`lam_pass_count.ml` + `lam_pass_lets_dce.ml`):

**Pass 1 (`collect_occurs`):** Single traversal builds a hash table mapping every
let-bound ident → `{times: int, captured: bool}`. Uses a local scope map (`bv`)
to distinguish captured vs non-captured uses. This is O(n).

**Pass 2 (`lets_helper`):** Single traversal consumes the pre-computed table.
For each `Llet`, it does an O(1) hash lookup to decide inline/substitute/keep.
Uses a mutable substitution table (`Hash_ident.t`) — when inlining, just
`Hash_ident.add subst v (simplif l1)` and the recursive `simplif l2` picks
it up. No per-binding analysis walks. This is O(n).

Key properties of OCaml's design:
- **No `free_variables()` calls** — not needed because the count pass already
  determined liveness
- **No `alias_use_info()` calls** — pre-computed in count pass
- **No `lambda_exports_ident()` calls** — export analysis is separate
- **No per-scope env cloning or save/restore** — just a mutable hash table with
  `Hash_ident.add` (which shadows, since OCaml's Hash_ident allows duplicates)
- **No `substitution_hits_assigned_free_variable()`** — mutation tracking is
  handled differently (Strict vs Alias let-kind already encodes this)

## Plan

### Phase 1: Pre-compute occurrence counts (eliminate O(n²))

Port `Lam_pass_count.collect_occurs` to Rust. Single traversal that builds:

```rust
struct UsedInfo {
    times: u32,
    captured: bool,
}
type OccTable = HashMap<Ident, UsedInfo>;
```

Track a local scope (`bv: HashMap<Ident, &mut UsedInfo>`) that gets cleared at
lambda/loop boundaries (to mark captured uses).

This replaces all per-binding calls to:
- `alias_use_info(id, &body)` → `occ_table.get(id)` — O(1)
- `free_variables(&body).contains(id)` → `occ_table.get(id).times > 0` — O(1)

**Verification:** After implementing, assert that the pre-computed counts match
the current per-binding `alias_use_info` results on all 657 test files before
removing the old code.

### Phase 2: Pre-compute export info (eliminate more body walks)

Port the export-related analysis to a pre-pass or integrate into the count pass:
- `lambda_exports_ident(body, id)` — can be computed once per module in a single
  traversal that collects all exported idents
- `export_only_single_use_allocating_constant_candidate` — depends on use count
  (now from occ table) + value shape (local check)

This eliminates the remaining per-binding O(body) walks.

### Phase 3: Mutable substitution table (eliminate save/restore)

Replace the `SimplifyEnv` save/restore pattern with OCaml's approach:

```rust
struct SimplifyState {
    subst: HashMap<Ident, Lambda>,       // shadows via insert, no restore needed
    string_table: HashMap<Ident, String>, // for string constant folding
    occ: OccTable,                        // from phase 1
}
```

OCaml's `Hash_ident.add` allows duplicate keys (latest shadows previous). In Rust,
since we process lets top-down and each ident is unique (SSA-like from lambda
lowering), a simple `HashMap::insert` suffices — the ident won't appear again
after its scope.

For block info, optional info, function info, and other per-binding metadata:
evaluate whether these are still needed given the pre-computed occ table. Many
of these exist because the current code needs to make inlining decisions
*during* traversal that OCaml makes via the count table.

**Key insight:** OCaml's `simplif` function is remarkably simple — it's basically
a fold over the lambda tree with a substitution lookup at `Lvar`. The Rust version
should converge to the same simplicity.

### Phase 4: Consolidate pre-passes

The current code runs multiple pre-passes before `simplify_with_env`:
- `deep_flatten_for_js_backend` — full traversal
- `collect_exported_idents` — full traversal
- `collect_exported_apply_bindings` — full traversal
- `collect_local_module_eta_alias_bindings` — full traversal
- `collect_inlineable_functions` — full traversal
- `collect_known_functions` — full traversal

Merge these into fewer passes. Ideally: one flatten pass + one analysis pass that
collects occurrence counts, export info, and inlineable functions in a single walk.

### Phase 5: Eliminate multi-pass pipeline

The old code ran the simplifier 3 times with intermediate DCE passes. Demo2
already reduced this to 1 pass. Verify that single-pass is sufficient and that
no parity regressions require re-introducing passes. If multi-pass is needed for
parity, do it with the O(n) design (re-run count + simplify) rather than the
current O(n²) design repeated.

## Constraints

- **No parity regressions.** Every change must preserve the current 593/657 (or
  improve it). Run `./scripts/test_js_output_parity.sh` after each phase.
- **Match or beat OCaml's efficiency.** The Rust implementation must be at least
  as efficient as OCaml's. No quadratic algorithms, no unnecessary allocations.
- **Incremental delivery.** Each phase is independently valuable and testable.
  Phase 1 alone eliminates the O(n²) bottleneck.

## Complexity targets

| Operation | Current | Target |
|-----------|---------|--------|
| Full simplify pass | O(n²) | O(n) |
| Per-binding decision | O(body) | O(1) lookup |
| Env scope enter/exit | 7 HashMap ops | 0 (or 1 insert) |
| Pre-passes | 6 × O(n) | 1-2 × O(n) |
| Total passes over tree | ~8 | 2-3 |

## Reference files

| File | Role |
|------|------|
| `compiler/core/lam_pass_count.ml` | OCaml occurrence counting — the model to port |
| `compiler/core/lam_pass_lets_dce.ml` | OCaml simplifier consuming count table |
| `compiler-rust/src/lambda/simplify.rs` | Current Rust implementation to refactor |
| `compiler/core/lam_pass_remove_alias.ml` | OCaml alias removal (separate pass) |
