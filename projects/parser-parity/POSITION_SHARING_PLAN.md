# Plan: Identity-Based Position Sharing (Remove Content-Based Caching)

## Rust Safety Requirement

- Do not introduce new `unsafe` Rust code for parser parity work.
- Find a safe Rust solution instead of using `unsafe`.

## Problem

OCaml shares positions by **pointer identity** — when the same variable is reused, Marshal shares the object. When two functions independently capture `let start_pos = p.start_pos`, they get different heap objects that are NOT shared, even if the values are identical.

Rust currently uses **content-based caching** (`get_or_push_start_pos()` checks if `pos == self.start_pos` and returns the cached `start_pos_idx`). This causes:
- **Over-sharing**: Nested functions that each capture start_pos get the SAME PosIdx (wrong)
- **Under-sharing**: Positions that OCaml shares via explicit variable passing may not share in Rust

The fix has two parts:
1. **Each function that captures its own `start_pos` in OCaml must call `push_start_pos()` (fresh) in Rust** instead of `start_pos_idx()` (cached)
2. **Remove content-based caching** from Position-based `mk_loc_*` methods — convert all callers to use PosIdx-based methods instead

## Strategy

### Phase A: Convert Position-based `mk_loc_*` callers to PosIdx-based

The Position-based methods (`mk_loc_to_prev_end(&start_pos)`, `mk_loc(&start, &end)`, etc.) internally call `get_or_push_start_pos()` which does content-based matching. We need to convert all callers to capture a `PosIdx` explicitly and use the `mk_loc_idx_*` variants.

**Pattern to replace:**
```rust
// OLD (content-based caching via get_or_push_start_pos):
let start_pos = p.start_pos;
// ... parsing ...
let loc = p.mk_loc_to_prev_end(&start_pos);

// NEW (identity-based via PosIdx):
let start_pos_idx = p.push_start_pos();  // or p.start_pos_idx() if sharing is intended
// ... parsing ...
let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
```

### Phase B: Fix parent→child position passing

Stop passing `outer_start_pos_idx` between functions where OCaml captures independently. The main case is type parsing:
- `parse_typ_expr_inner_with_start` currently passes `Some(start_pos_idx)` to `parse_atomic_typ_expr_with_start`
- OCaml does NOT pass start_pos between these — each captures its own

### Phase C: Remove content-based caching

After all callers use PosIdx-based methods, remove `get_or_push_start_pos()` and the Position-based `mk_loc_*` methods (or make them use fresh positions).

---

## Detailed Steps

### Step 1: Add `push_start_pos()` calls — expr.rs (~35 locations)

Convert all `let start_pos = p.start_pos` / `p.start_pos.clone()` captures that are followed by `mk_loc_to_prev_end(&start_pos)` to use `let start_pos_idx = p.push_start_pos()` + `mk_loc_idx_to_prev_end(start_pos_idx)`.

**Functions to update in expr.rs:**

1. `parse_parameter` (~line 1067) — `start_pos.clone()` used for `tilde_pos`, `start_pos` captures
2. `parse_atomic_expr` (~line 1568) — `start_pos_idx()` for main position capture (this is OK if it's the first capture at this token)
3. Let-binding functions (`parse_let_bindings`, `parse_let_binding_body`) — `start_pos` used for binding locations
4. `parse_record_expr` (~line 3190) — `expr_start` for field positions
5. JSX functions (`parse_jsx_*`) — multiple `start_pos` captures for element/tag locations
6. `parse_switch_body`, `parse_if_or_if_let_expression`, `parse_for_expression`, `parse_while_expression` — control flow start positions
7. `parse_try_expression` — try block start position
8. Template/string expressions — string start positions
9. `parse_braced_or_record_expr` — various inner position captures

**For each**: Determine if the function is the "owner" of that position (OCaml captures fresh `let start_pos = p.start_pos` at this point) — if so, use `push_start_pos()`. If it receives the position from a parent, keep using the passed PosIdx.

### Step 2: Add `push_start_pos()` calls — typ.rs (~15 locations)

1. `parse_poly_type_expr` (~line 134) — captures start_pos, calls parse_typ_expr_inner
2. `parse_typ_expr_inner_with_start` (~line 253) — **KEY**: currently accepts `outer_start_pos_idx`, should capture fresh when `None`
3. `parse_atomic_typ_expr_with_start` (~line 468) — **KEY**: should ALWAYS capture fresh (OCaml captures independently)
4. `parse_type_constr_with_start` (~line 687) — should capture fresh
5. `parse_function_type` (~line 763) — receives `start_pos_idx` from caller (correct — OCaml passes `~start_pos`)
6. Type variable captures (~line 164, 173) — for `'a` type vars
7. Object type parsing — start positions for `{..}` types
8. Tuple type parsing — start positions for `(t1, t2)` types

**Critical fix**: Stop passing `outer_start_pos_idx` from `parse_typ_expr_inner_with_start` to `parse_atomic_typ_expr_with_start`. Each should capture independently.

### Step 3: Add `push_start_pos()` calls — pattern.rs (~10 locations)

1. `parse_pattern` (~line 293) — captures start for or-pattern wrapping
2. `parse_single_pattern_with_alias` (~line 248) — captures start for alias patterns
3. `parse_atomic_pattern` (~line 455) — captures start for individual pattern constructs
4. `parse_list_pattern` — list pattern start
5. `parse_record_pattern` — record pattern start
6. `parse_array_pattern` — array pattern start
7. `parse_constructor_pattern_args` — constructor arg positions

### Step 4: Add `push_start_pos()` calls — module.rs (~15 locations)

1. `parse_structure_item` (~line 128) — dual capture (`start_pos_idx` + `start_pos.clone()`)
2. `parse_signature_item` (~line 424) — captures start for signature items
3. `parse_module_expr` (~line 618) — captures start for module expressions
4. `parse_primary_module_expr` (~line 769) — captures start for primary module exprs
5. `parse_module_type` — module type start positions
6. `parse_functor_arg` — functor argument positions
7. `parse_module_declaration` — module declaration positions
8. Various sub-parsers (open, include, exception, etc.)

### Step 5: Add `push_start_pos()` calls — core.rs and other files (~5 locations)

1. `parse_attributes` — attribute start positions
2. `parse_extension` — extension point positions
3. Any other files with Position-based location creation

### Step 6: Fix type parsing position passing (typ.rs)

**Before:**
```rust
fn parse_typ_expr_inner_with_start(p, outer_start_pos_idx: Option<PosIdx>) {
    let start_pos_idx = outer_start_pos_idx.unwrap_or_else(|| p.start_pos_idx());
    // ...
    let typ = parse_atomic_typ_expr_with_start(p, attrs, es6_arrow, Some(start_pos_idx));
}
```

**After:**
```rust
fn parse_typ_expr_inner_with_start(p, outer_start_pos_idx: Option<PosIdx>) {
    let start_pos_idx = outer_start_pos_idx.unwrap_or_else(|| p.push_start_pos());
    // ...
    // Do NOT pass start_pos_idx to atomic — OCaml captures fresh there
    let typ = parse_atomic_typ_expr_with_start(p, attrs, es6_arrow, None);
}
```

And in `parse_atomic_typ_expr_with_start`:
```rust
fn parse_atomic_typ_expr_with_start(p, ..., outer_start: Option<PosIdx>) {
    // Always capture fresh — OCaml's parseAtomicTypExpr captures its own start_pos
    let start_pos_idx = p.push_start_pos();
    // outer_start is only used for attributed types where OCaml DOES pass the position
    // ...
}
```

### Step 7: Remove content-based caching from state.rs

After all callers are converted:

1. **Remove** `get_or_push_start_pos()` (or change it to always push fresh)
2. **Remove** `mk_loc_to_prev_end(&Position)` — all callers now use `mk_loc_idx_to_prev_end(PosIdx)`
3. **Remove** `mk_loc(&Position, &Position)` — all callers now use `mk_loc_idx(PosIdx, PosIdx)`
4. **Remove** `mk_loc_to_end(&Position)` — all callers now use `mk_loc_idx_to_end(PosIdx)`
5. **Remove** `mk_loc_current()` — callers use explicit PosIdx capture + `mk_loc_idx()`
6. **Remove** `mk_loc_from_positions()`, `mk_loc_to_end_of(&Position, ..)`, `mk_loc_with_end_idx(&Position, ..)`, `mk_loc_from_start_of(..)`
7. **Keep** `mk_loc_spanning()` (takes LocIdx, not Position — no caching issue)
8. **Keep** all `mk_loc_idx_*` methods (these are identity-based)

### Step 8: Verify and iterate

1. Build the compiler: `cargo build --manifest-path compiler-rust/Cargo.toml --release`
2. Run parity tests: `./scripts/test_parser_ast_parity.sh 2>&1 | tail -50`
3. Test specific known-failing cases:
   ```bash
   echo 'external foo: int => int = "foo"' > /tmp/test.res
   ./packages/@rescript/darwin-arm64/bin/bsc.exe -bs-ast /tmp/test.res -o /tmp/ocaml.ast
   ./compiler-rust/target/release/bsc -bs-ast /tmp/test.res -o /tmp/rust.ast
   diff <(xxd /tmp/ocaml.ast) <(xxd /tmp/rust.ast)
   ```
4. If there are regressions, investigate which functions need `push_start_pos()` vs `start_pos_idx()`

---

## Key Decision Rules

For each position capture in Rust, determine which method to use:

| OCaml Pattern | Rust Method | Example |
|---|---|---|
| `let start_pos = p.Parser.start_pos` (local capture, not passed from parent) | `p.push_start_pos()` | `parse_atomic_expr`, `parse_atomic_typ_expr` |
| `p.Parser.start_pos` used directly in `mkLoc` (no intermediate variable) | `p.start_pos_idx()` | Inline location creation |
| Position received as `~start_pos` parameter from parent | Use the passed `PosIdx` parameter | `parse_arrow_type_rest`, `parse_tuple_expr` |
| `let end_pos = p.Parser.prev_end_pos` (captured once, reused in fold) | `p.prev_end_pos_idx()` | Arrow function end position |
| Position from existing AST node's location | `p.loc_start_idx(node.loc)` | Or-patterns, module application |

## Estimated Scope

- **expr.rs**: ~35 locations
- **typ.rs**: ~15 locations
- **pattern.rs**: ~10 locations
- **module.rs**: ~15 locations
- **core.rs + other**: ~5 locations
- **state.rs**: Remove/modify ~8 methods
- **Total**: ~80 code locations + ~8 method removals

## Risk Mitigation

- Make changes file-by-file, testing after each
- Start with typ.rs (the known problem area for external declarations)
- Keep the old methods available initially (deprecated) until all callers are converted
- Commit after each file is converted and tests pass or improve

---

## Tools

### Binary AST Inspector (`scripts/inspect_binary_ast.py`)

A pure Python 3 tool (no dependencies) for decoding and comparing binary AST files. Essential for debugging parity issues between OCaml and Rust compilers.

**Subcommands:**

| Command | Usage | Purpose |
|---|---|---|
| `decode` | `python3 scripts/inspect_binary_ast.py decode <file.ast> [--max-depth N]` | Full tree dump with object indices, type annotations (Position, Location), SHARED references |
| `compare` | `python3 scripts/inspect_binary_ast.py compare <ocaml.ast> <rust.ast>` | Header diffs, first byte difference, parallel tree walk showing up to 10 structural divergences |
| `summary` | `python3 scripts/inspect_binary_ast.py summary <file.ast>` | File size, deps, marshal header, object type histogram, top shared targets |
| `sharing` | `python3 scripts/inspect_binary_ast.py sharing <file.ast>` | Groups shared references by target, annotates Position/Location details, reference counts |
| `test` | `python3 scripts/inspect_binary_ast.py test <source.res>` | Runs both OCaml and Rust `bsc -bs-ast`, auto-compares, shows decoded diff at first divergence |

**Typical debugging workflow:**
```bash
# Quick check: does a file have parity?
python3 scripts/inspect_binary_ast.py test tests/syntax_tests/data/printer/expr/apply.res

# Investigate a known-failing .ast file
python3 scripts/inspect_binary_ast.py summary path/to/file.ast

# Deep dive into sharing differences
python3 scripts/inspect_binary_ast.py sharing path/to/file.ast

# Compare two .ast files directly (e.g. from /tmp after manual bsc runs)
python3 scripts/inspect_binary_ast.py compare /tmp/ocaml.ast /tmp/rust.ast

# Decode full tree for manual inspection
python3 scripts/inspect_binary_ast.py decode path/to/file.ast --max-depth 6
```
