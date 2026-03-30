# Ralph TODO: Raw Lambda Parity

**Last Updated:** 2026-03-30
**Status:** 4 completed, 5 open

## Goal

Achieve **100% unoptimized lambda parity** between the Rust compiler and the OCaml reference implementation using:

```bash
./scripts/test_lambda_parity.sh --unoptimized -j1
```

This is parity for the **pre-optimization raw lambda stage** (`-drawlambda`), not the later optimized lambda sexp dump.

## Current Baseline

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Unoptimized lambda parity: **180/657**
- Parity hunks: **1024**

## Working Rules

1. **Read the OCaml source first.** Do not invent raw-lambda behavior from the diff output.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Use hunk count as a navigation signal.** File count alone hides structural progress.
5. **Do not fix raw parity in the printer.** Fix the raw IR construction first.
6. **Do not touch unrelated dirty files.** This worktree already has unrelated edits.

## Accepted Progress So Far

- [x] Added a dedicated raw-lambda project baseline and loop discipline.
- [x] Ported raw constructor binding fixes:
  - `34672b27c` `raw-lambda: preserve constructor payload bind order`
  - `8e5f8e7e9` `raw-lambda: bind constructor fields from scrutinee`
  - `8e2e77d4c` `raw-lambda: preserve irrefutable var aliases`
- [x] Ported raw array translation:
  - `9daa6db0b` `raw-lambda: port raw array translation`
- [x] Ported OCaml switch compilation patterns:
  - `592d828b9` `raw-lambda: port OCaml switch case sorting, share_actions_sw, reintroduce_fail` (174→175)
  - `d8212d83c` `raw-lambda: use Pnull/Pundefined primitives for %null/%undefined`
  - `106c24295` `raw-lambda: support guards in constructor pattern matching` (175→176)
  - `6f29ca4e9` `raw-lambda: only use PjsFnMakeUnit for Nolabel unit args`

## Highest-Impact Open Tasks

- [ ] **Port OCaml grouped constructor/or/alias matching from `matching.ml`**
  - Focus on grouped `switch` + `catch` compilation, not local heuristics.
  - Primary targets:
    - `combine_constructor`
    - `share_actions_sw`
    - `reintroduce_fail`
    - positive/default fail construction used for overlapping rows
  - Main Rust file:
    - `compiler-rust/src/raw_lambda/convert.rs`

- [ ] **Eliminate raw fallbacks in `VariantPatternMatchingSpreads.res`**
  - Known fallback sites from `RUST_RAW_FALLBACK_TRACE=1`:
    - `match:scrut=Texp_ident:pat=Tpat_alias:cases=2:loc=55:3-58:4`
    - `match:scrut=Texp_ident:pat=Tpat_construct:cases=4:loc=36:3-41:4`
    - `match:scrut=Texp_ident:pat=Tpat_alias:cases=3:loc=29:3-33:4`
    - `match:scrut=Texp_ident:pat=Tpat_alias:cases=3:loc=22:3-26:4`
  - Required outcome:
    - OCaml-like grouped `switch`/`catch` raw shape instead of lowered-style `if` ladders

- [ ] **Port raw module alias/coercion handling from `translmod.ml`**
  - The remaining `Import.res` mismatch is not just path normalization.
  - Investigate OCaml raw handling for:
    - `Mty_alias (Mta_absent, _)`
    - `lambda_module_alias`
    - `apply_coercion`
  - Ensure Rust raw module translation mirrors OCaml before lowering.

- [ ] **Separate true raw-stage construction from later lowered-lambda behavior**
  - Audit `raw_lambda/mod.rs`, `convert.rs`, and `driver.rs`.
  - Remove places where raw translation still inherits lowered JS-oriented behavior.
  - The raw stage must stand on its own functionally, even if later lowering still consumes it.

- [ ] **Track hunk-leading clusters, not only file totals**
  - After each authoritative run, record the biggest remaining hunk clusters.
  - Use the cache under `.parity-cache/lambda/` and prefer structural clusters over smallest diffs.

## Current Evidence / Findings

- The raw stage already has separate scaffolding:
  - `compiler-rust/src/raw_lambda/mod.rs`
  - `compiler-rust/src/raw_lambda/convert.rs`
  - `compiler-rust/src/raw_lambda/print.rs`
- But the stage is not yet fully independent from lowered lambda behavior.
- `VariantPatternMatchingSpreads.res` and `VariantPatternMatchingSpreadsWithPayloads.res` are good canaries for grouped constructor matching.
- `Import.res` is the best canary for raw module alias/coercion mismatch.
- Local canary improvements often reduce structural distance without moving the global file count. Keep tracking hunk movement.

## Loop Checklist

For each iteration:

- [ ] Run `./scripts/test_lambda_parity.sh --unoptimized -j1`
- [ ] Pick one root-cause cluster
- [ ] Read the matching OCaml source
- [ ] Implement the Rust port
- [ ] Re-run focused checks
- [ ] Re-run the authoritative baseline
- [ ] Update this file with before/after counts and findings
- [ ] Commit immediately if the change is verified OCaml-aligned

## Session Log

### 2026-03-30 (session 4)

Starting parity: **179/657** with **1032** hunks.
Current parity: **180/657** with **1024** hunks.

**Commits this session:**
1. `3bc508afc` raw-lambda: port Tcoerce_primitive for external function wrappers
   - OCaml's includemod produces Tcoerce_primitive when a module's Val_prim is coerced to Val_reg (e.g., in include with constraint).
   - Updated PrimitiveCoercion to carry full PrimitiveDescription, type, loc, id.
   - Added transl_primitive_raw to generate wrapper functions matching OCaml.
   - Fixed make_module_block_raw to handle Tcoerce_primitive entries directly.
   - 9 files moved from structural to ident-only diffs.
2. `9b751d2e6` raw-lambda: map %fieldN/%setfieldN primitives to Pfield/Psetfield
   - OCaml's specialize_primitive maps %field0, %field1, etc. to Pfield(n, Fld_tuple).
   - 179→180, 1032→1030 hunks
3. `32d30bb9d` raw-lambda: eliminate trivial *sth* binding in optional parameter matching
   - OCaml's matching compiler optimizes `Some x -> x` to just `val_from_option(arg)`.
   - Targeted fix only for optional constructor patterns (not general let elimination).
   - 180/657, 1030→1024 hunks

**Remaining failure breakdown (477 files, 1024 hunks):**
- 267 ident-only (stamp numbers from type checker, not raw lambda)
- 210 structural diffs

**Top structural clusters:**
- 81 files: Extra `match/N` bindings for unused record fields (OCaml binds all fields, Rust skips unused)
- 50 files: field:tag fallback (constructor matching with refutable args → lowered if-chains)
- 37 files: letrec/init_mod (recursive module handling missing in Rust raw lambda)
- 9 files: Remaining external wrapper pattern (complex include paths)
- 7 files: *sth* wrapping (remaining cases not covered by targeted fix)

### 2026-03-30 (session 3)

Starting parity: **177/657** with **1036** hunks.
Current parity: **179/657** with **1032** hunks.

**Commits this session:**
1. `269c73cc6` raw-lambda: use Alias let-kind for type-annotated coercion bindings
   - OCaml's Matching.for_let sends Tpat_alias(Tpat_any, id, _) through compile_matching which produces Alias bindings when RHS is a variable.
   - For non-variable RHS, arg_to_var + bind_check wraps with Strict.
   - Fixes =a vs = mismatches in coercion bindings like `let b: t2 = (a :> t2)`.
2. `97ddb50f6` raw-lambda: fix empty record representation and catch handler ordering
   - Empty records now produce Pmakeblock(tag=0, []) matching OCaml (was 0a/unit).
   - Removed .rev() on share_actions_sw handlers to match OCaml's handler composition order.
   - 177→178 (+1 file: EmptyRecord.res)
3. `439ba4e34` raw-lambda: apply @inline attribute to let binding values
   - OCaml's transl_let calls add_inline_attribute on each binding's value.
4. `5fda9114d` raw-lambda: use field-by-field record update for small non-optional records
   - OCaml uses Pmakeblock with field reads (not duprecord+setfield) when size<20 and !optional.
5. `875d2c819` raw-lambda: use OCaml-style byte escaping for non-ASCII string content
   - OCaml escapes non-ASCII bytes as \xHH. Rust was using Debug formatting.
6. `93b1ea898` raw-lambda: fix BigInt sign inversion in constant conversion
   - TConstant::BigInt(bool, String) uses true=positive. Was passing as negative.
   - 178→179, 1036→1032 hunks

**Key findings:**

**Remaining failure breakdown (478 files, 1032 hunks):**
- 214+ ident-only (stamp numbers from type checker, not raw lambda)
- ~187 structural-only (real IR differences)
- ~46 both ident and structural

**Root cause: Ident stamp divergence blocks 214+ files**
The Rust type checker allocates ident stamps at different rates than OCaml. Simple files like `let x = 1; let y = 2` match perfectly, but complex files with externals, modules, or coercions diverge by 1-117 stamps. This is NOT a raw lambda issue - it's in the type checker's Ident.create calls. Most files with only ident diffs have exactly 1 hunk.

**Structural patterns in remaining files:**
- 34 files: field:tag fallback (constructor matching with refutable args → lowered if-chains)
- 28 files: makeblock/module structure differences (recursive modules, include wrappers)
- 18 files: catch/exit ordering (exit IDs from different global counter state)
- 17 files: field:[] tuple fallback (tuple matching with constructor sub-patterns)
- 11 files: some/option handling (try/catch wrapping for option-returning expressions)
- 5 files: switch structure (sparse vs dense switch construction)
- Others: import paths, jsx wrapping, string encoding

**OCaml matching.ml alias binding mechanics (new understanding):**
- `Matching.for_let` for `Tpat_var(id)` → `Llet(Strict, id, param, body)` directly
- `Matching.for_let` for `Tpat_alias(Tpat_any, id, _)` → goes through `compile_matching`
- Inside `compile_matching`, `simplify_cases` creates `bind Alias id arg action`
- But `compile_match`'s `bind_check str v arg lam` uses original `str=Strict` from args
- When arg is `Lvar(x)` and `Ident.same v x`: `bind` returns body unchanged (no extra binding)
- Result: inner alias binding from simplify uses `Alias`, outer scrutinee uses `Strict`
- Net effect: variable-to-variable coercion bindings get `Alias`, constant bindings get `Strict`

**OCaml record update strategy:**
- When `size < 20 && !optional`: field-by-field construction (read individual fields from init)
- When `size >= 20 || optional`: duprecord + setfield
- OCaml wraps init expression in `let init = expr in makeblock(field:0 init, field:1 init, ...)`

### 2026-03-30 (session 2)

Starting parity: **176/657** with **1036** hunks.
Current parity: **177/657** with **1036** hunks.

**Commits this session:**
1. `dc11732b0` raw-lambda: print PisNullUndefined as isnullable (matching OCaml)
2. `1886b2abe` raw-lambda: compute module coercion for Pmod_constraint (176→177)

### 2026-03-30

Starting parity: **171/657** with **1028** hunks.
Current parity: **175/657** with **1037** hunks.

### 2026-03-29

- Baseline recorded at **171/657** parity with **1028** hunks.
