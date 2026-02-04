# Ralph TODO: Binary AST Parity

## ⚠️ CRITICAL INSTRUCTIONS FOR AGENTS

1. **NEVER revert commits made by other agents or humans** - If you think a commit is wrong, document your concerns but DO NOT revert it.

2. **Commit your changes frequently** - Follow the instructions in CLAUDE.md about committing.

3. **Update baselines carefully** - Only add files to baselines when they truly pass; verify the test infrastructure is working correctly first.

4. **GET TO THE ROOT CAUSE - DO NOT GIVE UP** - When investigating an issue, go VERY DEEP. Do not stop at surface-level symptoms or give up when things get difficult. If you abandon an investigation halfway, the next agent (or you later) will have to start from scratch. The cost of incomplete debugging is enormous - you lose all context and have to rebuild understanding. Push through until you find the actual root cause, not just a workaround or hypothesis.

5. **Update this TODO when you discover work is already done** - Before starting a task, verify its current state. If you find that a task (or part of it) has already been completed by a previous agent, immediately mark it as done in this file with a brief note of what you found. This prevents future agents from wasting time re-investigating completed work.

6. **Use `scripts/inspect_binary_ast.py` as your primary debugging tool** - When investigating parity issues, start by using the inspector to compare OCaml and Rust AST output (`python3 scripts/inspect_binary_ast.py test <source.res>`). This shows you exactly where the two diverge. Once you've identified the divergence in the AST, look at the corresponding OCaml and Rust parser code to find the root cause. Only modify the Rust code to fix the issue. If the inspector tool is insufficient for your investigation (e.g., missing a mode, not decoding something correctly), improve the Python tool itself.

---

## Current Status

**Last Updated:** 2026-02-05

| Test Suite | Status |
|------------|--------|
| Syntax tests | 506/506 (100%) ✅ |
| sexp-locs | 1196/1196 (100%) ✅ |
| sexp-locs-ppx | 1175/1196 (98.2%) ✅ |
| bsc-ast | 806/1196 (67.4%) |

**Note:** The remaining 21 sexp-locs-ppx failures are structural differences in PPX transformations. Key issues:
- Expression-level await (`Pexp_letmodule` with `@res.await`) - needs module type decl hoisting
- FFI encoding differences (externals with @val, @module, etc.)
- Other PPX structural transformations

**Session progress (2026-02-05) - continued:**
- Fixed module-level `@res.await` transformation (Pstr_module):
  - Keep @res.await attribute on Pmty_typeof's inner module expr (matches OCaml's Mty.typeof_ ~loc me)
  - Keep @res.await on the inner pack expression (OCaml's remove_await_attribute uses != which doesn't work)
  - Keep @res.await on the transformed module expr attributes (OCaml's {e with pmod_desc = ...})
  - Preserve original pstr_loc from the structure item (not mb.pmb_loc)
- Fixed Pexp_await transformation to not copy attributes from the Pexp_await node to the transformed Pexp_apply (OCaml creates NEW expression with empty attributes)
- Result: sexp-locs-ppx improved from 1173/1196 (98.1%) to 1175/1196 (98.2%)

**Previous session progress (2026-02-05):**
- Fixed `inline_string_primitive` delimiter handling: OCaml's `parse_processed_delim` wraps `None` in `Some(DNone)`, and the input strings have "js" delimiter (not "*j") because Rust doesn't transform attribute payloads before extracting @inline. Added handling for `Some("js")` → `Some(DStarJ)`.
- Fixed FFI binary string encoding: Changed `encode_ffi_type` to use proper Latin-1 encoding and `marshal_prim_list` to convert back using `chars().map(|c| c as u8)`. This ensures FFI binary data survives the Latin-1 round-trip used by the sexp printer.
- Fixed attribute string transformation for Pexp_ident/Pexp_constant: OCaml's default_mapper always rewrites attributes even for simple expressions. Added `rewrite_attributes` call for these cases.
- Result: sexp-locs-ppx improved from 1172/1196 (98.0%) to 1173/1196 (98.1%)

---

## 🎯 PRIORITY: Focus on High-Impact Issues First

**TOP PRIORITY:** Fix sexp-locs-ppx differences FIRST. These are post-PPX AST structural/location differences between Rust and OCaml. Fixing these is the highest leverage work because:
- They represent real AST structural differences (not just marshal sharing artifacts)
- Each fix here likely also fixes corresponding bsc-ast failures
- sexp-locs-ppx diffs are easier to debug (human-readable sexp output) than binary bsc-ast diffs

**How to investigate sexp-locs-ppx failures:**
1. Run `./scripts/test_parser_ast_parity.sh` to generate diffs
2. Look at `$TEMP_DIR/sexp_locs_ppx_diffs/*.diff` for specific file differences
3. Compare OCaml vs Rust sexp output: `res_parser -print sexp-locs-ppx <file>` (both OCaml and Rust)
4. Categorize failures (missing PPX transform, wrong location, wrong structure, etc.)
5. Fix the Rust PPX code in `compiler-rust/src/binary_ast/ppx.rs`

**SECOND PRIORITY:** Once sexp-locs-ppx is at 100%, tackle remaining bsc-ast marshal sharing differences.

**Do NOT spend time on bsc-ast marshal sharing issues until sexp-locs-ppx is at or near 100%.**

---

## 🚨 CRITICAL: parsetree0 is NOT involved in .ast file generation!

**⚠️ WARNING: If your analysis concludes that parsetree0 causes .ast file differences, YOUR ANALYSIS IS WRONG. Go back and re-analyze.**

**This is a common mistake that wastes time. DO NOT make it.**

### How .ast files are generated (the ONLY path that matters):

1. Parser creates AST using **parsetree** (current format) with `LocIdx` arena indices
2. PPX runs on **parsetree** (NOT parsetree0)
3. `write_structure_ast_current()` / `write_signature_ast_current()` in `binary_ast/writer.rs` marshal the **parsetree** directly
4. **parsetree0 is NEVER involved**

### If you think parsetree0 is causing .ast differences:

**STOP. You are wrong.** Go back and trace the actual code path:
- `bsc -bs-ast` → `write_structure_ast_current()` → marshals **parsetree** directly
- The sharing issues (arity, location) are in `current_marshal.rs`, NOT in any parsetree0 code

| Component | Used for .ast files? | Used for PPX tools? |
|-----------|---------------------|---------------------|
| parsetree (current) | ✅ YES | ❌ NO |
| parsetree0 (frozen) | ❌ NO | ✅ YES |
| current_marshal.rs | ✅ YES | ❌ NO |
| mapper_to0.rs | ❌ NO | ✅ YES |

---

## ⚠️ CRITICAL: Content-Based Position Caching Is Wrong

**The `start_pos_cache` HashMap that caches positions by their VALUES is WRONG.**

OCaml shares positions by **pointer identity** - when the same variable is reused during parsing, the same position object is shared. OCaml does NOT deduplicate positions with identical content.

**The content-based caching causes BIDIRECTIONAL differences:**
- Sometimes Rust shares MORE than OCaml (wrong - sharing unrelated positions that happen to have same values)
- Sometimes Rust shares LESS than OCaml (wrong - not sharing positions that OCaml shares via variable reuse)

**This is NOT a "fundamental limitation" - it's a bug that needs fixing:**
1. Track position IDENTITY by reusing the same `PosIdx` when OCaml reuses the same position variable
2. Study OCaml's `res_parser.ml` to see which positions are assigned to variables and reused

**DO NOT mark tasks as "BLOCKED by position sharing" - this IS the task to complete.**

### Position Sharing Decision Rules

| OCaml Pattern | Rust Method |
|---|---|
| `let start_pos = p.Parser.start_pos` (local capture, same token) | `p.start_pos_idx()` (shared — same pointer in OCaml) |
| `let start_pos = p.Parser.start_pos` (captured, then p.next() called, then used) | Store `p.start_pos_idx()` BEFORE `p.next()` |
| Position received as `~start_pos` parameter from parent | Use the passed `PosIdx` |
| `let end_pos = p.Parser.prev_end_pos` | `p.prev_end_pos_idx()` |
| `let end_pos = p.Parser.end_pos` | `p.end_pos_idx()` |
| Position from existing AST node's location | `p.loc_start_idx(node.loc)` / `p.loc_end_idx(node.loc)` |

---

## Root Cause Analysis

The binary AST structure (sexp-locs) is 100% correct. The differences are in:
1. **Position sharing** during marshal serialization
2. **Dependency extraction** - fixed to match OCaml's `add_parent` semantics ✅

### What Works (byte-identical to OCaml)

- `let f = x => x` ✅
- `let f = (x, y) => x + y` ✅
- `let f = x => switch x { | A => 1 | B => 2 }` ✅
- `let x = {a: 1, b: 2}` ✅
- `let x = if true { 1 } else { 2 }` ✅
- `let x = <div />` ✅
- `let x = f(1)` ✅ (function calls)
- `let x = Foo.bar(1)` ✅ (module-qualified calls)
- `let x = !a; let y = !b` ✅ (unary operators)
- `let f = (~x) => x` ✅ (labeled arguments)
- JSX elements and containers ✅

### Remaining Blocking Issues (~390 files)

**Root cause:** OCaml's CSE (Common Subexpression Elimination) shares heap blocks with identical content. Rust doesn't replicate this.

**Key patterns:**
1. **PStr([]) payloads**: Empty attribute payloads shared within same parsing context
2. **Some(int) wrappers**: `Some(Closed)`, `Some(false)` etc. may or may not share
3. **String sharing**: Type variable names shared by OCaml CSE
4. **Attribute sharing**: Module-level attributes like `internal_expansive` are physically shared in OCaml

---

## Completed Work Summary

### PPX Transformations ✅
- `%raw` / `%%raw` handling
- String interpolation (`j"..."`, backticks → `"*j"` / `"bq"` delimiters)
- `@deriving(accessors)` - full OCaml wrapper structure
- Integer literal suffix handling
- `%debugger`, `%re`, `%external`, `%obj` extensions
- `@inline` let binding transformation (string, int, float, bool constants)
- `@inline` attribute for signatures
- async/await transformations
- Module-level await (`@res.await`)
- `internal.expansive` attribute via OXC parser
- `%%private` extension
- Pipe operator desugaring (`a->f` → `f(a)`)
- FFI external encoding (@module, @val, @scope, @as)
- Record let destructuring → Pexp_match
- Boolean match → if-then-else
- @as(_) parameter stripping
- Type declaration attribute rewriting

### Position/Arity Sharing ✅
- Arity arena with static indices for literal paths, fresh for computed
- Position caching fixes in `mk_loc_*` functions
- All Position-based `mk_loc_*` converted to PosIdx-based
- JSX closing tag position fix
- open_description location fix

### Dependency Extraction ✅ (100% correct)
- All 1196 files have identical dependency sections
- Module binding order fix
- Unpack name scoping fix
- Pmty_ident uses add_parent (not addmodule)
- With-constraint extraction fixed

---

## Tasks

### Phase 2: PPX Parity ✅ Complete
- [x] Tasks 2.1-2.9: All implemented

### Phase 5: Validation
- [x] Task 5.1-5.3: Achieved 823/1049 (78.5%)
- [ ] Task 5.4: Target 1000/1049 (95%) - Requires marshal sharing fixes
- [ ] Task 5.5: Target 1049/1049 (100%) - Full OCaml sharing parity

### Phase 6: Arity Arena ✅ Complete
- [x] Tasks 6.1-6.6: All implemented

### Phase 7: Position Sharing ✅ Complete
- [x] Tasks 7.1-7.8: All implemented

### Remaining sexp-locs-ppx Issues (21 files failing)

Categorized by root cause:

1. **@deriving(jsConverter)** - 5 files
   - User.res, SettingsStore.res, ImportPage.res, ColorTheme.res, Eth.res
   - OCaml generates include with empty module even for unsupported types
   - Low priority (generates warnings)

2. **@deriving(abstract)** - 3 files
   - typeDefinition.res, HighlightJs.res, ReactDOMRe.res
   - Complex transformation to include with module constraint
   - Medium priority

3. **Expression-level await (Pexp_letmodule with @res.await)** - 1 file
   - letmodule.res
   - Requires hoisting module type declarations to structure level
   - OCaml: bs_builtin_ppx.ml lines 703-752 (spelunk_vbs)

4. **FFI encoding differences** - ~12 files with externals
   - Warp_XHR.res, subscription.res, etc.
   - OCaml encodes @val, @module, etc. into pval_prim binary data
   - Rust keeps attributes but doesn't encode FFI info
   - See compiler/frontend/ast_external.ml for encoding logic

5. **Other** - Requires individual investigation
   - UsdPriceProvider.res (no clear pattern)

### Not Yet Implemented
- **%todo extension** - 0 test files use this

---

## Debugging Commands

```bash
# Run full parity test
./scripts/test_parser_ast_parity.sh 2>&1 | tail -50

# Test a single file
./scripts/test_parser_ast_parity.sh tests/syntax_tests/data/printer/expr/record.res

# Compare binary output
echo 'let f = x => x' > /tmp/test.res
./packages/@rescript/darwin-arm64/bin/bsc.exe -bs-ast /tmp/test.res -o /tmp/ocaml.ast
./compiler-rust/target/release/bsc -bs-ast /tmp/test.res -o /tmp/rust.ast
diff <(xxd /tmp/ocaml.ast) <(xxd /tmp/rust.ast)

# Build Rust compiler
cargo build --manifest-path compiler-rust/Cargo.toml --release
```

### Binary AST Inspector

```bash
# End-to-end parity check (MOST USEFUL)
python3 scripts/inspect_binary_ast.py test <source.res>

# Compare two .ast files
python3 scripts/inspect_binary_ast.py compare <ocaml.ast> <rust.ast>

# Quick overview
python3 scripts/inspect_binary_ast.py summary <file.ast>

# Sharing analysis
python3 scripts/inspect_binary_ast.py sharing <file.ast>

# Full tree dump
python3 scripts/inspect_binary_ast.py decode <file.ast> [--max-depth N]
```

---

## Reference Files

| File | Purpose |
|------|---------|
| `compiler-rust/src/parser/expr.rs` | Arrow function parsing |
| `compiler-rust/src/parser/state.rs` | Parser state |
| `compiler-rust/src/parse_arena.rs` | Position/location arena |
| `compiler-rust/src/binary_ast/current_marshal.rs` | Marshal serialization |
| `compiler-rust/src/binary_ast/ppx.rs` | PPX transformations |
| `compiler/syntax/src/res_parser.ml` | OCaml parser (reference) |

**NOT involved in .ast generation (PPX compatibility only):**
- `mapper_to0.rs`, `parsetree0.rs`, `parsetree0_marshal.rs`

---

## Notes

- sexp-locs passes 100% → AST structure is correct
- Differences are in binary serialization sharing patterns
- OCaml sharing = pointer equality; Rust sharing = arena indices
- Most failures are `.res` files (more complex than `.resi`)
