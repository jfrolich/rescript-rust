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
| sexp-locs-ppx | 1196/1196 (100%) ✅ |
| bsc-ast | 837/1196 (69.9%) |

**Session progress (2026-02-05) - newest:**
- Fixed dependency scoping bug in `deps.rs` (bound_modules): 836→837
  - Bug: Rust uses mutable `HashSet<String>` for bound_modules, but removes names
    on scope exit even when they were already present from outer scopes
  - OCaml uses functional (immutable) scoping — inner scopes can't remove outer bindings
  - Example: `module Set = { ... }` adds "Set" to bound, then
    `let sort = (..., module(Set: Set.S ...), ...) => ...` temporarily re-adds "Set",
    and on scope exit REMOVES it — making later `Set.Make(...)` incorrectly add "Set" as dep
  - Fix: Track which names are NEWLY added (not already bound) via `HashSet::insert()`
    return value, and only remove those on scope exit
  - Applied to: Pexp_let, Pexp_fun, Pexp_letmodule, add_case
  - Result: oprint.res now passes (was header-only diff due to spurious "Set" dependency)

**Session progress (2026-02-05) - previous:**
- Investigated bsc-ast marshal sharing differences (385 files failing)
- Attempted fixes for pval_prim list sharing and arity sharing, both caused regressions
- Attempted empty string `""` sharing — caused 91 regressions (OCaml doesn't always share empty strings)
- Investigated zero-arg block sharing — NOT viable (OCaml shares 1 of 39 identical blocks)
- Root cause analysis:
  - OCaml's Marshal shares objects by POINTER IDENTITY, not content
  - For `%%raw` expressions: OCaml shares pval_prim lists like `["#raw_stmt"]` because they're
    the same string literal in the PPX code (OCaml interns string literals)
  - For arity: OCaml shares `Some(1)` via CSE in the parser, but NOT in PPX-generated code
  - Content-based sharing (HashMap<String, u32>) causes bidirectional errors:
    - Shares things OCaml doesn't share (different allocations with same content)
    - May miss things OCaml shares (same pointer in OCaml, different in Rust)
- **Conclusion:** The bsc-ast differences are difficult to fix without tracking pointer identity,
  which requires architectural changes to the parser. sexp-locs-ppx parity proves the AST
  structure is correct; the remaining differences are marshal serialization artifacts.

**Session progress (2026-02-05) - previous:**
- Fixed @obj external unit arg FFI encoding - ReactDOMRe.res Style.make now passes
  - When an @obj external has a unit argument (Nolabel), the FFI encoding must
    include `empty_kind Extern_unit` (ObjEmpty + ExternUnit) in the Ffi_obj_create list
  - Previously code was skipping unit args entirely, missing 2 objects in FFI encoding
- **sexp-locs-ppx reached 100% parity (1196/1196 files)**

**Session progress (2026-02-05) - previous:**
- Fixed `@deriving({jsConverter: newType})` for record types:
  - Implemented `generate_js_converter_record` for record-to-JS conversion
  - Added `create_record_to_js_function` and `create_record_from_js_function`
  - Fixed location handling: field labels use pld_name.loc, expressions use ghost
  - Fixed signature function names to use tdcl.ptype_loc
  - subscription.res and Eth.res now pass sexp-locs-ppx
- Fixed `_revMap` location for polyvariant jsConverter (pattern var should use tdcl.ptype_loc)
- Started WIP implementation of `@deriving(abstract)`:
  - Basic structure generation working
  - Maker function with labeled/optional args
  - Accessor/setter generation
  - Remaining: FFI encoding, locations, arity
- Result: sexp-locs-ppx improved from 1187/1196 to 1193/1196 (99.7%)

**Session progress (2026-02-05) - previous:**
- Fixed @deriving(accessors) ghost location issues:
  - `core_type_of_type_declaration_with_attrs()`: Use ghost for ptyp_loc, use ptype_name.loc for longident
  - `generate_record_accessors_and_sigs()`: Use ghost for pvb_loc, pstr_loc, pval_loc, psig_loc
  - The outer include structure uses real locations (OCaml's gen_structure_signature passes ~loc explicitly)
- Fixed: UsdPriceProvider.res now passes sexp-locs-ppx
- Result: sexp-locs-ppx improved from 1186/1196 to 1187/1196 (99.2%)

**Session progress (2026-02-05) - previous:**
- Fixed FFI polyvariant string sharing: When encoding @string polyvariants,
  share the second string in (tag, name) pairs when tag == name.
  OCaml shares these because when there's no @as attribute, the same
  string pointer is used for both fields.
- Fixed %external transformation:
  - Use ghost locations for generated Pexp_ident expressions of Js.typeof
    and Js.undefinedToOption (OCaml's Ast_helper.Exp.ident uses default_loc)
  - Use Some("") delimiter for the identifier string constant
- Fixed: Warp_XHR.res, ReasonReactRouter.res now pass sexp-locs-ppx
- Result: sexp-locs-ppx improved from 1184/1196 (99.0%) to 1186/1196 (99.2%)

**Session progress (2026-02-05) - previous:**
- Reversed filtered FFI attributes to match OCaml ordering:
  - OCaml's parse_external_attributes uses fold_left with cons, naturally reversing order
  - Fixed: ReactEventRe.resi now passes
- Fixed result_is_unit calculation for nested arrow types:
  - Use result from list_of_arrow() instead of get_final_result_type()
  - For `int => (unit => unit)`, result should be `(unit => unit)`, not `unit`
  - Fixed: arrow.res now passes
- Fixed @obj external type reconstruction (Ptyp_any -> Ptyp_object):
  - Added `has_obj_attr()` to detect @obj attribute
  - Added `process_obj_type()` to transform type for @obj externals
  - Added `build_obj_ffi_type()` to generate FfiObjCreate with field names
  - Added `get_opt_arg_type()` and `to_undefined_type()` for optional handling
  - Fixed: attributes.res now passes
- Result: sexp-locs-ppx improved from 1181/1196 (98.7%) to 1184/1196 (99.0%)

**Session progress (2026-02-05) - previous:**
- Fixed @string/@int/@unwrap/@ignore polyvariant FFI encoding in `spec_of_ptyp`:
  - Added `check_type_ffi_attrs` to detect FFI attributes on types
  - Added `map_row_fields_into_strings` for @string polyvariant encoding
  - Added `map_row_fields_into_ints` for @int polyvariant encoding
  - Added `variant_can_unwrap` for @unwrap validation
  - Fixed: polyvariant.res, React.res, Next.res now pass
- Fixed Pexp_letmodule to recurse into module expression:
  - Previously externals inside let-module weren't processed
  - Fixed: block.res, expressions/block.res now pass
- Result: sexp-locs-ppx improved from 1176/1196 (98.3%) to 1181/1196 (98.7%)

**Session progress (2026-02-05) - previous:**
- Fixed expression-level await (`{ module M = @res.await ME; ... }`):
  - Added `create_await_module_expression` for Pexp_letmodule transformation
  - Added `spelunk_expression_for_await_module_types` to traverse expressions
  - Updated `rewrite_structure` to hoist module type declarations before Pstr_value
  - Fixed Pmod_constraint case (e.g., `module M = await (ME: MT)`)
  - Fixed package type location to use module_type_lid's location
  - letmodule.res now passes sexp-locs-ppx (bsc-ast has sharing diffs)
- Result: sexp-locs-ppx 1176/1196 (98.3%)

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

### Remaining sexp-locs-ppx Issues (15 files failing)

Categorized by root cause:

1. **@deriving(jsConverter)** - ✅ IMPLEMENTED
   - All files now pass: subscription.res, Eth.res
   - Implemented `generate_js_converter_record` for record types with newType option
   - Implemented polyvariant encoding with _map/_revMap

2. **@deriving(abstract)** - 3 files ⚠️ WIP IMPLEMENTATION
   - typeDefinition.res, HighlightJs.res, ReactDOMRe.res
   - OCaml: `ast_derive_abstract.ml`
   - Basic structure implemented in Rust ppx.rs
   - Remaining issues:
     - FFI binary encoding for maker/accessor primitives
     - Location handling for generated code
     - Arity encoding differences

3. **Expression-level await (Pexp_letmodule with @res.await)** - ✅ FIXED
   - letmodule.res - NOW PASSES

4. **@string/@int polyvariant FFI encoding** - ✅ FIXED
   - polyvariant.res, React.res, Next.res - NOW PASS
   - Fixed `spec_of_ptyp` to handle @string, @int, @unwrap, @ignore attributes
   - Fixed `Pexp_letmodule` to recurse into module expression for nested externals

5. **@obj result type reconstruction** - ✅ FIXED
   - attributes.res - NOW PASSES
   - Implemented `process_obj_type()` for type transformation
   - Implemented `build_obj_ffi_type()` for FfiObjCreate with field names

6. **FFI encoding differences** - ✅ arrow.res FIXED
   - Fixed `result_is_unit` calculation for nested arrow types
   - Remaining FFI issues: ReactEventRe.resi, ReasonReactRouter.res, Warp_XHR.res, UsdPriceProvider.res
   - These need further investigation of exact encoding differences

**Note:** Some files appear in multiple categories (e.g., subscription.res has jsConverter).

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
