# Ralph TODO: Binary AST Parity

**Last Updated:** 2026-02-01
**Overall Status:** 135/1049 bsc-ast tests passing (12.9%)
**sexp-locs Status:** 1049/1049 tests passing (100%) ✅

---

## Root Cause Analysis

The binary AST structure (sexp-locs) is 100% correct. The differences are in:
1. **Position sharing** during marshal serialization (fixed for simple cases)
2. **Dependency extraction** - fixed to match OCaml's `add_parent` semantics

### Current Status

Simple expressions now match OCaml byte-for-byte:
- `let f = x => x` ✅
- `let f = (x, y) => x + y` ✅
- `let f = () => id` ✅
- `let f = x => switch x { | A => 1 | B => 2 }` ✅
- `let f = x + y` ✅
- `let x = {a: 1, b: 2}` ✅
- `let x = if true { 1 } else { 2 }` ✅
- `let x = <div />` ✅

JSX with children still differs:
- `let x = <div> <span/> </div>` ❌ (OCaml: 229 bytes, Rust: 196 bytes - Rust smaller)

### Key Finding: Dependency Extraction Fix

OCaml's `Depend.add_parent` only adds the parent module of dotted paths:
- `Foo.bar` → adds "Foo"
- `bar` → adds nothing
- `None` → adds nothing (not `Ldot`, just `Lident`)

Previously Rust was adding all uppercase identifiers, incorrectly including `None` and `Some`.

---

## Tasks

### Phase 1: Investigate Position Sharing Patterns

- [x] **Task 1.1**: Analyze OCaml position sharing in arrow functions
  - Studied `compiler/syntax/src/res_parser.ml` and `res_core.ml`
  - Key insight: OCaml captures `end_pos = p.prev_end_pos` once and reuses it in fold_right
  - All Pexp_fun locations share the same end position pointer
  - Position sharing already works via value-based caching in Rust

- [x] **Task 1.2**: Compare Rust position creation in arrow functions
  - Arrow functions now produce byte-identical output for simple cases
  - Rust uses `get_or_push_prev_end_pos()` which caches positions by value
  - Simple arrow functions like `x => x`, `(x, y) => x + y` are working

- [x] **Task 1.3**: Fix dependency extraction
  - Fixed `add_longident` to match OCaml's `add_parent` semantics
  - Simple Lidents (e.g., `None`, `Some`) are no longer added as dependencies
  - Only parent modules of dotted paths are now extracted

- [x] **Task 1.4**: Implement pipe operator desugaring in PPX
  - OCaml: `ast_exp_apply.ml` transforms `a->f` into `f(a)`, etc.
  - Rust: Added full pipe desugaring to `ppx.rs`
  - Transformations:
    - `a->f` becomes `f(a)`
    - `a->f(b,c)` becomes `f(a,b,c)`
    - `a->#Variant` becomes `#Variant(a)`
    - `a->Constructor` becomes `Constructor(a)`
    - `a->b->c` becomes `c(b(a))` (chains correctly)
  - This was blocking many test files that use pipes

- [x] **Task 1.5**: Fix placeholder (`_`) string sharing in pipes
  - OCaml: Uses same `hidden_var = "__x"` string for both pattern and identifier
  - Rust: Was creating two different StrIdx values
  - Fixed: `arena.intern("__x")` once, then pass the StrIdx to create both pattern and identifiers
  - Uses `push_lident_from_idx()` to share the string between Ppat_var and Pexp_ident

### Phase 2: Built-in PPX Parity (Bs_builtin_ppx in Rust) - PREREQUISITE

**This phase is a prerequisite for binary parity.** OCaml runs `Ppx_entry.rewrite_implementation`
(which calls `Bs_builtin_ppx.mapper`) on the AST before saving to `.ast` files. Without these
transformations, binary output cannot match.

Currently `compiler-rust/src/binary_ast/ppx.rs` only implements **FFI external encoding**.
We need to implement the remaining transformations.

**Reference files:**
- OCaml: `compiler/frontend/bs_builtin_ppx.ml`
- OCaml: `compiler/frontend/ppx_entry.ml`
- Rust: `compiler-rust/src/binary_ast/ppx.rs`

- [x] **Task 2.1**: Implement `%raw` extension point handling
  - OCaml: `Ast_exp_handle_external.handle_raw_structure`
  - Transforms `[%raw "..."]` into appropriate AST nodes
  - Also handle `%%raw` at structure level
  - **Done**: Implemented both `%raw` (expression) and `%%raw` (structure) transformations.
    Creates `Pexp_letmodule` with local external using `#raw_expr` or `#raw_stmt`.

- [x] **Task 2.2**: Implement string interpolation (`j"..."` and backtick strings)
  - OCaml: `Ast_utf8_string_interp.transform_exp` / `transform_pat`
  - Transforms `"hello"` (js delimiter) to `"*j"` delimiter after transforming escape sequences
  - Transforms template strings (backticks) to `"bq"` delimiter
  - **Done**: Implemented in `transform_string_exp` and `transform_string_pat` in ppx.rs.
    Handles both expressions and patterns. Parity improved from 128 to 134 tests.

- [ ] **Task 2.3**: Implement `@deriving` transformations
  - OCaml: `Ast_derive_projector.init()`, `Ast_derive_js_mapper.init()`
  - `@deriving(accessors)` - generates accessor functions for variants
  - `@deriving(jsConverter)` - generates JS conversion functions
  - **Blocking issue**: OCaml strips `@deriving` attribute from type declarations after processing.
    Rust keeps the attribute, causing binary output to include extra bytes.
  - Related files: `ast_tdcls.ml`, `ast_derive.ml`, `ast_attributes.ml`

- [x] **Task 2.4**: Implement integer literal suffix handling
  - OCaml: `pat_mapper` and `expr_mapper` in bs_builtin_ppx.ml
  - Transform `Pconst_integer(s, Some 'l')` → `Pconst_integer(s, None)`
  - **Done**: Added to `rewrite_pattern` and `rewrite_expression` in ppx.rs.
    Parity improved from 134 to 135 tests.

- [x] **Task 2.5**: Implement `Pexp_extension` handling (partial)
  - OCaml: `Ast_exp_extension.handle_extension`
  - **Done**: Implemented `%debugger` in handle_debugger() in ppx.rs.
  - Also fixed letmodule dependency tracking so local modules (like `J`) aren't added as dependencies.
  - Note: `%debugger` still has minor position sharing differences (Phase 4 issue).
  - TODO: `%external`, `%obj`, `%re`, `%todo` still need implementation.

- [ ] **Task 2.6**: Implement `@inline` let binding transformation
  - Currently partial in Rust (helpers exist, rewrite has TODO)
  - Transform `@inline let x = "foo"` into external with FFI inline encoding

- [ ] **Task 2.7**: Implement async context tracking
  - OCaml: `async_context` ref and `in_function_def` ref in expr_mapper
  - Track whether we're inside an async function for proper transformation

### Phase 3: JSX Binary Differences (Deferred - mapper_to0 issue)

**Note:** Per instructions, mapper_to0.rs should NOT be modified unless absolutely necessary.
The JSX size differences are caused by list location handling in `map_jsx_children_to_list`:
- OCaml's `make_list_expression` creates unique locations for each cons cell
- Rust uses the same location for all cons cells
- OCaml's nil `[]` uses `loc_ghost = true`, Rust doesn't

This is a mapper_to0 issue, not a parser issue. sexp-locs passes 100% for JSX.

- [x] **Task 3.1**: Investigate JSX container element size difference (ANALYZED)
  - Root cause: `map_jsx_children_to_list` in mapper_to0.rs uses shared locations
  - OCaml builds list with unique locations per cons cell
  - This is a mapper_to0 issue, deferred per instructions

- [x] **Task 3.2**: Fix arrow function expression position sharing (DONE)
  - Simple cases now work: `x => x`, `(x, y) => x + y`
  - Multi-parameter and async arrow functions also work

### Phase 4: Systematic Position Sharing Audit

- [ ] **Task 4.1**: Audit all expression position creation
  - Binary expressions
  - Application expressions
  - Match/switch expressions
  - Block expressions

- [ ] **Task 4.2**: Audit pattern position creation
  - Tuple patterns
  - Record patterns
  - Array patterns

- [ ] **Task 4.3**: Audit type position creation
  - Arrow types with arity
  - Record type definitions

### Phase 5: Validation

- [ ] **Task 5.1**: Run full test suite, verify no regressions
- [ ] **Task 5.2**: Target 500/1049 bsc-ast parity (47%)
- [ ] **Task 5.3**: Target 750/1049 bsc-ast parity (71%)
- [ ] **Task 5.4**: Target 1000/1049 bsc-ast parity (95%)
- [ ] **Task 5.5**: Achieve 1049/1049 bsc-ast parity (100%)

---

## Debugging Commands

```bash
# Run full parity test
./scripts/test_parser_ast_parity.sh 2>&1 | tail -50

# Test a single file
./scripts/test_parser_ast_parity.sh tests/syntax_tests/data/printer/expr/record.res

# Compare binary output for a simple file (use bsc, not res_parser)
echo 'let f = x => x' > /tmp/test.res
./packages/@rescript/darwin-arm64/bin/bsc.exe -bs-ast /tmp/test.res -o /tmp/ocaml.ast
./compiler-rust/target/release/bsc -bs-ast /tmp/test.res -o /tmp/rust.ast
diff <(xxd /tmp/ocaml.ast) <(xxd /tmp/rust.ast)

# Build Rust compiler
cargo build --manifest-path compiler-rust/Cargo.toml --release
```

---

## Reference Files

| File | Purpose |
|------|---------|
| `compiler-rust/src/parser/expression.rs` | Arrow function parsing - where positions are created |
| `compiler-rust/src/parser/state.rs` | Parser state with prev_end_pos tracking |
| `compiler-rust/src/parse_arena.rs` | Position/location arena management |
| `compiler/syntax/src/res_parser.ml` | OCaml parser (reference) - study position variable reuse |
| `compiler/syntax/src/res_scanner.ml` | OCaml scanner (reference) - position creation |

---

## Important: Do NOT Modify parsetree0/ast0 (For Now)

**The current focus is position sharing in the parser** - positions that should have the same `PosIdx` are getting different indices during parsing. parsetree0/ast0 has its own issues but that's a separate task.

**Note on AST terminology:**
- **ast** (parsetree) - The current/main parsetree used by the compiler. This is what we're focused on. This is what gets serialized and saved to `.ast` files.
- **parsetree0/ast0** - Only used for PPXs (preprocessor extensions). NOT what gets saved to `.ast` files. Not our current focus.

Focus on these files:
- ✅ `compiler-rust/src/parser/` - Position creation and reuse during parsing
- ✅ `compiler-rust/src/parse_arena.rs` - Arena management for positions
- ✅ `compiler-rust/src/binary_ast/marshal.rs` - Can modify if needed

Do NOT touch these files unless absolutely necessary:
- ❌ `parsetree0.rs`
- ❌ `parsetree0_marshal.rs`
- ❌ `mapper_to0.rs`

## Important: No Content-Based Sharing Tricks

**Do NOT implement content-based sharing** (e.g., deduplicating positions with identical values). OCaml's sharing is based on **pointer/reference equality**, not content equality. If two positions have the same values but are different objects in OCaml, they should NOT be shared in Rust either.

The fix must be in how positions are created and reused during parsing - matching OCaml's pattern of reusing the same position variable.

---

## Notes

- The sexp-locs test passes 100%, so the AST structure is correct
- The difference is purely in binary serialization sharing patterns
- OCaml's sharing is based on pointer equality (same variable = same object)
- Rust's sharing uses arena indices (same PosIdx = same object in output)
- Most failures are in `.res` files (implementation files have more arrow functions)
- 71 of 123 passing files are `.resi` files (interfaces have simpler expressions)
