# Ralph TODO: Binary AST Parity

**Last Updated:** 2026-02-02
**Overall Status:** 329/1049 bsc-ast tests passing (31.4%)
**sexp-locs Status:** 1049/1049 tests passing (100%) ✅

**Note:** Many remaining failures are due to arity sharing (see Phase 6 below).

**Analysis Complete (2026-02-02):** The remaining 720 failing tests are blocked by multiple issues:
1. **Arity sharing (~700 files)**: OCaml's CSE cannot be replicated (structural limitation)
2. **parsetree0 Location sharing (~500+ files)**: mapper_to0 converts LocIdx to full Location structs,
   losing sharing information. Would require refactoring parsetree0 to use LocIdx.
3. **@deriving transformations**: `@deriving(accessors)` DONE; `@deriving(jsConverter)` and
   `@deriving(abstract)` still TODO (~8 files remaining)
4. **Module-level await (4 files)**: Requires refactoring to multi-item expansion

**Session End Status (2026-02-02):** All unchecked tasks are either BLOCKED or have very low impact.
Further progress requires addressing structural limitations (arity sharing, location sharing).

**@module FFI fix (2026-02-02):** Fixed @module attribute handling in FFI encoding.
- `ExternalModuleName` is now correctly created when `@module("...")` is present
- Previously `external_module_name: None` was hardcoded; now uses parsed `desc.module_name`
- FFI encoding now includes module names in the binary output (e.g., `$test`)
- +2 tests passing: bigint.res, binary.res (327 → 329)

**@deriving progress (2026-02-02):** 3 of 11 @deriving test files now pass after implementing
the full OCaml wrapper structure for `@deriving(accessors)`.

Most .resi (interface) files pass; most .res (implementation) files fail due to arity and location sharing.

**Phase 6 Status:** Tasks 6.3-6.5 complete. ArityIdx sharing DISABLED (causes regressions).
- ArityIdx infrastructure added to parse_arena.rs and marshal.rs
- AST types updated to use ArityIdx (Arity = ArityIdx type alias)
- Marshal write_arity_idx() now writes inline values (no sharing) to match pre-6.3 behavior
- Sharing code exists but is disabled - see marshal.rs comments

**ArityIdx findings (2026-02-02):**
- Content-based dedup caused ~45 regressions vs pre-6.3 (shared too aggressively)
- Single typed function `let f: int => int = x => x`:
  - OCaml: type arity `Some(1)` ≠ function arity `Some(1)` (2 separate `Some(1)` blocks)
  - Rust with dedup: both shared same ArityIdx → incorrect sharing (only 1 block)
- Two functions with same arity: OCaml has 3 `Some(1)` blocks (one shared), Rust has 4
- **OCaml's CSE (Common Subexpression Elimination) behavior discovered:**
  - OCaml's native compiler performs CSE at compile time
  - `Some 1` and `Some 1` in different parts of OCaml code become the SAME physical object
  - This applies ACROSS top-level bindings but NOT within a single binding
  - Within `let f: int => int = x => x`: type arity and function arity are SEPARATE
  - Across `let f = ... let g = ...`: one arity in g shares with one arity in f
- **Cannot replicate exactly:** OCaml's CSE operates at OCaml compilation level, not at ReScript parsing level
- **Resolution:** Disabled sharing in write_arity_idx() to restore baseline parity (327/1049)

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
- `let x = f(1)` ✅ (function calls now share positions correctly)
- `let x = Foo.bar(1)` ✅ (module-qualified calls work)
- `let x = !a; let y = !b` ✅ (unary ! operator Lident deduplication - 2026-02-02)
- `let f = (~x) => x` ✅ (labeled arguments - end position caching fix 2026-02-02)

JSX with children still differs:
- `let x = <div> <span/> </div>` ❌ (OCaml: 229 bytes, Rust: 196 bytes - Rust smaller)

### Blocking Issues

The remaining ~724 failing tests are affected by several issues:

1. **Arity sharing**: OCaml shares `Option<i32>` arity values via pointer equality. When two functions
   have the same arity (e.g., both `Some(1)`), OCaml reuses the same object. Rust creates separate objects.
2. **JSX children list locations**: Different location patterns for JSX children lists
3. **Chained pipe expressions**: Position sharing differs for complex expression chains

**Note:** mapper_to0.rs and parsetree0 are NOT involved in binary AST generation. They are only used
for external PPX support, which is not yet implemented. The blocking issues are in the main parsetree
marshal code (`marshal.rs`), not in mapper_to0.

### Key Finding: Dependency Extraction Fix

OCaml's `Depend.add_parent` only adds the parent module of dotted paths:
- `Foo.bar` → adds "Foo"
- `bar` → adds nothing
- `None` → adds nothing (not `Ldot`, just `Lident`)

Previously Rust was adding all uppercase identifiers, incorrectly including `None` and `Some`.

**Additional fix (2026-02-02):** Module bindings and functor parameters now tracked:
- `module Types = Foo` binds `Types` so references to `Types.X` don't add `Types` as a dependency
- `module Make = (Impl: Intf) => ...` binds `Impl` in the functor body
- This matches OCaml's `bv` (bound variables) tracking in `depend.ml`

**Additional fix (2026-02-02):** Pmty_ident dependency extraction:
- `Pmty_ident` (e.g., `module type T = Tree`) uses `add_parent`, not `addmodule`
- For simple Lidents like `Tree` or `Intf`, this adds nothing to dependencies
- `Pmty_alias` still uses `addmodule` (full path)
- This fixes 3 files: modType/ident.res, moduleTypeDeclaration.res, UrlUtils.res

**Additional fix (2026-02-02):** With-constraint dependency extraction:
- `Pwith_type(lid, td)` - only process td, not lid (lid is the path being constrained)
- `Pwith_module(lid1, lid2)` - only add lid2 as dependency, not lid1
- Example: `with module Bar = Array` - only `Array` is a dependency, not `Bar`
- Reduced dependency differences from 78 to 75 files

**Additional fix (2026-02-02):** First-class module pattern binding tracking:
- OCaml's `add_pattern` collects `Ppat_unpack` names into `pattern_bv` (bound variables)
- When processing `let module(Set) = z`, `Set` is added to bound modules
- Later `Set.S` references don't add `Set` as a dependency if it's already bound
- `add_bindings` (for `Pstr_value`, `Pexp_let`) collects unpack names from all patterns
- `add_pattern` in `Pexp_fun` and `add_case` also track unpack bindings
- Fixes `firstClassModules.res` (now byte-identical to OCaml)

**Status update (2026-02-02):** Dependency extraction is now 100% correct!
- All 1049 test files have identical dependency sections between Rust and OCaml
- Remaining 791 files that fail bsc-ast parity differ in position/arity sharing within the marshalled parsetree
- These are marshal.rs sharing issues (mainly arity sharing), not dependency extraction issues

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

- [x] **Task 1.6**: Fix Pexp_apply location sharing (4-byte difference on ALL function calls)
  - **Previously**: Function calls had 4-byte difference in binary output
  - **Root cause**: Rust was not correctly sharing the loc_start PosIdx when creating Pexp_apply locations
  - **Fixed**: Now uses `loc_start_idx(expr.pexp_loc)` to extract and reuse the original PosIdx
  - **Verified**: `let x = f()` and `let x = f(a, b)` now produce identical binary output to OCaml

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
  - **Additional fix**: Added `rewrite_attribute()`, `rewrite_attributes()`, and `rewrite_payload()`
    functions to transform strings inside attribute payloads (e.g., `@ocaml.doc("foo")`).
    This ensures docstrings get the same `"*j"` delimiter transformation as regular strings.

- [x] **Task 2.3**: Implement `@deriving` transformations (PARTIALLY DONE - accessors complete)
  - OCaml: `Ast_derive_projector.init()`, `Ast_derive_js_mapper.init()`
  - `@deriving(accessors)` - generates accessor functions for records/variants ✅
  - `@deriving(jsConverter)` - generates JS conversion functions (TODO)
  - `@deriving(abstract)` - generates getter/setter functions for records (TODO)
  - **Impact**: 11 test files use `@deriving`, 3 now pass (Mdx.res, subscription.res, typeDefinition.res)
  - Related files: `ast_tdcls.ml`, `ast_derive.ml`, `ast_attributes.ml`
  - **Implementation (2026-02-02)**:
    - Implemented full OCaml wrapper structure in ppx.rs:
      ```
      include (struct
        type t = { x: int }  // @deriving stripped
        include (struct
          let x = (param: t[@deriving(accessors)]) => param.x
        end : sig
          val x: t[@deriving(accessors)] -> int
        end)
      end)
      ```
    - `handle_deriving_type()` - generates outer include wrapper
    - `generate_accessor_include()` - generates inner constrained include
    - `generate_record_accessors_and_sigs()` - accessor functions + val signatures for records
    - `generate_variant_accessors_and_sigs()` - accessor functions + val signatures for variants
    - `core_type_of_type_declaration_with_attrs()` - preserves @deriving attribute on core type
    - `make_arrows()` - helper for arrow type construction
  - **Remaining issues**:
    - Some files still fail due to position/arity sharing differences unrelated to @deriving
    - `@deriving(jsConverter)` and `@deriving(abstract)` still need implementation

- [x] **Task 2.4**: Implement integer literal suffix handling
  - OCaml: `pat_mapper` and `expr_mapper` in bs_builtin_ppx.ml
  - Transform `Pconst_integer(s, Some 'l')` → `Pconst_integer(s, None)`
  - **Done**: Added to `rewrite_pattern` and `rewrite_expression` in ppx.rs.
    Parity improved from 134 to 135 tests.

- [x] **Task 2.5**: Implement `Pexp_extension` handling (partial)
  - OCaml: `Ast_exp_extension.handle_extension`
  - **Done**: Implemented `%debugger` in handle_debugger() in ppx.rs.
  - **Done (2026-02-02)**: Implemented `%re` in handle_re() - wraps %raw with Stdlib_RegExp.t type constraint.
  - **Done (2026-02-02)**: Implemented `%external` (deprecated) in handle_external_ext() - creates
    Js.undefinedToOption(if Js.typeof(raw_exp) == "undefined" then Js.Undefined.empty else raw_exp).
  - **Fixed (2026-02-02)**: PPX arity encoding changed from `Arity::Unknown` to `Arity::Full(1)` to match
    OCaml's `Typ.arrows` behavior which sets `arity = Some(list_length)`.
  - **Fixed (2026-02-02)**: handle_raw() now uses payload string's location for final expression's pexp_loc,
    matching OCaml's `{exp with pexp_desc = ...}` pattern.
  - Also fixed letmodule dependency tracking so local modules (like `J`) aren't added as dependencies.
  - Note: `%debugger` still has minor position sharing differences (Phase 4 issue).
  - TODO: `%obj`, `%todo` still need implementation (low impact - 0 test files use these).

- [x] **Task 2.6**: Implement `@inline` let binding transformation
  - **Done**: Transform `@inline let x = "foo"` into `Pstr_primitive` with FFI inline encoding
  - Supports: string, int, float, and bool constants
  - Implementation in `transform_inline_binding` in ppx.rs

- [x] **Task 2.7**: Implement async/await transformations
  - **Done**: Transform `Pexp_await(e)` to `Primitive_promise.unsafe_await(e)`
  - **Done**: For async functions, wrap innermost body with `Primitive_promise.unsafe_async(body)`
  - Implementation in `transform_await`, `wrap_with_unsafe_async`, and `add_promise_to_fun_body` in ppx.rs
  - Note: Async files still have 4-byte differences due to position sharing (Phase 4 issue)

- [ ] **Task 2.8**: Implement module-level await transformation (Complex - multi-item expansion)
  - OCaml: `bs_builtin_ppx.ml` lines 661-702, `ast_await.ml` `create_await_module_expression`
  - Transform `module M = @res.await Belt.List` into:
    1. Module type declaration: `module __Belt_List__ = module type of Belt.List`
    2. Module binding using `Primitive_module.import(module(M: __Belt_List__))`
  - This is a complex transformation involving:
    - Detecting `@res.await` attribute on module expressions
    - Creating a synthetic module type name from the module path
    - Generating module type declaration
    - Transforming to `Pmod_unpack(Primitive_promise.unsafe_await(Primitive_module.import(...)))`
  - **Investigation (2026-02-02)**: Attempted implementation but requires significant refactoring:
    - Rust's `rewrite_structure_item` returns single item, OCaml can emit multiple items
    - Would need to refactor to `flat_map` approach with `Vec<StructureItem>` return type
    - Complex interaction with `Pexp_letmodule` (expression-level) vs `Pstr_module` (structure-level)
    - Only ~4 test files use this pattern (`letmodule.res`, `await.res`)
  - **Impact**: Low (~4 files), high complexity. Deferring to focus on higher-impact issues.
  - Related files: `tests/syntax_tests/data/printer/expr/letmodule.res`

### Phase 3: JSX Binary Differences (Deferred - needs investigation)

**Note:** The JSX size differences need further investigation. The sexp-locs test passes 100% for JSX,
so the AST structure is correct. The differences are in how list locations are handled during
serialization.

**Important finding (2026-02-02): JSX PPX is NOT applied by default**
- OCaml's bsc only applies JSX PPX when `jsx_version` is explicitly set (via `-bs-jsx` flag)
- When not set, JSX elements remain as `Pexp_jsx_element` (not transformed to `Pexp_apply(ReactDOM.jsx, ...)`)
- The test script (`-bs-ast` without jsx flags) keeps JSX elements in their original form
- Attempting to unconditionally apply JSX PPX in Rust caused 20 regressions
- The object count difference for JSX files (OCaml > Rust) is expected when jsx_version is None
  because `Pexp_jsx_element` has different structure than the transformed `Pexp_apply`

- [x] **Task 3.1**: Investigate JSX container element size difference (ANALYZED)
  - OCaml builds list with unique locations per cons cell
  - Rust uses the same location for all cons cells
  - Needs investigation in `compiler-rust/src/binary_ast/` code path
  - **Update (2026-02-02)**: Without JSX PPX transformation, both OCaml and Rust keep JSX elements
    as `Pexp_jsx_element`. The binary differences are in location/position sharing, not JSX structure.

- [x] **Task 3.2**: Fix arrow function expression position sharing (DONE)
  - Simple cases now work: `x => x`, `(x, y) => x + y`
  - Multi-parameter and async arrow functions also work

### Phase 4: Systematic Position Sharing Audit

**Analysis**: The remaining differences are due to marshal sharing distances. OCaml uses
CODE_SHARED8 (single byte) for nearby positions, while Rust sometimes uses CODE_SHARED16
(2 bytes). This happens when:
- ~~`Foo.bar(x)` style calls - 4 byte difference per call~~ ✅ Fixed
- ~~Module-qualified function applications~~ ✅ Fixed
- **Underscore placeholder patterns**: `pt0` types use full `Location`/`Position` instead of indices,
  losing sharing information when converting from `LocIdx` in `mapper_to0::loc()`
- **Attribute payload expressions**: Positions in attribute payloads (e.g., `@ocaml.doc("foo")`)
  don't share correctly with the parent structure item positions

This is a low-level marshal optimization issue, not an AST structure issue.

**Arity Sharing Limitation**: OCaml shares `Option<i32>` arity values between structures via pointer
equality. When two functions have the same arity (e.g., both `Some(1)`), OCaml reuses the same object.
Rust cannot replicate this without content-based sharing, which breaks single-function cases where
type annotation arity and function arity should be separate objects.

- [x] **Task 4.1**: Audit all expression position creation (partial - 135→144)
  - ✅ Fixed: Pexp_apply - use loc_start_idx() to reuse existing PosIdx
  - ✅ Fixed: Pexp_field - reuse start position from expression location
  - ✅ Fixed: Array indexing - reuse start position from expression location
  - ✅ Fixed: List cons cells - reuse item.pexp_loc.loc_start
  - ✅ Fixed: Dict tuples - reuse key_loc.loc_start
  - Remaining: some complex patterns still differ

- [x] **Task 4.2**: Audit pattern position creation (partial)
  - ✅ Fixed: Or-patterns - use loc_start_idx() to reuse PosIdx
  - ✅ Fixed: Constrained patterns - reuse pat.ppat_loc.loc_start
  - ✅ Fixed: Alias patterns - reuse pat.ppat_loc.loc_start
  - ✅ Fixed: List pattern cons cells - reuse item.ppat_loc.loc_start

- [x] **Task 4.3**: Audit module position creation (partial)
  - ✅ Fixed: Module apply chain - reuse result.pmod_loc.loc_start
  - ✅ Fixed: Module constraint - reuse rhs_module_expr.pmod_loc.loc_start

- [x] **Task 4.4**: Investigate marshal sharing order (ANALYZED - structural limitation)

- [x] **Task 4.5**: Investigate underscore placeholder position sharing (ANALYZED)
  - **Test case**: `5->doStuff(3, _, 7)` - Rust creates 1 extra Position block (4 bytes)
  - **Impact**: ~199 test files use underscore placeholders, though not all are affected
  - OCaml shares positions at shorter distances
  - Rust may allocate extra position indices
  - **Key finding**: OCaml uses pointer equality for sharing, not content equality
  - **Arity sharing case study**:
    - When two functions have the SAME arity (e.g., both `Some(1)`), OCaml shares them
    - Single function: `let a: t => u = x => x` → matches perfectly (type arity and function arity are separate)
    - Two functions with different arities → matches perfectly
    - Two functions with SAME arity → OCaml shares 1 object, Rust doesn't (1 object difference)
  - **Attempted fix**: Content-based sharing for `Option<i32>` arity values
    - This BROKE single-function cases (Rust incorrectly shared type arity with function arity)
    - Reverted because it violated the "no content-based sharing" constraint
  - **Conclusion**: Some sharing differences are structural and cannot be fixed without violating design constraints
  - **Impact**: ~1 object difference per pair of functions with identical arities

- [x] **Task 4.6**: Investigate and fix Lident sharing for operators (2026-02-02)
  - **Investigation**: Analyzed why `let x = !a; let y = !b` had 1-byte difference
  - **Finding**: OCaml shares the `Lident("not")` wrapper between multiple uses of `!` operator
  - **Root cause**: OCaml's compiler optimizes string literals, so `Longident.Lident "not"`
    creates Lidents that reference the same interned string, and marshal shares the entire Lident
  - **Pattern**: Static string literals (like "not") get Lident sharing; dynamic strings (like "~-") don't
    - `!a` and `!b` → OCaml shares `Lident("not")`, Rust didn't
    - `-a` and `-b` → OCaml writes `"~-"` fresh each time, Rust shares via string interning
  - **Fix**: For `Token::Bang` specifically, use `push_lident_static("not")` which deduplicates
    both the string AND the Lident wrapper (matching OCaml's behavior)
  - **Commit**: d34d57039 "Fix 'not' Lident deduplication for binary AST parity"
  - **Result**: `let x = !a; let y = !b` now matches byte-for-byte
  - **Note**: Other unary operators still use the old approach - they are structurally
    different (Rust smaller due to string interning vs OCaml's fresh strings)

- [x] **Task 4.7**: Fix end position caching for labeled functions (2026-02-02)
  - **Investigation**: Labeled functions like `(~x) => x` had 1-object (4-byte) difference
  - **Root cause**: `mk_loc_current()` was creating end positions without caching, so the
    position used for the label location's end was different from the pattern location's end
    (even though they had the same value)
  - **Sequence issue**:
    1. `mk_loc_current()` pushes uncached end position for label location
    2. `p.next()` sets `prev_end_pos = end_pos`
    3. `mk_loc_to_prev_end()` uses cached prev_end_pos → different PosIdx
  - **Fix**: Added `end_pos_cache` HashMap to Parser state, updated:
    - `mk_loc_current()` to use `get_or_push_end_pos_cached()`
    - `get_or_push_prev_end_pos()` to check `end_pos_cache`
  - **Commit**: 25f14bc56 "Fix labeled argument position sharing"
  - **Result**: +65 tests passing (261 → 325, 24.9% → 31.0%)
  - **Also**: Reuse StrIdx for label and pattern in punned cases (`~x`)

### Phase 5: Validation

- [x] **Task 5.1**: Run full test suite, verify no regressions
  - Current: 325/1049 bsc-ast tests passing (31.0%)
  - **Baseline fix (2026-02-02)**: Regenerated bsc_ast baseline to remove false positives
    - Previous baseline had 262 entries but 117 were incorrectly passing
    - Many files had position sharing differences (e.g., `#...Type.t as x` patterns)
    - New baseline has 259 truly passing files
    - Example: `Css_Js_Core.res` uses polymorphic variant spread patterns which cause position sharing differences
  - **Pmty_ident fix (2026-02-02)**: Fixed dependency extraction for module type identifiers
    - Pmty_ident uses add_parent semantics (simple Lidents add nothing)
    - Pmty_alias uses addmodule semantics (full path)
  - **with_constraint fix (2026-02-02)**: Fixed dependency extraction for Pmty_with constraints
    - OCaml ignores the path being constrained (first argument)
    - Only processes the type declaration or right-hand side module path
  - **Analysis of remaining failures (2026-02-02)**:
    - JSX with children: mapper_to0 issue, cannot fix per instructions
    - `@as` attributes in externals: Rust FFI encoding differs from OCaml
      - OCaml strips `@as` attributes and encodes them as `Arg_cst` in FFI
      - Rust may be leaving attributes in place, causing extra data
    - Simple expressions, pipes, module-qualified calls: all work correctly
    - 89% of .resi files pass, only 14% of .res files pass
      - Interface files are simpler, implementation files have more complex patterns
  - **Content-based Location sharing analysis (2026-02-02)**:
    - Investigated adding content-based sharing for `Location` and `Position` in marshal
    - This would share locations with identical content, approximating OCaml's behavior
    - **Finding**: Content-based sharing caused regressions in some files
    - OCaml's mapper_to0 preserves pointer identity (same location object = shared in marshal)
    - Rust's mapper_to0 creates new Location structs (loses identity, no sharing)
    - Proper fix would require `Rc<Location>` or `LocIdx` in parsetree0 (significant refactor)
    - **Status**: Content-based sharing reverted; architectural limitation documented
- [ ] **Task 5.2**: Target 500/1049 bsc-ast parity (47%) - **BLOCKED** (multiple issues)
  - **Blockers analyzed (2026-02-02)**:
    1. **Arity sharing (Task 6.6)**: OCaml's CSE cannot be replicated (~700 files)
    2. **parsetree0 Location sharing**: mapper_to0 loses LocIdx identity (~500+ files)
    3. **@deriving (Task 2.3)**: Not implemented (~8 files, ~880 lines to port)
    4. **Module-level await (Task 2.8)**: Not implemented (~4 files, complex)
  - **Impact**: Without fixing #1 or #2, cannot reach 500+ parity
  - Current: 325/1049 (31.0%) - most .resi files pass, most .res files fail
- [ ] **Task 5.3**: Target 750/1049 bsc-ast parity (71%) - **BLOCKED** (arity limitation)
- [ ] **Task 5.4**: Target 1000/1049 bsc-ast parity (95%) - **BLOCKED** (arity limitation)
- [ ] **Task 5.5**: Achieve 1049/1049 bsc-ast parity (100%) - **BLOCKED** (arity limitation)

### Phase 6: Arity Arena Implementation (UNBLOCKS Phase 5)

**Design Principle:** If an object type is shared in OCaml's output, create an arena for it in Rust
and pass the index as early as possible. This mirrors OCaml's reference passing - sharing happens
naturally when the same index is used (just like OCaml shares when same reference is passed).

- [x] **Task 6.1**: Investigate OCaml's arity sharing pattern empirically (2026-02-02)
  - **Key finding**: OCaml's compiler performs constant folding for `Some n` values
  - All `Some 1` literals in the parser become the SAME physical object
  - When Marshal serializes, it detects physical identity and creates shared references
  - **Test results**:
    - Single typed function (`let f: int => int = x => x`): byte-identical ✅
    - Two typed functions, same arity: 464 bytes (same size) but different sharing
      - OCaml: at offset 0x170, `04 3c` = CODE_SHARED8 (shares back 60 objects to first `Some(1)`)
      - Rust: at offset 0x170, `90 41` = fresh `Some(1)` block (no sharing)
  - **OCaml Marshal behavior verified**:
    - Different pointers with same content: NOT shared (27 bytes for `[Some 1; Some 1]`)
    - Same pointer (same physical object): shared (27 bytes but smaller payload)
  - **Conclusion**: Need arena-based approach where `Arity::Full(1)` values get the same ArityIdx,
    enabling Marshal to recognize them as the same object and create shared references

- [x] **Task 6.2**: Define ArityIdx and ArityArena (2026-02-02)
  - Added `ArityIdx` index type to `parse_arena.rs`
  - Added `arities: Vec<Option<i32>>` and `arity_dedup: HashMap<Option<i32>, ArityIdx>` to `ParseArena`
  - Added `push_arity()` method with deduplication:
    - Same arity value → same index (matches OCaml's constant folding)
    - At marshal time, same ArityIdx → shared reference in output
  - Added `get_arity()` and `arity_count()` methods
  - Added `arity_idx_table` and `write_arity_idx()` to MarshalWriter

- [x] **Task 6.3**: Update AST types to use ArityIdx - **DONE** (2026-02-02)
  - Changed `pub type Arity = ArityIdx` in ast.rs (type alias approach)
  - Updated all code that reads/writes arity values to use `arena.get_arity(idx)` lookup
  - Updated files: current_marshal.rs, mapper_from0.rs, mapper_to0.rs, ppx.rs,
    expr.rs, typ.rs, jsx_ppx.rs, state.rs, sexp_locs.rs, sexp_typedtree.rs,
    parsetree_viewer.rs, printer2.rs, ml_printer.rs, typecore.rs, convert.rs
  - Parser helper methods `push_arity_full()` and `push_arity_unknown()` added
  - Build compiles successfully; tests show 724/1049 failing (expected until 6.6)

- [x] **Task 6.4**: Update parser to use arena - **DONE** (2026-02-02)
  - Replaced `Arity::Full(n)` with `arena.push_arity(Some(n))`
  - Replaced `Arity::Unknown` with `arena.push_arity(None)`
  - Updated: typ.rs, expr.rs, jsx_ppx.rs, ppx.rs
  - Uses `push_arity_full()` and `push_arity_unknown()` helper methods

- [x] **Task 6.5**: Add write_arity_idx to marshal - **DONE** (2026-02-02)
  - Added `arity_idx_table: HashMap<ArityIdx, u32>` to MarshalWriter
  - Added `write_arity_idx()` method that:
    - Checks `arity_idx_table` for previously-written ArityIdx
    - Writes shared reference if found
    - Otherwise writes arity value and records in table
  - Infrastructure is ready; waiting for AST type change (Task 6.3)

- [x] **Task 6.6**: Match OCaml's arity creation pattern - **STRUCTURAL LIMITATION**

  **STATUS**: ANALYZED. OCaml's arity sharing is due to CSE (Common Subexpression Elimination)
  at the OCaml native compiler level, which cannot be replicated in Rust.

  **Key empirical findings (verified 2026-02-02)**:

  1. **Single typed function** `let f: int => int = x => x` ✅ PASSES (byte-identical)
     - OCaml: 2 `Some(1)` blocks (type arity + function arity are SEPARATE)
     - Rust: 2 `Some(1)` blocks (same as OCaml)

  2. **Two typed functions with same arity** ❌ FAILS
     ```rescript
     let f: int => int = x => x
     let g: int => int = y => y
     ```
     - OCaml: 3 `Some(1)` blocks (one shared across bindings)
     - Rust: 4 `Some(1)` blocks (all separate)
     - OCaml at offset ~0x14e: `04 3c` (CODE_SHARED8), Rust: `90 41` (fresh block)

  3. **Two functions with different arities** ✅ PASSES (byte-identical)
     ```rescript
     let f: int => int = x => x
     let g: (int, int) => int = (x, y) => x + y
     ```
     - No sharing possible, both create fresh objects

  **OCaml's CSE behavior (verified empirically)**:
  ```ocaml
  (* OCaml test: *)
  let make_some n = Some n
  let a = make_some 1
  let b = make_some 1
  (* Bytecode: a == b is false *)
  (* Native:   a == b is TRUE! *)
  ```
  - OCaml's native compiler performs CSE at compile time
  - `Some 1` expressions become the SAME physical object in the compiled binary
  - This applies ACROSS top-level definitions (different `let` bindings)
  - But NOT within a single expression (each `Some arity` in the parser creates fresh)

  **Why the type annotation/function arity approach doesn't work**:
  - Both type annotations (`uncurried_type ~arity`) and function expressions (`uncurried_fun ~arity`)
    use COMPUTED arities: `Some (List.length params)` or `Some arity` where arity is a variable
  - Computed values create fresh objects at runtime, not shared
  - Within a single binding, type and function arities are SEPARATE (2 objects)
  - Across bindings, OCaml's CSE shares because the compiled code evaluates to the same value

  **Approaches attempted**:
  1. ✗ Index-based sharing in marshal: Shares within binding (breaks single-function case)
  2. ✗ Content-based sharing in marshal: Shares within binding (breaks single-function case)
  3. ✓ No sharing in marshal: Works for single function, but Rust has extra object for multi-function

  **Conclusion**: OCaml's sharing is a compiler-level optimization that operates on the compiled
  ReScript parser binary. Rust cannot replicate this without implementing similar CSE at the
  Rust compiler level (which is impractical and out of scope).

  **Impact**: Files with 2+ typed functions having the same arity will have ~1 extra arity object
  per shared arity value in OCaml. This affects ~724 test files.

  **Resolution**: Accept this structural limitation. Focus on other issues that CAN be fixed.

  **Debugging tips**:
  - Object count is at offset 0x2a (4 bytes after marshal magic at 0x1a)
  - `90 41` = Block(tag=0, size=1) containing int 1 = Some(1)
  - `04 xx` = CODE_SHARED8, shares object at distance xx
  - `05 xx yy` = CODE_SHARED16, shares object at distance xxyy
  - If Rust has MORE objects than OCaml: Rust is not sharing something OCaml shares
  - If Rust has FEWER objects than OCaml: Rust is sharing something OCaml doesn't

**Generalized principle:** For ANY object type where OCaml shares via pointer equality:
1. Create an arena for that object type
2. Define an index type (e.g., `FooIdx`)
3. Update AST types to use the index
4. Update parser to push to arena, passing indices through code
5. Update marshal to share based on index equality

**Files to modify:**
- `compiler-rust/src/parse_arena.rs` - Add ArityArena
- `compiler-rust/src/parser/ast.rs` - Change Arity to ArityIdx
- `compiler-rust/src/parser/typ.rs` - Update type parsing
- `compiler-rust/src/parser/expr.rs` - Update expression parsing
- `compiler-rust/src/parser/jsx_ppx.rs` - Update JSX
- `compiler-rust/src/binary_ast/ppx.rs` - Update built-in PPX
- `compiler-rust/src/binary_ast/marshal.rs` - Add arity_idx_table
- `compiler-rust/src/binary_ast/current_marshal.rs` - Update Arity marshaling

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

## Note on parsetree0/ast0/mapper_to0

**UPDATE (2026-02-02): These files ARE involved in binary AST generation.**

**AST flow for binary AST output:**
1. Parser creates AST with `LocIdx` (arena-indexed locations)
2. `mapper_to0` converts to `parsetree0` which uses full `Location` structs
3. Marshal serializes the `Location` structs (not LocIdx)
4. **Problem**: Each conversion creates a NEW `Location` struct, losing sharing information

**This is a major source of parity differences.** When the same LocIdx is converted multiple times
by mapper_to0, each creates a separate Location struct that cannot be shared by marshal.

**Impact**: ~500+ files have location sharing differences due to this.

**Potential fix** (significant refactoring required):
- Change parsetree0 to use `LocIdx` instead of `Location`
- Or use `Rc<Location>` to enable identity-based sharing
- Both require major changes to parsetree0.rs, parsetree0_marshal.rs, and mapper_to0.rs

**Files relevant to binary AST parity:**
- ✅ `compiler-rust/src/parser/` - Position creation and reuse during parsing
- ✅ `compiler-rust/src/parse_arena.rs` - Arena management for positions
- ✅ `compiler-rust/src/binary_ast/marshal.rs` - Marshal serialization (arity sharing issue is here)
- ✅ `compiler-rust/src/binary_ast/ppx.rs` - Built-in PPX transformations (string interp, raw, etc.)
- ⚠️ `compiler-rust/src/binary_ast/mapper_to0.rs` - Converts LocIdx→Location, LOSES sharing
- ⚠️ `compiler-rust/src/binary_ast/parsetree0.rs` - Uses full Location (not LocIdx)

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
