# Typedtree Parity: Status and Plan

## Current Status
- **Parity: 36/102 files (35%)**
- Started at 31/102 (30%) for this session

## Recently Completed Work

### Session Work (Jan 2026)

1. **Copy @tag and @unboxed attributes from type declaration to constructors**
   - File: `compiler-rust/src/types/typemod.rs`
   - Matches OCaml's `copy_tag_attr_from_decl` in typedecl.ml
   - Impact: +2 tests passing

2. **Implement simplify_signature (duplicate value detection)**
   - File: `compiler-rust/src/types/typemod.rs`
   - When a module has duplicate value bindings (e.g., `let x = 0; let x = 1`),
     OCaml wraps the module in `Tmod_constraint` with `Tmodtype_implicit`
   - Added `has_duplicate_values` helper function
   - Impact: +3 tests passing

3. **Fix include_declaration sexp output**
   - File: `compiler-rust/src/types/sexp_typedtree.rs`
   - Changed from placeholder `<include_declaration>` to full output
   - Added `sexp_include_declaration` function

### Previous Work

1. **Texp_constraint wrapper** - Expression type annotations now work correctly
2. **Type path handling** - Fixed `create_persistent` for type identifiers
3. **Optional field defaults** - Fixed longidents and required/optional flag in sexp output
4. **Texp_coerce fix** - Target type handling
5. **Type lookup fix** - Name-based fallback for field type lookup
6. **Object types** - Implemented Tobject, Tfield in type inference

## Remaining Failure Categories

### High Impact (Would fix many tests)

#### 1. FFI Extension Handling (%ffi)
**Files affected:** FFI.res, many JSX-related files
**Effort:** 8-16 hours

**Problem:** Rust returns placeholder `Int(0)` for `%ffi` extensions.

**What OCaml Does:**
1. Parses JavaScript string from extension payload
2. Detects function arity via Flow parser
3. Creates type constraint: `(_, _, ...) => _` matching arity
4. Wraps in letmodule with primitive declaration for `#raw_expr`
5. Result: `Pexp_constraint(Pexp_letmodule(J, ...), arrow_type)`

**Current Rust:** `type_extension_expr` just returns `Texp_constant(Int(0))`.

#### 2. Cycle Detection in Type Printing
**Files affected:** test_obj.res, test_eq.res, etc.
**Effort:** 2-4 hours

**Problem:** Type printing outputs full types instead of `<cycle>` for recursive types.

**Fix:** Track visited type nodes during sexp printing and output `<cycle>` when revisiting.

#### 3. Pattern Match Exhaustiveness
**Files affected:** gpr_5557.res, etc.
**Effort:** 8-16 hours

**Problem:** `Partial` vs `Total` flag is always set to `Total`.

**Current code (typecore.rs:2203):**
```rust
Partial::Total, // Assume total for now
```

**Fix:** Implement proper exhaustiveness analysis for patterns.

#### 4. Type Extension Handling (Tstr_typext)
**Files affected:** rebind_module.res, etc.
**Effort:** 4-8 hours

**Problem:** Type extensions output placeholder values instead of proper paths and constructors.

### Medium Impact

#### 5. External Declarations (@module)
**Files affected:** mocha.res, external-related files
**Effort:** 4-8 hours

**Problem:** External declarations with `@module` attribute not fully implemented.

### Verification

After each fix, run:
```bash
./scripts/test_typedtree_parity.sh tests/tests/src/<specific_file>.res  # Test single file
./scripts/test_typedtree_parity.sh --quick  # Stop on first failure
./scripts/test_typedtree_parity.sh          # Full test suite
```

## Key Files

| File | Purpose |
|------|---------|
| `compiler-rust/src/types/typemod.rs` | Module type checking, attribute handling |
| `compiler-rust/src/types/typecore.rs` | Expression type checking, FFI handling |
| `compiler-rust/src/types/sexp_typedtree.rs` | Typed tree sexp output |
| `compiler-rust/src/types/typedtree.rs` | Typed tree data structures |
| `compiler/ml/typemod.ml` | OCaml reference for module handling |
| `compiler/ml/typedecl.ml` | OCaml reference for type declaration handling |

## Progress History

| Date | Parity | Notes |
|------|--------|-------|
| Jan 2026 (session start) | 31/102 (30%) | - |
| Jan 2026 (after attribute fix) | 33/102 (32%) | +2 from @tag/@unboxed copying |
| Jan 2026 (after simplify_sig) | 36/102 (35%) | +3 from Tmod_constraint and include_declaration |
