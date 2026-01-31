# Typedtree Parity: Next Steps Plan

## Current Status
- **Parity: 28/87 files (32%)**
- 59 files still failing

## Failure Categories Analysis

Based on analysis of failing tests, here are the main categories of issues:

### Priority 1: High Impact Issues (Will fix many tests)

#### 1.1 Object Types Not Implemented
**Files affected:** test_obj.res, nested_obj_literal.res, object_type_spreads.res, and many others

**Issue:** Object types (`Tobject`, `Tfield`) are not properly implemented in the type system.

- OCaml produces: `Tobject (Tfield "say_hi" Fpresent (Tpoly ...) Tnil)`
- Rust produces: `Tvar None`

**Location:** `compiler-rust/src/types/typecore.rs` (Texp_send handling), `compiler-rust/src/types/type_expr.rs`

**Fix:**
1. Implement `Tobject` and `Tfield` type descriptors
2. Implement object type inference when accessing fields via `x["field"]` syntax
3. Fix `Texp_send` to include the third argument (`None` for method lookup result)

#### 1.2 Object/Record Literal Expressions (%obj, %ffi)
**Files affected:** FFI.res, nested_obj_literal.res, many JSX-related files

**Issue:** `%ffi` and `%obj` expressions produce placeholder `Texp_constant (Const_int 0)` instead of proper `Texp_letmodule` structure.

- OCaml produces: `Texp_letmodule "J" (Tmod_structure ...) (Texp_apply ...)`
- Rust produces: `Texp_constant (Const_int 0)`

**Location:** `compiler-rust/src/types/typecore.rs` (extension handling)

**Fix:**
1. Implement proper handling of `%ffi`, `%obj`, `%raw` extensions
2. Create the `Texp_letmodule` with the internal `J` module containing `unsafe_expr` primitive
3. Generate proper `Texp_apply` for the FFI call

#### 1.3 Type Constraint Expressions (Texp_constraint)
**Files affected:** FFI.res, many files with explicit type annotations on expressions

**Issue:** Expressions with type annotations don't include `Texp_constraint` wrapper.

- OCaml produces: `Texp_constraint (core_type ...) (expression ...)`
- Rust produces: just the expression without the constraint wrapper

**Location:** `compiler-rust/src/types/typecore.rs`

**Fix:**
1. When typing expressions with explicit type constraints, wrap in `Texp_constraint`
2. Store the `core_type` from the constraint

### Priority 2: Medium Impact Issues

#### 2.1 Cycle Detection in Type Printing
**Files affected:** functor_inst.res, float_record.res, and others with recursive/cyclic types

**Issue:** Type printing doesn't detect cycles, leading to different output format.

- OCaml produces: `<cycle>` for recursive type references
- Rust produces: expanded types or `Tvar None`

**Location:** `compiler-rust/src/types/typed_sexp.rs` (type printing)

**Fix:**
1. Track visited type nodes during printing
2. When a cycle is detected, output `<cycle>` instead of the full type

#### 2.2 Include Statements (Tstr_include, Tmod_constraint)
**Files affected:** include_side_effect.res, nested_include.res, rebind_module.res

**Issue:** Module includes and constraints not fully implemented.

**Location:** `compiler-rust/src/types/typemod.rs`

**Fix:**
1. Implement proper `Tstr_include` with `include_declaration`
2. Implement `Tmod_constraint` for module type constraints
3. Handle `Tmod_ident` for module identifiers

### Priority 3: Lower Impact Issues

#### 3.1 Texp_send Third Argument
**Files affected:** test_obj.res and object access patterns

**Issue:** `Texp_send` is missing the third argument (method lookup result).

- OCaml: `(Texp_send expr "field" None)`
- Rust: `(Texp_send expr "field")`

**Location:** `compiler-rust/src/types/typedtree.rs`, `compiler-rust/src/types/typed_sexp.rs`

**Fix:**
1. Add optional third argument to `Texp_send` variant
2. Update sexp printing to include the argument

#### 3.2 Record Field `required` Flag
**Files affected:** Some record-related tests

**Issue:** Optional fields should be marked as `required)` vs non-optional `required))` - the closing parens differ.

**Location:** `compiler-rust/src/types/typed_sexp.rs`

**Fix:** Review the sexp output format for record fields.

## Recommended Implementation Order

1. **Object Types (1.1)** - High impact, foundational for object-related features
2. **Type Constraint Expressions (1.3)** - Relatively simple, high impact
3. **Cycle Detection (2.1)** - Medium complexity, will fix multiple tests
4. **FFI/Object Literals (1.2)** - Complex but high impact
5. **Include Statements (2.2)** - Module system improvements
6. **Minor fixes (3.x)** - Quick wins

## Verification

After each fix, run:
```bash
./scripts/test_typedtree_parity.sh --quick  # Stop on first failure
./scripts/test_typedtree_parity.sh          # Full test suite
```

## Key Files to Modify

- `compiler-rust/src/types/typecore.rs` - Expression/pattern type checking
- `compiler-rust/src/types/typemod.rs` - Module/structure type checking
- `compiler-rust/src/types/type_expr.rs` - Type representation
- `compiler-rust/src/types/typedtree.rs` - Typed tree data structures
- `compiler-rust/src/types/typed_sexp.rs` - S-expression output
