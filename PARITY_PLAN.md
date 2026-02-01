# Typedtree Parity: Status and Action Plan

## Current Status
- **Parity: 44/102 files (43%)**
- **Failing: 58 files**

**Note:** Most remaining issues require structural changes to the type checker,
not just sexp output fixes. See "Issues Requiring Structural Changes" below.

### Recent Fixes
- **Module type sexp output** - Implemented proper ModuleType, ModuleTypeDesc, Signature, SignatureItem structures and sexp output for functor parameters. (+1 file)
- **Type extension handling** - Implemented proper type extension handling with actual paths and constructors. (+1 file)
- **`*j` delimiter transformation** - Fixed string delimiter transformation from `"js"` to `"*j"` during type checking. (+6 files)

## Issue Categories Summary

Based on analysis of all 66 failing files, the issues fall into these categories:

| Category | Files Affected | Effort | Priority |
|----------|---------------|--------|----------|
| 1. Cycle Detection | ~15 | 2-4 hours | HIGH |
| 2. Module Type Sexp | ~10 | 2-4 hours | HIGH |
| 3. Module Type Declaration Sexp | ~5 | 1-2 hours | HIGH |
| 4. Type Extension/Tstr_typext | ~5 | 4-8 hours | MEDIUM |
| 5. `*j` vs `js` Identifier | ~10 | 1-2 hours | HIGH |
| 6. Pattern Exhaustiveness | ~5 | 8-16 hours | LOW |
| 7. %ffi Extension | ~5 | 8-16 hours | LOW |
| 8. Tstr_primitive/Value Description | ~5 | 2-4 hours | MEDIUM |
| 9. Include/Tmod_constraint Structure | ~5 | 2-4 hours | MEDIUM |

**Estimated total effort: 30-60 hours**

---

## Detailed Action Items

### 1. FIX: Cycle Detection in Type Expression Sexp (HIGH PRIORITY)

**Files affected:** test_obj.res, test_eq.res, functor_inst.res, test_dup_param.res, nested_obj_literal.res, etc.

**Problem:** The `<cycle>` marker appears at different positions in Rust vs OCaml output.

**Root Cause Analysis (Updated 2026-02-01):**

The issue is more fundamental than cycle detection in printing. Investigation revealed:

1. **OCaml's primitive types are at GENERIC_LEVEL**: In OCaml's `Predef`, types like `type_int` are created with `newgenty` which sets level to `generic_level` (100000000).

2. **OCaml's `copy` function uses mutation for memoization**: When copying a type, OCaml mutates the original type descriptor to `Tsubst t` where `t` is the copy. This enables the memo check `| Tsubst ty -> ty` at the start of copy.

3. **The cycle pattern in OCaml is intentional**: For operator `+` with type `int -> int -> int` where all three `int` positions share the same type object:
   - When instantiated, all three positions get the SAME copy (via Tsubst memoization)
   - When printing the operator's type, the shared reference causes `<cycle>` markers
   - BUT the function `f`'s pattern type is built from DIFFERENT type variables that link to int

4. **Key insight**: After unification, type variables LINK to their unified types but remain distinct objects. When printing `f`'s type:
   - `param1_ty` -> Tlink -> int_copy_a
   - `param2_ty` -> Tlink -> int_copy_b  (DIFFERENT copy)
   - `return_ty` -> Tlink -> int_copy_c  (DIFFERENT copy)

   Since int_copy_a, int_copy_b, int_copy_c are different objects, no cycles appear.

5. **In Rust**: The current implementation creates types at current_level (0), not GENERIC_LEVEL. When `copy_type` is called on non-generic types, it returns them as-is (ReturnSelf), preserving sharing. This causes more cycles than expected.

**Attempted fixes that didn't work:**
- Making primitive types at GENERIC_LEVEL + adding memo to copy_type: This caused MORE cycle issues because the copied types also share references
- The fundamental issue is that Rust's type unification and construction needs to create separate type objects in the same places OCaml does

**What needs to happen:**
The fix requires understanding exactly where OCaml creates fresh type objects vs reuses existing ones during:
1. Type instantiation (copy function)
2. Function parameter type construction
3. Unification (link direction)

This is not a simple fix - it requires careful analysis of the type checking flow.

**Example Diff (test_eq.res):**
```
OCaml + operator type: <cycle> -> <cycle> -> Tvar None
OCaml f pattern type:  int -> int -> int (no cycles!)

Rust + operator type:  int -> <cycle> -> <cycle>
Rust f pattern type:   int -> <cycle> -> <cycle> (has cycles!)
```

**Estimated Effort:** 8-16 hours (structural change to type checker)

---

### 2. FIX: Module Type Sexp Output (HIGH PRIORITY)

**Files affected:** functors_one_arg_at_a_time.res, and ~10 others

**Problem:** Placeholder `<module_type>` instead of proper `Tmty_signature` output.

**Example Diff:**
```
OCaml:                              Rust:
  (Some                               <module_type>
    (module_type
      (Tmty_signature
        (signature))
      (attributes)))
```

**Fix Location:** `compiler-rust/src/types/sexp_typedtree.rs:1145-1165`

**Fix Details:**
Implement `sexp_module_type` function to match OCaml's `module_type ~with_locs mt`:

```rust
fn sexp_module_type(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, mt: &ModuleType) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, mt.mty_loc)]
    } else {
        vec![]
    };
    let desc = sexp_module_type_desc(arena, ctx, with_locs, &mt.mty_desc);
    let attrs = sexp_attributes(with_locs, &mt.mty_attributes);
    let mut items = vec![Sexp::atom("module_type")];
    items.extend(loc_sexp);
    items.push(desc);
    items.push(attrs);
    Sexp::list(items)
}

fn sexp_module_type_desc(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, desc: &ModuleTypeDesc) -> Sexp {
    match desc {
        ModuleTypeDesc::Tmty_ident(p, _) => Sexp::list(vec![Sexp::atom("Tmty_ident"), sexp_path(p)]),
        ModuleTypeDesc::Tmty_signature(sg) => Sexp::list(vec![Sexp::atom("Tmty_signature"), sexp_signature(arena, ctx, with_locs, sg)]),
        ModuleTypeDesc::Tmty_functor(id, _, mt_arg, mt_res) => {
            Sexp::list(vec![
                Sexp::atom("Tmty_functor"),
                sexp_ident(id),
                opt(|mt: &ModuleType| sexp_module_type(arena, ctx, with_locs, mt), mt_arg),
                sexp_module_type(arena, ctx, with_locs, mt_res),
            ])
        }
        // ... other cases
    }
}
```

Then update `sexp_module_expr_desc` at lines 1145 and 1164 to use this function.

**Estimated Effort:** 2-4 hours

---

### 3. FIX: Module Type Declaration Sexp Output (HIGH PRIORITY)

**Files affected:** gpr_3897_test.res, etc.

**Problem:** Placeholder `<module_type_declaration>` instead of proper output.

**Example Diff:**
```
OCaml:                                  Rust:
  (module_type_declaration                <module_type_declaration>
    "S"
    "S"
    (Some
      (module_type
        ...)))
```

**Fix Location:** `compiler-rust/src/types/sexp_typedtree.rs:1585-1587`

**Fix Details:**
Implement `sexp_module_type_declaration`:

```rust
fn sexp_module_type_declaration(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, mtd: &ModuleTypeDeclaration) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, mtd.mtd_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("module_type_declaration"),
        sexp_ident(&mtd.mtd_id),
        string(&mtd.mtd_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(opt(|mt: &ModuleType| sexp_module_type(arena, ctx, with_locs, mt), &mtd.mtd_type));
    items.push(sexp_attributes(with_locs, &mtd.mtd_attributes));
    Sexp::list(items)
}
```

**Estimated Effort:** 1-2 hours

---

### 4. FIX: `*j` vs `js` String Delimiter (HIGH PRIORITY)

**Files affected:** big_enum.res, as_inline_record_test.res, ~10 others

**Problem:** OCaml outputs `"*j"` for certain string delimiters but Rust outputs `"js"`.

**Example Diff:**
```
OCaml: "*j"
Rust:  "js"
```

**Root Cause:** The `*j` is a special internal representation in OCaml for template literals or special string syntax. The Rust printer isn't converting to this representation.

**Fix Location:** Likely in `sexp_constant` or string handling in `sexp_typedtree.rs`

**Fix Details:**
Look at how OCaml's `Const_string (s, delim)` handles the delimiter. When `delim` is `Some "js"`, it should print as `"*j"` in the sexp output.

Check `compiler/ml/sexp_typedtree.ml:76-77`:
```ocaml
| Const_string (s, delim) ->
  Sexp.list [Sexp.atom "Const_string"; string s; opt string delim]
```

The delimiter is printed directly, so the transformation must happen during type checking. Check how the string delimiter is set during constant creation.

**Estimated Effort:** 1-2 hours

---

### 5. FIX: Type Extension (Tstr_typext) Issues (MEDIUM PRIORITY)

**Files affected:** rebind_module.res, etc.

**Problem:** Extension paths show "placeholder" instead of actual path names.

**Example Diff:**
```
OCaml:                      Rust:
  "a")                        "placeholder")
  "a")                        "placeholder")
  ((extension_constructor     ())
    "A"
    "A"
    ...))
```

**Root Cause:** The type checker isn't properly populating the type extension data structures.

**Fix Location:** `compiler-rust/src/types/typemod.rs` (type extension handling)

**Fix Details:**
The issue is in how `Tstr_typext` items are created during module type checking. The extension path and constructors need to be properly filled in during type checking, not just in sexp output.

**Estimated Effort:** 4-8 hours

---

### 6. FIX: Tstr_primitive/Value Description (MEDIUM PRIORITY)

**Files affected:** mocha.res, etc.

**Problem:** Primitive value descriptions are empty or minimal.

**Example Diff:**
```
OCaml:                          Rust:
  (Tstr_primitive                 (empty or missing)
    (value_description
      "test"
      "test"
      (core_type ...)
      (prim ...)
      (attributes)))
```

**Fix Location:** Check `StructureItemDesc::Tstr_primitive` in `sexp_typedtree.rs`

**Fix Details:**
Ensure `sexp_value_description` is properly implemented and called for primitive declarations.

**Estimated Effort:** 2-4 hours

---

### 7. FIX: Include/Tmod_constraint Structure (MEDIUM PRIORITY)

**Files affected:** include_side_effect.res, include_side_effect_free.res, nested_include.res

**Problem:** Structure wrapping differences - attributes appearing in wrong places, Tmod_constraint not being applied.

**Root Cause:** The simplify_signature logic may not match OCaml's behavior for includes.

**Fix Location:** `compiler-rust/src/types/typemod.rs`

**Estimated Effort:** 2-4 hours

---

### 8. Pattern Exhaustiveness (LOW PRIORITY)

**Files affected:** gpr_5557.res, and others with match expressions

**Problem:** Always outputs `Total` instead of computing `Partial`.

**Fix Location:** `compiler-rust/src/types/typecore.rs:2203`

**Fix Details:**
This requires implementing a proper exhaustiveness checker which is a significant undertaking. For now, mark as low priority since it doesn't affect code generation correctness.

**Estimated Effort:** 8-16 hours (complex algorithm)

---

### 9. %ffi Extension Handling (LOW PRIORITY)

**Files affected:** FFI.res, JSX-related files

**Problem:** Returns `Texp_constant(Int(0))` placeholder instead of proper `Texp_letmodule` structure.

**Fix Location:** `compiler-rust/src/types/typecore.rs` (extension handling)

**Fix Details:**
Need to implement proper FFI extension handling that:
1. Parses JavaScript string from extension payload
2. Detects function arity via Flow parser
3. Creates proper type constraint and letmodule wrapper

This is a complex feature requiring Flow parser integration.

**Estimated Effort:** 8-16 hours

---

## Execution Order (Recommended)

### Phase 1: Quick Wins (5-10 hours) - Target: 60% parity
1. **`*j` vs `js` fix** - 1-2 hours, ~10 files
2. **Module type sexp** - 2-4 hours, ~10 files
3. **Module type declaration sexp** - 1-2 hours, ~5 files

### Phase 2: Medium Fixes (8-16 hours) - Target: 80% parity
4. **Cycle detection** - 2-4 hours, ~15 files
5. **Tstr_primitive** - 2-4 hours, ~5 files
6. **Include/Tmod_constraint** - 2-4 hours, ~5 files
7. **Type extension** - 4-8 hours, ~5 files

### Phase 3: Complex Fixes (16-32 hours) - Target: 100% parity
8. **Exhaustiveness** - 8-16 hours
9. **%ffi extension** - 8-16 hours

---

## Key Files Reference

| File | Purpose |
|------|---------|
| `compiler-rust/src/types/sexp_typedtree.rs` | Sexp output (most fixes here) |
| `compiler-rust/src/types/typemod.rs` | Module type checking |
| `compiler-rust/src/types/typecore.rs` | Expression type checking |
| `compiler-rust/src/types/typedtree.rs` | Data structures |
| `compiler/ml/sexp_typedtree.ml` | OCaml reference implementation |

---

## Testing Commands

```bash
# Test single file
./scripts/test_typedtree_parity.sh tests/tests/src/<file>.res

# Quick test (stop on first failure)
./scripts/test_typedtree_parity.sh --quick

# Full test suite
./scripts/test_typedtree_parity.sh

# View specific diff
diff -a /tmp/o.sexp /tmp/r.sexp
```

---

## Progress History

| Date | Parity | Notes |
|------|--------|-------|
| Jan 2026 (session start) | 31/102 (30%) | - |
| Jan 2026 | 33/102 (32%) | +2 from @tag/@unboxed copying |
| Jan 2026 | 36/102 (35%) | +3 from Tmod_constraint and include_declaration |
| Jan 2026 | 42/102 (41%) | +6 from `*j` delimiter transformation |
| Jan 2026 | 43/102 (42%) | +1 from type extension path fix |
| Jan 2026 | 43/102 (42%) | Added sexp_module_type_declaration (partial) |
| Jan 2026 | 44/102 (43%) | +1 from ModuleType structure and sexp output |

## Analysis Notes

### Issues Requiring Structural Changes

Several remaining issues require changes beyond sexp printing - they need modifications to the type checker or typedtree data structures:

1. **Module Type sexp** (~10 files) - PARTIALLY FIXED. The Rust `ModuleType` now has proper structure:
   ```rust
   pub struct ModuleType {
       pub mty_desc: ModuleTypeDesc,
       pub mty_loc: LocIdx,
       pub mty_attributes: Attributes,
   }
   ```
   The sexp output functions are implemented. Remaining issues:
   - `typemod.rs` still uses `ModuleType::placeholder()` instead of populating actual structures
   - `Pmod_constraint` uses `Tmodtype_implicit` when it should use `Tmodtype_explicit` with the actual typed module type
   - Need to implement `transl_modtype` to properly type module type expressions

2. **Value Description sexp** (~5 files) - Rust uses `ValueDescription` from decl.rs (Types level), but OCaml's typed tree has a separate typed `value_description` with:
   - `val_id: Ident`
   - `val_name: Loc<String>`
   - `val_desc: core_type` (the typed core_type)
   - `val_prim: Vec<String>` (primitive names)
   Currently `Tstr_primitive` outputs `<value_description>` placeholder.

3. **Cycle Detection** (~15 files) - The `<cycle>` marker appears at different positions in type trees. Example:
   ```
   OCaml: (Tpoly <cycle> ())  // cycle inside Tpoly body
   Rust:  (Tpoly (Tvar None) ()) <cycle>  // cycle after Tpoly
   ```

   **Root Cause Analysis (investigated):**
   - Both OCaml and Rust use the same approach: follow Tlink chains (repr), then use the resolved type's identity for cycle detection
   - The difference is in HOW types are linked during type inference
   - Example: For `let f = x => x["say_hi"]`, both `Tpoly body` and `Tarrow ret` resolve to the same type variable
   - In Rust: Tpoly body visited first → outputs content; Tarrow ret visited second → outputs `<cycle>`
   - In OCaml: Tarrow ret visited first → outputs content; Tpoly body visited second → outputs `<cycle>`

   This is caused by different type linking directions during unification in `typecore.ml` vs `typecore.rs`.
   The types are semantically equivalent but the internal Tlink structure differs.

   **Potential Fix:** Would require matching OCaml's exact type creation and unification order in type_send and related functions. This is invasive and risks breaking other type checking behavior.

4. **Type Extension** (FIXED) - Extension paths now properly populated.

5. **FFI Extension** (~5 files) - The `%ffi` extension returns placeholder instead of proper `Texp_letmodule` structure with parsed JavaScript.

6. **Pattern Exhaustiveness** (~5 files) - Always outputs `Total` instead of computing `Partial`. Requires implementing the exhaustiveness checking algorithm.

7. **Include/Tmod_constraint** (~5 files) - OCaml wraps includes with config attributes in `Tmod_constraint(Tmod_structure(...))`, Rust outputs them as separate items.

These issues require deeper investigation of the type checking implementation rather than sexp output fixes.
