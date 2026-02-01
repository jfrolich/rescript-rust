# Typedtree Parity: Status and Action Plan

## Current Status
- **Parity: 49/101 files (48%)**
- **Failing: 52 files**

**Note:** Most remaining issues require structural changes to the type checker,
not just sexp output fixes. See "Issues Requiring Structural Changes" below.

### Recent Fixes
- **Object type construction** - Fixed `Ptyp_object` to build proper `Tobject` with `Tfield` chain instead of using a fresh type variable. Also wrap object field core_types in `Ttyp_poly`. (2026-02-01)
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

### 1. FIX: Cycle Detection in Type Expression Sexp (BLOCKED - NEEDS DIFFERENT APPROACH)

**Files affected:** test_obj.res, test_eq.res, functor_inst.res, test_dup_param.res, nested_obj_literal.res, etc.

**Problem:** The `<cycle>` marker appears at different positions in Rust vs OCaml output.

**Current Status (Updated 2026-02-01):**

After investigation, the situation is more nuanced than originally thought. There are TWO different cycle patterns:

**Pattern A - Primitive operators (e.g., test_eq.res):**
- **OCaml** has cycles for primitive operator types
- **Rust** does NOT have cycles - shows fully resolved types

**Pattern B - Match expressions (e.g., switch_string.res, large_integer_pat.res):**
- **OCaml** shows fully resolved types
- **Rust** has cycles - shows `<cycle>` instead of the actual type

**Pattern C - Type variables (e.g., float_array.res - `let f = x => ([1., 2.], x)`):**
- **Both** have cycles, but in DIFFERENT positions
- This is a type traversal order difference - "first occurrence wins" vs "second occurrence wins"

```
OCaml: (Tarrow <cycle> (Ttuple (array float) (Tvar None)) ...)  // cycle on arg
Rust:  (Tarrow (Tvar None) (Ttuple (array float) <cycle>) ...)  // cycle in tuple
```

**Example A (test_eq.res - `let f = (x, y) => x + y`):**
```
OCaml + operator type: (Tarrow ... <cycle> (Tarrow ... <cycle> (Tvar None) ...) ...)
Rust + operator type:  (Tarrow ... int (Tarrow ... int int ...) ...)
```

**Example B (switch_string.res - `let foo = x => switch x { ... }`):**
```
OCaml foo type: (Tarrow ... string string ...)
Rust foo type:  (Tarrow ... string <cycle> ...)
```

The test script filters `<cycle>` lines, but after filtering:
- Pattern A: OCaml has `(Tvar None)`, Rust has `(Tconstr int)`
- Pattern B: OCaml has `(Tconstr string)`, Rust has incomplete structure

**Why the "fresh types" fix doesn't help:**

A proposed fix was to create fresh TypeExprRefs for each position in primitive operator signatures
(e.g., `fresh_int(ctx)` instead of reusing `int_ty`). This was based on the assumption that
Rust was showing false cycles due to shared type references.

However, testing shows that Rust ALREADY doesn't produce cycles for test_eq.res (0 `<cycle>` markers).
The difference is structural - after OCaml's cycles are filtered, its output has `(Tvar None)`
while Rust has resolved `(Tconstr int)`. These are semantically equivalent but structurally different.

**Root Cause Analysis:**

1. **OCaml's type sharing causes cycles**: When `+` is typed as `int -> int -> int` with a single
   shared `int` type object, unification causes cycles when printing.

2. **OCaml's cycle detection outputs `(Tvar None)`**: When a cycle is detected, OCaml outputs
   `<cycle>` for the repeated occurrence, leaving the return type as unresolved `(Tvar None)`.

3. **Rust creates separate type objects**: The current Rust implementation creates distinct
   TypeExprRefs during type checking, so no cycles appear.

4. **The outputs are semantically equivalent**: Both represent `int -> int -> int`, just with
   different internal representations that serialize differently.

**Options for resolution:**

1. **Update test normalization**: Modify `normalize_sexp` to also handle `(Tvar None)` vs
   `(Tconstr ...)` differences that result from cycle handling. This is a significant change.

2. **Make Rust match OCaml's cycle pattern**: Would require matching OCaml's exact type
   construction and sharing behavior. This is invasive and may break other type checking.

3. **Accept the difference**: The outputs are semantically equivalent. Consider marking these
   tests as "known different" or updating expectations.

**Estimated Effort:** 8-16 hours (requires either test infrastructure changes or deep type checker changes)

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

### 6. FIX: Tstr_primitive/Value Description (LOW PRIORITY - SERIALIZATION DIFFERENCE)

**Files affected:** mocha.res, gpr_658.res, etc.

**Problem:** OCaml bundles FFI attributes as binary data in the primitive list, while Rust outputs them separately.

**Example (mocha.res):**
```
OCaml:
  (prim
    "describe"
    "¦¾°BDÔ(describe°%mocha@@@@@")  <- binary marshaled @module attribute
  (attributes)

Rust:
  (prim
    "describe")
  (attributes
    (attribute
      "module"
      (PStr <structure>)))
```

**Root Cause:** OCaml's `val_prim` field contains the marshaled FFI specification including attributes like `@module`. This is an internal binary representation. Rust correctly outputs the attributes separately in a human-readable format.

**Current Status:** The `sexp_typed_value_description` function is complete and correct. The difference is in how OCaml serializes FFI metadata - it bundles attributes into the prim field as binary data.

**Options:**
1. **Match OCaml's binary format** - Would require marshaling attributes in the same way OCaml does. Complex and not beneficial.
2. **Update test normalization** - Normalize the prim/attributes sections to handle semantic equivalence.
3. **Accept the difference** - Both outputs are correct, just serialized differently.

**Estimated Effort:** Low priority - this is a serialization format difference, not a semantic one.

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
| Feb 2026 | 49/101 (48%) | Object type fix; investigation findings documented |

## Analysis Notes

### Newly Discovered Issues (Feb 2026)

4. **Record expressions in recursive bindings** - For files like rec_array_test.res, record expressions
   in recursive value bindings output empty field lists `()` in Rust instead of the actual fields.

   Example: `let rec vicky = {taughtBy: teacher}` outputs `(Texp_record () None)` in Rust
   instead of the properly populated fields.

   Root cause: Likely an issue with how the record type lookup interacts with recursive binding
   type checking. The type may not be fully resolved when the record fields are processed.

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

2. **Value Description sexp** (~5 files) - FIXED but with serialization difference.
   - The `sexp_typed_value_description` is fully implemented
   - Outputs: val_id, val_name, core_type, prim, attributes
   - Difference: OCaml bundles FFI attributes (like @module) as binary data in the prim field
   - Rust outputs attributes separately in human-readable format
   - This is a serialization format difference, not a semantic one

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
