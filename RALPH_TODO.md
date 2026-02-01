# Ralph TODO: Binary AST Parity

**Last Updated:** 2026-02-01
**Overall Status:** 126/1049 bsc-ast tests passing (12.0%)
**sexp-locs Status:** 1049/1049 tests passing (100%) ✅

---

## Root Cause Analysis

The binary AST structure (sexp-locs) is 100% correct. The difference is in **position sharing** during marshal serialization.

### Key Finding: Arrow Function Position Sharing

Comparing binary output for `let f = x => x`:
- OCaml: 198 bytes
- Rust: 206 bytes (8 bytes larger)

The difference: OCaml uses `CODE_SHARED8` references for positions that Rust writes as full position blocks.

```
# OCaml at offset 0x90 (uses shared reference):
04 0c 04 03   # CODE_SHARED8 with distance 0x0c, then more data

# Rust at same offset (writes full positions):
c0 04 16 41 40 48 c0 04 17 41 40 4e  # Full position blocks
```

### Root Cause

In OCaml's marshal format, positions with pointer equality get shared. OCaml reuses the same position object in multiple places. In Rust, we use `PosIdx` arena indices for sharing, but some positions that should be shared are getting different indices.

Specifically, when parsing arrow functions, certain positions (like the start/end of parameters and body) should share the same `PosIdx` but currently don't.

---

## Tasks

### Phase 1: Investigate Position Sharing Patterns

- [ ] **Task 1.1**: Analyze OCaml position sharing in arrow functions
  - Study `compiler/syntax/src/res_parser.ml` for `parseEs6ArrowExpression`
  - Identify which positions share the same variable/pointer
  - Document the expected sharing pattern

- [ ] **Task 1.2**: Compare Rust position creation in arrow functions
  - Study `compiler-rust/src/parser/expression.rs` for arrow function parsing
  - Log PosIdx values for positions created during `let f = x => x`
  - Identify where sharing diverges from OCaml

- [ ] **Task 1.3**: Create position sharing test harness
  - Add debug output to marshal writer showing position indices
  - Compare OCaml marshal trace vs Rust marshal trace for simple cases

### Phase 2: Fix Position Sharing

- [ ] **Task 2.1**: Fix arrow function expression position sharing
  - The body expression's location likely needs to share positions with parameter location
  - Match OCaml's pattern where `prev_end_pos` becomes the next token's context

- [ ] **Task 2.2**: Fix multi-parameter arrow function sharing
  - `let f = (x, y) => x + y` has 12 bytes difference (vs 8 for single param)
  - Additional sharing needed for tuple pattern positions

- [ ] **Task 2.3**: Fix async arrow function sharing
  - `let f = async x => x` also has 8 bytes difference
  - Verify async attribute positions use correct sharing

### Phase 3: Systematic Position Sharing Audit

- [ ] **Task 3.1**: Audit all expression position creation
  - Binary expressions
  - Application expressions
  - Match/switch expressions
  - Block expressions

- [ ] **Task 3.2**: Audit pattern position creation
  - Tuple patterns
  - Record patterns
  - Array patterns

- [ ] **Task 3.3**: Audit type position creation
  - Arrow types with arity
  - Record type definitions

### Phase 4: Validation

- [ ] **Task 4.1**: Run full test suite, verify no regressions
- [ ] **Task 4.2**: Target 500/1049 bsc-ast parity (47%)
- [ ] **Task 4.3**: Target 750/1049 bsc-ast parity (71%)
- [ ] **Task 4.4**: Target 1000/1049 bsc-ast parity (95%)
- [ ] **Task 4.5**: Achieve 1049/1049 bsc-ast parity (100%)

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
