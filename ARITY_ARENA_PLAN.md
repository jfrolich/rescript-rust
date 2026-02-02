# Plan: Arity Arena for Binary AST Parity

## Problem Statement

OCaml shares `Option<i32>` arity values via pointer equality during marshal serialization. When two functions have the same arity (e.g., both `Some(1)`), OCaml may reuse the same object. Rust currently creates separate objects, causing binary AST differences.

**Key observation:** OCaml's sharing is based on **pointer identity** - if the same reference is passed through the code, it gets shared. The solution is to mirror this: create an arena for arities and pass `ArityIdx` early, just like OCaml passes references.

## Design Principle

**If an object type is shared in OCaml's output, create an arena for it in Rust and pass the index as early as possible.**

This ensures:
1. The sharing logic in Rust matches OCaml naturally
2. No content-based heuristics needed - sharing happens because the same index is used
3. The code structure mirrors OCaml's reference passing

## Phase 1: Investigation

### Task 1.1: Empirically determine OCaml's arity sharing pattern

Create test cases to understand exactly what OCaml shares:

```rescript
// Test 1: Single function with type annotation
let f: int => int = x => x

// Test 2: Two functions, same arity
let f: int => int = x => x
let g: int => int = y => y

// Test 3: Two functions, different arity
let f: int => int = x => x
let g: (int, int) => int = (x, y) => x + y

// Test 4: Function without type annotation
let f = x => x
let g = y => y

// Test 5: Type annotation arity vs body arity (same function)
let f: int => int = x => x  // Does type arity share with body arity?
```

For each test:
1. Generate OCaml binary AST
2. Analyze marshal output to see which `Some(n)` blocks are shared vs separate
3. Document the sharing pattern

### Task 1.2: Identify all arity creation sites

Map where arities are created in both OCaml and Rust:

**Type arities (typ.rs / res_core.ml):**
- `Ptyp_arrow` creation
- Arrow type parsing

**Expression arities (expr.rs / res_core.ml):**
- `Pexp_fun` creation
- Arrow function parsing

**Other sites:**
- JSX PPX transformations
- Built-in PPX (ppx.rs)

## Phase 2: Arena Implementation

### Task 2.1: Define ArityIdx and ArityArena

```rust
// In parse_arena.rs or new file

/// Index into the arity arena
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArityIdx(u32);

/// Arena for arity values
/// Mirrors OCaml's reference-based sharing
pub struct ArityArena {
    arities: Vec<Option<i32>>,
}

impl ArityArena {
    pub fn new() -> Self {
        Self { arities: Vec::new() }
    }

    /// Push a new arity, returning its index
    /// This is the equivalent of OCaml allocating a new arity reference
    pub fn push(&mut self, arity: Option<i32>) -> ArityIdx {
        let idx = ArityIdx(self.arities.len() as u32);
        self.arities.push(arity);
        idx
    }

    /// Get arity value by index
    pub fn get(&self, idx: ArityIdx) -> Option<i32> {
        self.arities[idx.0 as usize]
    }
}
```

### Task 2.2: Integrate ArityArena into ParseArena

```rust
// In parse_arena.rs

pub struct ParseArena {
    // ... existing fields ...

    /// Arena for arity values
    pub arity_arena: ArityArena,
}

impl ParseArena {
    /// Push a new arity value
    pub fn push_arity(&mut self, arity: Option<i32>) -> ArityIdx {
        self.arity_arena.push(arity)
    }

    /// Get arity by index
    pub fn get_arity(&self, idx: ArityIdx) -> Option<i32> {
        self.arity_arena.get(idx)
    }
}
```

### Task 2.3: Update AST types to use ArityIdx

```rust
// In ast.rs

pub enum CoreTypeDesc {
    // ...
    Ptyp_arrow {
        arg: Box<TypeArg>,
        ret: Box<CoreType>,
        arity: ArityIdx,  // Changed from Arity
    },
    // ...
}

pub enum ExpressionDesc {
    // ...
    Pexp_fun {
        arg_label: ArgLabel,
        default: Option<Box<Expression>>,
        lhs: Pattern,
        rhs: Box<Expression>,
        arity: ArityIdx,  // Changed from Arity
        is_async: bool,
    },
    // ...
}
```

## Phase 3: Parser Updates

### Task 3.1: Update type parsing (typ.rs)

At each site where `Arity::Full(n)` or `Arity::Unknown` is created:

```rust
// Before:
arity: Arity::Full(1),

// After:
arity: p.arena.push_arity(Some(1)),
```

Key insight: Each `push_arity` call creates a NEW index, just like each OCaml allocation creates a new reference. Sharing happens when the SAME index is passed to multiple places.

### Task 3.2: Update expression parsing (expr.rs)

Same pattern - replace `Arity::*` with `p.arena.push_arity(...)`.

### Task 3.3: Update JSX PPX (jsx_ppx.rs)

Same pattern for JSX-generated functions.

### Task 3.4: Update built-in PPX (ppx.rs)

Same pattern for PPX-generated constructs.

## Phase 4: Marshal Updates

### Task 4.1: Update marshal to use ArityIdx sharing

```rust
// In marshal.rs

impl MarshalWriter {
    /// Maps ArityIdx to object counter (for arena-based sharing)
    arity_idx_table: HashMap<ArityIdx, u32>,

    /// Write an arity using arena-based sharing
    pub fn write_arity_idx(&mut self, idx: ArityIdx, arena: &ParseArena) {
        // Check if we've written this ArityIdx before
        if let Some(&obj_idx) = self.arity_idx_table.get(&idx) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        let arity = arena.get_arity(idx);
        match arity {
            None => {
                // None is encoded as integer 0, no sharing needed
                self.write_int(0);
            }
            Some(n) => {
                // Record object index BEFORE writing
                let obj_idx = self.obj_counter;

                // Write Some(n) as Block(tag=0, [n])
                self.write_block_header(0, 1);
                self.write_int(n as i64);

                // Record for future sharing
                self.arity_idx_table.insert(idx, obj_idx);
            }
        }
    }
}
```

### Task 4.2: Update current_marshal.rs

Update `Arity` (now `ArityIdx`) marshaling to use the new arena-based approach.

## Phase 5: Achieving OCaml Parity

### Task 5.1: Match OCaml's arity creation pattern

Based on Phase 1 findings, ensure Rust creates/reuses ArityIdx in the same pattern as OCaml creates/reuses references.

**If OCaml shares arities across functions:**
- Create the arity once (push to arena)
- Pass the same ArityIdx to multiple functions

**If OCaml keeps arities separate within a function:**
- Create separate ArityIdx for type annotation vs function body

### Task 5.2: Handle edge cases

- Nested functions
- Curried functions
- Async functions
- Type-annotated vs inferred arities

## Phase 6: Validation

### Task 6.1: Run binary AST parity tests

```bash
./scripts/test_parser_ast_parity.sh 2>&1 | tail -50
```

### Task 6.2: Verify specific test cases from Phase 1

Ensure the test cases from investigation phase now match byte-for-byte.

### Task 6.3: Check for regressions

Ensure no files that previously passed now fail.

## Generalized Principle

**For any object type where OCaml shares via pointer equality:**

1. Create an arena for that object type
2. Define an index type (e.g., `FooIdx`)
3. Update AST types to use the index instead of the value
4. Update parser to push values to arena, passing indices through the code
5. Update marshal to share based on index equality

This mirrors OCaml's reference semantics: same index = same object = shared in output.

## Files to Modify

- `compiler-rust/src/parse_arena.rs` - Add ArityArena
- `compiler-rust/src/parser/ast.rs` - Change Arity to ArityIdx in AST types
- `compiler-rust/src/parser/typ.rs` - Update type parsing
- `compiler-rust/src/parser/expr.rs` - Update expression parsing
- `compiler-rust/src/parser/jsx_ppx.rs` - Update JSX transformations
- `compiler-rust/src/binary_ast/ppx.rs` - Update built-in PPX
- `compiler-rust/src/binary_ast/marshal.rs` - Add arity_idx_table
- `compiler-rust/src/binary_ast/current_marshal.rs` - Update Arity marshaling
- `compiler-rust/src/binary_ast/parsetree0.rs` - May need ArityIdx support

## Success Criteria

- Binary AST parity improves from ~25% to significantly higher
- No regressions in existing passing tests
- sexp-locs tests remain at 100%
