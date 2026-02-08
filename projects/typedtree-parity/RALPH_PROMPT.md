# Ralph Loop: Binary AST Parity

You are working on achieving **byte-for-byte binary AST parity** between the Rust ReScript compiler and the OCaml reference implementation.

## Core Principle: 1:1 OCaml Port

**This is a 1:1 rewrite of the OCaml implementation in idiomatic Rust.**

- **Study the OCaml code first** - Before writing ANY code, read and understand the corresponding OCaml implementation. Don't guess or reverse-engineer from output.
- **Match the logic exactly** - The Rust code should follow the same algorithm, control flow, and edge case handling as OCaml.
- **Use idiomatic Rust** - Translate OCaml patterns to Rust equivalents (e.g., `Option` for `option`, `match` for pattern matching, `Vec` for lists).
- **NO global state** - This is the ONLY architectural difference from OCaml. Pass all state explicitly through function parameters and return values. Use `&mut` references or context structs instead of mutable global refs.

**Reference files to study:**
| OCaml File | Purpose |
|------------|---------|
| `compiler/depends/binary_ast.ml` | Binary AST writing |
| `compiler/ml/parsetree0.ml` | Frozen PPX-compatible AST |
| `compiler/common/ast_mapper_to0.ml` | Current -> parsetree0 mapping |
| `compiler/syntax/src/res_scanner.ml` | Position allocation |
| `compiler/syntax/src/res_parser.ml` | Position assignment |

When you encounter a parity issue:
1. Find the corresponding function in the OCaml code
2. Understand what it does and WHY
3. Ensure the Rust implementation matches that logic exactly
4. Only then make changes

## Priority: Compilation Before Parity

**Get all files to compile first, THEN fix parity.**

Currently only 96/657 files compile with the Rust compiler. The remaining 561 files fail with errors like `UndefinedMethod` (module path resolution) and `NotAVariantType` (variant/constructor resolution). Fixing these compilation failures is strictly higher priority than fixing sexp parity on the 96 files that already compile.

Rationale:
- A file that doesn't compile produces ZERO useful typed tree output
- Many parity issues will resolve themselves once the type checker handles more constructs correctly
- Compilation failures reveal missing type checker features that block large swaths of files

**Do NOT work on sexp parity tasks until Rust compiles all 657 files (or very close to it).**

## Your Task

Read `RALPH_TODO.md` and complete the next unchecked task. After completing a task:
1. Mark it `[x]` complete in `RALPH_TODO.md`
2. Update the status counts at the top
3. Commit your changes with an atomic commit
4. If all tasks are complete, output "RALPH_COMPLETE"

## Critical Rules

1. **ALWAYS read the OCaml implementation first** - Don't guess. Study the OCaml source to understand the correct behavior. The goal is a faithful port, not a reimagining.

2. **DO NOT modify parsetree0/ast0 code (for now)** - The current focus is **position sharing in the parser** - positions that should have the same `PosIdx` are getting different indices during parsing. parsetree0/ast0 has its own issues but that's a separate task. Focus on:
   - `compiler-rust/src/parser/` - Position creation and reuse during parsing
   - `compiler-rust/src/parse_arena.rs` - Arena management for positions
   - `compiler-rust/src/binary_ast/marshal.rs` - Can modify if needed
   - Do NOT touch `parsetree0.rs`, `parsetree0_marshal.rs`, or `mapper_to0.rs` unless absolutely necessary

3. **NO content-based sharing - REMOVE IT IF IT EXISTS** - OCaml's sharing is based on **pointer equality**, not content equality. If you find any content-based caching (like `start_pos_cache` HashMap that deduplicates by position VALUES, or `HashMap<(String, u32)>` that matches by string content), **this is a BUG that must be REMOVED**. The fix requires tracking IDENTITY during parsing - reusing the same index (`PosIdx`, `StrIdx`, `LocIdx`, etc.) when OCaml reuses the same pointer. Content-based caching causes BIDIRECTIONAL differences (sometimes Rust shares more, sometimes less) which is why it's fundamentally wrong. **DO NOT accept content-based caching as "just how it works" - FIX IT.**

   **Example of this anti-pattern (already fixed):** `ObjectField::Otag` used `Located<String>` instead of `Located<StrIdx>`. To share the `{txt; loc}` record between Otag and ArgLabel::Labelled in `%obj` PPX output, a `HashMap<(String, u32), u32>` was used for content-based sharing. The fix was to change Otag to use `StrIdx` (arena reference) and key the sharing table on `(StrIdx, LocIdx)` — proper identity-based sharing. **When you need sharing, use arena indices as keys, not content.**

4. **Run tests frequently** - After each change:
   ```bash
   timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40
   ```

4b. **ALWAYS use timeouts** - Logic errors can cause infinite loops in the compiler. EVERY compiler invocation must be wrapped with `timeout`. Use `timeout 10` for single-file compilations and `timeout 300` for batch test scripts. Never run the compiler without a timeout, especially when iterating over many files. A single infinite loop will block the agent session indefinitely.

5. **Commit after each fix** - Every time tests improve, commit immediately. Include the new parity in the commit message:
   ```bash
   git add <files> && git commit -m "Fix: <description>

   Binary AST parity: X/1049 bsc-ast matches

   Co-Authored-By: Claude <noreply@anthropic.com>"
   ```

   Get the current parity by running:
   ```bash
   ./scripts/test_parser_ast_parity.sh 2>&1 | grep -E "bsc-ast"
   ```

6. **Focus on root causes** - Many failures share the same root cause (usually position sharing). Fix the underlying issue rather than individual symptoms.

7. **Never modify expected files** - The OCaml-generated `.ast` files are the reference. Fix the Rust implementation to match them.

8. **Do NOT defer large tasks** - Task size is not a reason to defer or block. If a task requires touching 30+ files, that's fine—just do the implementation. Break it into smaller commits if needed, but complete the work. The goal is completion, not avoiding complexity.

9. **Do NOT accept bugs as "fundamental limitations"** - If you find incorrect behavior (like content-based position caching when OCaml uses pointer identity), this is a BUG to fix, not a "structural limitation" to document and move on. The goal is exact byte parity with OCaml. Any difference is a bug. Do not rationalize differences as acceptable.

10. **Use explicit `Idx` type names** - Do NOT create aliases like `type Arity = ArityIdx` or similar shortcuts. While it might reduce the number of changes needed, it creates confusion. Always use the explicit indexed type name (e.g., `ArityIdx`, `PosIdx`, `LocIdx`). If you encounter such aliases in the code, replace them with the explicit `Idx` names.

## Key Files

| File | Purpose |
|------|---------|
| `compiler-rust/src/parser/expression.rs` | Expression parsing - where positions are created |
| `compiler-rust/src/parser/state.rs` | Parser state with prev_end_pos tracking |
| `compiler-rust/src/parser/scanner.rs` | Scanner position creation |
| `compiler-rust/src/parse_arena.rs` | Position/location arena management |
| `compiler/syntax/src/res_parser.ml` | OCaml parser (reference) - study position variable reuse |
| `compiler/syntax/src/res_scanner.ml` | OCaml scanner (reference) |

## Debugging Workflow

**IMPORTANT: Always use `timeout` when invoking the compiler. Logic errors can cause infinite loops that block the agent session indefinitely.**

```bash
# Run full parity test (ALWAYS with timeout)
timeout 300 ./scripts/test_parser_ast_parity.sh

# Test a specific file (ALWAYS with timeout)
timeout 10 ./scripts/test_parser_ast_parity.sh tests/syntax_tests/data/printer/expr/record.res

# Compare binary output manually for a simple file
echo 'let f = x => x' > /tmp/test.res
timeout 10 ./packages/@rescript/darwin-arm64/bin/bsc.exe -bs-ast /tmp/test.res -o /tmp/ocaml.ast
timeout 10 ./compiler-rust/target/release/bsc -bs-ast /tmp/test.res -o /tmp/rust.ast
diff <(xxd /tmp/ocaml.ast) <(xxd /tmp/rust.ast)

# Build after changes
cargo build --manifest-path compiler-rust/Cargo.toml --release
```

## Current Status

- **AST structure (sexp-locs)**: 100% parity (1049/1049 files)
- **Binary output (bsc-ast)**: ~121 files with exact byte parity, ~928 with differences

## Known Issues to Fix

1. **Position sharing differences** - Rust creates fewer/more shared references than OCaml
   - OCaml's sharing is based on pointer equality
   - Rust uses arena indices to approximate this
   - Some patterns still produce different sharing behavior

2. **FFI encoding differences** - Files with `external` declarations
   - OCaml's PPX encodes FFI type information as a marshalled blob in `pval_prim`
   - See `compiler/frontend/external_ffi_types.ml` for the encoding

## OCaml Marshal Format Reference

### Sharing Reference Distance
When Marshal encounters a previously-seen object, it writes a shared reference:

| Distance  | Code            | Format                    |
|-----------|-----------------|---------------------------|
| 1-255     | CODE_SHARED8    | 1 byte offset             |
| 256-65535 | CODE_SHARED16   | 2 bytes big-endian offset |
| 65536+    | CODE_SHARED32   | 4 bytes big-endian offset |

### Position Sharing Pattern
The key sharing pattern occurs in the parser's `next()` function:

```
Token 1: "let" at positions 0-3
  Scanner creates: start_pos (id=1), end_pos (id=2)
  Parser assigns: p.start_pos <- id=1, p.end_pos <- id=2

Token 2: "x" at positions 4-5
  Scanner creates: start_pos (id=3), end_pos (id=4)
  Parser assigns:
    prev_end_pos <- p.end_pos (id=2)  <- SHARING: same ID as token 1's end
    p.start_pos <- id=3
    p.end_pos <- id=4
```

## OCaml → Rust Translation Patterns

When porting OCaml code, use these Rust equivalents:

| OCaml | Rust |
|-------|------|
| `option` | `Option<T>` |
| `list` | `Vec<T>` (or `&[T]` for parameters) |
| `ref` | `&mut T` parameter or field in context struct |
| `Hashtbl.t` | `HashMap<K, V>` |
| `match x with` | `match x { }` |
| `let rec` | Regular `fn` (Rust has no `rec` keyword) |
| `fun x -> ...` | `\|x\| ...` or `fn` |
| `Marshal.to_string` | Custom marshal writer |

## Progress Tracking

The current status is tracked in `RALPH_TODO.md`. Update it as you complete tasks.

Goal: Achieve byte-identical binary AST output for all 1049 test files.

## Exit Condition

Only output completion when typedtree parity is fully done:
- `timeout 300 ./scripts/test_typedtree_parity.sh --with-locs` reports `Rust bsc: N passed, 0 failed`
- The same run reports `Parity: N passed, 0 failed` (100% parity)
- No regressions have been introduced

When those conditions are true, output exactly:
```
RALPH_COMPLETE
```

This triggers the Ralph plugin's `--completion-promise` to stop the loop.
