# ReScript Rust Parser: Performance Optimization Progress

> **Note**: This is a living document. Update it as you complete optimizations, record benchmark results, or discover new opportunities. See [PLAN.md](./PLAN.md) for the full optimization roadmap.

## Critical: Binary AST Parity Must Be Preserved

**Every optimization must pass `./scripts/test_parser_ast_parity.sh` with zero regressions.** Run it before and after every change. See [PLAN.md](./PLAN.md#critical-constraints) for details.

---

## Overall Progress

| Tier | Description | Status | Progress |
|------|-------------|--------|----------|
| Tier 1 | High Impact: Scanner + Token | 🚧 In Progress | 1/4 |
| Tier 2 | Medium Impact: Token + Misc | ⏳ Not Started | 0/6 |
| Tier 3 | Medium Impact: AST + Advanced | ⏳ Not Started | 0/5 |
| Tier 4 | Architectural | ⏳ Not Started | 0/3 |

---

## Current Performance

**Baseline** (as of February 2026): Rust parser is 2-5x faster on small files, ~parity on large files.

Run benchmarks:
```bash
cargo test --release --lib -- benchmark_all --ignored --nocapture
```

---

## Tier 1 Progress: High Impact, Medium Effort

- [x] **1.0 Precomputed char/byte arrays** (already done)
  - Replaced O(n) `chars().nth(offset)` with precomputed `Vec<char>` + `Vec<usize>` byte_offsets
  - Scanner methods `next()`, `peek()`, `peek2()`, `peek3()` are now O(1)
  - Impact: 41x improvement on JSX benchmark (28ms -> 0.7ms)
  - Commit: 558e262ff

- [ ] **1.1 Byte-level scanning**
  - Operate directly on `&[u8]` instead of `Vec<char>`
  - ASCII fast path (byte < 0x80), UTF-8 slow path on demand
  - Eliminates Vec<char> allocation and char-to-byte indirection
  - Files: `scanner.rs`

- [ ] **1.2 Zero-copy token strings**
  - Change `Token` to `Token<'src>` with `&'src str` for identifiers/strings
  - Only allocate for escaped strings
  - Files: `token.rs`, `scanner.rs`, `state.rs`, `expr.rs`, `pattern.rs`, `typ.rs`, `module.rs`

- [ ] **1.3 String interning (StrIdx)**
  - Extend existing `StrIdx` to cover all identifier strings
  - Deduplicate repeated identifiers across the AST
  - Files: `token.rs`, `ast.rs`, scanner integration

---

## Tier 2 Progress: Medium Impact, Low-Medium Effort

- [ ] **2.1 Token kind/value split (SoA for tokens)**
  - Split `Token` into small `TokenKind` enum + separate value storage
  - 100/117 variants are zero-sized; SoA pattern (Roc: 12% speedup)
  - Files: `token.rs`, `state.rs`, all parsing modules

- [ ] **2.2 Enforce 16-byte enum sizes (OXC pattern)**
  - Box large variants to keep enums at 16 bytes max (OXC: 10% speedup)
  - Current: Token ~40-48 bytes, ExpressionDesc ~80-120 bytes
  - Files: `token.rs`, `ast.rs`

- [ ] **2.3 Strategic `#[inline]` annotations**
  - Profile to identify hot functions
  - Add `#[inline]` to scanner `next()`, `peek()`, `scan()`
  - Add `#[inline]` to parser `expect()`, `advance()`
  - Files: `scanner.rs`, `state.rs`

- [ ] **2.4 Lookup tables for character classification**
  - 256-byte tables for is_ident_start, is_digit, is_whitespace
  - Single array index instead of match/if-chain
  - Files: `scanner.rs`

- [ ] **2.5 Marshal Vec pre-allocation**
  - Pre-allocate `MarshalWriter` buffer based on source file size
  - Heuristic: ~4x source size for binary AST
  - Files: `binary_ast/marshal.rs`, `binary_ast/writer.rs`

- [ ] **2.6 Attributes side table**
  - Move attributes from inline `Vec<Attribute>` to side table
  - Most nodes have empty attributes; saves 24 bytes per node
  - Files: `ast.rs`, all parsing modules, PPX, marshal

---

## Tier 3 Progress: Medium Impact, Higher Effort

- [ ] **3.1 Index-based AST (ExprIdx/PatIdx)**
  - Replace `Box<Expression>` with `ExprIdx(u32)` into flat `Vec<Expression>` pools
  - Extends existing arena pattern (LocIdx, StrIdx, etc.)
  - Evidence: 2.4x speedup (Sampson), used by Sorbet
  - Files: `ast.rs`, `parse_arena.rs`, all parsing modules, PPX, marshal

- [ ] **3.2 SmallVec for AST nodes**
  - Replace `Vec<T>` with `SmallVec<[T; N]>` for small collections
  - Targets: function args (N=3), tuple elements (N=3), record fields (N=4)
  - Files: `ast.rs`, all parsing modules

- [ ] **3.3 SIMD whitespace/comment skipping**
  - Use SSE2/NEON to skip whitespace in 16-byte chunks
  - Significant for heavily indented files
  - Files: `scanner.rs`

- [ ] **3.4 Optimize `is_binary_op` and precedence lookup**
  - Encode precedence in token kind byte
  - Eliminate match dispatch for precedence checks
  - Files: `token.rs`, `expr.rs`

- [ ] **3.5 Optimize breadcrumb management**
  - Fixed-size stack (array + index) instead of Vec<Grammar>
  - Bounded max nesting depth
  - Files: `state.rs`

---

## Tier 4 Progress: Architectural

- [ ] **4.1 Bump-allocated AST (bumpalo)**
  - Use `bumpalo` for all AST node allocation (OXC: 20% speedup)
  - Free entire AST at once when parsing completes
  - Less incremental value if 3.1 (index-based AST) is done first
  - Files: `ast.rs`, all parsing modules, lifetime changes

- [ ] **4.2 Super-flat AST packing**
  - Pack each node into 8 bytes: tag + length + child_index
  - Evidence: 3x memory reduction (jhwlr.io)
  - Files: `ast.rs`, complete AST rewrite

- [ ] **4.3 Profile-Guided Optimization (PGO)**
  - Build instrumented binary, run on representative files, rebuild with profile data
  - Files: build configuration, CI pipeline

---

## Completed Optimizations

| Optimization | Date | Impact | Commit |
|-------------|------|--------|--------|
| Precomputed char/byte arrays | Jan 2026 | 41x on JSX benchmark | 558e262ff |

---

## Measurement Log

Record benchmark results here after each optimization.

### Baseline (February 2026)

```
Run: cargo test --release --lib -- benchmark_all --ignored --nocapture

Results: Rust is 2-5x faster on small files, ~parity on large files.
All 17 benchmarks pass (within 1.2x tolerance).
```

*Add new entries below as optimizations are applied.*
