# Parser Performance Engineering TODO

**Last Updated:** 2026-02-07
**Status:** 1/19 tasks complete

**Baseline:** Rust is 2-5x faster on small files (<10KB), ~0.7-1.0x on large files (20-60KB).
**Goal:** Maximize Rust parser speed across all file sizes while preserving byte-for-byte binary AST parity.

**Parity constraint:** Every change must pass `./scripts/test_parser_ast_parity.sh` with zero regressions.

---

## Tier 1: High Impact, Medium Effort (Scanner + Token)

These target the scanner and token representation where the parser spends most time.

- [x] **1.1 Byte-level scanning** — Replace `Vec<char>` with direct `&[u8]` byte operations. ASCII fast path (byte < 0x80), UTF-8 slow path on demand. Eliminates Vec<char> allocation and improves cache locality. OXC and SWC both use byte-level scanning. Files: `scanner.rs`. Scanner struct ~24 bytes smaller, eliminates Vec<char>/Vec<usize> heap allocations. Large files improved from 0.87x to 0.83x. All 1196 parity tests pass.

- [ ] **1.2 Zero-copy token strings** — Change `Token` to `Token<'src>` with `&'src str` slices borrowing from source for identifiers and string literals. Only allocate for escaped/interpolated strings. Requires lifetime parameter propagation through Token, Scanner, Parser. Files: `token.rs`, `scanner.rs`, `state.rs`, all parsing modules. Measure token allocation count before/after.

- [ ] **1.3 String interning via StrIdx** — Extend existing `StrIdx` arena to cover all identifier strings during parsing. Deduplicate repeated identifiers (e.g., common names like `t`, `x`, `unit`). Comparison becomes index equality instead of string comparison. Files: `token.rs`, `ast.rs`, scanner integration.

---

## Tier 2: Medium Impact, Low-Medium Effort

- [ ] **2.1 Token kind/value split (SoA for tokens)** — Split `Token` enum (~117 variants, ~40-48 bytes) into small `TokenKind` enum (1-2 bytes, no data) + separate `TokenValue` storage accessed only when needed. 100 of 117 variants are zero-sized (keywords, punctuation); only 17 carry payloads (Lident, Uident, String, Int, Float, etc.). Token kind is checked constantly during parsing (178+ clones in expr.rs alone); smaller enum = better cache + branch prediction. This is the SoA (struct-of-arrays) pattern applied to tokens. Evidence: Roc compiler saw 12% speedup from SoA transformation. Files: `token.rs`, `state.rs`, all parsing modules.

- [ ] **2.2 Enforce 16-byte enum sizes (OXC pattern)** — Measure current `std::mem::size_of::<Token>()` and all AST desc enums. Box large variants to keep enums at 16 bytes max. OXC enforces this with tests (`assert_eq!(size_of::<Expression>(), 16)`) and measured a 10% speedup from improved cache behavior. Current estimates: Token ~40-48 bytes, ExpressionDesc ~80-120 bytes, PatternDesc ~60-100 bytes, CoreTypeDesc ~80-120 bytes. Files: `token.rs`, `ast.rs`.

- [ ] **2.3 Strategic `#[inline]` annotations** — Profile to identify hot functions. Add `#[inline]` or `#[inline(always)]` on scanner `next()`, `peek()`, `scan_token()` and parser `expect()`, `advance()`, `next()`. Benchmark each annotation individually — `#[inline(always)]` can hurt if it bloats the caller. Files: `scanner.rs`, `state.rs`.

- [ ] **2.4 Lookup tables for character classification** — Replace match/if-chain character classification with 256-byte ASCII lookup tables. One array index instead of branching for `is_ident_start`, `is_ident_part`, `is_digit`, `is_whitespace`, etc. Files: `scanner.rs`.

- [ ] **2.5 Marshal Vec pre-allocation** — Pre-allocate `MarshalWriter` buffer based on source file size heuristic (e.g., 4x source bytes). Avoids repeated reallocation during serialization. Currently starts at 4KB. Files: `binary_ast/marshal.rs`, `binary_ast/writer.rs`.

- [ ] **2.6 Attributes side table** — Most AST nodes have empty `Vec<Attribute>`. Move attributes to a side table (`HashMap<NodeId, Vec<Attribute>>` or `Vec<Option<Vec<Attribute>>>`) instead of storing inline on every node. Reduces the size of every Expression, Pattern, and CoreType by ~24 bytes (Vec overhead). ECS-inspired optimization. Files: `ast.rs`, all parsing modules, PPX, marshal.

---

## Tier 3: Medium Impact, Higher Effort

- [ ] **3.1 Index-based AST (ExprIdx/PatIdx into ParseArena)** — Replace `Box<Expression>` with `ExprIdx(u32)` indices into flat `Vec<Expression>` pools in `ParseArena`. Similarly for Pattern, CoreType, etc. This extends the existing arena pattern (`LocIdx`, `StrIdx`, `LidentIdx`, `ArityIdx`) to all AST nodes. Eliminates all heap allocation for AST nodes, makes the entire AST a flat array with excellent cache locality. 32-bit indices are half the size of 64-bit pointers. Evidence: Adrian Sampson measured 2.4x speedup (38% of original time was `free()` alone; even excluding deallocation, 1.5x faster from cache locality). Sorbet uses this exact pattern (`NameRef`, `SymbolRef` as u32 indices). Files: `ast.rs`, `parse_arena.rs`, all parsing modules, PPX, marshal.

- [ ] **3.2 SmallVec for AST nodes** — Replace `Vec<T>` with `SmallVec<[T; N]>` for common small collections. Targets: function args (N=3), tuple elements (N=3), record fields (N=4), type params (N=2). Avoids heap allocation for typical cases. Add `smallvec` dependency. Files: `ast.rs`, all parsing modules.

- [ ] **3.3 SIMD whitespace/comment skipping** — Use SIMD (SSE2 on x86, NEON on ARM) to skip runs of whitespace in 16-byte chunks. Significant for heavily indented files. OXC uses this technique. Requires platform-specific code with fallback. Files: `scanner.rs`.

- [ ] **3.4 Optimize binary op precedence lookup** — Encode operator precedence directly in token kind (e.g., as a byte alongside the discriminant) instead of a match dispatch. The `is_binary_op` / `get_precedence` path is hit on every expression. Files: `token.rs`, `expr.rs`.

- [ ] **3.5 Optimize breadcrumb management** — Replace `Vec<(Grammar, Position)>` breadcrumb stack with a fixed-size array + index. Maximum nesting depth is bounded. Avoids Vec allocation, bounds checks, and potential reallocation. Files: `state.rs`.

---

## Tier 4: Architectural (Longer Term)

- [ ] **4.1 Bump-allocated AST (bumpalo)** — Use `bumpalo` bump allocator for all AST node allocation. The entire AST is freed at once when parsing completes, eliminating individual Box/Vec deallocation overhead. OXC measured ~20% speedup from this. Can be combined with or used instead of 3.1 (index-based AST). All `Box<T>` → `&'arena T`, all `Vec<T>` → `BVec<'arena, T>`. Files: `ast.rs`, all parsing modules, lifetime changes throughout. Note: If 3.1 (index-based AST) is done first, bumpalo may have less incremental value since most allocations are already eliminated.

- [ ] **4.2 Super-flat AST packing** — Pack each AST node into 8 bytes: `tag: u8` + `length: u24` + `first_child_index: u32`. Leaf nodes use 7 remaining bytes for inline data (e.g., StrIdx). Fixed-arity nodes use 3 bytes for inline data. Dynamic-arity nodes use length for child count. Evidence: ~3x memory reduction vs traditional tree. Bonus: bottom-up construction order means children always precede parents in the array, enabling linear left-to-right processing instead of recursive traversal (8% additional speedup). Files: `ast.rs`, complete rewrite of AST representation.

- [ ] **4.3 Profile-Guided Optimization (PGO)** — Build instrumented binary, run on representative ReScript files (idempotency tests), rebuild with profile data. Optimizes branch layouts, function placement, and inlining based on actual runtime profiles. Requires build script changes. Files: build configuration, Cargo.toml, CI pipeline.

---

## Commands Reference

```bash
# Build release binary
cargo build --manifest-path compiler-rust/Cargo.toml --release

# Run parity tests (MUST pass before and after every change)
./scripts/test_parser_ast_parity.sh 2>&1 | tail -20

# Quick parity (stop on first failure)
./scripts/test_parser_ast_parity.sh --quick

# Single benchmark (50 iterations)
cargo test --release --lib -- benchmark_regex --nocapture

# All benchmarks (700+ files, ~3 min)
cargo test --release --lib -- benchmark_all --ignored --nocapture

# Measure struct sizes (add to any test temporarily)
# println!("Token: {} bytes", std::mem::size_of::<Token>());
# println!("Expression: {} bytes", std::mem::size_of::<Expression>());
# println!("ExpressionDesc: {} bytes", std::mem::size_of::<ExpressionDesc>());
# println!("Scanner: {} bytes", std::mem::size_of::<Scanner>());
```

---

## Research References

Evidence for key optimizations:

| Approach | Source | Measured Impact |
|----------|--------|-----------------|
| Arena allocation (bumpalo) | OXC parser | ~20% speedup |
| Enum size enforcement (16 bytes) | OXC parser | ~10% speedup |
| Span compression (u32 offsets) | OXC parser | ~5% speedup |
| SoA / data-oriented design | Roc compiler (Tweede golf blog) | 12% speedup, 12% less memory |
| Index-based flat AST | Adrian Sampson (Cornell) | 2.4x speedup (38% was free() alone) |
| Super-flat 8-byte nodes | jhwlr.io | ~3x memory reduction |
| String interning | Sorbet (Stripe) | Integer comparison vs string comparison |
| Precomputed char/byte arrays | Already done (commit 558e262ff) | 41x on JSX benchmark |

Key resources:
- OXC performance: https://oxc.rs/docs/learn/performance
- Flattening ASTs: https://www.cs.cornell.edu/~asampson/blog/flattening.html
- Roc SoA: https://tweedegolf.nl/en/blog/88/data-oriented-design
- Why Sorbet is fast: https://blog.nelhage.com/post/why-sorbet-is-fast/
- Super-flat AST: https://jhwlr.io/super-flat-ast/

---

## Notes

- The scanner currently precomputes `Vec<char>` and `Vec<usize>` (byte offsets) upfront — this was the first optimization (41x improvement on JSX benchmark). Task 1.1 replaces this with direct byte-level scanning.
- Token enum has ~117 variants but only 17 carry payloads. The enum is ~40-48 bytes. Tasks 1.2, 2.1, 2.2 address this.
- The parser already uses arena indices (`PosIdx`, `LocIdx`, `StrIdx`, `LidentIdx`, `ArityIdx`) for position/location/string sharing. Task 3.1 extends this pattern to all AST nodes (ExprIdx, PatIdx, CoreTypeIdx).
- ExpressionDesc has 30 variants, PatternDesc 17, CoreTypeDesc 11. The largest variants (Pexp_fun with 6 fields, Pexp_apply with Vec) dominate the enum size. Boxing these per 2.2 is the quick win; 3.1/4.2 are the deeper refactors.
- MarshalWriter uses ~15 HashMap-based sharing tables. These are correctness-critical for binary parity. Don't optimize them unless profiling shows they're a bottleneck.
- Lookahead parsing (`lookahead_depth > 0`) skips arena allocations to avoid polluting position indices. Any scanner/parser changes must preserve this behavior.
- The marshal/PPX code does extensive pattern matching on AST desc enums (87+ matches for ExpressionDesc alone). Index-based AST (3.1) changes access patterns from `match expr.pexp_desc` to `match arena.get_expr(expr_idx).pexp_desc` — more verbose but not fundamentally different.
