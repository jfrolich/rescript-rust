# Parser Performance Engineering TODO

**Last Updated:** 2026-02-07
**Status:** 0/14 tasks complete

**Baseline:** Rust is 2-5x faster on small files (<10KB), ~0.7-1.0x on large files (20-60KB).
**Goal:** Maximize Rust parser speed across all file sizes while preserving byte-for-byte binary AST parity.

**Parity constraint:** Every change must pass `./scripts/test_parser_ast_parity.sh` with zero regressions.

---

## Tier 1: High Impact, Medium Effort (Scanner + Token)

These target the scanner and token representation where the parser spends most time.

- [ ] **1.1 Byte-level scanning** — Replace `Vec<char>` with direct `&[u8]` byte operations. ASCII fast path (byte < 0x80), UTF-8 slow path on demand. Eliminates Vec<char> allocation and improves cache locality. Study how OXC does this. Files: `scanner.rs`. Measure `size_of::<Scanner>()` before/after. Run parity + benchmarks.

- [ ] **1.2 Zero-copy token strings** — Change `Token` to `Token<'src>` with `&'src str` slices borrowing from source for identifiers and string literals. Only allocate for escaped/interpolated strings. Requires lifetime parameter propagation through Token, Scanner, Parser. Files: `token.rs`, `scanner.rs`, `state.rs`, all parsing modules. Measure token allocation count before/after.

- [ ] **1.3 String interning via StrIdx** — Extend existing `StrIdx` arena to cover all identifier strings during parsing. Deduplicate repeated identifiers (e.g., common names like `t`, `x`, `unit`). Comparison becomes index equality instead of string comparison. Files: `token.rs`, `ast.rs`, scanner integration.

---

## Tier 2: Medium Impact, Low-Medium Effort

- [ ] **2.1 Token kind/value split** — Split `Token` enum into small `TokenKind` (1-2 bytes, no data) and separate `TokenValue` storage accessed only when needed. Token kind is checked constantly during parsing; smaller enum = better cache + branch prediction. Measure `size_of::<Token>()` before (likely 40+ bytes) and after (target 8-16 bytes). Files: `token.rs`, `state.rs`, all parsing modules.

- [ ] **2.2 Reduce token enum size** — Measure current `std::mem::size_of::<Token>()`. Store embedded data (strings, numbers) out-of-band to minimize the enum size. Target 8-16 bytes. Can be done with or independently of 2.1. Files: `token.rs`.

- [ ] **2.3 Strategic `#[inline]` annotations** — Profile to identify hot functions. Add `#[inline]` or `#[inline(always)]` on scanner `next()`, `peek()`, `scan_token()` and parser `expect()`, `advance()`, `next()`. Benchmark each annotation individually — `#[inline(always)]` can hurt if it bloats the caller. Files: `scanner.rs`, `state.rs`.

- [ ] **2.4 Lookup tables for character classification** — Replace match/if-chain character classification with 256-byte ASCII lookup tables. One array index instead of branching for `is_ident_start`, `is_ident_part`, `is_digit`, `is_whitespace`, etc. Files: `scanner.rs`.

- [ ] **2.5 Marshal Vec pre-allocation** — Pre-allocate `MarshalWriter` buffer based on source file size heuristic (e.g., 4x source bytes). Avoids repeated reallocation during serialization. Currently starts at 4KB. Files: `binary_ast/marshal.rs`, `binary_ast/writer.rs`.

---

## Tier 3: Medium Impact, Higher Effort

- [ ] **3.1 SmallVec for AST nodes** — Replace `Vec<T>` with `SmallVec<[T; N]>` for common small collections. Targets: function args (N=3), tuple elements (N=3), record fields (N=4), type params (N=2). Avoids heap allocation for typical cases. Add `smallvec` dependency. Files: `ast.rs`, all parsing modules.

- [ ] **3.2 SIMD whitespace/comment skipping** — Use SIMD (SSE2 on x86, NEON on ARM) to skip runs of whitespace in 16-byte chunks. Significant for heavily indented files. OXC uses this technique. Requires platform-specific code with fallback. Files: `scanner.rs`.

- [ ] **3.3 Optimize binary op precedence lookup** — Encode operator precedence directly in token kind (e.g., as a byte alongside the discriminant) instead of a match dispatch. The `is_binary_op` / `get_precedence` path is hit on every expression. Files: `token.rs`, `expr.rs`.

- [ ] **3.4 Optimize breadcrumb management** — Replace `Vec<(Grammar, Position)>` breadcrumb stack with a fixed-size array + index. Maximum nesting depth is bounded. Avoids Vec allocation, bounds checks, and potential reallocation. Files: `state.rs`.

---

## Tier 4: Architectural (Longer Term)

- [ ] **4.1 Arena-allocated AST** — Use `bumpalo` bump allocator for all AST node allocation. The entire AST is freed at once when parsing completes, eliminating individual Box/Vec deallocation overhead. This is how OXC achieves best-in-class performance. Significant refactor: all `Box<T>` → `&'arena T`, all `Vec<T>` → `BVec<'arena, T>`. Files: `ast.rs`, all parsing modules, lifetime changes throughout.

- [ ] **4.2 Profile-Guided Optimization (PGO)** — Build instrumented binary, run on representative ReScript files (idempotency tests), rebuild with profile data. Optimizes branch layouts, function placement, and inlining based on actual runtime profiles. Requires build script changes. Files: build configuration, Cargo.toml, CI pipeline.

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
# println!("Scanner: {} bytes", std::mem::size_of::<Scanner>());
```

---

## Notes

- The scanner currently precomputes `Vec<char>` and `Vec<usize>` (byte offsets) upfront — this was the first optimization (41x improvement on JSX benchmark). Tasks 1.1 replaces this with direct byte-level scanning.
- Token enum carries `String` data for identifiers/literals, making it large (~40+ bytes). Tasks 1.2, 2.1, 2.2 address this.
- The parser already uses arena indices (`PosIdx`, `LocIdx`, `StrIdx`) for position/location sharing. Task 1.3 extends this to all identifiers.
- MarshalWriter uses ~15 HashMap-based sharing tables. These are correctness-critical for binary parity. Don't optimize them unless profiling shows they're a bottleneck.
- Lookahead parsing (`lookahead_depth > 0`) skips arena allocations to avoid polluting position indices. Any scanner/parser changes must preserve this behavior.
