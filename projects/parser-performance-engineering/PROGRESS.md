# ReScript Rust Parser: Performance Optimization Progress

> **Note**: This is a living document. Update it as you complete optimizations, record benchmark results, or discover new opportunities. See [PLAN.md](./PLAN.md) for the full optimization roadmap.

## Critical: Binary AST Parity Must Be Preserved

**Every optimization must pass `./scripts/test_parser_ast_parity.sh` with zero regressions.** Run it before and after every change. See [PLAN.md](./PLAN.md#critical-constraints) for details.

---

## Overall Progress

| Tier | Description | Status | Progress |
|------|-------------|--------|----------|
| Tier 1 | High Impact: Scanner + Token | 🚧 In Progress | 3/5 |
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

- [x] **1.1 Byte-level scanning**
  - Replaced `Vec<char>` + `Vec<usize>` with direct `&[u8]` byte operations
  - ASCII fast path (byte < 0x80), UTF-8 decode on demand for non-ASCII
  - Scanner struct ~24 bytes smaller, eliminates two heap allocations per parse
  - Key insight: source is Latin-1 encoded (each file byte → one char), so UTF-16 offset tracking must use codepoint-as-byte-pattern classification for parity
  - Impact: Large files 0.87x → 0.83x (~5% faster)
  - All 1196 parity tests pass with zero regressions
  - Files: `scanner.rs`

- [x] **1.2 Zero-copy token strings**
  - Changed `Token` to `Token<'a>` with `Cow<'a, str>` for all string-carrying variants
  - Scanner uses `Cow::Borrowed` for identifiers/numbers (zero-copy), `Cow::Owned` for escape-processed strings
  - DiagnosticCategory/Grammar use `Token<'static>` with `.into_owned()` at boundary
  - Impact: Large files 0.83x→0.80x (~4% faster), Medium 0.57x→0.55x
  - All 1196 parity tests pass with zero regressions
  - Files: `token.rs`, `scanner.rs`, `state.rs`, `diagnostics.rs`, `grammar.rs`, `core.rs`, `parse_arena.rs`, `expr.rs`, `pattern.rs`, `typ.rs`, `module.rs`

- [x] **1.3 String interning (StrIdx)**
  - Extended `Interner` to `Rc<str>` storage with separate `rc_cache` for Rc sharing
  - Added `push_interned()`: unique StrIdx + shared `Rc<str>` data (no heap alloc for dupes)
  - Converted ~68 call sites from `push_string(name.to_string())` to `push_interned_string(&name)`
  - Changed `push_lident`/`push_ldot` from `impl Into<String>` to `&str`
  - Key insight: `rc_cache` must be separate from `intern()` map to preserve marshal parity
  - Impact: Neutral timing (Large 0.82x vs 0.80x baseline, within noise). Memory benefit: shared Rc<str> for duplicate identifiers.
  - Files: `intern.rs`, `parse_arena.rs`, `state.rs`, `expr.rs`, `pattern.rs`, `typ.rs`, `module.rs`, `core.rs`, `jsx_ppx.rs`, `ppx.rs`
  - ⚠️ **NOTE:** Task 1.3 introduced `Rc<str>` in the Interner. This must be removed — see task 1.4.

- [ ] **1.4 Remove Rc<str> from Interner** ⚠️ HIGH PRIORITY
  - Replace `Rc<str>` with arena-friendly storage (e.g. `Vec<Box<str>>` + `HashMap<&str, usize>`)
  - Rc prevents Send+Sync and is slower than direct arena storage
  - Files: `intern.rs`

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
| Byte-level scanning | Feb 2026 | Large files 0.87x→0.83x, eliminates Vec allocs | 21ebc41e7 |
| Zero-copy token strings (Cow) | Feb 2026 | Large files 0.83x→0.80x (~4% faster) | fcab3e407 |
| String interning (Rc<str>) | Feb 2026 | Neutral timing, reduced memory allocs | ae9fa6ad2 |

---

## Measurement Log

Record benchmark results here after each optimization.

### Baseline (February 2026)

```
Run: cargo test --release --lib -- benchmark_all --ignored --nocapture

Results: Rust is 2-5x faster on small files, ~parity on large files.
All 17 benchmarks pass (within 1.2x tolerance).
```

### After 1.1 Byte-level scanning (February 2026)

```
Run: cargo test --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       14        0       0.83x       0.56x       0.98x
  Medium (10-30KB)              73       73        0       0.57x       0.23x       0.84x
  Small (1-10KB)               443      443        0       0.40x       0.23x       0.59x
  Tiny (<1KB)                  636      636        0       0.31x       0.25x       0.61x

Overall: 1166/1166 passing (1166 faster, 0 within tolerance), 38 skipped
Parity: 1196/1196 files pass
```

### After 1.2 Zero-copy token strings (February 2026)

```
Run: cargo test --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       14        0       0.80x       0.54x       0.95x
  Medium (10-30KB)              73       73        0       0.55x       0.22x       0.82x
  Small (1-10KB)               443      443        0       0.39x       0.22x       0.57x
  Tiny (<1KB)                  636      636        0       0.31x       0.25x       0.61x

Overall: 1166/1166 passing (1166 faster, 0 within tolerance), 38 skipped
Parity: 1196/1196 files pass
```

### After 1.3 String interning via Rc<str> (February 2026)

```
Run: cargo test --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       14        0       0.82x       0.59x       0.95x
  Medium (10-30KB)              73       73        0       0.55x       0.22x       0.76x
  Small (1-10KB)               443      443        0       0.39x       0.26x       0.55x
  Tiny (<1KB)                  636      636        0       0.31x       0.12x       0.59x

Overall: 1166/1166 passing (1166 faster, 0 within tolerance), 38 skipped
Parity: 1196/1196 files pass

Notes: Timing impact is neutral (within measurement noise of previous).
Primary benefit is reduced memory allocation — duplicate identifiers share
Rc<str> data via refcount bump instead of separate heap allocations.
```

*Add new entries below as optimizations are applied.*
