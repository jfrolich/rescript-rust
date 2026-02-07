# ReScript Rust Parser: Performance Optimization Progress

> **Note**: This is a living document. Update it as you complete optimizations, record benchmark results, or discover new opportunities. See [PLAN.md](./PLAN.md) for the full optimization roadmap.

## Critical: Binary AST Parity Must Be Preserved

**Every optimization must pass `./scripts/test_parser_ast_parity.sh` with zero regressions.** Run it before and after every change. See [PLAN.md](./PLAN.md#critical-constraints) for details.

---

## Overall Progress

| Tier | Description | Status | Progress |
|------|-------------|--------|----------|
| Tier 1 | High Impact: Scanner + Token | 🚧 In Progress | 4/6 |
| Tier 2 | High Impact: AST + Token Layout | ⏳ Not Started | 0/6 |
| Tier 3 | Medium Impact: DOD + Misc | ⏳ Not Started | 0/7 |
| Tier 4 | Architectural | ⏳ Not Started | 0/4 |

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
  - ⚠️ **NOTE:** Task 1.3 introduced `Rc<str>` in the Interner. Removed in task 1.4.

- [x] **1.4 Remove Rc<str> from Interner**
  - Replaced `Vec<Rc<str>>` → `Vec<Box<str>>`, `HashMap<Rc<str>, StrIdx>` → `HashMap<String, StrIdx>`
  - Removed `rc_cache` HashMap entirely; `push_interned()` now allocates a fresh `Box<str>` each time
  - Removed `use std::rc::Rc` — Interner is now Send+Sync compatible
  - Impact: Performance-neutral (within noise of baseline). Removes Rc overhead.
  - All 1196 parity tests pass with zero regressions
  - Files: `intern.rs`, `parse_arena.rs` (doc comments only)

- [x] **1.5 Zero-copy Constant and Label strings**
  - Changed `Constant::Integer/Float/String`, `Label`, `Ptyp_var`, `Ptyp_alias` to `Cow<'static, str>`
  - Uses `extend_cow_lifetime()` (unsafe transmute) to propagate zero-copy borrows from scanner to AST
  - ~15 hot-path `.clone().into_owned()` heap allocations eliminated
  - Only escape-processed strings (scanner's `Cow::Owned` paths) allocate
  - Impact: Large files 0.80x→0.77x (~4% faster)
  - All 1196 parity tests pass with zero regressions
  - Files: `ast.rs`, `expr.rs`, `typ.rs`, `pattern.rs`, `module.rs`, `sexp.rs`, `sexp_locs.rs`, `jsx_ppx.rs`, `ppx.rs`, `spice_ppx.rs`, `mapper_from0.rs`, `mapper_to0.rs`, `writer.rs`, `typecore.rs`

---

## Tier 2 Progress: High Impact — AST Memory Layout

- [ ] **2.1 Enforce 16-byte enum sizes (OXC pattern)** ⚠️ HIGH PRIORITY
  - Box large variants to keep enums at 16 bytes max (OXC: 10% speedup)
  - Current: ExpressionDesc ~80-120 bytes, but 85%+ of variants need <16 bytes
  - Pexp_fun (~100+ bytes) and Pexp_apply (~60 bytes) dominate; box these
  - Files: `token.rs`, `ast.rs`

- [ ] **2.2 Attributes side table** ⚠️ HIGH PRIORITY
  - Move attributes from inline `Vec<Attribute>` to side table
  - ~95% of nodes have empty attributes; saves 24 bytes per node
  - Combined with 2.1: Expression could shrink from ~150 bytes to ~20-24 bytes
  - Files: `ast.rs`, all parsing modules, PPX, marshal

- [ ] **2.3 Index-based AST (ExprIdx/PatIdx)**
  - Replace `Box<Expression>` with `ExprIdx(u32)` into flat `Vec<Expression>` pools
  - Extends existing arena pattern (LocIdx, StrIdx, etc.)
  - Eliminates per-node heap allocation (currently 5-15 Box allocs per expression)
  - Bottom-up construction → linear forward scan for traversal (prefetcher-friendly)
  - Evidence: 2.4x speedup (Sampson) + 8.2% bonus from linear scan
  - Files: `ast.rs`, `parse_arena.rs`, all parsing modules, PPX, marshal

- [ ] **2.4 Generalized sparse data / side tables**
  - Beyond attributes: move all Option<T> fields that are None >80% of the time to side tables
  - Candidates: Pexp_fun default arg, extension nodes, optional type annotations
  - Each eliminated Option saves 8-24 bytes per node in common case
  - Files: `ast.rs`, all parsing modules, PPX, marshal

- [ ] **2.5 Token kind/value split**
  - Split Token<'a> (~48 bytes) into TokenKind (1-2 bytes) + separate TokenPayload
  - 100/117 variants are zero-sized; 1-byte discriminant = 64 checks/cache line
  - Evidence: Zig compiler 64B→5B tokens, 22% speedup (Kelley)
  - Files: `token.rs`, `state.rs`, all parsing modules

- [ ] **2.6 Marshal sharing tables: HashMap → arena-indexed Vec**
  - 17 HashMaps trigger 8-12 random lookups per AST node — cache miss city
  - Keys are mostly arena indices (PosIdx, LocIdx, StrIdx) — use Vec<Option<u32>> instead
  - O(1) indexed lookup, no hashing, no pointer chasing, pre-sized from arena counts
  - Files: `binary_ast/marshal.rs`

---

## Tier 3 Progress: Medium Impact, Low-Medium Effort

- [ ] **3.1 Hot/cold split of Parser struct**
  - Parser is ~280 bytes (18+ fields, 4-5 cache lines), only ~50 bytes hot
  - Hot: token, positions, scanner. Cold: breadcrumbs, diagnostics, comments, regions
  - Move cold fields to separate ParserColdState — keep hot loop in 1 cache line
  - Files: `state.rs`

- [ ] **3.2 Strategic `#[inline]` annotations**
  - Profile to identify hot functions
  - Add `#[inline]` to scanner `next()`, `peek()`, `scan()`
  - Add `#[inline]` to parser `expect()`, `advance()`
  - Files: `scanner.rs`, `state.rs`

- [ ] **3.3 Lookup tables for character classification**
  - 256-byte tables for is_ident_start, is_digit, is_whitespace
  - Single array index instead of match/if-chain
  - Files: `scanner.rs`

- [ ] **3.4 Marshal Vec pre-allocation**
  - Pre-allocate `MarshalWriter` buffer based on source file size
  - Heuristic: ~4x source size for binary AST
  - Files: `binary_ast/marshal.rs`, `binary_ast/writer.rs`

- [ ] **3.5 SmallVec for AST nodes**
  - Replace `Vec<T>` with `SmallVec<[T; N]>` for small collections
  - Typical lengths: apply args 1-3, tuple 2-4, record fields 2-8
  - Files: `ast.rs`, all parsing modules

- [ ] **3.6 Optimize `is_binary_op` and precedence lookup**
  - Encode precedence in token kind byte
  - Eliminate match dispatch for precedence checks
  - Files: `token.rs`, `expr.rs`

- [ ] **3.7 Optimize breadcrumb management**
  - Fixed-size stack (array + index) instead of Vec<Grammar>
  - Bounded max nesting depth
  - Files: `state.rs`

---

## Tier 4 Progress: Architectural

- [ ] **4.1 SIMD whitespace/comment skipping**
  - Use SSE2/NEON to skip whitespace in 16-byte chunks
  - Significant for heavily indented files
  - Files: `scanner.rs`

- [ ] **4.2 Bump-allocated AST (bumpalo)**
  - Use `bumpalo` for all AST node allocation (OXC: 20% speedup)
  - Free entire AST at once when parsing completes
  - Less incremental value if 2.3 (index-based AST) is done first
  - Files: `ast.rs`, all parsing modules, lifetime changes

- [ ] **4.3 Super-flat AST packing**
  - Pack each node into 8 bytes: tag + length + child_index
  - Evidence: 3x memory reduction (jhwlr.io)
  - Files: `ast.rs`, complete AST rewrite

- [ ] **4.4 Profile-Guided Optimization (PGO)**
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
| Remove Rc<str> from Interner | Feb 2026 | Neutral timing, removes Rc overhead, enables Send+Sync | ce156406f |
| Zero-copy Constant and Label strings | Feb 2026 | Large 0.80x→0.77x (~4% faster) | ae09c8d1f |

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

### After 1.4 Remove Rc<str> from Interner (February 2026)

```
Run: cargo test --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       14        0       0.80x       0.58x       0.95x
  Medium (10-30KB)              73       73        0       0.55x       0.23x       0.77x
  Small (1-10KB)               443      443        0       0.39x       0.24x       0.70x
  Tiny (<1KB)                  636      636        0       0.31x       0.23x       0.44x

Overall: 1166/1166 passing (1166 faster, 0 within tolerance), 38 skipped
Parity: 1196/1196 files pass

Notes: Timing impact is neutral (within measurement noise of previous).
Change removes Rc<str> overhead and enables Send+Sync on the Interner,
unblocking potential future multi-threaded parsing.
```

### After 1.5 Zero-copy Constant and Label strings (February 2026)

```
Run: cargo test --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       13        1       0.77x       0.53x       1.04x
  Medium (10-30KB)              73       73        0       0.54x       0.30x       0.79x
  Small (1-10KB)               443      443        0       0.39x       0.24x       0.65x
  Tiny (<1KB)                  636      636        0       0.31x       0.13x       0.39x

Overall: 1166/1166 passing (1165 faster, 1 within tolerance), 38 skipped
Parity: 1196/1196 files pass

Notes: Measurable improvement on large files (0.80x→0.77x, ~4% faster).
Zero-copy Cow<'static, str> eliminates heap allocations for integer, float,
string constants, labels, type variables, and variant tags. Only escape-processed
strings allocate. Uses unsafe extend_cow_lifetime() transmute (sound because
source string outlives AST in all execution paths).
```

*Add new entries below as optimizations are applied.*
