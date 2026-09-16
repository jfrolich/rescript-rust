# ReScript Rust Parser: Performance Optimization Progress

> **Note**: This is a living document. Update it as you complete optimizations, record benchmark results, or discover new opportunities. See [PLAN.md](./PLAN.md) for the full optimization roadmap.

## Critical: Binary AST Parity Must Be Preserved

**Every optimization must pass `./scripts/test_parser_ast_parity.sh` with zero regressions.** Run it before and after every change. See [PLAN.md](./PLAN.md#critical-constraints) for details.

---

## September 2026: CI timing follow-up

The benchmarks in `parser/benchmark.rs` measure subprocess startup, parsing,
built-in PPX, and binary serialization—not parsing alone. Profiling the release
`Css_Legacy_Core` pipeline found 158 of 2,377 sampled stacks inside
`std::env::_var`, including debug-option lookups in position/location writers.

`MarshalWriter` now captures `DEBUG_MARSHAL` and `DEBUG_CONST_SHARE` once per
writer (both constructors), rather than polling the environment for every node.
The flags still control tracing only, including the existing presence-based
behavior for empty and `"0"` values. No process-global cache, identity/sharing
change, normalization, traversal change, or benchmark threshold change is used.
The reference output route remains `compiler/depends/binary_ast.ml:49-66`:
extract dependencies and serialize the AST with `output_value`.

### Local subprocess measurements

macOS arm64, ordinary release build, before source `94e6a4864`, 50 Hyperfine runs
per command with three warmups and no shell. Both Rust binaries and OCaml inherit
the same `RUST_BACKTRACE=1` environment, use the same input path and `-bs-ast`
arguments, and run under the shared heavy-work lock. All observations are kept.
Times below are **mean ± standard deviation [minimum, maximum]**, in milliseconds.

| Fixture | Before | After | Native OCaml |
| --- | --- | --- | --- |
| Arnold | 9.112 ± 0.273 [8.749, 10.172] | 8.357 ± 0.231 [7.957, 9.017] | 10.344 ± 2.427 [8.139, 17.281] |
| Css_Legacy_Core | 11.648 ± 3.381 [10.253, 29.979] | 9.726 ± 0.289 [9.319, 10.492] | 10.614 ± 0.328 [9.972, 11.669] |
| index | 9.445 ± 0.308 [8.971, 10.666] | 8.829 ± 0.249 [8.378, 9.398] | 9.253 ± 0.356 [8.725, 10.197] |

The CSS control outlier inflates its mean reduction; do not interpret that mean
as a reliable 16% gain. These are local subprocess measurements, not a Linux CI
pass or an end-to-end Tella performance claim. An earlier exploratory command
added an `env` executable only to its backtrace case; that comparison is confounded
by the extra exec and is **not evidence of backtrace overhead**.

### Validation and remaining limits

- Release compiler and Rewatch builds pass.
- Compiler tests: 1,358 library tests passed (108 ignored), one CLI test passed,
  16 integration tests passed (23 ignored), nine doctests passed (seven ignored).
- Core parser parity: 1,231/1,231 sexp-with-locations, 1,209 post-PPX checks
  (22 reference skips), 1,196 binary checks (35 reference skips), zero differences
  or parse failures. The warning fixture passes.
- The full parser script still exits 1 on its 12 existing Spice differences.
  All 12 Rust fixture outputs are byte-identical between the retained baseline
  binary and candidate; this change does not fix those differences.
- JavaScript: 344/344 focused fixtures and 610/610 corpus files.
- Diagnostics: 1,431/1,431. Debug-flag subprocess regression passes, including
  unchanged AST bytes with tracing enabled. All three measured fixture ASTs
  also match the retained baseline byte-for-byte.
- Linux CI acceptance remains pending; the 1.20× assertions are unchanged.
  External Tella parity was not repeated (its prior native run was blocked by
  missing Belt and a new run requires a fresh protected-input audit).

Commands, source/binary provenance, samples, all timing observations, and logs:
`/Users/jake/.opensession/artifacts/pr10-parser-timing-20260916T184334Z`.

---

## Overall Progress

| Tier | Description | Status | Progress |
|------|-------------|--------|----------|
| Tier 1 | High Impact: Scanner + Token | 🚧 In Progress | 4/6 |
| Tier 2 | High Impact: AST + Token Layout | 🚧 In Progress | 4/6 |
| Tier 3 | Medium Impact: DOD + Misc | ⏳ Not Started | 0/7 |
| Tier 4 | Architectural | ⏳ Not Started | 0/4 |

---

## Current Performance

**Baseline** (as of February 2026): Rust parser is 2-5x faster on small files, ~parity on large files.

Run benchmarks:
```bash
cargo test --release --lib -- benchmark_all --ignored --nocapture

# Repeated single-thread throughput (in-process, min/median/p95 KLOC/s)
RAYON_NUM_THREADS=1 PARSER_BENCH_WARMUP=2 PARSER_BENCH_RUNS=10 \
cargo test --manifest-path compiler-rust/Cargo.toml --release --lib -- benchmark_cold_repeat --ignored --nocapture
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

- [x] **2.1 Enforce 16-byte enum sizes (OXC pattern)** ✅ COMPLETE
  - Boxed large enum variants across all AST desc enums
  - Size reductions: ExpressionDesc 80→24, PatternDesc 64→24, CoreTypeDesc 64→16, StructureItemDesc 64→16, SignatureItemDesc 56→16, ModuleExprDesc 40→24, ModuleTypeDesc 32→16, Payload 48→16
  - Created PexpFun (80B) and PexpApply (40B) named structs for largest variants
  - Used automated `fix_boxing.py` for bulk rewriting across 26 files
  - Performance: ~neutral (Large 0.77x→0.81x, additional Box allocs offset cache benefits)
  - Foundation for arena allocation (task 2.3) which eliminates Box overhead
  - Zero parity regressions (1193/1196 sexp-locs match; 3 unrelated OCaml ref changes)
  - Files: `ast.rs` + 25 dependent files

- [x] **2.2 Attributes newtype (Option<Box<Vec>>)** ✅ COMPLETE
  - Replaced `type Attributes = Vec<Attribute>` (24 bytes) with newtype `struct Attributes(Option<Box<Vec<Attribute>>>)` (8 bytes)
  - Empty attributes (95%+ of nodes) = `None` — zero heap allocation
  - Full API via Deref, IntoIterator, FromIterator, plus push/extend/concat methods
  - Expression 40→24 bytes (40%), Pattern 40→24 bytes, CoreType 40→24 bytes
  - ValueBinding 112→64 bytes (43%), PexpFun 80→64 bytes, TypeDeclaration 160→128 bytes
  - Performance: neutral (Large 0.80x→0.81x, within noise)
  - Parity: zero regressions
  - AttrsIdx(u32) infrastructure added to ParseArena for future 24→16 byte reduction
  - Files: `ast.rs` + 20 dependent files

- [x] **2.3 Index-based AST (ExprIdx/PatIdx)** ✅ COMPLETE
  - Replaced Box<Expression/Pattern/CoreType/ModuleExpr/ModuleType> with u32 index types
  - Five arena pools in ParseArena: expressions, patterns, core_types, mod_exprs, mod_types
  - All AST desc enum variants use indices for recursive references
  - Fixed 112 borrow checker errors: owned returns, read-only signatures, split push patterns
  - ExpressionDesc 24→16 bytes (target!), PatternDesc 24→16, ModuleExprDesc 24→16
  - PexpFun 64→56, PexpApply 40→32
  - Performance: neutral (Large 0.81x, consistent with previous)
  - Parity: zero regressions
  - Files: `ast.rs`, `parse_arena.rs`, `ppx.rs`, `jsx_ppx.rs` + all parsing/PPX/marshal

- [x] **2.4 Generalized sparse data / side tables** ✅ COMPLETE
  - Beyond attributes: move all Option<T> fields that are None >80% of the time to side tables
  - Completed sparse expression payload coverage:
    - `Pexp_fun.default`
    - `Case.pc_guard`
    - `Pexp_construct` payload arg
    - `Pexp_variant` payload arg
    - `Pexp_record` spread/base expression
    - `Pexp_ifthenelse` else-branch
    - `Pexp_coerce` source type
  - Side-table reads are now threaded through parser/mapper/marshal paths with inline fallback guardrails for parity safety.
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
| Box large enum variants (OXC pattern) | Feb 2026 | Neutral (enum sizes 64-80→16-24 bytes) | 8ab6f5d66 |
| Attributes newtype (Option<Box<Vec>>) | Feb 2026 | Neutral timing; Expression/Pattern/CoreType 40→24 bytes (40%) | 74867e6dc |
| Index-based AST (ExprIdx/PatIdx) | Feb 2026 | Neutral timing; ExpressionDesc/PatternDesc/ModuleExprDesc 24→16 bytes (target!) | dda3dbb46 |

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

### After 2.1 Box large enum variants (February 2026)

```
Run: cargo test --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       14        0       0.81x       0.63x       0.93x
  Medium (10-30KB)              73       73        0       0.55x       0.26x       0.77x
  Small (1-10KB)               443      443        0       0.39x       0.25x       0.71x
  Tiny (<1KB)                  636      636        0       0.30x       0.23x       0.41x

Overall: 1166/1166 passing (1166 faster, 0 within tolerance), 38 skipped
Parity: zero regressions from boxing changes

AST Enum Sizes (before → after):
  ExpressionDesc:     80 → 24 bytes (3.3x reduction)
  PatternDesc:        64 → 24 bytes (2.7x reduction)
  CoreTypeDesc:       64 → 16 bytes (4x reduction, target hit!)
  StructureItemDesc:  64 → 16 bytes (4x reduction, target hit!)
  SignatureItemDesc:  56 → 16 bytes (3.5x reduction, target hit!)
  ModuleExprDesc:     40 → 24 bytes (1.7x reduction)
  ModuleTypeDesc:     32 → 16 bytes (2x reduction, target hit!)
  Payload:            48 → 16 bytes (3x reduction, target hit!)
  Token:              80 bytes (unchanged, addressed in task 2.5)

Notes: Performance is roughly neutral. Large files show a slight regression
(0.77x→0.81x) from additional Box heap allocations for every boxed variant
construction. Smaller files show slight improvement from better cache locality.
The boxing is a structural prerequisite for arena allocation (task 2.3) which
will eliminate the Box overhead while retaining the cache-friendly enum sizes.
5 of 8 AST enums hit the 16-byte target; ExpressionDesc and PatternDesc at
24 bytes due to variants that carry 2 fields (discriminant + Box pointer = 16
bytes, but alignment of inner data pushes to 24). ModuleExprDesc at 24 bytes.
```

### After 2.2 Attributes newtype (February 2026)

```
Run: cargo test --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       14        0       0.81x       0.65x       0.92x
  Medium (10-30KB)              73       73        0       0.54x       0.19x       0.77x
  Small (1-10KB)               443      443        0       0.40x       0.26x       0.83x
  Tiny (<1KB)                  636      636        0       0.31x       0.25x       0.84x

Overall: 1166/1166 passing (1166 faster, 0 within tolerance), 38 skipped
Parity: zero regressions from Attributes newtype

AST Node Sizes (before → after):
  Expression:         40 → 24 bytes (40% reduction)
  Pattern:            40 → 24 bytes (40% reduction)
  CoreType:           40 → 24 bytes (40% reduction)
  ValueBinding:      112 → 64 bytes (43% reduction)
  PexpFun:            80 → 64 bytes (20% reduction)
  TypeDeclaration:   160 → 128 bytes (20% reduction)
  Attributes:         24 → 8 bytes (67% reduction, inline on every node)

Notes: Timing is roughly neutral (within measurement noise). The primary benefit
is reduced memory footprint — 16 fewer bytes per Expression, Pattern, and CoreType
node from eliminating the 24-byte Vec overhead. 95%+ of nodes have empty
attributes, so the Option<Box<...>> = None case (zero allocation) dominates.
AttrsIdx(u32) infrastructure was added to ParseArena for a potential future
reduction from 24 to 16 bytes (8→4 byte field), to be done alongside task 2.3
(index-based AST).
```

### After 2.3 Index-based AST (ExprIdx/PatIdx) (February 2026)

```
Run: cargo test --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       14        0       0.81x       0.67x       0.92x
  Medium (10-30KB)              73       73        0       0.54x       0.22x       0.80x
  Small (1-10KB)               443      443        0       0.38x       0.29x       0.64x
  Tiny (<1KB)                  636      636        0       0.30x       0.18x       0.94x

Overall: 1166/1166 passing (1166 faster, 0 within tolerance), 38 skipped
Parity: zero regressions (pre-existing 3 sexp-locs diffs unchanged)

AST Enum Sizes (before → after):
  ExpressionDesc:     24 → 16 bytes (target hit!)
  PatternDesc:        24 → 16 bytes (target hit!)
  ModuleExprDesc:     24 → 16 bytes (target hit!)
  PexpFun:            64 → 56 bytes (12.5% reduction)
  PexpApply:          40 → 32 bytes (20% reduction)
  All other AST enums: 16 bytes (unchanged, already at target)

Notes: Performance is neutral (Large 0.81x, consistent with previous 0.81x).
The index-based AST replaces 8-byte Box<T> pointers with 4-byte u32 indices,
bringing ExpressionDesc, PatternDesc, and ModuleExprDesc to the 16-byte target.
The primary benefit is structural: AST nodes are now stored in flat Vec pools
enabling future linear traversal and cache-friendly access patterns.
Fixed 112 borrow checker errors across ppx.rs and jsx_ppx.rs by:
(1) changing arena-borrowing functions to return owned data,
(2) converting read-only functions from &mut to & signatures,
(3) splitting nested arena.push_X(fn(..., arena)) into separate let bindings.
```

### Post-2.3 follow-up: arena-index stabilization (February 2026)

```
Scope: Finish uncommitted arena-index migration work in parser/binary_ast modules.
Fixed borrow-checker regressions in ppx/jsx/printer paths and updated binary_ast writer tests
to use ExprIdx/PatIdx fixtures so benchmark test targets compile again.

Benchmark (before, from last 2.3 baseline):
  Large avg factor:  0.81x
  Medium avg factor: 0.54x
  Small avg factor:  0.38x
  Tiny avg factor:   0.30x

Benchmark (after):
Run: cargo test --manifest-path compiler-rust/Cargo.toml --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       13        1       0.81x       0.58x       1.05x
  Medium (10-30KB)              73       73        0       0.53x       0.20x       0.75x
  Small (1-10KB)               443      443        0       0.39x       0.24x       0.95x
  Tiny (<1KB)                  636      635        1       0.32x       0.19x       1.13x

Overall: 1166/1166 passing (1164 faster, 2 within tolerance), 38 skipped

Parity:
  ./scripts/test_parser_ast_parity.sh (baseline unchanged)
  sexp-locs differences:      3
  sexp-locs-ppx differences:  7
  bsc-ast differences:        4 (non-regression)

Result: Performance remains neutral overall versus the previous 2.3 baseline.
```

### Task 2.4 substep: reserve/init APIs + sparse side-table scaffolding (February 2026)

```
Scope:
- Added generic `Arena::reserve_with()` + `Arena::initialize()` for two-phase node construction.
- Added `ParseArena` reserve/initialize APIs for expression/pattern/core_type/module arenas.
- Added sparse side-table scaffolding keyed by owning `ExprIdx`:
  - `expr_fun_defaults: Vec<Option<ExprIdx>>`
  - `expr_case_guards: Vec<Option<Box<[Option<ExprIdx>]>>>`
  - accessor/mutator APIs: `set_fun_default`, `fun_default`, `set_case_guards`, `case_guards`, `case_guard`
- Ensured hot push paths stay direct (`push_*` does not route through reserve/init) to avoid overhead.
- Added unit tests for reserve/init and sparse table behavior.

Benchmark (before):
Run: cargo test --manifest-path compiler-rust/Cargo.toml --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       13        1       0.79x       0.58x       1.02x
  Medium (10-30KB)              73       73        0       0.54x       0.26x       0.77x
  Small (1-10KB)               443      443        0       0.39x       0.28x       0.55x
  Tiny (<1KB)                  636      636        0       0.31x       0.15x       0.44x

Benchmark (after):
Run: cargo test --manifest-path compiler-rust/Cargo.toml --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       14        0       0.79x       0.60x       0.93x
  Medium (10-30KB)              73       73        0       0.54x       0.24x       0.73x
  Small (1-10KB)               443      442        1       0.39x       0.27x       1.05x
  Tiny (<1KB)                  636      636        0       0.31x       0.20x       0.43x

Overall: 1166/1166 passing (1165 faster, 1 within tolerance), 38 skipped

Parity:
  ./scripts/test_parser_ast_parity.sh
  SUCCESS: All 1196 files have full parity

Result:
- Infrastructure complete for the first 2.4 migration phase (two-phase APIs + keyed sparse tables).
- Runtime throughput remains neutral (within benchmark noise).
- No parity regressions.
```

### Task 2.4 substep: thread sparse side-table population/consumption (February 2026)

```
Scope:
- Threaded sparse side-table population through normal expression insertion paths:
  - `ParseArena::push_expr` now seeds `expr_fun_defaults` / `expr_case_guards` from
    `Pexp_fun` and `Pexp_match`/`Pexp_try` payloads.
  - `ParseArena::initialize_expr` now mirrors the same seeding for reserve/init two-phase writes.
- Added sparse-read fallbacks for migration safety:
  - `fun_default` and `case_guard` now fall back to inline AST fields when sparse entries are absent.
  - `get_expr_mut` clears sparse cache entries for the edited slot to avoid stale sparse snapshots.
- Threaded side-table consumption in conversion/serialization paths:
  - `mapper_to0` now reads function defaults/case guards through arena sparse accessors
    keyed by owning `ExprIdx` + case index.
  - Marshal writer now tracks current `ExprIdx` / case-owner context so `Pexp_fun` default
    and `Case.pc_guard` serialization reads sparse entries first (with fallback).
- Added ParseArena unit coverage for seeded sparse entries + fallback behavior after mutation.

Benchmark (before):
Run: cargo test --manifest-path compiler-rust/Cargo.toml --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       14        0       0.80x       0.64x       0.94x
  Medium (10-30KB)              73       73        0       0.53x       0.25x       0.77x
  Small (1-10KB)               443      443        0       0.39x       0.13x       0.60x
  Tiny (<1KB)                  636      636        0       0.31x       0.24x       0.67x

Benchmark (after):
Run: cargo test --manifest-path compiler-rust/Cargo.toml --release --lib -- benchmark_all --ignored --nocapture

  Size Tier                  Files   Faster       OK Avg Factor Min Factor Max Factor
  -------------------------------------------------------------------------------------
  Large (>30KB)                 14       14        0       0.80x       0.60x       0.94x
  Medium (10-30KB)              73       73        0       0.55x       0.24x       0.78x
  Small (1-10KB)               443      443        0       0.39x       0.19x       0.63x
  Tiny (<1KB)                  636      636        0       0.31x       0.26x       0.39x

Overall: 1166/1166 passing (1166 faster, 0 within tolerance), 38 skipped

Parity:
  ./scripts/test_parser_ast_parity.sh --quick
  ./scripts/test_parser_ast_parity.sh
  SUCCESS: All 1196 files have full parity

Result:
- Side-table migration plumbing is now active in parser/mapper/marshal paths for the
  initial sparse targets (`PexpFun.default`, `Case.pc_guard`).
- Throughput is neutral (within benchmark noise); this step is correctness/infrastructure work.
- No parity regressions.
```

### Task 2.4 completion (Generalized sparse data / side tables) — COMPLETE

```
Status: Completed as [x] in RALPH_TODO.md.

Completed sparse expression payload migration:
- `PexpFun.default`
- `Case.pc_guard`
- `Pexp_construct` payload
- `Pexp_variant` payload
- `Pexp_record` spread/base
- `Pexp_ifthenelse` else branch
- `Pexp_coerce` source type

Completed plumbing:
- ParseArena now stores and clears sparse side-table entries for all fields above.
- `mapper_to0` consumes sparse fields (owner-index keyed) with inline fallback.
- current marshal path consumes sparse fields (owner-index keyed) with inline fallback.
- Unit tests cover seeded side-table extraction plus fallback-after-mutation behavior.

Validation:
- `./scripts/test_parser_ast_parity.sh --quick`
  SUCCESS: all 3506 files have full parity.
- Targeted `bsc -bs-ast` byte comparisons for grammar fixtures covering:
  `constructor`, `polyvariant`, `record`, `if`, and `coerce`
  all match between Rust and OCaml.
- In-process benchmark spot check:
  `RAYON_NUM_THREADS=1 PARSER_BENCH_WARMUP=0 PARSER_BENCH_RUNS=1 ... benchmark_cold_repeat`
  completed successfully (no benchmark crashes/regressions in the migrated paths).
```

### Task 4.2 policy (bumpalo) — PROFILING GATED

```
Decision:
- The default allocation path is to continue extending typed arena/index storage, not to
  immediately migrate to bump allocation.
- Rationale: task 2.3 already moved recursive AST nodes into ParseArena Vec pools, which
  removes most per-node Box allocation overhead.
- First finish the remaining high-impact allocation work:
  - 2.4 sparse side tables
  - 2.6 marshal sharing HashMap -> arena-indexed Vec
  - 3.5 SmallVec for tiny per-node collections (where profiling supports it)

Gate to start bumpalo work:
- Re-run flamegraph/perf after the items above.
- Start 4.2 only if allocator/deallocator stacks remain a top bottleneck on representative
  parser workloads (for example >10% wall time or consistently top hotspots).

Expected effect:
- OXC's "~20%" bumpalo number is treated as an upper-bound reference from a different AST
  allocation shape, not an automatic expectation for this parser after 2.3.
```

*Add new entries below as optimizations are applied.*
