# ReScript Rust Parser: Performance Optimization Plan

## Executive Summary

Goal: Make the ReScript Rust parser the fastest possible implementation. The parser already achieves 2-5x faster performance than the OCaml parser on small files and rough parity on large files. This plan outlines a systematic optimization strategy to achieve best-in-class parsing performance across all file sizes.

---

## September 2026: CI timing follow-up

- [x] Profile the full `bsc -bs-ast` path used by the three failing CI benchmarks.
- [x] Capture debug flags per `MarshalWriter`, removing per-node environment queries without changing serialization or benchmark assertions.
- [x] Verify release tests, core AST byte parity, JavaScript output, diagnostic output, and before/after debug-trace behavior. See [PROGRESS.md](./PROGRESS.md#september-2026-ci-timing-follow-up) for measurements and limitations.
- [ ] Confirm the unchanged 1.20× limit on Linux CI. Local measurements are not Linux acceptance; external Tella validation was not repeated.

## Motivation

The Rust parser is a fully functional drop-in replacement for the OCaml parser, producing byte-for-byte identical binary AST output for all 1,312 test files. With correctness established, the focus shifts to performance:

1. **Already fast on small files**: 2-5x faster than OCaml on grammar-level tests (< 10KB)
2. **Parity on large files**: ~1.0x on real-world files (20-60KB), within the 1.2x tolerance
3. **Opportunity**: Modern Rust parsing techniques (OXC, SWC, tree-sitter) demonstrate that significantly faster parsing is achievable
4. **Build system impact**: The parser runs on every source file during compilation; even small improvements compound across large projects

---

## Critical Constraints

**Every optimization MUST preserve byte-for-byte binary AST parity with the OCaml parser.** This is non-negotiable.

The binary AST (`bsc -bs-ast` output) includes dependency extraction, source path, and OCaml Marshal-encoded parsetree. The Rust output must be identical to the OCaml output byte-for-byte. This is verified by:

```bash
# Full parity test suite (1300+ files, parallel, with regression tracking)
./scripts/test_parser_ast_parity.sh

# Quick iteration on a single file
./scripts/test_parser_ast_parity.sh tests/syntax_tests/data/printer/expr/apply.res

# Stop on first failure
./scripts/test_parser_ast_parity.sh --quick
```

The test suite checks:
1. **sexp-locs parity** — AST structure + locations + attributes match (readable diffs)
2. **sexp-locs-ppx parity** — Post-PPX AST structure + locations match
3. **bsc-ast parity** — Full `bsc -bs-ast` binary output is byte-identical
4. **spice-ppx parity** — OCaml bsc with external spice PPX vs Rust internal PPX

Baselines are maintained in `tests/parity_baselines/`. The suite is append-only: once a file passes, it must never regress.

**Before and after every optimization**: run `./scripts/test_parser_ast_parity.sh` and verify zero regressions.

---

## Current Architecture

### Pipeline

```
Source Code (UTF-8 &str)
       |
   [Scanner]  scanner.rs (~53KB)
   - Precomputes chars: Vec<char> and byte_offsets: Vec<usize> in O(n)
   - O(1) character access: next(), peek(), peek2(), peek3()
   - Tracks: char offset, UTF-16 column, line number, byte offset
   - Output: ScanResult { start_pos, end_pos, Token }
       |
   [Parser]  state.rs (~40KB) + expr.rs (~252KB) + pattern.rs + typ.rs + module.rs
   - Recursive descent with breadcrumb-based error recovery
   - Lookahead via snapshot save/restore
   - Arena-indexed locations (LocIdx) and arities (ArityIdx)
       |
   [AST]  ast.rs (~29KB)
   - Expression, Pattern, CoreType, Structure, Signature
   - All nodes carry LocIdx for location tracking
       |
   [PPX Transform]  jsx_ppx.rs (~136KB)
   - JSX desugaring to function calls
   - Attribute-based transformations
       |
   [Dependency Extraction]  deps.rs
   - Walk AST for module references
   - Sorted BTreeSet output
       |
   [Marshal / Binary AST]  binary_ast/ (~8 files)
   - Parsetree -> Parsetree0 (frozen PPX-compatible format)
   - OCaml Marshal format writer with identity-based sharing
   - Output: .ast / .iast files
```

### Key Data Structures

| Structure | File | Description |
|-----------|------|-------------|
| `Scanner<'src>` | scanner.rs | Holds source, precomputed chars/byte_offsets, position state |
| `Token` | token.rs | 102-variant enum: keywords, operators, literals, identifiers |
| `Parser<'src>` | state.rs | Current token, positions, breadcrumbs, diagnostics, arena |
| `Expression` / `ExpressionDesc` | ast.rs | AST expression nodes |
| `CoreType` / `CoreTypeDesc` | ast.rs | AST type nodes |
| `Pattern` / `PatternDesc` | ast.rs | AST pattern nodes |
| `LocIdx` / `ArityIdx` | ast.rs | Arena-indexed locations and arities |
| `MarshalWriter` | marshal.rs | Binary serialization with object sharing |

---

## Current Performance Baseline

Benchmarks run via `cargo test --release --lib -- benchmark_all --ignored --nocapture`.

Both compilers run as subprocesses: `bsc -bs-ast -o <tmpfile> <input.res>`. Minimum time over 50 iterations (2 warmup).

### Grammar Expression Tests (Small Files)

| Test | Size | Rust | OCaml | Factor | Status |
|------|------|------|-------|--------|--------|
| grammar/regex | ~2KB | ~4ms | ~10ms | ~0.4x | FASTER |
| grammar/arrow | ~3KB | ~4ms | ~10ms | ~0.4x | FASTER |
| grammar/if | ~2KB | ~4ms | ~10ms | ~0.4x | FASTER |
| grammar/UncurriedByDefault | ~8KB | ~5ms | ~10ms | ~0.5x | FASTER |
| grammar/block | ~3KB | ~4ms | ~10ms | ~0.4x | FASTER |
| grammar/constants | ~3KB | ~4ms | ~10ms | ~0.4x | FASTER |
| grammar/record | ~5KB | ~4ms | ~10ms | ~0.4x | FASTER |
| grammar/binary | ~4KB | ~4ms | ~10ms | ~0.4x | FASTER |
| grammar/array | ~2KB | ~4ms | ~10ms | ~0.4x | FASTER |
| grammar/switch | ~3KB | ~4ms | ~10ms | ~0.4x | FASTER |
| grammar/async | ~2KB | ~4ms | ~10ms | ~0.4x | FASTER |
| grammar/firstClassModule | ~3KB | ~4ms | ~10ms | ~0.4x | FASTER |

### Real-World Idempotency Tests (Large Files)

| Test | Size | Rust | OCaml | Factor | Status |
|------|------|------|-------|--------|--------|
| idempotency/ReactDOMRe | ~20KB | ~7ms | ~10ms | ~0.7x | FASTER |
| idempotency/Css_Legacy_Core | ~45KB | ~10ms | ~12ms | ~0.8x | FASTER |
| idempotency/Arnold | ~35KB | ~9ms | ~11ms | ~0.8x | FASTER |
| idempotency/index | ~25KB | ~8ms | ~10ms | ~0.8x | FASTER |
| idempotency/EmitJs | ~60KB | ~12ms | ~12ms | ~1.0x | OK |

*Note: Exact numbers vary by machine. Run benchmarks locally for accurate results.*

---

## Optimization Strategy

### Tier 1: High Impact, Medium Effort

These target the scanner and token representation, where the parser spends most of its time.

#### 1.1 Byte-Level Scanning

**Current**: Scanner precomputes `Vec<char>` from UTF-8 source, then indexes into chars.

**Proposed**: Operate directly on `&[u8]` bytes. Most ReScript source is ASCII; handle multi-byte sequences only when encountered.

**Expected impact**: Eliminate Vec<char> allocation and improve cache locality. OXC and SWC both use byte-level scanning.

**Approach**:
```
- Replace chars: Vec<char> with src_bytes: &[u8]
- next()/peek() operate on bytes
- ASCII fast path: byte < 0x80
- Multi-byte slow path: decode UTF-8 on demand
- Track byte offset directly (no char-to-byte mapping needed)
```

#### 1.2 Zero-Copy Token Strings

**Current**: Token variants like `Lident(String)`, `String(String)` allocate owned strings.

**Proposed**: Use `&'src str` slices borrowing from the source, avoiding allocation for identifiers and string literals.

**Expected impact**: Reduce allocator pressure significantly (identifiers are the most common token). Requires lifetime parameter on Token.

**Approach**:
```
- Token<'src> with &'src str for identifiers, strings
- Only allocate for escaped strings (rare)
- Consider SmolStr or StrIdx for cases where ownership is needed
```

#### 1.3 String Interning (StrIdx)

**Current**: Identifiers are stored as `String` in tokens and AST nodes.

**Proposed**: Intern all identifier strings into a `StringInterner` (already partially present as `StrIdx`), deduplicating repeated identifiers.

**Expected impact**: Reduce memory usage and improve comparison speed (pointer equality instead of string comparison).

#### 1.5 Zero-Copy Constant and Label Strings

**Current**: Task 1.2 introduced `Cow<'a, str>` in tokens, but the AST's `Constant` type still uses owned `String`:
```rust
enum Constant {
    Integer(String, Option<char>),
    Float(String, Option<char>),
    String(String, Option<String>),
    // ...
}
type Label = String;
```

Every integer, float, and string literal calls `.clone().into_owned()` to convert the borrowed `Cow` into an owned `String` — ~15 call sites in the hot parsing path. Since strings are never modified after parsing, this allocation is unnecessary.

**Proposed**: Change `Constant` and `Label` to carry `Cow<'a, str>` (or `&'a str`), propagating the source lifetime into the AST. Only escape-processed strings (the scanner's 5 `Cow::Owned` paths: escape sequences in string literals and exotic identifiers) would allocate. The 99% common case stays zero-copy from source bytes all the way into the AST.

**Expected impact**: Eliminates one heap allocation per literal in the hot path. Most significant for files with many string/number literals.

### Tier 2: High Impact — AST Memory Layout

Analysis shows that the biggest performance wins are in AST node representation, not token handling. The parser processes one token at a time (no token array), so token SoA doesn't apply. But AST nodes are allocated on the heap, stored in large enums with massive padding waste, and carry empty attribute vectors. Fixing these is where the Roc/OXC/Sampson research results actually apply.

#### 2.1 Enforce 16-byte Enum Sizes (OXC Pattern)

**Current**: AST desc enums are large (ExpressionDesc ~80-120 bytes, Token ~40-48 bytes) because the enum size equals the size of the largest variant. But 85%+ of ExpressionDesc variants need <16 bytes — `Pexp_ident`, `Pexp_constant`, etc. are tiny. The enum is dominated by `Pexp_fun` (~100+ bytes, 6 fields) and `Pexp_apply` (~60 bytes, Vec).

**Proposed**: Box large variants to keep all enums at 16 bytes max. OXC enforces this with compile-time tests and measured a **10% speedup** from improved cache behavior.

**Approach**:
```rust
// Before: large enum (~120 bytes)
enum ExpressionDesc {
    Pexp_fun(ArgLabel, Option<Expression>, Pattern, Box<Expression>, ArityIdx, bool),
    Pexp_ident(Located<LongidentIdx>),
    // ...
}

// After: 16-byte enum (large variants boxed)
enum ExpressionDesc {
    Pexp_fun(Box<FunExpr>),  // Large variant boxed
    Pexp_ident(Located<LongidentIdx>),  // Small variant stays inline
    // ...
}
```

#### 2.2 Attributes Side Table

**Current**: Every AST node stores `Vec<Attribute>` inline, adding 24 bytes even when empty (~95% of nodes have no attributes).

**Proposed**: Move attributes to a separate side table indexed by node ID. Only nodes with attributes have entries. Reduces the size of every Expression, Pattern, and CoreType node by 24 bytes.

**Combined with 2.1**: These two together could shrink Expression from ~150 bytes to ~20-24 bytes.

#### 2.3 Index-Based AST (ExprIdx/PatIdx)

**Current**: AST nodes use `Box<Expression>`, `Vec<Expression>` etc. for tree structure. Each node is a separate heap allocation.

**Proposed**: Store all AST nodes in flat `Vec<Expression>` pools in `ParseArena`, referenced by `ExprIdx(u32)` indices. This extends the existing arena pattern (`LocIdx`, `StrIdx`, `LidentIdx`, `ArityIdx`) to all AST nodes. Eliminates per-node heap allocation.

**Expected impact**: Adrian Sampson (Cornell) measured a **2.4x speedup** from this transformation. 38% of the original time was spent on `free()` alone; even excluding deallocation, the flat version was 1.5x faster from cache locality. Sorbet (Stripe's Ruby type checker) uses this exact pattern.

**Approach**:
```rust
// Before: pointer-based
struct Expression {
    pexp_desc: ExpressionDesc,
    pexp_loc: LocIdx,
    pexp_attributes: Vec<Attribute>,
}
enum ExpressionDesc {
    Pexp_apply { funct: Box<Expression>, args: Vec<(ArgLabel, Expression)>, ... },
    // ...
}

// After: index-based
pub struct ExprIdx(pub u32);
pub struct PatIdx(pub u32);
pub struct CoreTypeIdx(pub u32);

// In ParseArena:
expressions: Vec<Expression>,
patterns: Vec<Pattern>,
core_types: Vec<CoreType>,

enum ExpressionDesc {
    Pexp_apply { funct: ExprIdx, args: Vec<(ArgLabel, ExprIdx)>, ... },
    // ...
}
```

#### 2.4 Generalized Sparse Data / Side Tables

**Current**: Various AST fields carry `Option<T>` data that is None >80% of the time. Each unused Option still takes 8-24 bytes per node.

**Proposed**: Move rarely-used optional fields to side tables keyed by node index. Candidates: `Pexp_fun`'s default argument, extension nodes, optional type annotations. Only nodes that actually use the field pay storage cost. This is Kelley's sparse data pattern: "When 90% of a field's values are the default, don't store the field in the struct at all."

### Tier 3: Medium Impact, Low-Medium Effort

#### 3.1 Hot/Cold Split of Parser Struct

**Current**: Parser struct is ~280 bytes (18+ fields) spanning 4-5 cache lines. The inner parsing loop only touches ~50 bytes (token, positions, scanner).

**Proposed**: Move cold fields (`breadcrumbs`, `diagnostics`, `comments`, `regions`, depth counters, `current_type_name_path`, `inline_types_found`) to a separate `ParserColdState` accessed via pointer. Keeps the hot parsing loop within 1 cache line.

#### 3.2 Strategic `#[inline]` Annotations

**Current**: Compiler decides inlining heuristics.

**Proposed**: Profile-guided `#[inline]` and `#[inline(always)]` on hot scanner/parser methods like `next()`, `peek()`, `scan()`, `expect()`.

#### 3.3 Lookup Tables for Character Classification

**Current**: Character classification uses match statements or if-chains.

**Proposed**: 256-byte lookup tables for ASCII character properties (is_ident_start, is_digit, is_whitespace, etc.). Single array index instead of branching.

#### 3.4 Marshal Vec Pre-allocation

**Current**: `MarshalWriter` grows its `Vec<u8>` buffer dynamically.

**Proposed**: Pre-allocate based on source file size heuristic (e.g., 4x source size for binary AST output). Avoids repeated reallocation during serialization.

#### 3.5 SmallVec for AST Nodes

**Current**: AST nodes use `Vec<T>` for children (e.g., function args, tuple elements).

**Proposed**: Use `SmallVec<[T; N]>` for common small collections (most functions have 1-3 args, most tuples have 2-3 elements). Avoids heap allocation for typical cases.

#### 3.6 Optimize `is_binary_op` and Precedence Lookup

**Current**: Operator precedence uses a match on Token enum.

**Proposed**: Encode precedence directly in the token kind (e.g., as a byte alongside the kind discriminant), eliminating the match.

#### 3.7 Optimize Breadcrumb Management

**Current**: Breadcrumbs (grammar context stack) use `Vec<Grammar>` with push/pop.

**Proposed**: Use a fixed-size stack (array + index) for breadcrumbs, since maximum nesting depth is bounded. Avoids Vec allocation and bounds checks.

#### 2.5 Token Kind/Value Split

**Current**: `Token<'a>` is a single enum (~40-48 bytes) where the discriminant and payload are bundled. 100 of 117 variants are zero-sized (keywords, punctuation), but the enum is sized for the largest variant. The parser's inner loop constantly matches on token kinds.

**Proposed**: Split into `TokenKind` (1-2 byte enum, no data) + separate `TokenPayload` (accessed only when needed). Store as separate fields in the Parser struct. The inner parsing loop operates on the 1-byte `TokenKind`, and only accesses `TokenPayload` when constructing AST nodes.

**Expected impact**: A 1-byte discriminant means 64 token kind checks fit in a single cache line vs ~1 with the current 48-byte enum. Even with single-token-at-a-time processing, the smaller discriminant improves branch prediction and reduces the Parser struct's cache footprint. Evidence: Zig compiler reduced tokens from 64 bytes to 5 bytes, achieving **22% faster** tokenization (Kelley).

**Approach**:
```rust
enum TokenKind { Lident, Uident, Int, Float, String, If, Let, ... }  // 1-2 bytes
enum TokenPayload<'a> {
    None,
    String(Cow<'a, str>),
    Int { value: Cow<'a, str>, suffix: Option<char> },
    // ...
}
// In Parser:
struct Parser<'src> {
    token_kind: TokenKind,           // hot: checked constantly
    token_payload: TokenPayload<'src>, // cold: accessed only for AST construction
    // ...
}
```

#### 2.6 Marshal Sharing Tables: HashMap → Arena-Indexed Vec

**Current**: MarshalWriter has 17 HashMaps for identity-based sharing. Each AST node triggers 8-12 random HashMap lookups — guaranteed cache misses.

**Proposed**: Since most keys are already arena indices (`PosIdx`, `LocIdx`, `StrIdx`), replace HashMaps with `Vec<Option<u32>>` indexed directly by the arena index. O(1) lookup with no hashing, no pointer chasing. Pre-size based on arena counts.

#### Super-Flat AST Packing

**Current**: AST nodes are Rust structs with enum variants.

**Proposed**: Pack each AST node into 8 bytes: `tag: u8` + `length: u24` + `first_child_index: u32`. Children stored contiguously in a flat array. Leaf nodes use remaining bytes for inline data.

**Expected impact**: ~3x memory reduction. Bottom-up construction enables linear array traversal instead of recursive tree walks (8% additional speedup).

### Tier 4: Architectural (Longer Term)

#### 4.1 SIMD-Accelerated Whitespace/Comment Skipping

**Current**: Whitespace skipping is character-by-character.

**Proposed**: Use SIMD instructions (SSE2/NEON) to skip runs of whitespace and find the next non-whitespace character in 16-byte chunks.

**Expected impact**: Significant for files with lots of whitespace/indentation. OXC uses this technique.

#### 4.2 Bump-Allocated AST (bumpalo)

**Current**: Recursive AST nodes are already in typed arena `Vec<T>` pools after task 2.3 (`ExprIdx`, `PatIdx`, etc.), so most per-node heap allocation has been removed.

**Policy**: Prioritize extending the current index/arena model before introducing `bumpalo`:
- finish sparse side tables (2.4),
- convert marshal sharing tables to arena-indexed `Vec` lookups (2.6),
- and apply inline small-collection storage (3.5) where it helps.

**Profiling gate**: Revisit `bumpalo` only if, after the steps above, flamegraphs/perf still show allocator/deallocator stacks as a top bottleneck (for example, >10% wall time or a top hotspot on representative parser workloads).

**If gate is met**: Run `bumpalo` as an isolated spike, then keep it only if it produces measurable wins without parity regressions.

#### 4.3 Profile-Guided Optimization (PGO)

**Current**: Standard release build with LTO.

**Proposed**: Use PGO with representative ReScript files as training data. The compiler optimizes branch layouts, function placement, and inlining based on actual runtime profiles.

**Approach**:
```bash
# Step 1: Build instrumented binary
RUSTFLAGS="-Cprofile-generate=/tmp/pgo-data" cargo build --release

# Step 2: Run on representative files
for f in tests/syntax_tests/data/idempotency/**/*.res; do
    target/release/bsc -bs-ast -o /dev/null "$f"
done

# Step 3: Merge profile data
llvm-profdata merge -o /tmp/pgo-data/merged.profdata /tmp/pgo-data/

# Step 4: Build optimized binary
RUSTFLAGS="-Cprofile-use=/tmp/pgo-data/merged.profdata" cargo build --release
```

---

## Evidence Base

| Approach | Source | Measured Impact |
|----------|--------|-----------------|
| Arena allocation (bumpalo) | OXC parser | ~20% speedup (reference only; profiling-gated here post-2.4/2.6) |
| Enum size enforcement (16 bytes) | OXC parser | ~10% speedup |
| Span compression (u32 offsets) | OXC parser | ~5% speedup |
| Data-oriented design (AST nodes) | Roc compiler | 12% speedup, 12% less memory |
| Index-based flat AST | Adrian Sampson (Cornell) | 2.4x speedup |
| Super-flat 8-byte nodes | jhwlr.io | ~3x memory reduction |
| String interning | Sorbet (Stripe) | Integer comparison vs string comparison |
| Precomputed char/byte arrays | Already done | 41x on JSX benchmark |

---

## Measurement Methodology

### Exe-vs-Exe Subprocess Benchmarks

The primary benchmark compares Rust and OCaml `bsc` binaries running as subprocesses, measuring the full parse-to-binary-AST pipeline:

```bash
bsc -bs-ast -o <tmpfile> <input.res>
```

**Configuration** (in `benchmark.rs`):
- 50 iterations per test, 2 warmup runs
- **Minimum** time used (not mean) - OS scheduling noise only adds time
- Maximum allowed slowdown: 1.2x (20% tolerance for subprocess overhead)
- Tests run only in release mode (`cfg!(debug_assertions)` guard)

### Running Benchmarks

```bash
# Individual test
cargo test --release --lib -- benchmark_regex --nocapture

# All benchmarks (ignored by default)
cargo test --release --lib -- benchmark_all --ignored --nocapture

# Quick check if Rust bsc exists
ls -la target/release/bsc
```

### Interpreting Results

| Factor | Status | Meaning |
|--------|--------|---------|
| < 1.0x | FASTER | Rust is faster than OCaml |
| 1.0-1.2x | OK | Within acceptable tolerance |
| > 1.2x | SLOW | Regression - needs investigation |

### Profiling

```bash
# CPU profiling with flamegraph
cargo install flamegraph
cargo flamegraph --release --bin bsc -- -bs-ast -o /dev/null large_file.res

# Memory profiling with DHAT
cargo install dhat
# Add dhat instrumentation, run, analyze dhat-heap.json

# Instruction-level profiling with perf
perf stat -e instructions,cache-misses,branch-misses \
    target/release/bsc -bs-ast -o /dev/null large_file.res
```

---

## References

### Parser Implementations
- **OXC** (Oxidation Compiler): https://oxc.rs/ - Rust-based JS/TS toolchain with best-in-class parser performance. Uses byte-level scanning, arena allocation, zero-copy tokens, and 16-byte enum enforcement.
  - Performance guide: https://oxc.rs/docs/learn/performance
  - AST guide: https://oxc.rs/docs/contribute/parser/ast
- **SWC** (Speedy Web Compiler): https://swc.rs/ - Rust-based JS/TS compiler. Demonstrates effective use of string interning and SIMD.
- **tree-sitter**: https://tree-sitter.github.io/ - Incremental parsing with flat subtree arrays and inline/heap discrimination.
- **Sorbet**: https://github.com/sorbet/sorbet - Stripe's Ruby type checker. Uses u32 index-based references everywhere. See: https://blog.nelhage.com/post/why-sorbet-is-fast/

### Techniques
- **Flattening ASTs**: https://www.cs.cornell.edu/~asampson/blog/flattening.html - Adrian Sampson's 2.4x speedup from index-based flat AST.
- **Super-flat AST**: https://jhwlr.io/super-flat-ast/ - 8-byte packed nodes, 3x memory reduction.
- **Data-oriented design for parsers**: https://tweedegolf.nl/en/blog/88/data-oriented-design - Roc compiler SoA transformation, 12% speedup.
- **Rust Parsing Best Practices**: https://matklad.github.io/ - Blog posts on parser architecture, arena allocation, and performance techniques by the rust-analyzer author.

### Project
- **Compiler Rewrite Plan**: See [PLAN.md](../compiler-rewrite/PLAN.md) for the overall compiler rewrite plan.
- **Compiler Rewrite Progress**: See [PROGRESS.md](../compiler-rewrite/PROGRESS.md) for rewrite progress tracking.
