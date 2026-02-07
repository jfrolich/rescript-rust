# ReScript Rust Parser: Performance Optimization Plan

## Executive Summary

Goal: Make the ReScript Rust parser the fastest possible implementation. The parser already achieves 2-5x faster performance than the OCaml parser on small files and rough parity on large files. This plan outlines a systematic optimization strategy to achieve best-in-class parsing performance across all file sizes.

---

## Motivation

The Rust parser is a fully functional drop-in replacement for the OCaml parser, producing byte-for-byte identical binary AST output for all 1,312 test files. With correctness established, the focus shifts to performance:

1. **Already fast on small files**: 2-5x faster than OCaml on grammar-level tests (< 10KB)
2. **Parity on large files**: ~1.0x on real-world files (20-60KB), within the 1.2x tolerance
3. **Opportunity**: Modern Rust parsing techniques (OXC, SWC, tree-sitter) demonstrate that significantly faster parsing is achievable
4. **Build system impact**: The parser runs on every source file during compilation; even small improvements compound across large projects

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

### Tier 2: Medium Impact, Low-Medium Effort

#### 2.1 Token Kind/Value Split

**Current**: Single `Token` enum carries both the kind and the value (e.g., `Lident(String)`).

**Proposed**: Split into `TokenKind` (small enum, no data) and separate value storage. The kind is checked frequently during parsing; making it smaller improves branch prediction and cache usage.

**Approach**:
```
enum TokenKind { Lident, Uident, Int, Float, String, ... }  // 1-2 bytes
struct TokenValue { ... }  // Stored separately, accessed only when needed
```

#### 2.2 Reduce Token Enum Size

**Current**: Token is 102 variants with embedded data, likely 40+ bytes per token.

**Proposed**: Minimize token size by storing data out-of-band. Measure `std::mem::size_of::<Token>()` and target 8-16 bytes.

#### 2.3 Strategic `#[inline]` Annotations

**Current**: Compiler decides inlining heuristics.

**Proposed**: Profile-guided `#[inline]` and `#[inline(always)]` on hot scanner/parser methods like `next()`, `peek()`, `scan()`, `expect()`.

#### 2.4 Lookup Tables for Character Classification

**Current**: Character classification uses match statements or if-chains.

**Proposed**: 256-byte lookup tables for ASCII character properties (is_ident_start, is_digit, is_whitespace, etc.). Single array index instead of branching.

#### 2.5 Marshal Vec Pre-allocation

**Current**: `MarshalWriter` grows its `Vec<u8>` buffer dynamically.

**Proposed**: Pre-allocate based on source file size heuristic (e.g., 4x source size for binary AST output). Avoids repeated reallocation during serialization.

### Tier 3: Medium Impact, Higher Effort

#### 3.1 SmallVec for AST Nodes

**Current**: AST nodes use `Vec<T>` for children (e.g., function args, tuple elements).

**Proposed**: Use `SmallVec<[T; N]>` for common small collections (most functions have 1-3 args, most tuples have 2-3 elements). Avoids heap allocation for typical cases.

#### 3.2 SIMD-Accelerated Whitespace/Comment Skipping

**Current**: Whitespace skipping is character-by-character.

**Proposed**: Use SIMD instructions (SSE2/NEON) to skip runs of whitespace and find the next non-whitespace character in 16-byte chunks.

**Expected impact**: Significant for files with lots of whitespace/indentation. OXC uses this technique.

#### 3.3 Optimize `is_binary_op` and Precedence Lookup

**Current**: Operator precedence uses a match on Token enum.

**Proposed**: Encode precedence directly in the token kind (e.g., as a byte alongside the kind discriminant), eliminating the match.

#### 3.4 Optimize Breadcrumb Management

**Current**: Breadcrumbs (grammar context stack) use `Vec<Grammar>` with push/pop.

**Proposed**: Use a fixed-size stack (array + index) for breadcrumbs, since maximum nesting depth is bounded. Avoids Vec allocation and bounds checks.

### Tier 4: Architectural (Longer Term)

#### 4.1 Arena-Allocated AST

**Current**: AST nodes are heap-allocated via `Box<T>` and `Vec<T>`.

**Proposed**: Allocate all AST nodes from a bump allocator (e.g., `bumpalo`). The entire AST is freed at once when parsing completes. Eliminates individual deallocation overhead.

**Expected impact**: Significant for large files with deep AST trees. This is how OXC achieves its best performance.

#### 4.2 Profile-Guided Optimization (PGO)

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

- **OXC** (Oxidation Compiler): https://oxc.rs/ - Rust-based JS/TS toolchain with best-in-class parser performance. Uses byte-level scanning, arena allocation, and zero-copy tokens.
- **SWC** (Speedy Web Compiler): https://swc.rs/ - Rust-based JS/TS compiler. Demonstrates effective use of string interning and SIMD.
- **tree-sitter**: https://tree-sitter.github.io/ - Incremental parsing library with efficient memory layout and error recovery.
- **Rust Parsing Best Practices**: https://matklad.github.io/ - Blog posts on parser architecture, arena allocation, and performance techniques by the rust-analyzer author.
- **Binary AST Parity Plan**: See [BINARY_PARITY_PLAN.md](./BINARY_PARITY_PLAN.md) for the overall compiler rewrite plan.
- **Binary AST Parity Progress**: See [BINARY_PARITY_PROGRESS.md](./BINARY_PARITY_PROGRESS.md) for rewrite progress tracking.
