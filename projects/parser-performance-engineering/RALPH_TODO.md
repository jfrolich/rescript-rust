# Parser Performance Engineering TODO

**Last Updated:** 2026-02-08
**Status:** 8/23 tasks complete, 0 deferred

**Baseline:** Rust is 2-5x faster on small files (<10KB), ~0.7-1.0x on large files (20-60KB).
**Goal:** Maximize Rust parser speed across all file sizes while preserving byte-for-byte binary AST parity.

**Parity constraint:** Every change must pass `./scripts/test_parser_ast_parity.sh` with zero regressions.
After parser/PPX optimization work, rerun `./scripts/test_parser_ast_parity.sh` explicitly as a required post-optimization gate (optimizations can silently change traversal and rewrite behavior).

---

## Tier 1: High Impact, Medium Effort (Scanner + Token)

These target the scanner and token representation where the parser spends most time.

- [x] **1.1 Byte-level scanning** — Replace `Vec<char>` with direct `&[u8]` byte operations. ASCII fast path (byte < 0x80), UTF-8 slow path on demand. Eliminates Vec<char> allocation and improves cache locality. OXC and SWC both use byte-level scanning. Files: `scanner.rs`. Scanner struct ~24 bytes smaller, eliminates Vec<char>/Vec<usize> heap allocations. Large files improved from 0.87x to 0.83x. All 1196 parity tests pass.

- [x] **1.2 Zero-copy token strings** — Changed `Token` to `Token<'a>` with `Cow<'a, str>` for all string-carrying variants. Scanner produces `Cow::Borrowed` for identifiers and literals (zero-copy from source), `Cow::Owned` only for escape-processed strings. Lifetime propagated through Scanner, Parser, ScanResult, ScannerSnapshot. DiagnosticCategory and Grammar use `Token<'static>` with `.into_owned()` at the boundary. Files: `token.rs`, `scanner.rs`, `state.rs`, `diagnostics.rs`, `grammar.rs`, `core.rs`, `parse_arena.rs`, `expr.rs`, `pattern.rs`, `typ.rs`, `module.rs`. Impact: Large files 0.83x→0.80x (~4% faster), Medium 0.57x→0.55x. All 1196 parity tests pass.

- [x] **1.3 String interning via StrIdx** — Extended `Interner` with `push_interned()` method that returns unique StrIdx values (preserving marshal identity semantics) while sharing underlying string data to avoid heap allocation for duplicate identifiers. Converted ~68 parser call sites from `push_string(name.to_string())` to `push_interned_string(&name)`. Changed `push_lident`/`push_ldot` signatures from `impl Into<String>` to `&str`. Key insight: the interning cache must be separate from the `intern()` map to avoid polluting `intern()`'s deduplication (which would break marshal sharing parity). Performance: neutral (Large 0.82x, within noise of 0.80x baseline). Primary benefit is reduced memory allocation for duplicate identifiers. Files: `intern.rs`, `parse_arena.rs`, `state.rs`, `expr.rs`, `pattern.rs`, `typ.rs`, `module.rs`, `core.rs`, `jsx_ppx.rs`, `ppx.rs`. All 1196 parity tests pass.

- [x] **1.4 Remove Rc<str> from Interner** — Replaced all `Rc<str>` with `Box<str>` in the Interner. Changed `Vec<Rc<str>>` → `Vec<Box<str>>`, `HashMap<Rc<str>, StrIdx>` → `HashMap<String, StrIdx>`, removed `rc_cache` HashMap entirely. `push_interned()` now simply allocates a `Box<str>` each time (the Rc sharing from task 1.3 was performance-neutral). Removed `use std::rc::Rc`. Interner is now Send+Sync compatible. Impact: Performance-neutral (within noise of baseline). All 1196 parity tests pass. Files: `intern.rs`, `parse_arena.rs` (doc comments only).

- [x] **1.5 Zero-copy Constant and Label strings** — Changed `Constant::Integer(String)`, `Constant::Float(String)`, `Constant::String(String, Option<String>)`, `Label` (type alias), `Ptyp_var(String)`, and `Ptyp_alias(_, String)` to use `Cow<'static, str>`. Uses `extend_cow_lifetime()` (unsafe transmute, sound because source outlives AST) to propagate zero-copy borrows from scanner through to AST. Eliminated ~15 hot-path `.clone().into_owned()` heap allocations. Only escape-processed strings allocate. Impact: Large files 0.80x→0.77x (~4% faster). All 1196 parity tests pass. Files: `ast.rs`, `expr.rs`, `typ.rs`, `pattern.rs`, `module.rs`, `sexp.rs`, `sexp_locs.rs`, `jsx_ppx.rs`, `ppx.rs`, `spice_ppx.rs`, `mapper_from0.rs`, `mapper_to0.rs`, `writer.rs`, `typecore.rs`.

---

## Tier 2: High Impact — AST Memory Layout

These target the AST node representation, where the biggest memory and cache wins are. Analysis shows ExpressionDesc is ~120 bytes but 85% of variants need <16 bytes — enormous padding waste. Every node also carries an empty 24-byte `Vec<Attribute>`. Fixing these two issues alone could shrink Expression from ~150 bytes to ~20-24 bytes.

- [x] **2.1 Enforce 16-byte enum sizes (OXC pattern)** — Boxed large enum variants across all AST desc enums. Results: ExpressionDesc 80→24 bytes, PatternDesc 64→24 bytes, CoreTypeDesc 64→16 bytes, StructureItemDesc 64→16 bytes, SignatureItemDesc 56→16 bytes, ModuleExprDesc 40→24 bytes, ModuleTypeDesc 32→16 bytes, Payload 48→16 bytes. Created named structs PexpFun (80 bytes) and PexpApply (40 bytes) for the largest ExpressionDesc variants. Performance: neutral overall (Large 0.77x→0.81x slight regression from additional Box allocations, offset by better cache locality on smaller files). The boxing is a foundation for arena allocation (task 2.3) which will eliminate Box overhead while keeping cache benefits. Used automated `fix_boxing.py` script for bulk rewriting across 26 files. Files: `ast.rs` + 25 dependent files across parser, binary_ast, types.

- [x] **2.2 Attributes newtype (Option<Box<Vec>>)** — Replaced `type Attributes = Vec<Attribute>` (24 bytes inline) with a newtype `struct Attributes(Option<Box<Vec<Attribute>>>)` (8 bytes inline). Empty attributes (95%+ of nodes) are `None` — zero heap allocation. Non-empty attributes use `Some(Box::new(vec![...]))`. Provides full API compatibility via `Deref<Target=[Attribute]>`, `IntoIterator`, `FromIterator`, `From<Vec>`, plus methods: `new()`, `from_vec()`, `is_empty()`, `len()`, `iter()`, `push()`, `insert()`, `extend()`, `concat()`, `into_vec()`. Results: Expression 40→24 bytes (40% reduction), Pattern 40→24 bytes, CoreType 40→24 bytes, ValueBinding 112→64 bytes (43%), PexpFun 80→64 bytes, TypeDeclaration 160→128 bytes. Performance: neutral (Large 0.80x→0.81x, within noise). Infrastructure for AttrsIdx(u32) added to ParseArena for future 24→16 byte reduction (to be done alongside task 2.3). Files: `ast.rs` + 20 dependent files across parser, binary_ast, types, lambda.

- [x] **2.3 Index-based AST (ExprIdx/PatIdx into ParseArena)** — Replaced `Box<Expression>` with `ExprIdx(u32)`, `Box<Pattern>` with `PatIdx(u32)`, `Box<CoreType>` with `CoreTypeIdx(u32)`, `Box<ModuleExpr>` with `ModExprIdx(u32)`, `Box<ModuleType>` with `ModTypeIdx(u32)` indices into flat `Vec<T>` pools in `ParseArena`. All recursive AST references now use 4-byte indices instead of 8-byte pointers. Arena pools (`expressions`, `patterns`, `core_types`, `mod_exprs`, `mod_types`) with `push_*`/`get_*` methods. Fixed 112 borrow checker errors in ppx.rs and jsx_ppx.rs by: (1) changing `list_of_arrow`/`get_result_type`/`get_final_result_type`/`destruct_open_tuple` to return owned data instead of arena references, (2) changing read-only functions (`is_unit_type`, `get_payload_int`, `get_payload_string_with_delim`, `has_external_attrs`, `is_rs_external`) from `&mut ParseArena` to `&ParseArena`, (3) splitting `arena.push_X(fn(..., arena))` patterns into separate `let` bindings. AST enum sizes: ExpressionDesc 24→16 bytes (hit 16-byte target!), PatternDesc 24→16, ModuleExprDesc 24→16. PexpFun 64→56, PexpApply 40→32. Performance: neutral (Large 0.81x, within noise). Zero parity regressions. Files: `ast.rs`, `parse_arena.rs`, `ppx.rs`, `jsx_ppx.rs` + all parsing/PPX/marshal modules.

- [x] **2.4 Generalized sparse data / side tables** — COMPLETE: sparse side-table migration now covers `PexpFun.default`, `Case.pc_guard`, and follow-on expression payload options (`construct/variant/record/if/coerce`) with parser/mapper/marshal plumbing and parity gates passing.
  - Why this shape: sparse `Option<...>` fields are currently embedded in by-value nodes before arena index assignment; side tables must be keyed by stable node indices.
  - Initial scope: `PexpFun.default` and `Case.pc_guard`, then expand to `Pexp_construct/variant/record/if/coerce` option payloads after parity is stable.
  - Enabling API work (required first):
    - [x] Add reserve/initialize APIs for expression/pattern/core_type/module node arenas (or equivalent builder APIs that guarantee stable early index assignment).
    - [x] Add sparse side tables in `ParseArena` keyed by node indices for initial `ExprIdx` owners (`PexpFun.default`, `Case.pc_guard`) with explicit reset semantics on expression slot initialization.
    - [x] Thread parser/PPX/mapper/marshal paths to populate and consume the new side tables.
  - Migration order (must stay in this order):
    - Parser construction paths
    - PPX / JSX transforms
    - Mapper conversions (`mapper_from0` / `mapper_to0`)
    - Marshal writer sharing-sensitive paths
  - Parity guardrails:
    - `./scripts/test_parser_ast_parity.sh --quick` on each substep
    - full `./scripts/test_parser_ast_parity.sh` before/after each migrated field family
    - benchmark check after each phase to catch regressions
  - Exit criteria:
    - target sparse fields moved to side tables
    - no new parity regressions
    - measurable AST size reduction on expression-heavy paths
  - See `PROGRESS.md` (Task 2.4 plan) for detailed rollout and rationale.

- [ ] **2.5 Token kind/value split** — Split `Token<'a>` enum (~40-48 bytes) into a small `TokenKind` enum (1-2 bytes, no data) + separate `TokenPayload` storage accessed only when needed. 100 of 117 variants are zero-sized (keywords, punctuation); only 17 carry payloads. The parser's inner loop constantly checks token kinds — a 1-byte discriminant means 64 token checks per cache line vs ~1 with the current 48-byte enum. Even though the parser processes one token at a time, the smaller discriminant improves branch prediction and reduces the working set of the Parser struct. Evidence: Zig compiler reduced tokens from 64 bytes to 5 bytes with 22% speedup. Approach: `TokenKind` enum for the discriminant, `TokenPayload` union/enum for the rare data, stored as separate fields in the Parser struct. Files: `token.rs`, `state.rs`, all parsing modules.

- [ ] **2.6 Marshal sharing tables: HashMap → arena-indexed Vec** — The MarshalWriter has 17 HashMaps for identity-based sharing. Each AST node triggers 8-12 random HashMap lookups across different tables — guaranteed cache misses. Since most keys are already arena indices (`PosIdx`, `LocIdx`, `StrIdx`), replace HashMaps with `Vec<Option<u32>>` indexed by the arena index directly. O(1) lookup with no hashing, no random pointer chasing. Pre-size based on arena counts (we know exact sizes). This could significantly speed up serialization. Files: `binary_ast/marshal.rs`.

---

## Tier 3: Medium Impact, Low-Medium Effort

- [ ] **3.1 Hot/cold split of Parser struct** — The Parser struct is ~280 bytes (18+ fields) spanning 4-5 cache lines, but the inner parsing loop only touches ~50 bytes: `token`, position fields, `scanner`. Cold fields (`breadcrumbs`, `diagnostics`, `comments`, `regions`, depth counters, `current_type_name_path`, `inline_types_found`) should be moved to a separate `ParserColdState` accessed via pointer. Keeps the hot parsing loop within 1 cache line. Files: `state.rs`.

- [ ] **3.2 Strategic `#[inline]` annotations** — Profile to identify hot functions. Add `#[inline]` or `#[inline(always)]` on scanner `next()`, `peek()`, `scan_token()` and parser `expect()`, `advance()`, `next()`. Benchmark each annotation individually — `#[inline(always)]` can hurt if it bloats the caller. Files: `scanner.rs`, `state.rs`.

- [ ] **3.3 Lookup tables for character classification** — Replace match/if-chain character classification with 256-byte ASCII lookup tables. One array index instead of branching for `is_ident_start`, `is_ident_part`, `is_digit`, `is_whitespace`, etc. Files: `scanner.rs`.

- [ ] **3.4 Marshal Vec pre-allocation** — Pre-allocate `MarshalWriter` buffer based on source file size heuristic (e.g., 4x source bytes). Avoids repeated reallocation during serialization. Currently starts at 4KB. Files: `binary_ast/marshal.rs`, `binary_ast/writer.rs`.

- [ ] **3.5 SmallVec for AST nodes** — Replace `Vec<T>` with `SmallVec<[T; N]>` for common small collections. Targets: function args (N=3), tuple elements (N=3), record fields (N=4), type params (N=2). Typical lengths are 1-3 items but Vec allocates minimum capacity of 4. Avoids heap allocation for typical cases. Add `smallvec` dependency. Files: `ast.rs`, all parsing modules.

- [ ] **3.6 Optimize binary op precedence lookup** — Encode operator precedence directly in token kind (e.g., as a byte alongside the discriminant) instead of a match dispatch. The `is_binary_op` / `get_precedence` path is hit on every expression. Files: `token.rs`, `expr.rs`.

- [ ] **3.7 Optimize breadcrumb management** — Replace `Vec<(Grammar, Position)>` breadcrumb stack with a fixed-size array + index. Maximum nesting depth is bounded. Avoids Vec allocation, bounds checks, and potential reallocation. Files: `state.rs`.

---

## Tier 4: Architectural (Longer Term)

- [ ] **4.1 SIMD whitespace/comment skipping** — Use SIMD (SSE2 on x86, NEON on ARM) to skip runs of whitespace in 16-byte chunks. Significant for heavily indented files. OXC uses this technique. Requires platform-specific code with fallback. Files: `scanner.rs`.

- [ ] **4.2 Bump-allocated AST (bumpalo, profiling-gated)** — Revisit `bumpalo` only after allocation-focused index/arena work lands (`2.4` side tables, `2.6` marshal HashMap→arena-indexed Vec, then `3.5` SmallVec where it helps). Rationale: 2.3 already moved recursive AST nodes into typed arena Vec pools, so most per-node heap allocation is already gone. Start 4.2 only if post-2.4/2.6 flamegraph/perf still shows allocator/deallocator stacks as a top parser bottleneck (for example >10% wall time or consistently top hotspots). If gated in, run as an isolated spike and keep only with measurable wins plus zero parity regressions. Files: `ast.rs`, all parsing modules, lifetime changes throughout.

- [ ] **4.3 Super-flat AST packing** — Pack each AST node into 8 bytes: `tag: u8` + `length: u24` + `first_child_index: u32`. Leaf nodes use 7 remaining bytes for inline data (e.g., StrIdx). Fixed-arity nodes use 3 bytes for inline data. Dynamic-arity nodes use length for child count. Evidence: ~3x memory reduction vs traditional tree. Bonus: bottom-up construction order means children always precede parents in the array, enabling linear left-to-right processing instead of recursive traversal (8% additional speedup). Files: `ast.rs`, complete rewrite of AST representation.

- [ ] **4.4 Profile-Guided Optimization (PGO)** — Build instrumented binary, run on representative ReScript files (idempotency tests), rebuild with profile data. Optimizes branch layouts, function placement, and inlining based on actual runtime profiles. Requires build script changes. Files: build configuration, Cargo.toml, CI pipeline.

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

# Repeated single-thread throughput (in-process, min/median/p95 KLOC/s)
RAYON_NUM_THREADS=1 PARSER_BENCH_WARMUP=2 PARSER_BENCH_RUNS=10 \
cargo test --manifest-path compiler-rust/Cargo.toml --release --lib -- benchmark_cold_repeat --ignored --nocapture

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
| Hot/cold data splitting | Roc compiler (Tweede golf blog) | 12% speedup, 12% less memory |
| Index-based flat AST | Adrian Sampson (Cornell) | 2.4x speedup (38% was free() alone) |
| Linear scan of flat AST | Adrian Sampson (Cornell) | Additional 8.2% on top of flattening |
| Super-flat 8-byte nodes | jhwlr.io | ~3x memory reduction |
| SoA tokens (64B → 5B) | Zig compiler (Kelley) | 22% faster tokenization |
| SoA AST nodes (120B → 15.6B) | Zig compiler (Kelley) | 22% faster parse |
| Sparse data in side tables | Kelley DOD talk | Reduced per-entity footprint 50% |
| String interning | Sorbet (Stripe) | Integer comparison vs string comparison |
| Precomputed char/byte arrays | Already done (commit 558e262ff) | 41x on JSX benchmark |
| Remove virtual dispatch | Muratori | 1.5x from eliminating indirection |
| Full DOD pipeline | jhwlr.io | 3x throughput, 65% less memory |

Key resources:
- OXC performance: https://oxc.rs/docs/learn/performance
- Flattening ASTs: https://www.cs.cornell.edu/~asampson/blog/flattening.html
- Roc hot/cold splitting: https://tweedegolf.nl/en/blog/88/data-oriented-design
- Why Sorbet is fast: https://blog.nelhage.com/post/why-sorbet-is-fast/
- Super-flat AST: https://jhwlr.io/super-flat-ast/
- Kelley DOD (Zig): https://www.josherich.me/podcast/andrew-kelley-practical-data-oriented-design-dod
- Mike Acton DOD talk: https://www.youtube.com/watch?v=rX0ItVEVjHc
- Muratori "Clean Code" perf: https://www.computerenhance.com/p/clean-code-horrible-performance
- Pointer chasing vs linear: https://en.algorithmica.org/hpc/cpu-cache/pointers/

---

## Notes

- **No `Rc`/`Arc`** — Do not use `Rc<T>` or `Arc<T>`. They prevent sharing memory between threads and are slower than arena allocation. Use arena indices, bump-allocated references, or owned/borrowed data instead. The existing `Rc<str>` in the Interner (from task 1.3) must be removed — see task 1.4.
- The scanner currently precomputes `Vec<char>` and `Vec<usize>` (byte offsets) upfront — this was the first optimization (41x improvement on JSX benchmark). Task 1.1 replaces this with direct byte-level scanning.
- Token enum has ~117 variants but only 17 carry payloads. The enum is ~40-48 bytes. Task 1.2 (zero-copy Cow) addresses string payloads; task 2.1 (16-byte enums) addresses enum size; task 2.5 (token kind/value split) separates the 1-byte discriminant from the rare payloads for better cache utilization.
- The parser already uses arena indices (`PosIdx`, `LocIdx`, `StrIdx`, `LidentIdx`, `ArityIdx`) for position/location/string sharing. Task 3.1 extends this pattern to all AST nodes (ExprIdx, PatIdx, CoreTypeIdx).
- ExpressionDesc has 28 variants, PatternDesc 17, CoreTypeDesc 11. The largest variants (Pexp_fun with 6 fields ~100+ bytes, Pexp_apply with Vec ~60 bytes) dominate enum size while 85%+ of variants need <16 bytes. Boxing large variants per 2.1 is the quick win; 2.3/4.3 are the deeper refactors.
- MarshalWriter uses 17 HashMap-based sharing tables. These are correctness-critical for binary parity. Task 2.6 proposes replacing them with arena-indexed Vec lookups (O(1), no hashing). Must verify parity is preserved.
- Lookahead parsing (`lookahead_depth > 0`) skips arena allocations to avoid polluting position indices. Any scanner/parser changes must preserve this behavior.
- The marshal/PPX code does extensive pattern matching on AST desc enums (87+ matches for ExpressionDesc alone). Index-based AST (3.1) changes access patterns from `match expr.pexp_desc` to `match arena.get_expr(expr_idx).pexp_desc` — more verbose but not fundamentally different.
