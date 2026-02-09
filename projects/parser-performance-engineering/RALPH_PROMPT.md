# Ralph Loop: Parser Performance Engineering

You are optimizing the **Rust ReScript parser** for maximum performance while preserving **byte-for-byte binary AST parity** with the OCaml reference implementation.

## Core Principle: Performance Without Regressions

**Every optimization MUST preserve binary AST parity.** This is non-negotiable. The Rust `bsc -bs-ast` output must be byte-identical to the OCaml output for all test files.

Before and after every change:
```bash
# Parity test (MUST show zero regressions)
./scripts/test_parser_ast_parity.sh 2>&1 | tail -20
```

## Your Task

Before selecting any new task, always check for unfinished local work:

1. Run `git status --short` first.
2. If there are uncommitted changes, assume they are an unfinished task in progress.
3. Continue and finish that in-progress task first (parity + benchmarks + docs updates), then commit it.
4. Only when the working tree is clean, read `RALPH_TODO.md` and start the next unchecked task.

After completing a task:
1. Run parity tests — zero regressions required
2. Run benchmarks and record results
3. Mark the task `[x]` complete in `RALPH_TODO.md`
4. Update `PROGRESS.md` with benchmark results
5. Commit your changes with an atomic commit
6. If all tasks are complete, output "RALPH_COMPLETE"
7. Never mention or print `RALPH_COMPLETE` early. The loop stops on that token, so only emit it when the Exit Condition below is truly satisfied.

### When an optimization threatens binary parity

Some optimizations may seem to conflict with byte-for-byte binary AST parity. For example, changing AST node layout may affect marshal serialization order, or arena allocation may change object identity patterns that the marshal's sharing tables depend on.

**Try hard to find a way to preserve parity.** Most optimizations CAN be made parity-safe with the right approach:

1. **Prototype and test first** — Actually try the optimization and run `./scripts/test_parser_ast_parity.sh`. Don't assume it will break parity.
2. **If parity breaks, analyze the root cause** — Use `python3 scripts/inspect_binary_ast.py test <file.res>` to understand exactly what changed. Is it serialization order? Object sharing? Position identity?
3. **Try to fix the parity issue** — Common strategies:
   - **Serialization order changed?** → Adjust the marshal code to traverse in the original order, even if internal layout differs.
   - **Object sharing changed?** → Update the marshal's sharing tables to key on the new indices/references instead of the old ones.
   - **Position identity changed?** → Ensure the new data structure preserves the same arena indices that the marshal depends on.
   - **Decouple internal representation from serialization** — The internal AST can use a different layout than what gets serialized. Add a translation layer if needed.
4. **Only defer as a last resort** — If after genuine effort you cannot preserve parity, document why in `PROGRESS.md`:
   - What you tried (every approach, not just one)
   - How parity broke (which files, what kind of difference)
   - Why it's fundamentally incompatible (not just "it's hard" — explain the structural reason)
   - Whether it could become possible after the parity constraint is relaxed
5. **Mark deferred tasks as `[~]`** in `RALPH_TODO.md` with a note: `— DEFERRED: <reason>. See PROGRESS.md.`

## Critical Rules

1. **Parity first, performance second** — Never commit a performance improvement that breaks even one parity test. Run `./scripts/test_parser_ast_parity.sh` before and after every change.

1. **No `Rc` or `Arc` — ever** — Do not use `Rc<T>` or `Arc<T>` anywhere. Reference counting prevents sharing memory between threads and is slower than arena allocation. Prefer arena-allocated indices (e.g., `ExprIdx(u32)` into a `Vec<T>` pool), `&'arena T` references from bump allocators like `bumpalo`, or owned/borrowed data (`Box<T>`, `&T`, `Cow<'a, T>`). The parser's existing `StrIdx`/`LocIdx`/`PosIdx` pattern is the model to follow. **The existing `Rc<str>` in `intern.rs` (from task 1.3) must be removed — this is task 1.4 and is high priority.**

2. **ALWAYS run benchmarks** — Every optimization MUST have benchmark numbers. This is the whole point of this project. For every task:
   ```bash
   # BEFORE starting: record baseline
   cargo build --manifest-path compiler-rust/Cargo.toml --release
   cargo test --release --lib -- benchmark_all --ignored --nocapture 2>&1 | tail -30

   # AFTER implementing: verify improvement
   cargo build --manifest-path compiler-rust/Cargo.toml --release
   cargo test --release --lib -- benchmark_all --ignored --nocapture 2>&1 | tail -30
   ```
   Record both before/after numbers in your commit message AND in `PROGRESS.md`. If you don't have benchmark numbers, the task is NOT complete.

3. **Profile before optimizing** — Don't guess where time is spent. Use flamegraphs, `perf stat`, or `cargo bench` to identify actual hotspots before writing code.

4. **Small, incremental changes** — Each task should be one focused optimization. Don't combine multiple optimizations in one commit. This makes it easy to identify regressions.

5. **Commit after each improvement** — Every successful optimization gets committed immediately:
   ```bash
   git add <files> && git commit -m "Perf: <description>

   Benchmark (before): <key numbers>
   Benchmark (after):  <key numbers>
   Parity: zero regressions

   Co-Authored-By: Claude <noreply@anthropic.com>"
   ```

6. **Revert if no measurable improvement** — If an optimization doesn't show measurable improvement in benchmarks, revert it. Don't add complexity without payoff. Record the null result in `PROGRESS.md` anyway (negative results are valuable).

7. **Study OXC/SWC for patterns** — These are the state-of-the-art Rust parsers. When implementing an optimization (especially byte-level scanning, zero-copy tokens, SIMD), study how OXC does it first.

## Key Files

| File | Purpose |
|------|---------|
| `compiler-rust/src/parser/ast.rs` | AST nodes — **primary optimization target** (enum sizes, attributes, allocation) |
| `compiler-rust/src/parse_arena.rs` | Arena allocation — index-based AST pools |
| `compiler-rust/src/parser/scanner.rs` | Scanner — byte-level scanning, character classification |
| `compiler-rust/src/parser/token.rs` | Token enum — size optimization |
| `compiler-rust/src/parser/state.rs` | Parser state — position tracking, breadcrumbs |
| `compiler-rust/src/parser/expr.rs` | Expression parsing — hot parsing loops |
| `compiler-rust/src/parser/benchmark.rs` | Benchmark harness |
| `compiler-rust/src/binary_ast/marshal.rs` | Marshal writer — buffer allocation, sharing tables |
| `compiler-rust/src/intern.rs` | String interner — Rc removal target (task 1.4) |

## Current Architecture

```
Source (&str) -> Scanner (Vec<char> + Vec<usize>) -> Token (enum with String data)
  -> Parser (recursive descent) -> AST (Box/Vec allocated) -> Marshal (Vec<u8> buffer)
```

**Key performance characteristics:**
- Scanner precomputes `Vec<char>` and `Vec<usize>` (byte offsets) upfront for O(1) access
- Token enum carries `String` data for identifiers/literals (~40+ bytes per token)
- Parser uses `Vec<(Grammar, Position)>` for breadcrumb stack
- MarshalWriter starts with 4KB `Vec<u8>` buffer, grows dynamically

## Benchmarks

```bash
# Quick single benchmark (50 iterations)
cargo test --release --lib -- benchmark_regex --nocapture

# All benchmarks (700+ files, 10 iterations — ~3 min)
cargo test --release --lib -- benchmark_all --ignored --nocapture

# Build release binary first
cargo build --manifest-path compiler-rust/Cargo.toml --release
```

Benchmark measures `bsc -bs-ast -o <tmpfile> <input.res>` for both Rust and OCaml as subprocesses. Uses minimum time over iterations. MAX_SLOWDOWN_FACTOR = 1.2x.

**Current baseline:** Rust is 2-5x faster on small files (<10KB), ~0.7-1.0x on large files (20-60KB).

## Profiling

```bash
# Flamegraph (requires cargo-flamegraph)
cargo flamegraph --release --bin bsc -- -bs-ast -o /dev/null <large_file.res>

# Measure token/struct sizes
# Add to a test: println!("Token size: {}", std::mem::size_of::<Token>());

# Instruction-level profiling (Linux)
perf stat -e instructions,cache-misses,branch-misses \
    target/release/bsc -bs-ast -o /dev/null <large_file.res>
```

## Debugging / Checking Parity

```bash
# Full parity test
./scripts/test_parser_ast_parity.sh

# Single file parity
./scripts/test_parser_ast_parity.sh tests/syntax_tests/data/printer/expr/record.res

# Quick parity (stop on first failure)
./scripts/test_parser_ast_parity.sh --quick
```

## Reference Material

- **PLAN.md** in this directory — Full optimization roadmap with 4 tiers and 19 items
- **PROGRESS.md** in this directory — Optimization progress and benchmark log
- **OXC parser**: https://github.com/nickel-org/nickel.rs — Study byte-level scanning, arena allocation
- **matklad blog**: https://matklad.github.io/ — Rust parser architecture best practices

## Exit Condition

When all tasks in `RALPH_TODO.md` are either `[x]` (completed) or `[~]` (deferred with documented reason), output exactly:
```
RALPH_COMPLETE
```

Do not output or mention `RALPH_COMPLETE` for partial progress, plans, examples, or "almost done" states. If any task remains unchecked (`[ ]`), continue working and do not emit the token.
