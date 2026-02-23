# Ralph Loop: Typed Tree Parity (with Locations)

You are working on achieving **100% typedtree parity** between the Rust compiler and the OCaml reference implementation using `-dtyped-sexp-locs`.

## Current Baseline (2026-02-22)

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Typedtree parity (`-dtyped-sexp-locs`): **607/657** (50 diffs)
- Parser/binary parity guard is fully green

**IMPORTANT: Read `RALPH_GUIDANCE.md` before starting work.** It contains:
- 15 specific missing fixes from typed-ast-parity branch (with commit hashes, OCaml refs, test names)
- Exact code changes needed for each fix
- Known anti-patterns that cause regressions (DO NOT RETRY)
- **DO NOT change sexp_typedtree.rs cycle detection** — causes 607→220 regression

## Core Principle: 1:1 OCaml Port

- **Read OCaml first** before touching Rust.
- **Match OCaml control flow exactly** (algorithm, ordering, edge cases).
- **No shortcuts, no heuristic hacks, no local special-casing by filename.**
- Use idiomatic Rust only as a translation of OCaml behavior.

Primary OCaml references:
- `compiler/ml/typecore.ml`
- `compiler/ml/ctype.ml`
- `compiler/ml/typemod.ml`
- `compiler/ml/sexp_typedtree.ml`
- `compiler/ml/typedtree.mli`

Primary Rust implementation files:
- `compiler-rust/src/types/typecore.rs`
- `compiler-rust/src/types/ctype.rs`
- `compiler-rust/src/types/typemod.rs`
- `compiler-rust/src/types/sexp_typedtree.rs`
- `compiler-rust/src/types/typedtree.rs`

## Hard-Task Mandate (No Shortcut Policy)

1. **Tackle the hardest remaining root-cause cluster first** (largest failing group), not easy one-off files.
2. **No docs-only revalidation commits.** A commit must include meaningful code changes that advance parity/compile coverage, or add new unchecked root-cause tasks with concrete evidence.
3. **If all TODO tasks are checked but parity < 657/657, create new unchecked tasks immediately** from the current failing-file manifest before coding.
4. **At most one parity-neutral experiment per hypothesis.** Revert and move to a new hypothesis quickly; do not loop.
5. **No “fundamental limitation” claims** without OCaml source proof and a concrete follow-up plan.

## Your Task Each Iteration

1. Open `RALPH_TODO.md`.
2. Pick the next unchecked task.
3. Read the OCaml reference functions for that task.
4. Implement the Rust port.
5. Run targeted tests with timeouts.
6. Run deterministic full parity check with timeouts.
7. Update `RALPH_TODO.md` with:
   - What changed
   - OCaml functions read
   - Exact before/after parity counts
8. Commit atomically.
9. Stop (one task per session).

If there are no unchecked tasks, create new unchecked tasks from the current failure list first, then continue.

## Required Commands (Always with Timeout)

```bash
# Build Rust compiler
timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release

# Full parity check (builds OCaml + Rust sexp via rewatch, compares raw output)
./scripts/test_typedtree_parity.sh

# Single file (regenerates sexp for just that file via rewatch --filter, ~1s)
./scripts/test_typedtree_parity.sh async_inline

# Glob pattern
./scripts/test_typedtree_parity.sh "belt_*"

# File path (extracts module name automatically)
./scripts/test_typedtree_parity.sh tests/tests/src/a.res

# Parser/binary guard (must stay green)
timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40
```

Never run Rust compiler/test commands without timeout.

### How the parity script works

Both OCaml and Rust sexp are generated via **rewatch** (single command each):
1. `rescript build` — normal build (produces .cmi/.cmj)
2. `rescript build --dump-typed-sexp` — OCaml bsc generates sexp to `lib/ocaml/*.sexp`
3. `rescript build --dump-typed-sexp --rust` — Rust in-process generates sexp to `lib/ocaml/*.sexp`

The script saves OCaml sexp files before Rust overwrites them, then does **raw byte-for-byte comparison** (`cmp -s`). All results persist in `.parity-cache/` for inspection:
- `.parity-cache/$label/ocaml/*.sexp` — raw OCaml sexp files
- `.parity-cache/$label/rust/*.sexp` — raw Rust sexp files
- `.parity-cache/$label/diffs/*.diff` — per-module diffs (only for failing files)
- `.parity-cache/$label/summary.txt` — counts
- `.parity-cache/$label/failures.txt` — list of failing modules

### Raw comparison — no post-processing

The comparison is **raw, byte-for-byte** with zero post-processing. No stripping of non-printable characters, no trimming whitespace, no normalizing newlines. Both compilers must produce **identical output**. If there are differences in whitespace, trailing newlines, or non-printable characters, fix the Rust output to match OCaml exactly — do NOT add post-processing to the comparison script.

## Failure-Driven Workflow

1. Generate current failing-file manifest from deterministic run.
2. Group failures by shared root cause (first divergent typedtree node path).
3. Prioritize by cluster size and risk.
4. Solve one cluster at a time with OCaml-aligned changes.
5. Require parity delta after each successful fix.

**IMPORTANT: Follow the task list in RALPH_TODO.md (tasks 2-16). Key order:**
1. **Predef variances, prefix rewriting, coercion subtype** — small, independent fixes
2. **Deep-copy Tvariant/Tobject/Tfield, expand abbreviations, build_as_type** — ctype.rs/typecore.rs fixes
3. **Label type param sharing, pattern var shallow copies, scrutinee protection** — typecore.rs fixes
4. **Force-generalize module sigs, GADT equations** — complex infrastructure
5. **Per-case generalization, begin_def in type_function** — requires update_level_expand guard
6. **Stack-based cycle detection — TRY LAST** (regresses 607→220 on current branch, only after all above)
7. **Hard failures** — mario_game, reasonReact, defunctor_make_test

**NEVER change sexp_typedtree.rs cycle detection until step 6. It WILL regress.**

## Commit Rules

- Commit after each meaningful fix.
- Keep commits atomic (one concern).
- Include parity delta in commit message.
- Use DCO sign-off.

Example:

```bash
git add <files>
git commit -m "Fix: align <component> with OCaml <function>

Typedtree parity: 612 -> 614 / 657 (-dtyped-sexp-locs)

Signed-off-by: <name> <email>"
```

## Exit Condition

Output exactly:

```text
RALPH_COMPLETE
```

Only when all are true:
- `./scripts/test_typedtree_parity.sh` reports `SUCCESS: Full parity across all modules!`
- parser/binary parity guard remains fully green
- `RALPH_TODO.md` has no unchecked tasks remaining
