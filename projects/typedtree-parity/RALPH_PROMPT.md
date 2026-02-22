# Ralph Loop: Typed Tree Parity (with Locations)

You are working on achieving **100% typedtree parity** between the Rust compiler and the OCaml reference implementation using `-dtyped-sexp-locs`.

## Verified Baseline (2026-02-17)

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Typedtree parity (`-dtyped-sexp-locs`): **612/657** (45 diffs)
- Parser/binary parity guard is fully green

This loop is currently stalled by process drift (docs-only revalidation and no unchecked tasks), not by lack of remaining work.

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

# Deterministic typedtree parity baseline
timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1

# Quick single-file probe
timeout 60 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1 --quick tests/tests/src/<file>.res

# Parser/binary guard (must stay green)
timeout 300 ./scripts/test_parser_ast_parity.sh 2>&1 | tail -40
```

Never run Rust compiler/test commands without timeout.

## Failure-Driven Workflow

1. Generate current failing-file manifest from deterministic run.
2. Group failures by shared root cause (first divergent typedtree node path).
3. Prioritize by cluster size and risk.
4. Solve one cluster at a time with OCaml-aligned changes.
5. Require parity delta after each successful fix.

Seed clusters to prioritize:
- Set/map cycle-sharing drift (`bs_mutable_set_test.res`, `bs_set_int_test.res`, `bs_poly_map_test.res`, `test_set.res`, `bs_queue_test.res`)
- Option/constructor identity drift (`option_repr_test.res`)
- Labeled/optional application drift (`jsx_optional_props_test.res`)
- Residual syntax/typing drift (`miss_colon_test.res`)

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
- `timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`
  - reports `Rust bsc: 657 passed, 0 failed`
  - reports `Parity: 657 passed, 0 failed`
- parser/binary parity guard remains fully green
- `RALPH_TODO.md` has no unchecked tasks remaining
