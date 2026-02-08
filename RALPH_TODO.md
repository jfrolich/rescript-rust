# Ralph TODO: Typed Tree Parity (with Locations)

## Goal

Achieve 100% parity on the typed tree S-expression output (with locations) between the OCaml and Rust compilers. The test compares `-dtyped-sexp-locs` output from both compilers on all files in `tests/tests/src/`.

## Instructions for Agents

1. **NEVER revert commits made by other agents or humans** - If you think a commit is wrong, document your concerns but DO NOT revert it.
2. **Commit your changes frequently** - Follow the instructions in CLAUDE.md about committing.
3. **Follow the OCaml reference implementation exactly** - This is a 1:1 port. Do not invent new approaches. Read the OCaml code first, then replicate in Rust.
4. **GET TO THE ROOT CAUSE - DO NOT GIVE UP** - When investigating an issue, go deep. Do not stop at surface-level symptoms.
5. **Update this TODO when you discover work is already done** - Before starting a task, verify its current state.
6. **One task per session** - Complete one task, commit, stop. Each new task should start with a fresh context.

---

## ⚠️ ALWAYS USE TIMEOUTS — THE RUST COMPILER WILL INFINITE LOOP

The Rust type checker is incomplete and **WILL hang/infinite loop** on many inputs. You MUST wrap every invocation of the Rust compiler (`bsc`, test scripts, cargo test) with a timeout. **No exceptions.**

- **Single file tests:** `timeout 10 ./compiler-rust/target/release/bsc ...`
- **Test scripts:** `timeout 300 ./scripts/test_typedtree_parity.sh ...`
- **Cargo tests:** `timeout 120 cargo test ...`

If you run the Rust compiler without a timeout, it WILL hang indefinitely and block your entire session. The OCaml compiler does NOT have this problem — only the Rust compiler needs timeouts.

---

## How to Test

```bash
# Build the Rust compiler
cargo build --manifest-path compiler-rust/Cargo.toml --release

# Run the typed tree parity test suite (compares -dtyped-sexp output)
timeout 300 ./scripts/test_typedtree_parity.sh

# Test a single file (fastest for iteration — always use timeout!)
timeout 10 ./scripts/test_typedtree_parity.sh tests/tests/src/a.res

# Test files matching a pattern
timeout 60 ./scripts/test_typedtree_parity.sh "Core_Array"

# Quick mode (stop on first failure, show diff)
timeout 300 ./scripts/test_typedtree_parity.sh --quick

# Skip rewatch build (if already built)
timeout 300 ./scripts/test_typedtree_parity.sh --no-build

# With locations (ultimate goal)
timeout 300 ./scripts/test_typedtree_parity.sh --with-locs

# Manual comparison of a single file (ALWAYS use timeout on the Rust compiler)
echo 'let x = 1' > /tmp/test.res
./_build/install/default/bin/bsc -dtyped-sexp-locs /tmp/test.res 2>/tmp/ocaml.sexp
timeout 10 ./compiler-rust/target/release/bsc -dtyped-sexp-locs /tmp/test.res 2>/tmp/rust.sexp
diff /tmp/ocaml.sexp /tmp/rust.sexp
```

The test script:
1. Builds the test project with `rewatch` (using the OCaml compiler)
2. Gets compiler args for each file via `rescript compiler-args`
3. Runs both OCaml and Rust `bsc -dtyped-sexp` on each file
4. Diffs the stderr output (sexp goes to stderr)
5. Reports pass/fail counts

The `-dtyped-sexp` flag outputs the typed tree without locations. The `-dtyped-sexp-locs` flag includes locations. Our goal is parity on the **with-locs** variant.

---

## Current Status

**Last Updated:** 2026-02-08

|  | Status |
|--|--------|
| OCaml compiles | 659/659 |
| Rust compiles | 588/659 (71 fail) |
| Parity match (-dtyped-sexp) | 305/588 (51.9%) |

**Previous milestones completed:**
- Parser AST structure: 100% parity (sexp-locs 1196/1196)
- Syntax tests: 506/506 (100%)
- CMI loading and module resolution (0.2)
- Pipe-to-tuple distribution in desugar_pipe
- Path substitution for CMI-loaded modules (Tconstr rewriting)
- Module alias path rewriting (Belt.Array -> Pdot, not Pident)
- Qualified module paths for opened sub-modules (md_path on ModuleDeclaration)
- Fix _include_ path for non-ident include statements
- Fix type alias expansion: copy manifests during expansion to prevent corruption
- Propagate arity in arrow type unification

---

## Architecture Overview

```
ReScript Source (.res)
  -> Parser (compiler-rust/src/parser/)
  -> Parsetree (surface AST)
  -> PPX transforms (compiler-rust/src/binary_ast/ppx.rs)
  -> Parsetree (transformed)
  -> Type Checker (compiler-rust/src/types/)
  -> Typedtree (typed AST)    <-- THIS IS WHAT WE'RE COMPARING
  -> Lambda IR -> JS IR -> JavaScript
```

The type checker takes a Parsetree and produces a Typedtree. The Typedtree is the AST annotated with:
- Resolved paths (`Path.t`) for all identifiers
- Type expressions (`type_expr`) for all expressions and patterns
- Environments (`Env.t`) at each node
- Source locations (`Location.t`) at each node

---

## Reference Files

### OCaml (the reference implementation to match)

| File | Purpose |
|------|---------|
| `compiler/ml/typedtree.ml` | Typed AST implementation |
| `compiler/ml/typedtree.mli` | Typed AST type definitions — **primary reference** |
| `compiler/ml/sexp_typedtree.ml` | S-expression printer — **what we must match** |
| `compiler/ml/typecore.ml` | Expression/pattern type checking |
| `compiler/ml/typemod.ml` | Module type checking |
| `compiler/ml/typedecl.ml` | Type declaration checking |
| `compiler/ml/typetexp.ml` | Type expression translation |
| `compiler/ml/ctype.ml` | Core type operations / unification |
| `compiler/ml/env.ml` | Type environment |
| `compiler/ml/types.ml` | Core type representation |
| `compiler/ml/types.mli` | Core type representation interface |
| `compiler/ml/btype.ml` | Basic type operations |
| `compiler/ml/includemod.ml` | Module signature matching |
| `docs/TYPING.adoc` | Overview of the type checker architecture |

### Rust (our implementation)

| File | Purpose |
|------|---------|
| `compiler-rust/src/types/mod.rs` | Module root, re-exports |
| `compiler-rust/src/types/typedtree.rs` | Typed AST definitions |
| `compiler-rust/src/types/sexp_typedtree.rs` | S-expression printer (must match OCaml's) |
| `compiler-rust/src/types/typecore.rs` | Expression/pattern type checking |
| `compiler-rust/src/types/typemod.rs` | Module type checking |
| `compiler-rust/src/types/context.rs` | TypeContext with arena-based allocation |
| `compiler-rust/src/types/ctype.rs` | Core type operations (unify, generalize) |
| `compiler-rust/src/types/env.rs` | Type environment |
| `compiler-rust/src/types/type_expr.rs` | Type expression representation |
| `compiler-rust/src/types/decl.rs` | Type/value declarations |
| `compiler-rust/src/types/btype.rs` | Basic type operations |
| `compiler-rust/src/types/path.rs` | Module paths |
| `compiler-rust/src/types/asttypes.rs` | Common AST types |
| `compiler-rust/src/types/includemod.rs` | Signature matching |
| `compiler-rust/src/types/variance.rs` | Variance analysis |

---

## Key Areas for Improvement

### Rust Compilation Failures (91 files)

91 files fail to compile with the Rust type checker. Top error patterns:

| Error | Count | Description |
|-------|-------|-------------|
| UndefinedMethod | 24 | Module field access treated as method call |
| ExprTypeClash (FunctionCall) | 20 | Function call type mismatches |
| ExprTypeClash (general) | 19 | General type mismatches |
| PatternTypeClash | 6 | Pattern matching type issues |
| Stack overflow | 4 | Infinite recursion in type checker |
| Parse errors | 4 | Unsupported syntax |
| NotAVariantType | 2 | Variant type resolution |

### Parity Diff Categories (280 files with diffs)

Of the 566 files that compile, 286 match and 280 differ. Diff categories (overlap):

| Category | Files | Description |
|----------|-------|-------------|
| Module path | 229 | Pident vs Pdot differences |
| Cycle detection | 121 | OCaml prints `<cycle>`, Rust expands shared types |
| Arity (Some N vs None) | 66 | Arrow type arity annotations missing |
| Tvariant | 43 | Polymorphic variant type inference |
| Belt alias | 21 | Belt module alias name resolution |
| Stdlib prefix | 23 | Missing Pdot(Pident("Stdlib"), X) |
| Texp_open | 13 | Missing local open expression nodes |
| Pervasives prefix | 14 | Missing Pdot(Pident("Pervasives"), X) |
| Partial/Total | 11 | Pattern exhaustiveness |
| External encoding | 3 | External attribute string encoding |

### Root Causes (Highest Impact)

1. **Cycle detection in sexp output** (121 files): OCaml's `instance()` creates shared type nodes; the sexp printer detects these and prints `<cycle>`. Rust creates fresh nodes so sharing patterns differ. Fixing this requires either implementing OCaml-style type sharing in `instance()` or a two-pass sexp printer.

2. **Arrow type arity** (66 files): When creating arrow types during type checking, arity annotations (`Some(N)`) are not always propagated. Fix: ensure arity is set on all Tarrow types created during type inference.

3. **Module path qualification** (229 files): Various issues with module path resolution including local module paths, Belt alias resolution, and missing type path rewriting in various contexts.

### CMI File Loading (Task 0.2) ✅

Infrastructure for loading `.cmi` files (compiled module interfaces) has been implemented. This is critical for resolving external module references.

---

## Debugging Tips

1. **Start with simple files** - Test with `let x = 1`, `let f = x => x`, `type t = int` before complex files
2. **Compare sexp output side by side** - Pipe through `diff -u` for readable diffs
3. **Check both with and without locations** - Structural issues show up in both modes, location issues only in with-locs mode
4. **Read the OCaml type checker code** - When the Rust output is wrong, trace through the OCaml code to understand what it should produce

---

## Notes

- The OCaml sexp printer skips `Env.t` (never prints environments) and `Types.signature` (type field in structures)
- Ident stamps are skipped in both printers (only names are printed) for determinism
- `type_expr` is printed by following `Tlink` chains via `Btype.repr` in OCaml
- The `with_locs` parameter controls whether locations are included — both printers support this toggle
- `Texp_for` uses `Parsetree.pattern` (not `Typedtree.pattern`) for the loop variable pattern in OCaml
