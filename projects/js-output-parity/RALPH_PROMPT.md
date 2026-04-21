# Ralph Loop: JS Output Parity

## ⚠️ MANDATORY FIRST TASK — DELETE THE MONOLITH

**Before doing ANYTHING else, you MUST delete `simplify_with_env` and the entire
`SimplifyEnv` struct from `compiler-rust/src/lambda/simplify.rs`.** Delete all
~114 helper functions that only feed the monolith. This is ~15,000 lines of code
that must go.

Then wire up the OCaml pipeline from `lam_compile_main.ml:148-200` using:
- Passes you already ported: `pass_exits`, `pass_lets_dce`, `pass_count`
- Stubs (identity functions) for passes not yet ported: `collect_info`, `remove_alias`, `alpha_conversion`, `deep_flatten`

**Parity WILL regress. That is expected and required.** Do NOT try to preserve
the current score. Do NOT add workarounds. Fix regressions only by porting more
OCaml code faithfully.

Read `PERFORMANCE_PLAN.md` for the full plan and `PLAN.md` for constraints.

---

You are working on achieving **100% emitted JavaScript parity** between the
Rust compiler and the OCaml reference implementation using the checked-in JS
snapshots.

## Current Baseline

Use the latest measured baseline from `RALPH_TODO.md`.

The authoritative command is:

```bash
timeout 1800 ./scripts/test_js_output_parity.sh
```

This keeps Spice PPX parity enabled as a guard and measures the JS snapshot
section through the existing parity harness on the canonical 657-file in-repo
set by default. Use `--with-external` only as a secondary sweep.

## Upstream Status

For this project, assume the upstream parity stages are already complete:

- typedtree parity: **657/657**
- raw lambda parity: **657/657**
- optimized lambda parity: **657/657**

There are no open issues to solve there. The remaining work is in the backend
after optimized lambda.

## Core Principle: 1:1 OCaml Backend Port

- **Read OCaml first** before touching Rust.
- **Do not treat JS diffs as a printer-only problem by default.**
- **Do not fix emitted JS by adding ad hoc string rewrites.**
- **Do not keep the legacy typedtree -> `LambdaCompiler` shortcut as the long-term JS path.**
- **Do not spend time reopening typedtree or lambda parity work. Those stages are already green.**
- **Match the OCaml backend stage boundaries exactly.**

Primary OCaml references:

- `compiler/core/lam_compile_main.ml`
- `compiler/core/lam_compile.ml`
- `compiler/core/lam_coercion.ml`
- `compiler/core/j.ml`
- `compiler/core/js_pass_*.ml`
- `compiler/core/js_dump_program.ml`
- `compiler/core/js_dump.ml`

Primary Rust implementation files:

- `compiler-rust/src/driver.rs`
- `compiler-rust/src/raw_lambda/convert.rs`
- `compiler-rust/src/raw_lambda/lower.rs`
- `compiler-rust/src/lambda/compile.rs`
- `compiler-rust/src/js_ir/mod.rs`
- `compiler-rust/src/js_ir/printer.rs`

## Correctness Rule

If a change is **verified OCaml-aligned**, keep it and commit it even if local
parity or hunk counts temporarily regress.

Parity numbers are navigation tools, not the definition of correctness.

## Your Loop

For each iteration:

1. **Check: is `simplify_with_env` deleted?** If NO, delete it now. That is your
   only task until it's gone.
2. **Check: is the OCaml pipeline wired up?** If NO, wire it up with stubs.
3. **Check: are all passes from PERFORMANCE_PLAN.md ported?** If NO, port the
   next one (collect_info, remove_alias, deep_flatten, alpha_conversion).
4. Only after ALL of the above are done: pick parity clusters and fix them by
   reading the OCaml source and porting behavior faithfully.
5. Run the authoritative baseline, commit, update RALPH_TODO.md.

Only stop if:

- full JS snapshot parity is reached, or
- there is a genuine hard blocker that requires human input.

## Required Commands

Always use timeouts for compiler invocations.

```bash
# Build Rust compiler
timeout 600 cargo build --manifest-path compiler-rust/Cargo.toml --release

# Authoritative JS baseline
timeout 1800 ./scripts/test_js_output_parity.sh

# Faster direct single-file repro against a checked-in snapshot (.mjs example)
timeout 10 ./compiler-rust/target/release/bsc \
  -bs-package-name rescript-tests \
  -bs-module-type esmodule \
  tests/tests/src/ExternalShadow.res \
  -o /tmp/ExternalShadow.mjs
diff -u tests/tests/src/ExternalShadow.mjs /tmp/ExternalShadow.mjs | sed -n '1,220p'

# CommonJS / .bs.js example
timeout 10 ./compiler-rust/target/release/bsc \
  -bs-package-name rescript-tests \
  /absolute/path/to/file.res \
  -o /tmp/file.bs.js
diff -u /absolute/path/to/file.bs.js /tmp/file.bs.js | sed -n '1,220p'
```

## Prioritization

1. **Correct the backend routing in `driver.rs`**
   - stop compiling final JS from the legacy `LambdaConverter` shortcut
   - route codegen through the raw-lambda / lowering path
2. **Eliminate compile-error clusters**
   - crashes and hard compile failures are higher priority than textual diffs
3. **Port the OCaml backend stages in order**
   - lambda passes
   - coercion/grouping
   - lambda/group -> JS IR lowering
   - JS passes
   - final dump/print
4. **Use small internal files first**
   - validate one backend rule at a time before attacking large external files
5. **Treat printer work as the last mile**
   - only do printer-only fixes after the IR/path is clearly aligned

## Commit Rules

- Commit every verified OCaml-aligned improvement immediately.
- Keep commits atomic.
- Include baseline deltas in the commit message when available.
- Use DCO sign-off.

Example:

```bash
git add <files>
git commit -s -m "js-output: route backend through raw-lambda lowering

JS snapshot parity: 0 -> 12 / 2784
Compile errors: 1928 -> 1871
Output diffs: 856 -> 901"
```

## Exit Condition

Only when all are true:

- `./scripts/test_js_output_parity.sh` reports full parity
- `RALPH_TODO.md` has no unchecked tasks remaining
- typedtree, raw lambda, and optimized lambda guards still pass where applicable

Do not output or mention `RALPH_COMPLETE` early.
