# Error Output Parity Plan

## Goal

Make user-facing parse errors and compiler/typechecker errors match the OCaml
compiler exactly when the same invalid ReScript file is compiled with the Rust
compiler.

The oracle is always the OCaml implementation in this branch. The harness should
compare OCaml output to Rust output directly, not to hand-maintained snapshots.
Snapshots can still exist for existing tests, but they are not the parity source
of truth.

## Implementation Rule

Implementation fixes should follow the OCaml implementation 1:1 as much as
possible. When an error differs, read the relevant OCaml source first and port
the same control flow, location choice, warning/error ordering, and reporting
logic into Rust instead of adding output-specific special cases.

Any compiler/parser code added for this project should be treated as a direct
port of the OCaml implementation first. Prefer matching the OCaml data flow and
error constructors over patching only the final rendered text. If the Rust code
needs to differ for local architecture reasons, document the reason in the code
or commit message and keep the externally visible diagnostic behavior
byte-for-byte identical.

## Existing Work To Reuse

Parser diagnostics already have a project and matrix:

- `projects/parser-diagnostics-parity/PLAN.md`
- `projects/parser-diagnostics-parity/INVENTORY.md`
- `tests/syntax_tests/data/parsing/diagnostics_numbers.csv`
- `scripts/check_parser_diagnostics_numbers.sh`

The new harness reuses that parser matrix and adds compiler/typechecker error
coverage.

Existing compiler error fixtures:

- `tests/build_tests/super_errors/fixtures`

Those fixtures are useful as an initial broad corpus, but they are not exhaustive
by OCaml error variant. The exhaustive suite should be driven by source
inventory, then mapped to minimal fixtures.

## Harness

New script:

```bash
./scripts/test_error_output_parity.sh
```

What it does:

1. Runs parser diagnostics fixtures from
   `tests/syntax_tests/data/parsing/diagnostics_numbers.csv` through
   `res_parser` and `res_parser_rust`. Parser error rows use
   `-jsx-version 4 -recover -print ml` so recovered invalid parse trees follow
   the OCaml driver path that prints diagnostics without applying JSX PPX
   rewrites.
2. Runs compiler diagnostics fixtures through OCaml `bsc` and Rust `bsc`.
3. Compares parser exit status and combined stdout/stderr byte-for-byte with no
   output normalization.
4. Compares compiler exit status and stderr byte-for-byte with no output
   normalization. Compiler stdout is captured separately as `.stdout` only to
   aid debugging.
5. Writes outputs and diffs under `.parity-cache/error-output/`.

Useful commands:

```bash
# Build prerequisites
eval $(opam env --shell=sh) && make lib
cargo build --manifest-path compiler-rust/Cargo.toml

# All current parser and compiler diagnostics fixtures
./scripts/test_error_output_parity.sh

# Parser only
./scripts/test_error_output_parity.sh --parser-only

# Compiler/typechecker only
./scripts/test_error_output_parity.sh --compiler-only

# One fixture or substring
./scripts/test_error_output_parity.sh --compiler-only arity_mismatch
```

The compiler fixture extension point is:

- `tests/error_output_parity/compiler/fixtures/*.res`
- `tests/error_output_parity/compiler/fixtures/*.resi`
- `tests/error_output_parity/compiler/cases.tsv`

Use `cases.tsv` when a fixture needs non-default flags.

## Fixture Policy

Each fixture should have one primary diagnostic target.

Add a short comment at the top when the target is not obvious:

```rescript
// error-output-parity: Typecore.Apply_non_function
1(2)
```

For multi-file cases, keep the dependency next to the failing fixture and add the
exact command flags to `cases.tsv`.

Avoid using generated snapshots as the source of truth. The check should pass
when OCaml and Rust match today, and fail whenever Rust diverges from OCaml.
Paths and color behavior must be made stable by invoking both compilers the same
way, not by rewriting their output after the fact.

## Source Inventory

Compiler/typechecker error variants should be inventoried from these OCaml
sources first:

- `compiler/ml/typecore.ml`
- `compiler/ml/typetexp.ml`
- `compiler/ml/typedecl.ml`
- `compiler/ml/typemod.ml`
- `compiler/ml/includemod.ml`
- `compiler/ml/includecore.ml`
- `compiler/ml/env.ml`
- `compiler/ml/rec_check.ml`
- `compiler/ml/syntaxerr.ml`
- `compiler/ml/translcore.ml`
- `compiler/ml/translmod.ml`
- `compiler/ml/transl_recmodule.ml`
- `compiler/ml/ast_untagged_variants.ml`
- `compiler/ml/cmi_format.ml`

The starting inventory is in `COMPILER_ERROR_INVENTORY.md`.

For each OCaml error variant:

1. Find where it is raised.
2. Create the smallest `.res` or `.resi` file that reaches that branch.
3. Verify OCaml emits that branch by reading the raise site and report function.
4. Add the fixture and map it to the variant.
5. Run the parity harness.
6. Fix Rust diagnostics/reporting to match OCaml.

If a variant is genuinely unreachable from normal ReScript source, document it
as `unreachable` with the source-level reason instead of forcing a fake test.

## Phases

1. Lock the inventory and coverage matrix.
   - Every parser diagnostic category is already covered by the parser matrix.
   - Add compiler/typechecker rows for every OCaml error variant.

2. Seed compiler fixtures.
   - Start by mapping existing `super_errors` fixtures to OCaml variants.
   - Add new reduced fixtures only for uncovered variants.
   - Prefer direct `bsc` cases over build-system cases unless package setup is
     needed to trigger the error.

3. Compare and fix.
   - Run `./scripts/test_error_output_parity.sh --compiler-only`.
   - For each diff, read the OCaml report function before changing Rust.
   - Fix Rust error construction, location selection, message text, or renderer
     formatting as appropriate.

4. Gate regressions.
   - Keep the direct OCaml-vs-Rust script as the authority.
   - Add CI/local target once the known corpus is stable enough.

## Acceptance Criteria

- Parser diagnostics match for the numbered parser matrix.
- Compiler diagnostics match for every reachable OCaml compiler/typechecker
  error variant.
- Any unreachable/internal variants are documented with source links and reason.
- The Rust compiler does not panic or hang on any diagnostic fixture.
- The parity script exits non-zero on any exit-status or output mismatch.
