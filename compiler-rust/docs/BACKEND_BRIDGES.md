# Backend bridge oracle (S2.2)

The default backend remains `Legacy`. Set `RESCRIPT_BACKEND=check` to import
lowered Lambda into Bir, validate it, export it with raw Lambda constructors,
and compare the existing `sexp_lambda` dumps. Differences are errors naming
the unit, stage and first differing line. `Unsupported` leaves the legacy path
in use. `RESCRIPT_BACKEND=new` currently exercises the same bridge check:
replacement lowering does not exist in this stage. Neither opt-in mode changes
which JavaScript is emitted. Unknown environment values select `Legacy`.
`CompilerOptions.backend` can also select a mode directly.

Set `RESCRIPT_BACKEND_STATS` to a fresh **directory** to collect JSON reports,
grouped by source unit. Outcome files are immutable across processes; if
multiple output modes revisit a unit, any fallback wins over success. They contain unit paths,
not source or generated text. Delete old reports before starting a new run, or
use the harness, which always creates fresh temporary report directories.

After building rewatch and the OCaml reference prerequisites, run:

```sh
python3 scripts/test_backend_coverage.py --target debug
```

The harness checks the runtime, tests/tests and focused JS parity fixtures.
Every supported import is validated. The committed `tests/backend_coverage.txt`
ratchet requires that unit coverage and the supported share do not fall and
that neither total fallbacks nor any reason's count grows. `--record` explicitly
updates that baseline; it is never used in CI. Corpus units are implementations
that reach the backend, not interfaces; dependencies are excluded from the
runtime and tests/tests totals. Fixture units include the fixture harness's
compilation inputs, across its output modes; a source compiled in several modes
is counted once, with a fallback if any mode was unsupported.

## Representation limits

Lambda import preserves all node kinds but can return these static reasons:

- `shared Lambda node`: Bir is a tree; expanding a DAG can be exponential.
- `float constant spelling`: Bir stores bits, but the identity oracle preserves
  the legacy spelling (including noncanonical and hexadecimal spellings).
- `non-contiguous binder run`, `multiply bound identifier`,
  `distinct global identities with one name`: incompatible identity layout.
- `function arity outside u16`, `empty recursive binding group`: packed layout.
- `reused static catch label`, `unbound static exit label`: catch-table layout.

The exporter also rejects JS-level nodes, released let values, missing legacy
identity metadata, unknown enum encodings, out-of-range integers, malformed
bigint sign markers and incompatible switch keys. These cannot be produced by
a successful unmodified Lambda import. Identity side tables retain only legacy
identifiers, not a hidden copy of the source tree. They never allocate stamps.

Bulk construction requires a fresh Bir. `finish_bulk` computes captures and
weighted uses before the tree is validated or edited. Import and export decode
each reachable source node once; explicit work stacks avoid Rust recursion.
