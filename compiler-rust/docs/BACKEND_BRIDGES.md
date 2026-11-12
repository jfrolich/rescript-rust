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
Before each package build it runs `rescript clean` so the shadow oracle sees
source compilation rather than an incremental cache hit, including when the
executable has embedded runtime interfaces. A corpus with zero reports is an
error, not successful coverage.
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
- `invalid float constant spelling`: the spelling cannot be parsed by the
  OCaml-compatible float parser. Valid spellings, including hexadecimal floats,
  infinities, NaNs and signed zero, are retained verbatim.
- `non-contiguous binder run`, `multiply bound identifier`,
  `distinct global identities with one name`: incompatible identity layout.
- `function arity outside u16`, `empty recursive binding group`: packed layout.
- `use count outside u32`, `use weight outside u32`: weighted count capacity.
- `reused static catch label`, `unbound static exit label`: catch-table layout.

The exporter also rejects JS-level nodes, released let values, missing legacy
identity metadata, unknown enum encodings, out-of-range integers, malformed
bigint sign markers and incompatible switch keys. These cannot be produced by
a successful unmodified Lambda import. Identity side tables retain only legacy
identifiers, not a hidden copy of the source tree. They never allocate stamps.

Bulk construction requires a fresh Bir. `finish_bulk` computes captures and
weighted uses before the tree is validated or edited. Import and export decode
each reachable source node once; explicit work stacks avoid Rust recursion.

## Unfinished JS bridge

`bridge::import_js` returns `Unsupported("JS arena import not implemented")`
for the whole JS program. No J-level conversion or J-level coverage is claimed
by the Lambda ratchet. This is the outstanding part of S2.2, not a completed
replacement backend or an S3 emitter.

## Float identity and folding

Float constants use an interned spelling and a cached IEEE-754 value. Different
spellings of the same value have different constant IDs. Interning performs one
text hash lookup followed by a dense string-indexed constant-cache access;
reading the value needs one constant-array read, not another parse. Recursive
constant blocks and options use the same pool. Lambda array elements are normal
constant nodes. Constructor/pointer decorations and switch keys already retain
their float spelling in their legacy metadata; they do not pass through the
numeric constant pool.

Future folding compares values, but printing preserves spelling. The current
legacy folders (`lambda/arena.rs::fold_prim`, `raw_lambda/lower.rs`) fold
float comparisons to booleans and float-to-int conversions to integers; they do
not synthesize float arithmetic results. OCaml's `js_exp_make.ml:1613-1637`
only folds integer operands in `float_add`/`float_minus`. Thus there is no current
float-result spelling rule to port. If a future fold synthesizes such a result,
it must reproduce the corresponding legacy operation, not reuse an arbitrary
equal operand's spelling. The existing numeric rendering rule (not arithmetic
folding) is `compiler/core/js_number.ml:42-57`: Infinity/-Infinity/NaN, an exact
integer if possible, otherwise the first round-tripping precision of 12, 15,
or 18 significant digits (`ocaml_float::js_number_to_string` in Rust).

Bulk import accumulates weighted uses once in the arena, indexed by variable
ID. `try_finish_bulk` reports weight/count overflow as `Unsupported`; a failed
partially finalized arena is discarded. No importer use-count maps are needed.
