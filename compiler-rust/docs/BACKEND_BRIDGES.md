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

## Normalising rules oracle (S4.1, stage `lambda-norm`)

In the same opt-in modes every unit is also checked against `LamArena`'s
smart constructors (`bir::shadow::check_norm`, `bir::replay`). The report
files of this stage are named `lambda-norm.<outcome>.json` beside the
bridge's; the harness counts each stage on its own and the ratchet file has
one entry per stage.

1. Replay. The arguments a smart constructor saw exist only inside
   `raw_lambda::lower::Lowering`. Raw nodes stay in the arena lowering
   returns, so the shadow lowers the raw root again on a copy of the arena
   with a recording hook (`lower_traced`; the default lowering is the same
   code with a hook that compiles to nothing) and gets every call lowering
   made to `if_`, `seq`, `prim`, `prim_with_id` and `make_apply`, with its
   arguments and result. It then builds the unit in a fresh `Bir` during
   bulk construction: nodes lowering built plainly are imported as they
   are; for a recorded call the arguments are built into a plain node and
   offered to the engine. The export must print like the lowered Lambda,
   before `collapse`.
2. Renormalisation. Lowering never calls `switch_with` or
   `string_switch_with` and builds some nodes plainly on purpose. The
   lowered unit is therefore also rebuilt bottom-up through every legacy
   smart constructor (`legacy_renormalise`) and compared with one
   normalising pass of the engine over the imported unit. This is what a
   pass that rebuilds a spine does to the nodes on it.

A difference in either is an error naming the unit, the comparison and the
first differing line. An unsupported shape is a counted fallback with the
bridge's reasons. The report records how many calls were replayed and which
rows of the rule table (BACKEND_REDESIGN.md C.5) fired; the harness prints
the totals per corpus. They are not part of the ratchet.

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

## Post-pass JS bridge (S3.1a)

`bridge_j::import_js` and `bridge_j::export_js` convert the post-pass dependency
program to J-level Bir and back into a fresh JsArena. The old S2.2 stub is not
this API. Every expression and statement kind is matched exhaustively; lists
and expression chains use explicit postorder stacks. Legacy identifiers,
ordered exports, the export set, name reservations, required modules and the
side-effect reason are preserved without allocating new stamps. File-level
directives and resolver settings are printer inputs, not JsArena fields; the
shadow comparison must supply the same inputs to both printers.

The bridge does not run optimizations or change the emitter. No J-level
coverage is implied by the existing Lambda-stage ratchet. Representation limits
are explicit `Unsupported` values: shared unbounded non-leaf nodes, repeated
binders, non-contiguous parameter runs, invalid float spelling or template
segment counts, and a try without either handler or finaliser. Shared leaves
and at most four-child shapes whose children are leaves are copied per edge;
this bounds expansion rather than unfolding a potentially exponential DAG.
These are never silently changed into another shape. Full module metadata is
stored in the J import pool; the remaining printer metadata fits the existing
J payloads and auxiliary words (BACKEND_REDESIGN.md B.3/B.5).

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

## J-level shadow stage (`js-bridge`)

Both opt-in backend modes now check the post-pass JS program immediately before
printing. The original and the exported program use the legacy printer with the
same resolver, file directives, debug/JSX options and header choice. Unsupported
representations are reported by reason; a mismatch or invalid Bir is a compiler
error naming the source unit. Default mode does not import or print a second
program. The coverage harness ratchets `js-bridge` separately; Lambda stage
counts are unchanged. The emitter and its view trait are not part of this slice.

## J bridge costs and variable facts

Import and export are iterative postorder traversals. Work/result stacks and
export list buffers are reused; metadata is stored in the existing side pools.
The importer allocates encounter bitmaps once, indexed by legacy node slots.
A repeated non-leaf is supported only when its expansion is constant-size
(at most four leaf children). Thus costs are linear in input nodes and list
entries even for sharing: arbitrary DAGs do not expand exponentially. The
10,000-statement and 10,000-term concatenation/comma/logical-chain tests bound
import visits and export arena accesses, without recursing through the printer.
The bridge uses the existing Bir bulk constructors; those constructors still
use SmallVec scratch for child/binder lists and debug-only duplicate checks.

Bulk finalization establishes Var-node use counts, binder links, parameter
facts/flags, export flags, captured flags and assignment flags. SDecl gets the
existing constant, alias, function, block/mutable-block and optional facts;
unknown values stay Unknown. No J normalization or stronger constant/purity
analysis is claimed. For-of/await-of and catch bindings keep Unknown facts,
matching the current editing API. Unbound legacy identities are marked JS_GLOBAL
so they remain representable, including undeclared exports after a throw.

`SForRangeExisting` represents a range that reuses an already declared variable
(`init: None`), rather than binding that VarId twice. Its explicit Var child
counts the header use; the target is ASSIGNED, and variables encountered in
this loop are conservatively CAPTURED (including locals). This is deliberately
conservative until J rounds refine the capture boundary rules. `SRest` with aux
bit 15 retains the legacy RecordRest value descriptor, including its own cold
metadata, while exposing all destructured binders through SRest's existing
binder schema. Its field/rest facts remain Unknown. This is distinct from a
future SRest built directly from the source object.

An explicit `Some(LamLoc::NONE)` is retained, not confused with no location:
J nodes use JS_LOC_PRESENT; clause locations use Option<LamLoc> (still four
bytes). Character decoration, which need not equal the integer value, is kept
in a spare JNumber word with JS_CHAR_PRESENT; the constant fact remains the
actual integer. Negative static field positions are retained by using the
same i32::MIN sentinel as JsArena.
