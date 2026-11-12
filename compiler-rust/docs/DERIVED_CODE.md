# Derived-code cost census

`@spice` expands types into ordinary syntax, behind `binary_ast::derive`.
That syntax pays the same frontend, checking, Lambda and JavaScript costs as
handwritten functions. This audit does **not** change the generated codecs or
add a typechecker shortcut. Byte-identical JavaScript and the same diagnostics
remain requirements, including a referenced type with no codec in scope.

## Reproduction

Build a normal fat-LTO release, not a thin-LTO or debug binary:

```sh
cargo build --release --manifest-path rewatch/Cargo.toml
export RESCRIPT_RUNTIME="$PWD/packages/@rescript/runtime"
export RAYON_NUM_THREADS=1
rewatch/target/release/rescript clean tests/ppx_spice
# Choose a new output file: the census appends; it does not truncate.
RESCRIPT_DERIVED_CENSUS=/tmp/derived-fixture.jsonl RESCRIPT_PHASE_TIMINGS=1 \
  rewatch/target/release/rescript build tests/ppx_spice
python3 scripts/derived_census_summary.py /tmp/derived-fixture.jsonl \
  --modules-from tests/ppx_spice/src
```

Use the same commands with a large application's directory in place of
`tests/ppx_spice`, and omit `--modules-from` to include dependencies. A build
which finds everything up to date has no compiled modules to report: clean
first. Runtime and package dependencies must be installed as for a normal build.

For **checker counts**, additionally set `RESCRIPT_COMPILER_COUNTERS=1` and
keep `RAYON_NUM_THREADS=1`. The four columns are fresh variables, top-level
unifications, nodes copied by instance sessions, and lazy environment cache
hits plus misses. These are the existing counters, not new per-node probes.
They are process-global; concurrent item attribution is unavailable, not zero.
The JSON field is null when counters are disabled or more than one worker is
requested. Run this separately from timing measurements: the existing graph
censuses and allocation-site counters are expensive and perturb timings.
Runtime compilation may use a separate pool; these process-counter deltas are
not an isolation guarantee for arbitrary concurrent compilation clients.

The variable is read in one source location, at compiler-option creation.
Each compilation owns its record, carries it through the worker boundary and
appends one JSON line under one output lock. No timer is called by census
probes when the option is absent. Records identify module basenames and the
implementation/interface kind, not absolute paths. A failed compilation may
stop before emitting its record; the census is not a replacement for the
build's diagnostic log.

## Attribution and schema

Times are integer nanoseconds. Each phase has `derived`, `other` and
`estimated` fields. Generation is timed inside the derive. Typechecking is
item-exclusive: nested structure-item intervals are subtracted from their
parents. Raw-Lambda value-group translation is measured after translation of
the continuation, so recursive traversal does not double-charge the tail.
Remaining module-level work is explicitly distinguished:

- Frontend rewrite/validation, remaining Lambda lowering, Lambda passes,
  JavaScript lowering and printing use the module's syntax-node proportions.
  They are **estimates**, not per-function profiler samples.
- Typechecking overhead outside the item loop, environment setup and signature
  publication are charged to other work.
- JavaScript byte and line totals are actual emitted totals, but their split is
  estimated using syntax weights. Syntax weight is not a source map and cannot
  prove the exact bytes contributed by a particular binding.
- Body sizes are generated, pre-rewrite node occurrences. Module syntax counts
  are post-rewrite occurrences; these are different populations.
- Parameterised and recursive-group rows overlap the base shape classes.
- Template keys retain complete encoded structure, rather than a lossy hash.
  Names of local types, fields, constructors, generated field variables and
  parameter-codec arguments are normalized. Explicit keys and source defaults
  retain their values. Locations, arena indices and sharing are excluded.
  Syntax with a scalar payload not handled by the key encoder has a null key;
  it is never merged with another binding by an approximate fingerprint.
- The summary counts distinct keys **among supported bindings**, and reports
  unsupported bindings beside that number. Its size-weighted fraction is the
  sum of one body size per distinct supported key divided by all generated
  binding-body nodes. Unsupported bodies still have to be processed individually.

Syntax counts are recorded during the existing validation traversal, not in a
second observer pass. The ordinary compiler specializes counting away; the
census specialization visits certified expression subtrees to count them. If
builtin validation is disabled, the same visitor only counts syntax, without
issuing warnings. Attribute payloads are metadata and excluded from these
module syntax weights. Shape/body keys are collected together at generation.
The provenance bitmap uses binding-pool start slots, not a newly introduced
structure-item index.

## Fixture project

The project is the existing `tests/ppx_spice` corpus, with a build configuration
that enables the builtin mapper. It covers records, optional fields, renamed
keys, payload and payload-free variants, aliases, polymorphic and unboxed
variants, tuples, options, arrays, dictionaries, results, parameters and
recursive serde shapes. Additional fixtures cover lists, plain recursive and
mutually recursive types, and an abstract type exported with custom codecs.
The `errors/` directory contains derive failures; they are not part of a
successful timing build. Exhaustive checker-error coverage is not claimed.

### Current fixture observation

Linux x86-64, fat-LTO release at `66b8bc4e0`, one worker, one clean build.
29 implementation files and six interfaces; dependencies excluded. This is a
timing observation, not an optimization speedup claim.

Modules/interfaces: 35

| Phase | Derived ms | Other ms | Attribution |
|---|---:|---:|---|
| parse_other | 0.000 | 7.193 | measured |
| generation | 3.244 | 0.020 | measured |
| frontend | 1.906 | 0.405 | node-weighted estimate |
| environment | 0.000 | 1.363 | measured |
| typecheck | 57.758 | 18.612 | measured |
| signature | 0.000 | 2.405 | measured |
| conversion | 17.831 | 1.183 | measured |
| lambda_lowering | 3.985 | 0.371 | node-weighted estimate |
| lambda_passes | 9.611 | 0.741 | node-weighted estimate |
| lowering | 27.181 | 1.642 | node-weighted estimate |
| printing | 5.028 | 0.439 | node-weighted estimate |
| gentype | 0.000 | 0.000 | measured |

| Size | Derived | Other |
|---|---:|---:|
| bindings | 401 | 53 |
| syntax_nodes | 33447 | 2805 |
| js_bytes (estimated split) | 426486 | 26062 |
| js_lines (estimated split) | 15124 | 1139 |

Counter availability: 0/35 records.

| Shape | Bindings | Min nodes | P50 | P90 | P99 | Max |
|---|---:|---:|---:|---:|---:|---:|
| constructor_application | 69 | 5 | 7 | 9 | 21 | 21 |
| parameterised (overlap) | 18 | 25 | 45 | 234 | 595 | 595 |
| polymorphic_variant | 40 | 14 | 36 | 228 | 405 | 405 |
| record | 102 | 21 | 42 | 171 | 719 | 929 |
| recursive group (overlap) | 27 | 21 | 68 | 446 | 1133 | 1133 |
| tuple | 9 | 18 | 44 | 188 | 188 | 188 |
| variant | 181 | 13 | 48 | 234 | 799 | 1133 |

Distinct templates: 239 among 401 supported bindings; duplicate bindings: 162; unsupported templates: 0.
Distinct-template body nodes: 26352 / 32909 (80.1%); unsupported body nodes: 0.
Singleton templates: 118; highest frequencies: [6, 6, 6, 6, 4, 4].

A separate counter-enabled run reports all 35 fixture records:

| Checker counter | Derived | Other |
|---|---:|---:|
| Fresh variables | 23,221 | 3,112 |
| Top-level unifications | 61,223 | 3,315 |
| Instance copied nodes | 64,459 | 2,600 |
| Lazy environment lookups | 37,723 | 789 |

## A 3,735-module application

Supplied measurement: one-worker clean release build at `1898b2100`, 3,841
census records including dependencies. These numbers are retained as measured;
they are not silently replaced by a later run on another machine.

| Phase | Derived ms | Other ms | Attribution |
|---|---:|---:|---|
| Generation inside derive | 32.5 | 1.2 | measured |
| Frontend rewrite and validation | 19.7 | 141.6 | node-weighted estimate |
| Typechecking | 333.9 | 1,659.6 | measured item-exclusive |
| Conversion to Lambda | 79.0 | 243.5 | measured value-group translation |
| Lambda lowering | not recorded | not recorded | timer-enablement defect at cited head |
| Lambda passes | not recorded | not recorded | timer-enablement defect at cited head |
| JavaScript lowering | not recorded | not recorded | timer-enablement defect at cited head |
| Printing | 41.0 | 151.9 | node-weighted estimate |
| Parsing | 0 | 377.3 | measured |

The cited head wrote zero in the three missing buckets when the census was
used without a phase-timing flag: an earlier `timing::enabled()` call could
cache false before option creation. Enabling census timing must update that
cached flag, not attempt a second `OnceLock::set`. Zero was a measurement bug,
not evidence that these phases were free.

| Size | Derived | Other or total |
|---|---:|---:|
| Bindings | 7,200 | 23,664 other |
| Syntax nodes | 606,277 | 1,750,063 other |
| JavaScript bytes (estimated split) | 8.04 MB | 29.85 MB total |
| JavaScript lines (estimated split) | 233,738 | 899,776 total |

Derived syntax is 25.7% of the nodes; measured derived checking is 16.8% of
checking and conversion is 24.5% of conversion. The build takes approximately
5,200 ms with one worker. The reported derived phase subtotal is about 506 ms,
9.7% of the build, **before** the missing Lambda/backend work. A node-weighted
projection adds roughly three percentage points; that projection is not an
additional measured interval.

| Shape | Bindings | Min nodes | P50 | P90 | P99 | Max |
|---|---:|---:|---:|---:|---:|---:|
| Record | 5,988 | 21 | 45 | 171 | 589 | 4,584 |
| Variant | 637 | 5 | 30 | 111 | 1,355 | 2,775 |
| Constructor application | 518 | 5 | 5 | 7 | 72 | 98 |
| Polymorphic variant | 57 | 13 | 28 | 81 | 147 | 147 |
| Parameterised (overlap) | 9 | — | — | — | — | — |
| Recursive group (overlap) | 6 | — | — | — | — | — |

There are **2,865 distinct normalized templates among 7,197 supported
bindings**, with three unsupported. Of those templates, 1,246 occur once;
the highest frequencies are 278, 226, 154, 139, 124 and 104. The supplied size-weighted estimate is **64.5%** for one copy of each
distinct supported template. The denominator matters: the local follow-up
counts 381,608 distinct supported nodes out of 591,813 supported body nodes
(64.5%). Including 4,846 unsupported nodes gives 596,659 total body nodes;
retaining those individually as well would retain 64.8% of all body nodes. Repetition by
binding count therefore exaggerates the work removable by template sharing:
the large codecs are often unique. Checking each template once could remove
only about a third of derived body checking under a node-proportional cost
model, not most of it. That is a model, not a measured typechecker shortcut.

### Local follow-up: previously missing backend buckets

A separate Linux x86-64 fat-LTO release run at `66b8bc4e0`, one worker and
3,841 records, verifies the fixed buckets. Do not add these measurements to
the supplied application table: they are from a different machine/run.

| Phase | Derived ms | Other ms | Attribution |
|---|---:|---:|---|
| Lambda lowering | 51.106 | 236.405 | node-weighted estimate |
| Lambda passes | 146.611 | 450.175 | node-weighted estimate |
| JavaScript lowering | 232.839 | 890.563 | node-weighted estimate |

The local follow-up reproduces 2,865 supported distinct templates, three
unsupported bindings, 1,246 singletons and the same six highest frequencies.
Its parse total reconciles within 0.052%, typechecking within 0.099%, and
Lambda, optimization and codegen within rounding. Use canonical project and
runtime paths (`realpath`) when invoking the build directly; the benchmark and
comparison scripts already canonicalize their project argument.

## Reductions tested

All fixture comparisons below used fat-LTO release binaries, one worker,
clean builds and no census/counter instrumentation. The corpus was the original
28-implementation fixture sample. Cachegrind minima are taken separately for
each binary; the measurements are not CI results.

| Candidate | Before Ir | After Ir | Result |
|---|---:|---:|---|
| Certify simple generated functions/local bindings | 1,967,311,972 | 1,967,470,634 | +0.0081%; **discarded** |
| Eliminate path vectors, pre-size codec bindings, move final encoder | 1,967,311,972 | 1,966,047,515 | −0.0643%; retained |

The certificate experiment reused child proofs and only admitted non-async,
single-parameter functions with variable/wildcard patterns and no defaults,
and lets with attribute-free variable/wildcard bindings. Matches, constraints,
raw/template expressions, structural patterns, modules, attributes and async
or n-ary function metadata still needed the normal mapper/validation paths.
The extra proof work outweighed the few skipped visits. Four cachegrind
candidate runs and five baseline runs supplied the minima above. No certificate
extension is left in the code and no saving is claimed for it.

The retained allocation change followed a callgrind profile: the former
`longident_matches` and its collector accounted for 614,060 self instructions
in one fixture build, before accounting for allocator callees. It now compares
borrowed path segments iteratively, using constant stack space and no temporary
vector. A 10,000-segment test verifies 10,000 comparisons. Codec declaration
vectors reserve their exact zero-to-three binding count, and the final encoder
is moved instead of cloned again. Five cachegrind runs per side supplied the
retained result.

Both reductions preserved all 71 compared signatures and 28 generated
JavaScript files; both fixture builds emitted zero diagnostics. This successful
fixture comparison alone is not coverage of derive/checker error diagnostics.

Hyperfine (five runs, one warmup, clean before every run):

| Experiment | Before mean ± SD | Before min–max | After mean ± SD | After min–max |
|---|---:|---:|---:|---:|
| Certificates, discarded | 309.3 ± 27.3 ms | 273.4–348.3 ms | 278.6 ± 12.0 ms | 268.5–299.0 ms |
| Allocation, retained | 267.3 ± 13.5 ms | 252.5–285.8 ms | 376.1 ± 45.2 ms | 322.9–431.0 ms |

Wall times disagree with the instruction evidence. They demonstrate no
reliable wall-time saving. Do not present the allocation change as a measured
wall-time speedup.

The allocation change also passed an application comparison: **3,735
signatures, 32 diagnostics in 18 files, and 3,980 generated files are unchanged**.
The final census-fix release was separately compared with the saved allocation
candidate, with the same result. One application cachegrind run per side:

| Metric | Before | Allocation candidate |
|---|---:|---:|
| Instructions | 69,341,998,656 | 69,315,789,769 |
| Instructions/source line | 105,595.291 | 105,555.379 |
| Generated files | 3,980 | 3,980 |

This is **−0.0378% instructions**, not a repeated application timing benchmark.
The compared source population has 656,677 lines including dependencies and
build copies. The ordered generated-output digest is identical on both sides:
`0a3d301322cf7febdbf8793ae8c3dcbc1ecbadf44670c3b52cecbc5437a02408`.
Use `scripts/bench_project.sh PROJECT BEFORE AFTER --runtime-from CHECKOUT`
to repeat the output/instruction comparison.

Reproduce comparisons with saved before/after release executables:

```sh
export RESCRIPT_RUNTIME="$PWD/packages/@rescript/runtime" RAYON_NUM_THREADS=1
BEFORE clean tests/ppx_spice
valgrind --tool=cachegrind --cachegrind-out-file=before.cg BEFORE build tests/ppx_spice
AFTER clean tests/ppx_spice
valgrind --tool=cachegrind --cachegrind-out-file=after.cg AFTER build tests/ppx_spice
python3 scripts/compare_checker_builds.py tests/ppx_spice BEFORE AFTER
hyperfine --runs 5 --warmup 1 --prepare 'BEFORE clean tests/ppx_spice' \
  'BEFORE build tests/ppx_spice' 'AFTER build tests/ppx_spice'
```

## What a design could remove

This section identifies redundant work; **none of these designs is implemented
by this audit**. The measurements are those of the application table above.

| Phase | Measured derived work | Redundant in principle; obligations that remain |
|---|---|---|
| Generation | 32.5 ms; 606,277 derived syntax nodes overall | Ordinary AST allocation can be replaced by a compact derive description. Attribute validation and custom-codec references must remain. |
| Frontend rewrite/validation | 19.7 ms, estimated | Known generated syntax need not be re-recognized or recursively reconstructed. User-supplied defaults, custom codecs and attribute payloads still need their normal rewrites and diagnostics. The discarded certificate experiment is not proof of a profitable blanket skip. |
| Typechecking | 333.9 ms | The derive already knows much of each function's intended type and body schema. Inferring that again is redundant. Instantiating parameters, checking custom codecs and missing codec names, recursion, visibility and diagnostic locations is not. Template sharing is bounded by the 64.5% distinct-node fraction, not by the raw duplicate-binding fraction. |
| Conversion to Lambda | 79.0 ms | Constructing and then traversing a full typed body can be avoided if an explicitly checked derive description lowers directly. Preserve the existing coercions, recursion and naming semantics and identical emitted JavaScript. |
| Lambda lowering/passes | 51.106 / 146.611 ms in the separate local follow-up, estimated | Repeated generic simplification of fixed codec forms may be redundant. A future design must profile individual passes before claiming a saving; these module-wide splits are not sufficient evidence. |
| JavaScript lowering | 232.839 ms in the separate local follow-up, estimated | Repeated translation of fixed templates may be avoided. Every existing tag representation, optional-field convention and error path must still produce identical JavaScript. |
| Printing | 41.0 ms, estimated; 8.04 MB / 233,738 lines attributed to derived code | Tree traversal and repetitive formatting may be avoidable, but emitting bytes is not. Escaping, identifier names, whitespace, source maps and genType output remain observable contracts. |

## Verification and remaining scope

`python3 scripts/test_derived_census.py --rescript rewatch/target/release/rescript`
checks census-only enablement (no phase-timing environment variables), private
path exclusion, the 2% reconciliation gate, and rejection of missing/wrongly
typed custom codecs. The release fixture run reconciles parse within **0.057%**
and other phases within rounding. The former 14.4% parse deficit came from
location retries discarding the first parse's census. Those intervals now
accumulate into the surviving record without duplicating binding counts.
Twenty derive-error fixtures pass their table-driven unit test. The application
comparison above adds real diagnostic parity; exhaustive error coverage is not
claimed.

Local compiler and rewatch builds pass, rewatch tests pass, and JavaScript
parity passes **721/721**. The full local compiler test run reports 1,810 passed,
48 reference-dependent failures and 25 ignored; it is not a green full-suite
claim. CI must verify the published final head.

Signature-generated declarations remain charged to other work. Syntax counting now shares the validation walk, whose visitor is pinned to
16 bytes and tested on 10,000 elements with and without validation. The dense
provenance bitmap is indexed by binding-pool starts rather than structure-item
slots. Earlier tables predate this fusion and included attribute payload nodes;
they remain labelled observations, not silently updated measurements. Unsupported templates are individually reported rather
than guessed. These limitations are not hidden by the phase reconciliation
or the small allocation saving. The stricter +0.02% default-path CI budget also
must be verified on the final published head, not inferred from fixture data.


### Census engineering follow-up

Declaration-name preparation now borrows source spellings and represents codec
prefixes/suffixes virtually. It no longer formats and interns a string per field,
codec name or parameter, or clones a polymorphic-variant declaration. The single
binding buffer remains the destination for encoded bytes. This is opt-in census
work: **no default-path speedup is claimed** for this cleanup. A before/after
fixture check preserves every template byte, shape and node count in 35 records.
Additional 10,000-element tests cover field preparation (including borrowed
pointer identity), name-sort comparison bounds, spelling iteration, qualified
paths, function parameters, application arguments, records, patterns and types.
The visitor remains 16 bytes; virtual-name entries and their spelling tag have
size assertions as well.
