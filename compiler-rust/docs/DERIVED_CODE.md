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

The variable is read in one source location, once per process through a
`OnceLock<Option<PathBuf>>`; compiler options copy the cached result.
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
- Typechecking overhead outside the item checker, environment setup and signature
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


### Disabled-path isolation

The ordinary unused-attribute visitor retains trunk's inline fields and callback
set. Only an enabled census uses the separate 16-byte counting wrapper; a macro
shares validation bodies without an extra state-pointer load in ordinary visits.
The environment switch is cached once per process. Item-checking and conversion
snapshots live in cold, non-inlined helpers, so the ordinary checker loop has one
option test and no timer/counter snapshot locals. Name checking and environment
setup remain uninstrumented there and are charged to other work by reconciliation.
No identifier-table lookup or typechecking algorithm was changed. Instruction
measurements, rather than a presumed inlining explanation, decide whether this
removes the reported default-path cost.


## Slice 3b census — 2026-11-13

Measured at `5ff9f97de` with a release compiler and one worker. These are single-run census timings, not benchmark speedups. General groups are charged to their first blocking reason; generated body syntax nodes come from the existing shape walk. Failure events report the last obligation and its expected owner shape, not a diagnostic or a resolved actual type. Abandoned attempts are not counted again as completed modules.

### A 3,735-module application

Modules/interfaces: 3760

| Phase | Derived ms | Other ms | Attribution |
|---|---:|---:|---|
| parse_other | 0.000 | 640.899 | measured |
| generation | 90.109 | 2.294 | measured |
| frontend | 9.938 | 248.014 | node-weighted estimate |
| environment | 0.000 | 102.813 | measured |
| typecheck | 422.467 | 4150.779 | measured |
| signature | 0.000 | 248.595 | measured |
| conversion | 199.503 | 638.622 | measured |
| lambda_lowering | 16.480 | 211.805 | node-weighted estimate |
| lambda_passes | 52.153 | 474.404 | node-weighted estimate |
| lowering | 77.584 | 854.431 | node-weighted estimate |
| printing | 26.884 | 303.303 | node-weighted estimate |
| gentype | 0.000 | 203.757 | measured |

Path timing availability: 3760/3760 records.

| Phase | Bindings on a plan ms | General bindings ms |
|---|---:|---:|
| typecheck | 247.055 | 175.412 |
| conversion | 157.671 | 41.833 |

| Path | Bindings |
|---|---:|
| custom_codec | 36 |
| failed_obligation | 21 |
| not_yet_planned | 136 |
| plan | 6392 |
| recursive_group | 6 |
| shared_names | 0 |
| switch | 0 |
| type_parameters | 9 |
| unboxed | 0 |
| unmeasured_shape | 87 |
| unsupported_variant | 9 |
| user_expression | 504 |

| Failed obligation / expected type shape | Abandoned attempts |
|---|---:|
| constructor / result | 2 |

General cost availability: 3760/3760 records.

| General reason | Bindings | Generated body syntax nodes | Typecheck ms |
|---|---:|---:|---:|
| custom_codec | 36 | 5700 | 6.415 |
| user_expression | 504 | 124796 | 138.336 |
| type_parameters | 9 | 480 | 0.561 |
| recursive_group | 6 | 1016 | 1.202 |
| shared_names | 0 | 0 | 0.000 |
| unmeasured_shape | 87 | 4335 | 6.991 |
| unboxed | 0 | 0 | 0.000 |
| not_yet_planned | 136 | 15248 | 19.415 |
| unsupported_variant | 9 | 571 | 0.684 |
| switch | 0 | 0 | 0.000 |
| failed_obligation | 21 | 1070 | 1.809 |

| First unplanned form | Bindings |
|---|---:|
| json_identity | 136 |
| applied_user_codec | 0 |
| applied_module_path | 0 |
| unsupported_type | 0 |
| constant_fallback | 0 |
| empty_record | 0 |
| template_literal | 0 |
| declaration_shape | 0 |

| Size | Derived | Other |
|---|---:|---:|
| bindings | 7200 | 22320 |
| syntax_nodes | 156442 | 1668982 |
| js_bytes (estimated split) | 3590189 | 26000666 |
| js_lines (estimated split) | 92530 | 793278 |

Counter availability: 0/3760 records.

| Shape | Bindings | Min nodes | P50 | P90 | P99 | Max |
|---|---:|---:|---:|---:|---:|---:|
| constructor_application | 18 | 20 | 24 | 96 | 98 | 98 |
| parameterised (overlap) | 9 | 23 | 38 | 132 | 132 | 132 |
| polymorphic_variant | 57 | 13 | 28 | 81 | 147 | 147 |
| record | 712 | 21 | 100 | 460 | 1856 | 4584 |
| recursive group (overlap) | 6 | 39 | 136 | 529 | 529 | 529 |
| variant | 21 | 5 | 49 | 596 | 2775 | 2775 |

Distinct templates: 481 among 805 supported bindings; duplicate bindings: 324; unsupported templates: 3.
Distinct-template body nodes: 119396 / 153216 (77.9%); unsupported body nodes: 4846.
Singleton templates: 219; highest frequencies: [10, 6, 6, 6, 5, 4].


### tests/ppx_spice

Modules/interfaces: 37

| Phase | Derived ms | Other ms | Attribution |
|---|---:|---:|---|
| parse_other | 0.000 | 3.691 | measured |
| generation | 3.047 | 0.009 | measured |
| frontend | 0.793 | 0.417 | node-weighted estimate |
| environment | 0.000 | 1.671 | measured |
| typecheck | 27.162 | 9.277 | measured |
| signature | 0.000 | 1.440 | measured |
| conversion | 8.934 | 0.704 | measured |
| lambda_lowering | 1.604 | 0.465 | node-weighted estimate |
| lambda_passes | 5.800 | 1.712 | node-weighted estimate |
| lowering | 12.351 | 2.366 | node-weighted estimate |
| printing | 2.587 | 0.879 | node-weighted estimate |
| gentype | 0.000 | 0.000 | measured |

Path timing availability: 37/37 records.

| Phase | Bindings on a plan ms | General bindings ms |
|---|---:|---:|
| typecheck | 4.618 | 22.543 |
| conversion | 2.817 | 6.117 |

| Path | Bindings |
|---|---:|
| custom_codec | 3 |
| failed_obligation | 12 |
| not_yet_planned | 6 |
| plan | 226 |
| recursive_group | 27 |
| shared_names | 0 |
| switch | 0 |
| type_parameters | 18 |
| unboxed | 12 |
| unmeasured_shape | 136 |
| unsupported_variant | 0 |
| user_expression | 9 |

| Failed obligation / expected type shape | Abandoned attempts |
|---|---:|
| value / codec_function | 1 |

General cost availability: 37/37 records.

| General reason | Bindings | Generated body syntax nodes | Typecheck ms |
|---|---:|---:|---:|
| custom_codec | 3 | 1001 | 0.896 |
| user_expression | 9 | 387 | 0.605 |
| type_parameters | 18 | 1721 | 1.607 |
| recursive_group | 27 | 4614 | 4.044 |
| shared_names | 0 | 0 | 0.000 |
| unmeasured_shape | 136 | 14238 | 14.232 |
| unboxed | 12 | 366 | 0.650 |
| not_yet_planned | 6 | 361 | 0.365 |
| unsupported_variant | 0 | 0 | 0.000 |
| switch | 0 | 0 | 0.000 |
| failed_obligation | 12 | 84 | 0.143 |

| First unplanned form | Bindings |
|---|---:|
| json_identity | 3 |
| applied_user_codec | 3 |
| applied_module_path | 0 |
| unsupported_type | 0 |
| constant_fallback | 0 |
| empty_record | 0 |
| template_literal | 0 |
| declaration_shape | 0 |

| Size | Derived | Other |
|---|---:|---:|
| bindings | 449 | 66 |
| syntax_nodes | 23148 | 2557 |
| js_bytes (estimated split) | 364553 | 99681 |
| js_lines (estimated split) | 13310 | 3442 |

Counter availability: 0/37 records.

| Shape | Bindings | Min nodes | P50 | P90 | P99 | Max |
|---|---:|---:|---:|---:|---:|---:|
| constructor_application | 15 | 5 | 7 | 9 | 21 | 21 |
| parameterised (overlap) | 18 | 25 | 45 | 234 | 595 | 595 |
| polymorphic_variant | 40 | 14 | 36 | 228 | 405 | 405 |
| record | 21 | 25 | 44 | 99 | 281 | 281 |
| recursive group (overlap) | 27 | 21 | 68 | 446 | 1133 | 1133 |
| tuple | 9 | 18 | 44 | 188 | 188 | 188 |
| variant | 138 | 13 | 54 | 366 | 799 | 1133 |

Distinct templates: 134 among 223 supported bindings; duplicate bindings: 89; unsupported templates: 0.
Distinct-template body nodes: 18661 / 22772 (81.9%); unsupported body nodes: 0.
Singleton templates: 65; highest frequencies: [6, 4, 4, 4, 4, 4].


### Measurement order and limits

Planned discharge is the largest actionable typechecking bucket. All 136 application bindings classified `not_yet_planned` stop at the JSON identity codec. Both abandoned application attempts last visited a result-constructor obligation. This orders investigation as planned discharge, JSON identity plans, then upfront classification of constructor conflicts. User expressions remain general under Q5.

An initial census-disabled Cachegrind run at `a4c557d1c` retired 65,265,265,045 instructions. Its exclusive symbol counts include 53,962,454 in the discharge closure, 44,185,701 in skeleton instantiation and 39,410,903 in plan lowering node visits. Shared callees such as unification include ordinary code too: these numbers **do not** establish inclusive costs by obligation kind or per field. The required attributed profile and before/after validation remain outstanding.


### Constructor-description sharing experiment

An unqualified constructor description is now stored once per name per binding,
indexed by its interned string handle. The binding's obligation-start handle is
the epoch, so no description crosses an environment boundary. Every obligation
still performs its original lookup, usage marking, instantiation and unification.
No cache is keyed by a template or by type equality. Qualified descriptions retain
their existing lookup ownership. The 10,000-field record test keeps exactly seven
description slots, the same as one or two fields; its existing discharge step
counts are unchanged.

`bench_project.sh`, one worker, isolated experiment against the census compiler:

| Measurement | Before | After |
|---|---:|---:|
| Application instructions | 65,146,787,362 | 65,127,051,438 |
| Generated files | 3,980 | 3,980 |

Difference: **−0.0302945%**. Both output digests:
`0a3d301322cf7febdbf8793ae8c3dcbc1ecbadf44670c3b52cecbc5437a02408`.
`compare_checker_builds.py` reports no difference in 3,735 signatures, diagnostics
in 18 files, or 3,980 generated files. This is a small measured saving, not evidence
that constructor cloning is the largest avoidable obligation cost. No default-path
saving is claimed; the census-disabled +0.02% gate remains to be measured against
trunk.


### Additional validation of constructor sharing

- Compiler build and focused derive/plan/discharge/lowering tests pass; the full
  compiler suite was not run locally.
- Rewatch build and tests pass: 210 unit, one integration and eight snapshot tests.
- Clippy with warnings denied passes for all targets with all features and with
  no default features.
- Check-mode builds of both Spice projects and the application finish compilation.
- All 15 existing derived diagnostic fixtures pass in default/general/check modes.
  They were invoked through their `input.js`, the same entry used by
  `scripts/test.js`; the latter has no per-fixture selector and runs all build tests.
- Application outputs at one worker, ten workers and ten-worker general mode:
  3,980 files in each, digest
  `0a3d301322cf7febdbf8793ae8c3dcbc1ecbadf44670c3b52cecbc5437a02408`.
- `test_worker_determinism.py tests/ppx_spice` passes for 1/8 workers and two shuffle
  seeds: 74 signatures and 144 stored entries agree. That script excludes the
  fixture's `lib` outputs, so its generated-file comparison contains zero files;
  it is not evidence of JavaScript equality (the check-mode build supplies that).
- Census integration passes, including phase reconciliation within 2% and both
  negative codec cases. Eleven summary unit tests pass.

The `script-tests` job in `.github/workflows/rust-rewrite-validation.yml` does not
run the summary unit tests. The pull request supplies the exact additional step;
no workflow file is changed here.


### JSON identity plans

The plan now expresses the identity encoder and `v => Ok(v)` decoder with a
body-shape equality obligation, a relative local for the closed nested function,
and explicit constructor/function source locations. The equality uses ordinary
unification: it does not skip checks for supposedly ground types. Constructor
lookup and usage marking stay in general typing order.

The application census moves from 6,392 planned bindings before this slice to
6,534: all 136 `not_yet_planned` bindings and six variant bindings now use plans.
Two result-constructor retries still remain. The application check-mode build
finishes compilation. Raw Lambda equality tests cover aliases, arrays, required
and optional record fields and variant payloads; the inline-source-map oracle
also passes. The source-map test initially exposed missing function and
constructor expression locations; those locations now use the existing `At`
node and a dense explicit-constructor-location side table.

| JSON record work | 1 field | 2 fields | 10,000 fields |
|---|---:|---:|---:|
| Discharge lookups | 32 | 52 | 200,012 |
| Instances | 23 | 37 | 140,009 |
| Counted unifications | 32 | 55 | 230,009 |
| Body nodes / lowering visits | 86 | 140 | 540,032 |
| Raw Lambda terms | 101 | 161 | 600,041 |

An isolated one-worker application comparison against constructor sharing:
65,145,326,775 → 65,029,449,437 instructions (**−0.1778751%**).
Both produce 3,980 files with digest
`0a3d301322cf7febdbf8793ae8c3dcbc1ecbadf44670c3b52cecbc5437a02408`.
Counts from separate comparison runs vary; this delta uses the two sides of the
same run, not a baseline borrowed from the previous experiment.
