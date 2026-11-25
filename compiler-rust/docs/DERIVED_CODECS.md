# Derived codecs without the whole pipeline

Status: slices 1–3 are implemented; slice 4 remains. The original design and
its estimates are retained below, followed by implementation results in each
slice. The original measurement patch is in `prototypes/derived-codecs/`.

`@spice` on a type declaration derives `<name>_encode`, `<name>_encodeJson` and
`<name>_decode`. Today the derive appends syntax to the `ParseArena`, and that
syntax is rewritten, inferred, converted to Lambda, optimised, lowered and
printed like hand-written code. This document answers whether the derive can
hand the checker and the backend something cheaper, and specifies the slices.

Decisions already taken and not reopened here: `@spice` is supported as it is;
the derive stays behind the one seam `binary_ast/derive.rs`; the checker and the
backend learn "this item is derived" and what the seam hands them, never Spice;
the generated JavaScript, the accepted and rejected programs, the diagnostics,
the exported signature and worker-count independence do not change.

All paths are relative to `compiler-rust/src/` unless they start with another
top-level directory. Code was read at trunk `1b3f1bd68f`; pull request #194
(`derive/census.rs`, `derive/shape.rs`, the derived bit per value group) was
read and built at `1898b21000`.

## Where the task description and the code disagree

- **Three bindings, not two.** `generate_codec_decls` (`binary_ast/spice_ppx.rs`)
  emits `<name>_encode`, `<name>_encodeJson` (carrying `@warning("-32")`) and
  `<name>_decode`. The encoder body is generated once and cloned into both
  encoder bindings, so the checker and the backend process it twice.
- **There were no error fixtures for derived code** (slice 1 added
  `tests/build_tests/super_errors_derived`). No file under
  `tests/build_tests/` contains `@spice`; `tests/ppx_spice` holds only programs
  that compile. The diagnostics below were produced by compiling small probes
  with a build of #194. Slice 1 adds the fixtures.
- **`tests/ppx_spice` was not a buildable project on trunk.** Its `rescript.json`
  and `package.json` arrived with #194.
- **The Spice library is project source, not part of the compiler.** The
  generated code calls `Spice.*` (`tests/ppx_spice/src/Spice.res`), `Dict.*`,
  `Option.*` and the constructors `Ok`, `Error`, `Some`, `None`, `JSON.Object`
  by name, resolved in the user's environment at the point of the type
  declaration. Nothing about their types, arities or bodies is fixed by the
  derive.
- **The derive is not hygienic**, and today's behaviour includes that (see Q1).

## Measurements

The application figures are the ones supplied with the task (a 3,735-module
application, one worker, release build of #194, clean build, about 5,200 ms):

| Phase | Derived ms | Share of build | Attribution |
|---|---:|---:|---|
| generation in the derive | 32.5 | 0.63% | measured |
| front-end rewrite and validation | 19.7 | 0.38% | node-weighted estimate |
| type checking | 333.9 | 6.42% | measured |
| conversion to Lambda | 79.0 | 1.52% | measured |
| printing | 41.0 | 0.79% | node-weighted estimate |
| **sum** | **506.1** | **9.73%** | |
| Lambda passes and lowering | about 156 | about 3.0% | not split; by node share |

Two runs were made on `tests/ppx_spice` (34 units, 386 derived bindings,
32,902 derived syntax nodes), both with a debug build of #194, one worker.

**Run 1, checker counters** (`RESCRIPT_COMPILER_COUNTERS=1` with the census):

| Checker counter | Derived | Other | Derived per derived syntax node |
|---|---:|---:|---:|
| fresh variables | 22,782 | 3,042 | 0.69 |
| top-level unifications | 60,244 | 3,261 | 1.83 |
| instance-copied type nodes | 63,549 | 2,536 | 1.93 |
| lazy environment lookups | 37,054 | 778 | 1.13 |

The largest fresh-variable sites of the build are `subst_with_memo` and
`try_enforce_constraints` (`types/ctype.rs`, abbreviation expansion during
unification), `apply_arg_label_for_param` and `type_match_cases_batch_non_gadt`,
`type_let_bindings`, `type_function_nary` and `type_field`
(`types/typecore.rs`).

**Run 2, Lambda after the passes per template**
(`prototypes/derived-codecs/derived-postpass-dump.patch` and
`derived_postpass_compare.py`). Of 226 templates joined to a top-level binding,
113 have two or more bindings. For all 113 the Lambda after the passes is the
same across the instances of the template, once the names the derive declared
are replaced by their template indices and identifier stamps and static exit
numbers are renumbered. The exit numbers differ between instances (one counter
per unit: 34 and 54 for the same `size_decode` in two units) and do not reach
the JavaScript: the two functions are byte-identical. On this corpus the
distinct templates hold 80.4% of the derived nodes (application: 64.5%).

That result holds only because the corpus never puts one template in two
different surroundings. Q2 gives the two-line counterexample.

## Q1. Type checking

### What the generated code is

Read from `records_generate_encoder`, `records_generate_decoder`,
`records_generate_flat_decoder_expr`, `variants_generate_codecs`,
`codecs_generate_constr_codecs`, `codecs_generate_codecs_for` and
`generate_codec_decls`:

| Shape | Encoder body | Decoder body |
|---|---|---|
| constructor application `type ids = array<id>` | `v => (Spice.arrayToJson(id_encodeJson))(v)` | `v => (Spice.arrayFromJson(id_decode))(v)` |
| record | `v => (v => (JSON.Object(Dict.fromArray(Spice.filterOptional([("x", Some(codec(v.x))), …]))): JSON.t))(v)` | `v => (v => switch (v: JSON.t) { \| JSON.Object(dict) => switch Option.getOr(Option.map(Dict.get(dict, "x"), codec), Spice.error("x" ++ " missing", v)) { \| Ok(spice_field_x) => … Ok({x: spice_field_x, …}) \| Error(e: Spice.decodeError) => Spice.error(~path="." ++ "x" ++ e.path, e.message, e.value) } \| _ => Spice.error("Not an object", v) })(v)` |
| variant | `v => (v => switch v { \| C(v0, …) => JSON.Array([JSON.String("C"), codec(v0), …]) … })(v)` | match on `JSON.Array`, the head string, the argument count, then one `Ok`/`Error` match per argument |

Each binding is the eta-expansion `v => generated(v)` built by
`generate_codec_decls`; a type parameter `'a` adds one `encoder_a`/`decoder_a`
parameter.

### What the checker does, and what the derive already knows

`type_structure_item` (`types/typemod.rs`, arm `Pstr_value`) calls
`type_binding`, then reads the bound identifiers back from the environment with
`push_sig_values_from_env_pattern`. Per generated expression kind:

| Expression kind | Checker work today | Fixed by the derive |
|---|---|---|
| binding group | `type_let_bindings`: one fresh variable per binding, `begin_def`/`end_def`, pattern typing, generalisation, unused-value registration | the names, the count, and (see below) the type |
| `v => …` | `type_function_nary`: a fresh variable per parameter and one for the result, pattern typing of the parameter, one environment extension | parameter and result types |
| `f(a)` | `type_application`: instance copy of `f`'s type, a fresh variable where the label is checked (`apply_arg_label_for_param`), one unification per argument, one for the result; abbreviation expansion (`subst_with_memo`) whenever a library type is an abbreviation | everything except the type of `f` when `f` is not declared by the derive |
| identifier | one environment lookup, usage marking, the deprecation check, one instance copy | which name; for locals, the type |
| `v.x` | `type_field`: label lookup by name and disambiguation, fresh variables for the record type, instance of the label, one unification | the label is field `x` of the declaration being derived |
| `{x: …}`, `C(…)`, `` `C(…) `` | `type_record`, `type_construct`: lookup by name, disambiguation against the expected type, instance of the description, one unification per argument | which declaration, which position |
| `Ok`, `Error`, `Some`, `None`, `JSON.Object`, `JSON.Array`, `JSON.String` | the same constructor path, resolved by name in the user's environment | nothing: they are whatever those names mean there |
| `switch` | `type_match_cases_batch_non_gadt`: a fresh variable per case, pattern typing, one unification per case body, then `check_partial` and `check_unused` (`types/parmatch.rs`) | every generated match is exhaustive and has no redundant case: each ends in a catch-all, or lists every constructor of the declaration |
| `(e: JSON.t)`, `(e: Spice.decodeError)` | `transl_type` of the annotation (a type lookup), one unification | which type name |
| `"x"`, `"x" ++ " missing"` | constant typing; `++` is an application | the type is `string` |
| `@spice.default(e)`, `@spice.key(e)`, `@spice.codec(e)`, `@spice.fallback(e)` | the user's expression, typed in the body's scope | nothing |

So nearly all of the 0.69 fresh variables, 1.83 unifications and 1.93 copied
type nodes per node have a result the derive could state. What it cannot state
is confined to the leaves: what each free name resolves to, and the types of
the values behind those names.

### Three things the cheap path must respect

1. **Free names are resolved in the user's environment.** Shadowing changes
   today's result:

   ```rescript
   type mine = Ok(int) | Bad
   @spice
   type r = {a: int}
   ```

   fails today with `This has type: r / But it's expected to have type: int`,
   because the generated `Ok({a: …})` resolves to `mine`. A module named
   `Option` without `getOr` fails with `The value getOr can't be found in
   Option`.

2. **User expressions capture the generated binders.**

   ```rescript
   let v = 2
   @spice
   type t = {@spice.default(v) b: int}
   ```

   fails today at `4:52` with `This has type: JSON.t / But it's expected to
   have type: int`: `v` is the decoder's parameter. A user expression is typed
   in an environment that contains the template's binders (`v`, `dict`,
   `spice_field_*`, `e`).

3. **Labels and constructors are resolved by name, last declaration wins.**
   `v.x` is not tied to the declaration being derived. For
   `type a = {x: int} and b = {x: int}` both encoders read the label of `b`.

### The cheapest sound path

The seam hands the checker, per derived item, a **plan**: for each binding its
name and attributes, a **type skeleton**, and an ordered list of
**obligations**. The checker discharges the obligations and enters the bindings
into the environment. It does not see a body.

Obligations, in the order today's inference would meet the corresponding
nodes (the order fixes which failure is reported first and the order of
warnings):

| Obligation | Discharge | Records |
|---|---|---|
| `Value(name, skeleton)` | the lookup `type_ident` performs (usage marking, deprecation check), one instance, one unification with the instantiated skeleton | the resolved path and value kind (for the backend), the instance |
| `Label(name, position)` | label lookup by name; succeeds only if the first candidate is field `position` of the declaration being derived; marks the label used | the label description |
| `Constructor(name, expected)` | constructor lookup by name; succeeds only if it is constructor `expected` of the declaration being derived, or the stated constructor of a stated type obligation (`Ok` of the predefined `result`, `JSON.Object` of the type the `JSON.t` obligation resolved); marks it used in the positions today's body uses it (pattern in encoders, construction in decoders) | the constructor description |
| `Type(name)` | the lookup `transl_type` performs for the annotation | the path |
| `Literal(expr, skeleton)` | a constant payload (`@spice.key("k")`, `@spice.default(0)`): its constant type unified with the skeleton | nothing |

A plan never contains a non-constant user expression: such items stay on the
general path (Q5).

**The recorded type.** The skeleton says what must unify; it is not always the
node that is recorded. Inference today records, for a record or a variant,
`t => JSON.t` built from the label or constructor instance and the `JSON.t`
annotation, and for a constructor application the instantiated type of the
applied library codec (`array<id> => JSON.t`, not `ids => JSON.t`, and whatever
abbreviation the library's own signature uses for the decoder's result). Each
binding of a plan therefore names its type source: `Stated` (the skeleton
instance) or `ResultOf(obligation, applied arguments)` (the instance recorded
by that obligation, after its codec parameters were unified). The checker
generalises that node as `type_let_bindings` does and enters it with the same
`Env` call, in the same binding order, so `push_sig_values_from_env_pattern`
is replaced by reading the same value descriptions. The byte comparison of the
stored interface is the gate for this rule.

**Soundness.** A binding's type is correct if every free name has the type the
body uses it at (the `Value` obligations), every label and constructor is the
one the template was built for (the `Label` and `Constructor` obligations), and
the template itself is well typed given those, which is a property of the
derive checked once per template shape by the oracle, not per instance.

**Cost.** One discharge is O(obligations): per field of a record two `Value`
obligations per encoder binding and one per decoder, one `Label`, plus about a
dozen fixed names per item. For the median record (45 nodes, two to three
fields) that is roughly one obligation per 10 to 15 body nodes, each one
lookup, one instance of a small type and one unification, against today's 1.13
lookups, 1.83 unifications and 1.93 copied nodes per node.

### Diagnostics and warnings derived code can produce today

Produced with probes (rewatch build, default warnings plus the corpus flags):

| Case | Today's output | New path |
|---|---|---|
| field, argument or alias of a type with no codec in scope | `The value plain_encodeJson can't be found`, file only, no range (the identifier carries the none location) | the `Value` obligation fails: fall back |
| `@spice.codec(bad)` with `bad = (1, 2)` | `This can't be called, it's not a function. It has type: int`, file only | custom codecs are on the general path (Q5) |
| custom codec of another type | `This has type: int / But this function argument is expecting: string`, file only | general path |
| `@spice.default("x")` on an `int` field | `2:26-28`, `This has type: string / But it's expected to have type: int` | the `Literal` obligation fails: fall back |
| shadowed `Ok`, `Option`, … | as shown above | the `Constructor` or `Value` obligation fails: fall back |
| unsupported type (function, `any`, module) | `Can't generate codecs for function type`, a front-end error raised by the derive itself | unchanged: raised before a plan exists |
| deprecated codec (`@deprecated` on `M.t_encodeJson`) | warning 3 `deprecated: M.t_encodeJson`, file only, **twice** (once per encoder binding) | the lookup of the `Value` obligation emits it; each encoder binding has its own obligation, so twice, in the same order |
| codec reached through an `open` | marks the open used (no warning 33); an unrelated `open` still warns | the same lookup marks the open |
| codec hidden by an interface | no warning 32, also for a `hidden_encode` nothing uses (observed; the cause was not established). `_encodeJson` carries `@warning("-32")` | the bindings are entered as today and the `-32` attribute travels in the plan; the oracle compares the warnings |
| non-exhaustive or redundant match (8, 11), unused variable (26, 27) | cannot occur: every generated match is total and every binder is used (checked by reading the generators; the oracle asserts no such warning on the corpus) | not produced |
| unused constructor or label of a private declaration | suppressed today because the body uses each | the `Label` and `Constructor` obligations mark each |

**Fallback rule.** When any obligation of an item fails, the checker abandons
the unit: nothing of the attempt is reported or published. Whoever holds the
unit's source runs the front end again with plans off, which generates the
unit's derived code as syntax, and compiles that. The diagnostic is today's
because it is produced by today's code on today's syntax, and a deprecation is
reported once because the warnings of the abandoned attempt are dropped with
it. The syntax of an item is therefore generated only where it is needed: for
a unit with a failed obligation, for `RESCRIPT_DERIVED_PATH=general` and for
the reference compile of `check`, and for a tree that is stored or printed
instead of compiled. An item whose plan holds costs no generation and no
front-end rewrite. (Slice 1 generated the syntax beside every plan and typed
it per item after restoring the type state; the checker holds the parse arena
by shared reference, so syntax made on demand has no arena to live in that
the readers of the typed tree could also read. Compiling the unit again needs
no second handle space. Its cost, one more front end and type check of the
unit, falls only on a unit with a failed obligation: one that reports an
error, or one whose library has another shape than the plan states.)

### What reads the typed body afterwards

| Reader | Code | What the new path records instead |
|---|---|---|
| conversion to Lambda | `convert_structure_items_raw` (`raw_lambda/convert.rs`), arm `Tstr_value` | a typed item `Tstr_derived` holding the plan handle, the bound identifiers and the obligation results (paths, value kinds, label and constructor descriptions); see Q2 |
| unit reads for incremental builds | `structure_reads` (`types/unit_reads.rs`), a walk over the typed tree collecting every path rooted at a unit and every type | the paths of the discharged obligations and the bindings' types, pushed by the same collector from the obligation results. The set must equal today's; the oracle compares it |
| unused-value, unused-open, unused-constructor warnings | usage cells (`types/usage.rs`), set by lookups | set by the obligations' lookups, as listed above |
| the recursion check and `let rec` ordering | `rec_structure_item`, `typed_structure_item_uses_ident` (`types/typecore.rs`) | recursive groups stay on the general path (Q5) |
| genType | `translate_structure_item`, `structure_item_check_annotation` (`gentype/`) | nothing: derived bindings carry no genType annotation; both functions get a `Tstr_derived` arm returning what an unannotated `Tstr_value` returns. Types exported through the signature are unaffected |
| editor tooling | `for_structure_item` (`analysis/process_cmt.rs`) and the stored `.cmt` | the bound names with their types and the none location, as today. Derived bodies carry only none or ghost locations, except the built-in codec identifiers, which carry the location of the field's type constructor (`expr_ident_spice_codecs_with_loc`). Whether any editor feature surfaces those was not established (see Risks) |
| debugging dumps | `types/sexp_typedtree.rs` | prints the plan handle and the binding types |

**Verdict Q1: yes, with two conditions.** The checker discharges ordered
obligations and records the type without a body, provided (1) any failed
obligation falls back to today's path for that item, and (2) the recorded type
is taken from the node inference would record (`Stated` or `ResultOf`), gated
by the stored-interface comparison.

## Q2. Backend

### What today's output depends on outside the binding

Each row was observed on a probe or on the corpus:

| Dependency | Evidence | Code |
|---|---|---|
| in-module alias propagation | with `@spice type id = string` above it, `{id: id}` encodes as `Spice.stringToJson(v.id)`; with `@spice type id = {raw: string}` it encodes as `id_encodeJson(v.id)`. The same codec passed as an argument (`Spice.optionToJson(n_encodeJson, v.n)`) is not replaced | `simplify_alias` (`lambda/lam_pass_remove_alias.rs`) |
| arity of library functions from export summaries | `Spice.optionToJson(codec)(v.tag)` is printed `Spice.optionToJson(Spice.stringToJson, extra)` because the summary of `Spice` gives arity 2 | `alpha_conversion` with the external arity resolver; `cmj_export_arities` |
| cross-module inlining | only the constants `null`, `undefined`, `true`, `false` by default; small closed functions only under `-bs-cross-module-opt`. `A.id_decode` stays a reference | `cmj_export_constant_from_lambda`, `collect_cmj_export_lambdas_from_simplified_lambda` (`lambda/lam_compile.rs`) |
| constant folding | `"x" ++ " missing"` becomes `"x missing"` (fixed per template); `@spice.default(e)` with `let e = 1` above becomes `_0: 1` (not fixed) | the passes |
| local names | `tmp`, `tmp$1`, `extra`, `e$3` are chosen per function during lowering and printing; top-level `tmp`, `extra`, `v` in the same module did not change them | lowering and the printer |
| statement shape | a four-field record hoists `let tmp = …` for the first fields because the last one needs `let extra = v.tag`; a two-field record whose option field has an in-module codec prints both inline | lowering |
| exports | listed in binding order; with an interface, `hidden_encode` is removed while `hidden_encodeJson` and `hidden_decode` stay because another codec uses them | `handle_exports` (`lambda/lam_compile_main.rs`), the dead-code passes |
| imports | `Spice` and `Stdlib_Option` enter the header because the Lambda references them; `Dict.get` is an external and adds none; sorted by `ocaml_sort_modules` | `collect_possible_required_modules_in_arena`, `take_possible_required_modules` |
| eta reduction | `id_encode` prints as `let id_encode = Spice.stringToJson;` although the Lambda after the passes is still `function v -> Spice.stringToJson v` | lowering |
| source maps | derived nodes carry the none location except the built-in codec identifiers and user payloads | the `lam_locs` side table |
| type-directed forms | `Some(encoded)` converts to `some_not_nest` because the payload type is `JSON.t`; `JSON.Object(d)` is the identity; `Dict.fromArray` is `Object.fromEntries` from its external declaration; `Ok(None)` is the constant block `[Ok: undefined]`; the match on `JSON.t` is a `typeof` dispatch from the untagged-variant layout | `raw_lambda/convert.rs`, `raw_lambda/typeopt.rs`, `raw_lambda/matching.rs`, `types/variant_runtime.rs` |

### The three options

**(c) Emit JavaScript-level nodes directly: no.** The statement shape and the
local names come out of lowering decisions that depend on the neighbours of an
expression. Smallest example: `{x: int, y: float, name: string, tag:
option<string>}` prints `let tmp = Spice.intToJson(v.x); … let extra = v.tag;`
before the array, while `{id: id, n: option<n>}` with `n` derived in the same
module prints everything inline. A JavaScript template per shape would have to
reimplement those decisions, and the export summary (arity, purity) would have
to be derived separately.

**(b) Emit the IR after the passes: no.** Run 2 found the post-pass Lambda
fixed for 113 of 113 shared templates, but that is a property of the corpus.
Smallest example where it changes the output:

```rescript
// P.res                      // Q.res
@spice type id = string       @spice type id = {raw: string}
@spice type u = {id: id}      @spice type u = {id: id}
```

`u_encode` is one template in both units. After the passes it is
`(apply (field:stringToJson global Spice!) (field:id v))` in `P` and
`(apply id_encodeJson (field:id v))` in `Q`. A second example is
`@spice.default(e)` with a top-level constant `e`. The passes are also
whole-unit (`simplify_in_arena` runs each pass over one arena), so skipping
them for a derived body needs a per-node "already normal" mark that every pass
honours, and the arity table (`meta.ident_tbl`) that the export summary is read
from is filled by those same passes.

**(a) Emit raw Lambda from the plan, keep the passes and the lowering: yes,
with one condition.** Everything in the table above except the last row is
decided after conversion, by code that stays. The last row is what conversion
does, and it is local: it needs the plan and the obligation results (value
kinds for externals, label and constructor descriptions, the layout of
`JSON.t`), which the checker recorded. The condition: the emitter must not
contain its own copy of any type-directed decision or of match compilation. It
builds each node through the functions `convert.rs` uses for the corresponding
typed node, split so they take descriptions and already converted arguments,
and it compiles each `switch` by handing `compile_matching`
(`raw_lambda/matching.rs`) patterns built from the constructor descriptions.
Smallest example where a hand-written emitter would differ: `Some(codec(v.x))`
emitted as a plain `Some` block instead of `some_not_nest`.

**Verdict Q2: (a), yes with that condition; (b) and (c) no.** If the first
commit of slice 2 shows that `compile_matching` cannot be driven without typed
expression nodes at acceptable size, the fallback design is to have the seam
hand the checker a typed body built without inference and keep conversion
untouched; that saves less (see Savings) and is recorded here so the decision
is not re-derived.

## Q3. One check per template

**Verdict: no, not on top of Q1 and Q2(a); it would only matter for (b) or
(c).**

- Checking under Q1 is O(obligations) per binding, and obligations are per
  instance: the names differ and the environment differs. A template cache
  removes none of them.
- Emission under Q2(a) writes O(nodes) Lambda nodes per instance. A cached
  template would still be copied with fresh identifiers and the instance's
  names, which is the same O(nodes) of the same kind of work.
- For the passes and lowering a cache needs (b), which is refuted. Its upper
  bound even so: the duplicate share is 100% − 64.5% = 35.5% of derived nodes,
  so at most 35.5% × 156 ms ≈ 55 ms (1.1% of the build), before the cost of
  instantiating.
- Against today's path a cache would save at most 35.5% × 333.9 ms ≈ 119 ms of
  checking (2.3%). Q1 removes 250 to 300 ms without it.

## Q4. What other modules see

| Artifact | Produced today by | On the new path |
|---|---|---|
| stored interface (signature items of the bindings) | `push_sig_values_from_env_pattern` reading the environment after `type_binding` | the same value descriptions, entered by the discharge with the type chosen by the type-source rule, in the same order; published by the unchanged code |
| interface check against a `.resi` | signature inclusion on those value descriptions | unchanged |
| export arity | `cmj_export_arities` (`lambda/lam_compile_main.rs`) from `meta.ident_tbl`, filled by `collect_info_with_external_arity` during the passes and by `handle_exports` | unchanged code on the Lambda the emitter produced |
| inlinable constants and bodies | `cmj_export_constant_from_lambda`, `collect_cmj_export_lambdas_from_simplified_lambda` on the simplified Lambda | unchanged code |
| purity (the `/* No side effect */` trailer and the summary's flag) | computed after conversion, from the unit's Lambda and lowered program | unchanged code |
| unit reads | `structure_reads` | from the obligation results (Q1) |

Because (a) keeps everything from the raw Lambda onward, the export summary
needs no second derivation. That is the main reason to prefer (a).

## Q5. What stays on the general path

The classifier is a function behind the seam, total over type declarations,
returning `Plan` or `General(reason)`; there is no "unknown" result. General:

| Case | Reason |
|---|---|
| `@spice.codec(e)` on any type in the declaration | a user expression in the body |
| `@spice.default(e)`, `@spice.key(e)`, `@spice.fallback(e)` with a non-constant payload | a user expression that can capture the template's binders |
| type parameters (9 bindings in the application) | the encoder and decoder parameters make the type polymorphic; too rare to pay for |
| recursive groups (6 bindings) | need the recursion check and `let rec` ordering on a typed body |
| a `type … and …` group in which two declarations share a label or constructor name | the label obligations would resolve to the wrong declaration |
| `@spice.serde` variants and polymorphic variants, polymorphic variants (57 bindings), tuples | not among the three measured shapes; each can move later if a census shows it matters |
| `@unboxed` declarations | a different body per representation; rare |

An item reaches the general path in two ways: the classifier returns `General`
in the front end (the syntax is generated as today and the item is an ordinary
derived value group), or a plan's obligations fail in the checker (the unit is
compiled again with plans off, and the seam generates the syntax then). Both are tested by the same three means: a unit
test per reason that the classifier returns it; the error fixtures added in
slice 1 (the probes of Q1) under `tests/build_tests/super_errors/` with a
project that enables the derive; and the oracle, which compiles every unit of
`tests/ppx_spice` both ways.

## Target design

```
type declaration with @spice
        │  derive::classify                      (front end, behind the seam)
        ├── General(reason) ──► syntax, as today ──► whole pipeline
        └── Plan ──► StructureItemDesc::Pstr_derived(DerivedIdx)
                         │
   checker: type_structure_item, arm Pstr_derived
        discharge obligations in order (lookups, instances, unifications)
        ├── one fails ──► abandon the unit; its source is compiled again
        │                 with plans off (every item as syntax, as today)
        └── all hold ──► enter bindings, record results
                         Tstr_derived { plan, idents, results }
                         │
   conversion: convert_structure_items_raw, arm Tstr_derived
        derive::lower(plan, results, builder) ──► raw Lambda
        (through convert.rs's own node builders and compile_matching)
                         │
   passes, lowering, printing, export summary: unchanged
```

**The plan** lives in the `ParseArena` in dense pools indexed by `u32`
handles: `DerivedIdx` per item, a range of bindings per item, a range of
obligations and a range of body nodes per binding, one pool of skeleton nodes.
It is generic: skeleton nodes are `Var`, `Self` (the declaration being
derived), `Named(type obligation, args)`, `Arrow`, `Tuple`; body nodes are a
small typed core (`Local`, `Free(obligation)`, `Apply`, `Function`, `Field`,
`Record`, `Construct`, `Tuple`, `Array`, `String`, `Concat`, `Switch`, `Let`,
`Annotate`). Neither the checker nor the backend matches on a Spice name. Sizes
are pinned: an obligation and a body node are at most 16 bytes, a skeleton node
8 bytes.

**The seam** grows from four functions to these: the two detectors, the
signature expander (interfaces are unchanged: they contain only value
declarations), the structure expander, which classifies each group of
declarations and makes its plan or its syntax (today's
`map_type_decl_structure`), `free_names` (the names a plan resolves, for the
dependency scan), and the lowering. Deleting the derive still means
emptying these bodies.

**State per compilation.** Obligation results are a dense table indexed by
obligation handle, owned by the unit's checker context and passed to
conversion by reference. No hash map, no lock, no per-node allocation: the
discharge allocates the instances it unifies and nothing else.

### Savings

Percentages are of the application's one-worker build (5,200 ms). "Measured"
means the base is a measured interval; every removal fraction is extrapolated,
because nothing was prototyped.

| Phase | Today | Removed | Saving of the build | Basis |
|---|---:|---:|---:|---|
| generation | 32.5 ms measured | 30 to 60%: a plan is one compact node per body node, without the clone of the encoder body into two bindings and without `LocCloner` | 0.2 to 0.4% | extrapolated |
| front-end rewrite | 19.7 ms estimated | 80 to 100%: there is no syntax to rewrite | 0.3 to 0.4% | extrapolated from an estimate |
| type checking | 333.9 ms measured | 75 to 90%: one obligation per 10 to 15 nodes against 1.1 lookups, 1.8 unifications and 1.9 copied nodes per node (run 1) | 4.8 to 5.8% | extrapolated from counters |
| conversion | 79.0 ms measured | 40 to 70%: no typed-tree walk and no type-directed dispatch, but match compilation stays | 0.6 to 1.1% | extrapolated |
| passes and lowering | about 156 ms, not split | 0 | 0 | |
| printing | 41.0 ms estimated | 0: the JavaScript still has to be written | 0 | |
| **total** | **about 662 ms, 12.7%** | | **5.9 to 7.6%** | |

With the general-path items subtracted (their share of derived nodes was not
measured; 0 to 5% assumed), the range is **5.6 to 7.6% of the build**. That is
between 44% and 60% of the 12.7 points derived code costs (9.7 measured plus
about 3). What remains, 5.1 to 7.1 points: the passes and the lowering (about
3), printing (0.8), the obligations (0.6 to 1.6), Lambda emission (0.4 to 0.9),
plan construction (0.2 to 0.4) and the general-path items.

With the fallback design of Q2 (a typed body built without inference,
conversion unchanged) the type-checking saving drops to an estimated 60 to
75% and the other rows to zero: 3.9 to 4.8% of the build.

The `Instruction count` check runs on `tests/tests`, which derives nothing: on
the default path every slice saves nothing there and must cost nothing.

## The oracle

Today's path is the oracle. One switch, `RESCRIPT_DERIVED_PATH`, read once when
the compiler options are created (where `RESCRIPT_DERIVED_CENSUS` is read in
#194) and carried in the options:

- unset: plans are used;
- `general`: the classifier returns `General` for every item (today's
  behaviour, the reference);
- `check`: each unit with at least one plan is compiled both ways in the same
  process and the following are compared; a difference fails the build naming
  the unit and the first differing binding:
  - the JavaScript bytes, and the source map when enabled;
  - the signature in canonical form (`types/canonical_sig.rs`). The stored
    interface bytes and their fingerprint are not compared: they record which
    type nodes two values share, and a discharge instantiates each binding's
    codec on its own where typing a group shares the nodes of one annotation;
  - the export summary: arities, constants, inlinable bodies, purity;
  - the unit reads, as sets;
  - the warnings, as text in order.

The JSON identity fixture also checks the abbreviation-memo observation O11
in `CHECKER_REWRITE.md`, not an independently demonstrated diagnostic difference.
General application inference instances the callee and runs `lower_args`
(`types/typecore.rs::type_application_parts`; `compiler/ml/typecore.ml:2826–2828`),
whose arrow-spine walk expands the return type as well as lowering argument
levels (`compiler/ml/typecore.ml:2503–2514`). Expanding `JSON.t` records its
representative in the simple-abbreviation memo, so a later instance can reuse
that representative for both concrete occurrences through `find_repr`
(`types/ctype.rs::copy_type_cached`; `compiler/ml/ctype.ml:778–782`). This explains
why the general path's later `values_encodeJson` shares its array element and
result nodes while the plan without application lowering does not; the signature
oracle and successful-program fixture retain that distinction.

Diagnostics are gated on the error fixtures by running each with the switch
unset and with `general` and comparing the output byte for byte, and by the
`super_errors` expectations themselves.

In CI, one step (the workflow file is edited by the maintainers):

```sh
RESCRIPT_RUNTIME="$PWD/packages/@rescript/runtime" RESCRIPT_DERIVED_PATH=check \
  rewatch/target/release/rescript build tests/ppx_spice
```

On a large application the maintainers run the same command with the switch,
plus `scripts/compare_checker_builds.py` and `scripts/bench_project.sh` between
a `general` build and a default build of the same binary.

The switch exists only until the last slice. It then goes, together with the
dual compilation; what replaces it is a test that compiles `tests/ppx_spice`
with a classifier forced to `General` through a function parameter and
compares the JavaScript, which keeps the two forms from drifting.

**What is not deleted.** The syntax generators of `spice_ppx.rs` remain: they
are the general path and the producer of every diagnostic. The design removes
the whole-pipeline *use* for supported items that discharge; it does not
remove generator code. A reviewer applying "what you replace is deleted" should
read it this way: after the last slice a supported item has exactly one
success path and no switch selects another.

## Slices

All slices depend on #194 (merged: the derived bit, the census, the
buildable `tests/ppx_spice`). Sizes are of new non-test lines.

### Slice 1. The plan, the obligations and the oracle, for constructor applications

- **Files:** `binary_ast/derive.rs`, new `binary_ast/derive/plan.rs`,
  `binary_ast/spice_ppx.rs` (classifier and plan builder for one shape),
  `parser/ast.rs` (`Pstr_derived`), `parse_arena.rs` (pools),
  `types/typedtree.rs` (`Tstr_derived`), new `types/derived.rs` (discharge),
  `types/typemod.rs` (one arm), new `raw_lambda/convert/derived.rs` (as built; lowering of
  `Local`, `Free`, `Apply`, `Function`), `raw_lambda/convert.rs` (one arm),
  `types/unit_reads.rs`, `driver.rs` (the switch and `check`),
  every exhaustive match on the two item enums, fixtures.
- **Deletes:** nothing; it adds the switch that the last slice deletes.
- **End state:**
  `rg -n "Pstr_derived" compiler-rust/src | wc -l` is at least 8;
  `rg -n "fn discharge" compiler-rust/src/types/derived.rs` matches;
  `rg -n "spice|Spice" compiler-rust/src/types compiler-rust/src/raw_lambda`
  has no new match;
  `rg -n "RESCRIPT_DERIVED_PATH" compiler-rust/src` matches only `driver.rs`;
  `rg -l "@spice" tests/build_tests` is non-empty.
- **Gates:** `cargo test` for `compiler-rust` and `rewatch`; the `check` build
  of `tests/ppx_spice`; the fixtures with and without `general`; CI.
- **Size:** about 1,400 lines.
- **Saving:** none measurable (518 bindings of about 5 nodes in the
  application). It buys the mechanism and the oracle.
- **Less capable model:** no. It sets the seam contract and the type-source
  rule.

```text
Task: derived codecs slice 1. Repository jfrolich/rescript-rust, base branch
ocaml-to-rust-rewrite, after pull request #194 is merged. Read AGENTS.md and
compiler-rust/docs/DERIVED_CODECS.md first; the document is the specification
and this prompt only orders the work. Do not change .github/workflows.

Goal: a `@spice` type declaration whose manifest is a type constructor
application (the shape `codecs_generate_constr_codecs` and
`codecs_parameterize_codecs` handle in compiler-rust/src/binary_ast/spice_ppx.rs,
for example `type id = string`, `type ids = array<id>`,
`type m = option<A.t>`), with no type parameter, no `@spice.codec`, no
`@spice.fallback`, not `@unboxed`, not in a recursive group, is no longer
expanded to syntax. Everything else behaves exactly as today. You may not
substitute a smaller goal such as adding only the data types or only the
classifier: the slice is done when such a declaration compiles through
`Pstr_derived` end to end and the `check` build passes.

Commits, in this order, each building and passing `cargo test
--manifest-path compiler-rust/Cargo.toml`:

1. Fixtures first. Add a project under tests/build_tests/super_errors (or the
   multi-file variant if the derive needs the Spice library as a second file)
   that enables the built-in derive, with one fixture per row of the table
   "Diagnostics and warnings derived code can produce today" in the document,
   and record today's output as the expectation. Update tests/ERROR_VARIANTS.md.
   No compiler change in this commit.
2. `binary_ast/derive/plan.rs`: the pools and handles (`DerivedIdx`, binding,
   obligation, skeleton node, body node) stored in `ParseArena`, with
   `size_of` tests: obligation <= 16 bytes, body node <= 16 bytes, skeleton
   node <= 8 bytes, every handle 4 bytes. Doc comment on each function with
   its cost.
3. `StructureItemDesc::Pstr_derived(DerivedIdx)` in the parse tree and
   `Tstr_derived` in the typed tree. Add the arm to every match on either enum
   without using a `_` arm; in the binary AST and parsetree0 mappers write the
   item's general form (call `derive::general_form`), so nothing downstream of
   a stored .ast sees the new item.
4. Behind the seam: `derive::classify` (returns `Plan` or `General(reason)`,
   an enum with one variant per row of the Q5 table), `derive::plan` for the
   constructor-application shape, and `derive::general_form` (today's
   `map_type_decl_structure` output for one item). Obligations are pushed in
   the order `type_binding` meets the corresponding identifiers today: write a
   unit test that asserts that order against the identifiers of the general
   form for five declarations.
5. `types/derived.rs`: `discharge(tctx, env, item) -> Result<Discharged,
   Fallback>` implementing the obligation table of the document for `Value`
   and `Type`, the `ResultOf` type source, warning buffering, and restore on
   failure with `snapshot_type_state`. The arm in `type_structure_item`
   (types/typemod.rs) calls it and on `Fallback` type-checks
   `derive::general_form` with `type_binding`. Results go in a dense table
   indexed by obligation handle. Step-count test: an item with 10,000
   obligations performs exactly 10,000 lookups, 10,000 instances and 10,000
   unifications (count through the existing perf counters or a test counter
   passed as a parameter; no global).
6. `raw_lambda/convert/derived.rs`: `lower(plan, results, builder)` for the body nodes
   `Local`, `Free`, `Apply`, `Function`, producing for each binding the raw
   Lambda `convert_let_with_body_raw` produces today for the general form.
   Unit test: for ten declarations, the printed raw Lambda of both forms is
   equal after renumbering identifier stamps. Step-count test at 10,000 body
   nodes: one builder call per node, no allocation per node.
7. `types/unit_reads.rs`: reads of a `Tstr_derived` item from the obligation
   results and the binding types; test that the set equals the general form's
   for the same ten declarations.
8. The switch: `RESCRIPT_DERIVED_PATH` read once where the compiler options
   are created, values unset / `general` / `check` exactly as the section "The
   oracle" specifies, including every comparison listed there.

Checks to run and paste into the pull request body:
- cargo build and cargo test for compiler-rust and rewatch;
- `RESCRIPT_DERIVED_PATH=check rewatch/target/release/rescript build
  tests/ppx_spice` (must finish with no difference);
- each fixture of commit 1 built with the switch unset and with `general`,
  outputs byte-identical;
- `rg -n "spice|Spice" compiler-rust/src/types compiler-rust/src/raw_lambda`
  before and after: no new match;
- a census of tests/ppx_spice: how many bindings took a plan, how many each
  `General` reason, how many fallbacks.
Say plainly in the body that this slice saves nothing measurable and that the
default path (tests/tests) is unchanged; the Instruction count check must be
within its limit. Give the CI step from the document's oracle section in the
body for the maintainers to add.
```

### Slice 2. Records

**Status: done.** A record with at least one field takes a plan. The
discharge of its labels does not split `type_record`: the labels of the record
expression hold when each name's first candidate in scope is the label at the
field's position of one non-private record, all of whose labels are written,
and anything else fails the obligation. Kept general beyond the table of Q5: an
empty record, a template literal as a key or default, a `JSON.t` field, and a
field of a user's type applied to arguments (its codec takes the arguments'
codecs one at a time, which a plan's skeleton does not describe).
`check` compared source maps already. Not measured: the application.

- **Files:** `binary_ast/spice_ppx.rs` (plan builder for records),
  `binary_ast/derive/plan.rs` (the remaining body nodes), `types/derived.rs`
  (`Label`, `Constructor`, `Literal`), `raw_lambda/convert/derived.rs`,
  `raw_lambda/convert.rs` (node builders split out of the typed-node
  functions), `raw_lambda/matching.rs` (an entry taking patterns built from
  descriptions, if the existing one cannot be called).
- **Deletes:** the bodies of the `convert.rs` functions that were split move
  into the shared builders; no copy remains. The census's syntax-node count for
  planned items goes (there is no syntax); the census reports plan nodes.
- **End state:** `rg -n "some_not_nest|Psome_not_nest" compiler-rust/src/raw_lambda/convert/derived.rs`
  has no match (the decision lives in one place);
  `rg -n "fn compile_matching" compiler-rust/src/raw_lambda` shows one
  definition; a census of `tests/ppx_spice` shows every record without a
  general reason taking a plan.
- **Gates:** as slice 1, plus the application run by the maintainers
  (`check`, then `scripts/bench_project.sh` general against default).
- **Size:** about 1,800 lines.
- **Saving:** the bulk: records are 5,988 of 7,200 bindings. Expected 5.0 to
  6.6% of the application's build.
- **Less capable model:** no. The match-compilation entry is the riskiest step
  of the design.

```text
Task: derived codecs slice 2, records. Repository jfrolich/rescript-rust, base
ocaml-to-rust-rewrite, after slice 1 is merged. Read AGENTS.md and
compiler-rust/docs/DERIVED_CODECS.md (Q1, Q2, Target design) first.

Goal: a `@spice` record declaration (the shape `records_generate_codecs` in
compiler-rust/src/binary_ast/spice_ppx.rs handles: plain fields, optional
fields `x?: t`, `option<t>` fields, `@spice.key("literal")`,
`@spice.default(<constant literal>)`) takes a plan. Every `General` reason of
the Q5 table still applies. The slice is not done by supporting encoders only,
or by supporting records without optional fields.

Commits in order:

1. Characterisation, no behaviour change. In a test module of
   raw_lambda/convert/derived.rs, for each of these general-form bodies print the raw
   Lambda today's converter produces and pin it: field access; record
   construction with an optional field; `Some(e)` where `e : JSON.t`;
   `Ok(None)`; `JSON.Object(d)`; `Dict.fromArray(e)` and `Dict.get(d, k)`;
   `Spice.error(~path=p, m, v)` and `Spice.error(m, v)`; `a ++ b`; the match
   `switch (v: JSON.t) { | JSON.Object(dict) => e1 | _ => e2 }`; the match
   `switch e { | Ok(x) => e1 | Error(e: Spice.decodeError) => e2 }`. These are
   the forms `records_generate_encoder` and `records_generate_flat_decoder_expr`
   emit. If the two matches cannot be produced by calling `compile_matching`
   (raw_lambda/matching.rs) with patterns allocated in its `PatArena` from the
   constructor descriptions, stop after this commit and report: the document
   names the fallback design and that decision is not yours to take.
2. Split the functions of raw_lambda/convert.rs that build those nodes so each
   takes the description (label, constructor, value kind) and the already
   converted arguments; the typed-node functions call the split ones. No copy
   of a type-directed decision may exist twice. JavaScript parity scripts must
   be unchanged by this commit alone.
3. Plan builder for records behind the seam, obligations in today's
   typing order (extend the order test of slice 1 to five records, including
   one with an optional and one with a defaulted field).
4. `types/derived.rs`: `Label`, `Constructor` and `Literal` obligations as the
   document's table defines them, including usage marking in the positions
   today's body uses (pattern in encoders, construction in decoders), and the
   `Stated` type source. A `type a = {x: int} and b = {x: int}` group must
   classify `General`.
5. `raw_lambda/convert/derived.rs`: lowering of the remaining body nodes through the
   split builders and `compile_matching`. Unit test: for each record of
   tests/ppx_spice/src/Records.res and OptionalFieldRecords.res, the raw Lambda
   of both forms is equal after renumbering stamps and static exit numbers.
   Step-count test: a 10,000-field record makes O(fields) builder calls; assert
   the exact count per field.
6. Extend the `check` comparison if anything listed in the oracle section was
   not yet compared for records (source maps with a `@spice.default` literal).

Checks to paste: cargo build and test for compiler-rust and rewatch;
`RESCRIPT_DERIVED_PATH=check` build of tests/ppx_spice; the slice-1 fixtures
with and without `general`; `./scripts/test_js_output_parity.sh`; the census
(plans, general reasons, fallbacks) on tests/ppx_spice; on Linux,
`scripts/compare_build_instructions.py` for tests/tests (expected: no change)
and for tests/ppx_spice between `general` and default (report the number, do
not round it into a claim about another project).
```

### Slice 3. Variants

#### Implementation and measurements

`binary_ast/spice_ppx/plan/variant.rs` builds ordinary constructors, tuple
payloads, inline records and string/float aliases. Inline records reuse the
record encoder and decoder builders. Every declared constructor is an ordered
`Constructor` obligation in pattern position in each encoder and construction
position in the decoder. The five-variant order test compares those obligations
with a walk of the general syntax.

The generic plan adds prefix-pooled patterns, conditionals, lets, integer
constants, multi-argument construction, record updates and application
locations. The existing converter builds the terms; its match compiler handles
constructor and string switches and decomposes tuple scrutinees. No variant
selection switch remains. `General(NotYetPlanned)` no longer classifies a
variant; `unsupported_variant` identifies unsupported payload codecs,
attributes, generalized constructors or pool-capacity limits before discharge.
`Aliased_variant_payload` pins one impossible form: a scalar alias with a payload
has an unbound `json_arr` in the general decoder. The original private-declaration
fixture confirms constructors used only by codecs do not warn in either path.

Body nodes, obligations and cases remain 16 bytes; pattern nodes are 8 bytes.
Generated names reuse one spelling buffer per item. Per-constructor variable,
node and case lists use item-wide scratch pools, not one `Vec` per constructor.
The constructor obligation no longer stores an unused type-obligation handle;
its result skeleton already states that type. Arity uses `u16`, with checked
capacity boundaries including the extra failure/wildcard cases.

The tests at 10,000 one-argument constructors pin:

| Work | Fixed part | Per constructor | Total |
|---|---:|---:|---:|
| Builder obligations | 10 | 23 | 230,010 |
| Builder body nodes / lowering body visits | 38 | 45 | 450,038 |
| Pattern nodes / lowering pattern visits | 2 | 10 | 100,002 |
| Discharge lookups | 10 | 23 | 230,010 |
| Discharge instances | 7 | 20 | 200,007 |
| Discharge counted unifications | 7 | 23 | 230,007 |
| Emitted raw Lambda terms | 68 | 58 | 580,068 |

These counts are for one argument per constructor. The general decoder's
multiple-argument error matrix has quadratic size in a constructor's arity;
the plan preserves that matrix rather than changing its match semantics.
The full `Variants.res` raw Lambda is equal after stamp and exit renumbering.
The source-map oracle exposed missing constructor-application locations; an
explicit `At` node fixes them without changing child locations. An external-codec
regression test fails without that node; the complete Spice fixture also passes
with linked maps enabled.

Release measurements at `40a0c61d1`, compared with the pre-slice compiler at
`b91b359ba` (one worker; the candidate also incorporates intervening trunk):

| Application census | Before | After |
|---|---:|---:|
| Planned bindings | 5,776 | 6,392 |
| General variant bindings | 637 | 21 |
| `not_yet_planned` bindings | 764 | 136 |
| `unsupported_variant` bindings | 0 | 9 |
| `failed_obligation` bindings | 18 | 21 |
| Units retried | 2 | 2 |

The same two units retry; counting the newly eligible bindings in those units
increases the fallback binding count, not the number of retries. Other census
reasons are unchanged: user expressions 504, unmeasured shapes 87, custom codecs
36, type parameters 9 and recursive groups 6.

`bench_project.sh` on the 3,735-module application produced identical 3,980
outputs and counted 65,447,816,693 instructions before and 65,092,842,723 after
(**−0.5424%**). `compare_checker_builds.py` found no difference in 3,735 signatures,
18 diagnostic logs or 3,980 JavaScript/related outputs. Hyperfine (five measured
runs, one warmup) measured the candidate at 9.095 ± 0.363 s, range 8.789–9.559 s;
the earlier baseline was 10.155 ± 0.319 s, range 9.652–10.532 s. These timings were
not interleaved; the instruction comparison is the stronger performance result.

On `tests/ppx_spice`, the candidate's default path retired 1,934,170,258
instructions versus 1,997,544,344 with `general` (about **−3.17%**). This comparison
includes the earlier plan slices; it is not the incremental saving of variants.
`tests/tests` derives no codecs, so this change saves nothing there; CI's
instruction-count gate protects that path.

Local gates pass: compiler build, 33 focused derived tests and 15 plan tests;
rewatch build and tests (209 unit, one integration and eight runtime-snapshot
tests); check-mode builds of both Spice projects and the application; all 15
diagnostic fixtures in unset/general/check modes; and the linked-map Spice build.
The full compiler suite and OCaml output parity are CI gates, not local runs.

The original slice specification follows.


- **Files:** `binary_ast/spice_ppx.rs` (plan builder for
  `variants_generate_codecs` without `@spice.serde`),
  `raw_lambda/convert/derived.rs` (`Switch` on a declared constructor and on a string).
- **Deletes:** nothing beyond the per-shape `General(NotYetPlanned)` reason for
  variants.
- **End state:** `rg -n "NotYetPlanned" compiler-rust/src/binary_ast` lists
  only the shapes the Q5 table keeps general.
- **Gates:** as slice 2.
- **Size:** about 900 lines.
- **Saving:** 637 bindings, with the largest bodies (P99 1,355 nodes):
  expected 0.6 to 1.0% of the application's build.
- **Less capable model:** yes, once slice 2 is merged: it follows the pattern
  with two new match forms.

```text
Task: derived codecs slice 3, variants. Repository jfrolich/rescript-rust, base
ocaml-to-rust-rewrite, after slice 2 is merged. Read AGENTS.md and
compiler-rust/docs/DERIVED_CODECS.md first.

Goal: a `@spice` variant declaration without `@spice.serde`, handled today by
`variants_generate_codecs`, `variants_generate_encoder_case` and
`variants_generate_decoder_case` in compiler-rust/src/binary_ast/spice_ppx.rs
(constant constructors, constructors with arguments, inline records,
`@spice.as("literal")`), takes a plan. `@unboxed` variants, `@spice.serde`
variants and every other `General` reason of the Q5 table stay general. Do not
narrow the goal to constant-only variants.

Commits in order:

1. Characterisation: pin the raw Lambda today's converter produces for the
   encoder match over a variant with a constant, a one-argument and an
   inline-record constructor, and for the decoder's matches (`JSON.Array`
   with an empty array, the head `JSON.String("C")` cases, the argument-count
   test, the per-argument `Ok`/`Error` match).
2. Plan builder for variants behind the seam; obligations in today's typing
   order (order test on five variants). Every constructor of the declaration
   gets a `Constructor` obligation in the encoder (pattern use) and in the
   decoder (construction use).
3. Lowering of `Switch` over declared constructors and over strings through
   `compile_matching`, never a hand-built decision tree. Unit test: for every
   variant of tests/ppx_spice/src/Variants.res the raw Lambda of both forms is
   equal after renumbering stamps and static exit numbers. Step-count test at
   10,000 constructors: assert the exact number of builder calls per
   constructor and that nothing is quadratic.
4. Remove the `NotYetPlanned` reason for variants.

Checks to paste: the same list as slice 2, plus a fixture (with and without
`general`) for a private variant whose constructors are used only by its
codecs, asserting no unused-constructor warning in either mode.
```

### Slice 3b as built

The census separates successful planned typechecking/conversion from general
bindings, reports a closed unsupported-form census and inclusive costs for all
six obligation kinds. General group reasons use dense parse-value-list tables.
Retry events identify the last obligation and expected owner, not the resolved
conflicting type; the retry remains the safety net.

JSON identity plans remove the application's 136 formerly unplanned bindings.
The final application census is 6,534 plans, 21 upfront
`shadowed_result_constructor`, zero `failed_obligation` and zero
`json_identity_argument`. Local JSON aliases are resolved syntactically in the
same lazy prefix scan; the unchanged oracle fixture covers direct and nested
containers, alias uses, records and variants. Exposed encoder applications whose
sharing differs take the named general reason before planning. No linking-only
inference or application-callee lowering is retained.

Constructor descriptions use a dense name table keyed by binding epoch and
`Owner`, owned by a fresh typed arena per unit. All lookups, usage marks,
instantiation and unification remain. The isolated sharing experiment saved
0.0302945%; a 10,000-field record retains seven descriptions. Inclusive profile
and measured marginal per-field costs are in `DERIVED_CODE.md`; marginal
per-variant-constructor instruction attribution was **not measured**.

Source-prefix scope is lazy and tested on 10,000 distinct derived items,
10,000 constructors, and 10,000 nested items. The no-derive test exercises the
real dispatch and observes zero scope work. No-derive units still execute the
constant-time dispatch, empty prefix initialization, and disabled census probes
per rewritten item and per type declaration; this is not zero total overhead.

Spice/application check builds and 19 diagnostic fixtures in all three modes
pass. The census-off gate is CI's fat-LTO, one-codegen-unit comparison; the
separate local default-16-unit table is not substituted for it. The reviewed
`d306a20b68` CI comparison was -0.014%; subsequent correction-head CI is reported
in the PR body rather than claimed from this historical measurement.
Unresolved external/opened JSON arguments now carry a 16-byte
`NotJsonIdentity` obligation. It reads the owning declaration's checked manifest,
uses exact path lookup with spelling recovery refused, and bounds each nullary
alias walk at 64 declarations. It compares shared declaration identity and
normalized canonical paths, without new inference or abbreviation writes.
The cross-unit/module-alias/open/legacy fixtures pass check mode; record controls
retain plans. Application plans stay 6,534 with six guards emitted and zero guard
failures; generated outputs remain identical. Detailed commands and limits are
in `DERIVED_CODE.md`.
`RESCRIPT_DERIVED_PATH` and the oracle remain; slice 4 is held below.

### Slice 4. Remove the switch

**Status: held until the new checker handles derived items.**

- **Files:** `driver.rs`, a test under `compiler-rust/tests/` or the existing
  Spice test module.
- **Deletes:** `RESCRIPT_DERIVED_PATH`, the dual compilation and its
  comparisons, the CI step (maintainers).
- **End state:** `rg -n "RESCRIPT_DERIVED_PATH" .` has no match;
  `rg -n "DerivedPath" compiler-rust/src` has no match.
- **Gates:** the new forced-`General` parity test on `tests/ppx_spice`; CI.
- **Size:** minus about 250 lines, plus an 80-line test.
- **Saving:** none.
- **Less capable model:** yes.

Polymorphic variants, tuples, `@spice.serde`, custom codecs and parameterised
types are not sliced. Each needs a census first that shows its share.

## Risks and what was not measured in the original projection

The following are historical limits of the initial projection, not the status
of the implemented slices described above.

- **Nothing was prototyped.** Every removal fraction is extrapolated. The
  type-checking range rests on counter ratios from `tests/ppx_spice`, whose mix
  (172 variant bindings, 99 record bindings) is unlike the application's
  (637 and 5,988).
- **The Lambda passes and the lowering were not split** between derived and
  other code. "About 3 points" is a node-share extrapolation, and so is the
  claim of what remains.
- **Match compilation through `compile_matching` without typed expression
  nodes was not tried.** It is the first commit of slice 2 and the document's
  one explicit decision point.
- **Type sources.** That `Stated` and `ResultOf` reproduce the node inference
  records, including which abbreviation a library signature uses, was reasoned
  from `type_function_nary` and `type_application`, not tested. The
  stored-interface comparison of the oracle is what catches it; a variant of
  the Spice library whose codecs are annotated with abbreviations should be
  added to the corpus in slice 1.
- **Coverage.** The census does not count `@spice.codec`, non-constant
  payloads or shared label names. If they are common in the application, the
  saving shrinks in proportion. Slice 1's census reports the reasons.
- **Stored `.ast` and external PPX.** Where the binary AST is written relative
  to the derive, and whether an external `-ppx` can run after it, was not
  established; slice 1 writes the general form there so nothing changes, at
  the cost of generating syntax in that configuration.
- **Editor tooling.** Whether hover, references or rename read the typed
  bodies of derived bindings (through the type-constructor locations the
  built-in codec identifiers carry) was not established.
- **Functor bodies and first-class modules.** A derived declaration inside a
  module expression takes a plan like one at the top level (slice 2); the
  walks over nested structures read the obligation results where they read
  the identifiers of a typed body. `%%private` admits no type declaration, so
  no derived declaration sits in one.
- **Obligation order.** The first reported failure and the order of
  deprecation warnings depend on discharging in today's typing order. The
  order tests assert it for a handful of declarations; the fixtures and the
  oracle carry the rest.
- **Time, not instructions.** The application figures are single wall-clock
  runs with one worker. With several workers the shares apply to processor
  time, not to elapsed time.
