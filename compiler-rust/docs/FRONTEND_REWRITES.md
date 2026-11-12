# Built-in frontend rewrites

This inventory describes `src/binary_ast/ppx.rs`, not an OCaml-compatible
intermediate representation. The observable contract is JavaScript,
diagnostics, and usable compiler artifacts. Moving a rewrite must preserve
warning/error order as well as its successful result.

## Boundaries

`rewrite_structure_with_warnings` and `rewrite_signature_with_warnings` are
entry points. `check::Checker` validates the original tree before mapping;
`NestedExternals` validates nested external declarations, and
`UnusedAttributeSweep` runs separately. These traversals are **not** redundant
just because a node's successful rewrite is the identity.

JSX lowering is a separate parser frontend mapper (`parser/jsx_ppx.rs`);
`ppx::rewrite_jsx_element` only recursively maps its expressions. Derives enter
through `binary_ast::derive`, which delegates to `spice_ppx` on the current tree.
External executable PPXs are not part of this pipeline.

## Inventory

Function names below are in `binary_ast::ppx` unless qualified. “Parser” means
at node completion, not at token consumption. “Checker” means at consumption,
before the construct's ordinary typing rule. Destinations are proposals, not
claims that these moves have been implemented.

| Match | Produced result | Function(s) | Context beyond node | Candidate destination |
|---|---|---|---|---|
| External `@val`, `@module`, `@scope`, `@send`, `@new`, `@get`, `@set`, `@get_index`, `@set_index`, `@variadic`, `@return`, `@obj`, `@taggedTemplate` | Encoded `ExternalFfi` primitive and consumed FFI attributes | `is_rs_external`, `encode_external`, `build_external_decl`, `filter_ffi_attributes` | Full declaration type, primitive, attribute usage and diagnostics | Checker declaration entry |
| External argument/result annotations, including `@as`, `@string`, `@int`, `@unwrap`, `@ignore`, optional labels and return wrappers | Parameter labels/constants/conversions, result conversion metadata | `build_arg_type_specs`, `refine_arg_type`, `external_type_ffi_attr`, `build_obj_ffi_type` | Enclosing external declaration and argument position | Checker external encoding |
| `@obj` external with wildcard return | Object result type with argument-derived fields | `process_obj_type` | All external arguments and declaration location | Checker external encoding |
| Relative-path module external | Constrained include containing external, preventing cross-module inlining | `rewrite_structure_item_no_spice`, `check_decl`, `is_package_relative_path` | Declaration's module source | Checker declaration entry |
| `@inline` single nonrecursive constant binding | Inline external primitive | `transform_inline_binding`, `inline_string_semantic` | Binding pattern, recursiveness; semantic literal text | Parser completed binding or checker binding entry |
| `@inline(value)` signature value | Inline external primitive | `transform_inline_sig_value` | Declared type and payload | Checker signature value entry |
| Integer expression with `l` suffix | Original node retained; digits read by `Constant::integer_digits` | `typecore::convert_constant`, `check_constant`, inline constant consumers | None | Direct (implemented) |
| Integer pattern with `l` suffix | Original pattern handle retained; same digit accessor | `typecore::convert_constant`, `check_constant` | None | Direct (implemented) |
| Binary `a -> f` | Application, constructor/variant application or tuple pipe, with temporary binding when needed | `desugar_pipe`, `rewrite_pipe_rhs`, `pipe_tuple_map`, `pipe_bound`, `fresh_bound_name` | Names in RHS, evaluation count/order | Parser completed pipe or checker expression entry |
| Single nonrecursive record/dictionary-pattern local binding (including alias), except packed module RHS | Typed match from one borrowed case; merged expression/binding attributes | `parsetree_viewer::single_record_binding`, `typecore::type_match` | Binding group and RHS shape | Direct (implemented) |
| Supported `let?`/unwrap binding | Match with early-return and continuation cases | `classify_let_unwrap_pattern`, `rewrite_unwrap_binding_let` | Experimental-feature setting, top-level vs local context | Checker binding entry |
| Simple tuple binding with matching tuple RHS (possibly under opens) | Separate bindings, preserving opens | `rewrite_value_binding`, `destruct_open_tuple`, `restore_exp` | Complete pattern/RHS; recursive bindings excluded; value-constraint side data | Parser completed binding group or checker binding entry |
| Record pattern binding to packed module identifier | Separate bindings referring to module fields | `rewrite_value_binding` | Complete RHS and unqualified field patterns | Checker binding entry |
| Two unguarded true/false match cases | Typed conditional with arms in boolean order | `parsetree_viewer::boolean_match_arms`, `typecore::type_conditional` | Both cases | Direct (implemented) |
| `async` function | Existing typed promise application, without a parsed wrapper | `typecore::type_body_with_module_unpacks`, `type_promise_application` | Parameter/module-unpack scope and parameter location | Direct (implemented) |
| `await e` | Existing typed `Primitive_promise.unsafe_await` application, without a parsed wrapper | `typecore::type_promise_application`, `ParseArena::ghost_location` | Validation needs enclosing async function; ghost location comes from operand | Direct (implemented); `transform_await` serves module await only |
| Awaited module alias, with optional module-type constraint | Dynamic import expression, module unpack and module type declaration | `transform_module_await`, `create_await_module_expression`, `local_module_type_decl` | Per-structure module-type-name deduplication | Checker module entry; not node-local parser work |
| Local awaited module inside a value binding | Hoisted module type declarations plus rewritten local module | `spelunk_value_bindings_for_await_module_types`, `spelunk_expression_for_await_module_types`, `rewrite_expr` (`Pexp_letmodule`) | Enclosing structure, deduplication, original binding before rewriting | Checker structure/binding entry |
| `@this` function | Method callback record/constrained callback/unsafe-to-method application | `rewrite_method_callback_expression`, `split_this_attrs` | Function arity, async body and parameter shape | Checker function entry |
| `@this` on braces around function | Attribute forwarded through braces to function; unrelated attributes retained | `add_this_to_braced_function`, `rewrite_expr` (`Pexp_braces`) | Braced descendant shape; rewritten inner location | Parser completed braced expression or checker expression entry |
| `@this` arrow type | `Js.OO.Callback.arityN<...>` type | `rewrite_core_type` | N-ary arrow side table or recorded arity | Checker type entry |
| Object type field attributes | Last `@this` forwarded to field type; other attributes reversed; `@set` retained for checker | `rewrite_object_fields`, `process_attributes_rev` | Field type | Checker object type entry |
| `%raw` / `Pexp_raw` expression | Local raw external application, with function-literal information | `handle_raw`, `handle_raw_node`, `raw_expression`, `raw_local_external_apply` | JS parser classification, payload and source locations | Checker expression entry |
| `%ffi` / raw FFI node | FFI raw expression with literal function arity | `handle_ffi`, `ffi_expression`, `detect_js_function_arity` | JS source classification | Checker expression entry |
| Regexp literal | Constrained raw expression of `RegExp.t` | `rewrite_expr` (`Pexp_regexp`) | Separate regexp validation/warnings | Parser completed regexp or checker expression entry |
| `%todo` / `Pexp_todo` | `Stdlib_JsError.throwWithMessage` with source position and optional message | `handle_extension`, `todo` | Source filename, line, columns; separate warning | Checker expression entry |
| `%%raw` / `Pstr_raw` | Evaluation of raw-statement external | `handle_raw_structure`, `handle_raw_structure_node`, `raw_structure` | Payload/source location, JS statement validation | Checker structure item entry |
| Consecutive `%%private` items | Local module and overriding open | `private_extension_structure_items`, `wrap_in_local_module`, `rewrite_structure_impl` | Adjacent items, local-name counter, mapper order | Checker structure entry; not node-local |
| `@deriving(accessors)` type group | Type declarations and generated record getters / variant constructors in constrained includes | `handle_deriving_type`, `generate_accessor_include`, `generate_record_accessors_and_sigs`, `generate_variant_accessors_and_sigs` | Whole mutually recursive type group; gentype attributes; structure/signature distinction | Checker type-group entry |
| Spice derive attributes | Encoder/decoder declarations and signatures | `derive::expand_structure_item_with_mapper`, `derive::expand_signature_item_with_mapper`, `spice_ppx::map_type_decl_structure`, `spice_ppx::generate_sig_decls` | Mapper activation over containing structure/signature; derive configuration, type group | Checker type-group entry; preserve activation semantics |
| Attributes and extension payloads traversed by the mapper | Recursively rewritten payload AST | `rewrite_attribute`, `rewrite_payload`, `rewrite_attributes` | Payload kind; `PTyp` is retained; unknown expression extensions are retained without descending | Parser payload completion or checker attribute consumer |
| JSX component annotations on bindings/descriptions | Annotation round-trip through attributes and dedicated component side data | `rewrite_value_binding_without_flattening`, `rewrite_structure_item_no_spice`, `rewrite_signature_item_no_spice`, `ast_jsx_component::take` | Binding/description representation | Checker binding/description entry |
| JSX elements/fragments and component declarations (separate mapper) | React/JSX runtime calls, props records and component wrappers/signatures | `parser::jsx_ppx::{transform_jsx_element,transform_jsx_fragment,mk_react_jsx,make_props_record_type,make_props_record_type_sig}` | JSX version/module/mode configuration and component scope | Parser completion with explicit configuration, or checker component entry |

Many comments still describe string-delimiter normalization from an older
representation. The current `rewrite_expr`/`rewrite_pattern` constant
branches do not rewrite every string: do not infer a trigger from those comments.
Likewise, `@get`/`@set` object fields are not expanded here; the checker consumes
them. Unknown attributes still matter because their payloads can contain real
rewrite targets.

## Safe subtree skipping

`ParseArena::push_expr` computes a bottom-up certificate using existing child
certificates. `rewrite_free_exprs` holds two bits per expression, not fields on
each node (see Validation traversals). `expr_needs_no_rewrite` is an O(1) lookup used by `rewrite_expr`.
The whitelist contains attribute-free ordinary applications (not pipes),
constants except `l` integers, identifiers, break/continue, tuples, arrays,
constructors/variants, field access, assertions, sequences, while loops,
ternaries, if expressions and records, provided every expression child is also
certified. New/unknown expression variants default to the full mapper.

Functions, patterns, types, braces, modules, bindings, extensions, JSX and all
attributes remain conservative. In particular, braces must not be skipped based
only on their own attributes: an enclosing `@this` can be forwarded through them.
Only certified diagnostic-free expression subtrees are skipped by validation. The marshal location marker is retained for
the skipped root; attribute-free descendants do not require attribute-wrapper
sharing markers. This does not claim byte-identical intermediate AST encoding.

`get_expr_mut` and `initialize_expr` invalidate the changed index and all later
certificates. Certified parents are allocated after their certified children;
reserved slots are never certified. This deliberately sacrifices some skip
opportunities rather than keeping stale proofs after mutation. Shared synthetic
expressions have no certificate. No new global state or unsafe code is used.

## Expansions

The expression mapper (`rewrite_expr`) rebuilds nothing. It visits the
expressions that have no certificate, where they are, and a construct a
rewrite applies to gets its desugared form **appended** and recorded with
`ParseArena::set_expansion(original, expanded)`. The expansion refers to the
children by their handles as parsed; the node as parsed and all of its
ancestors keep their nodes. Readers of the tree as compiled resolve a handle
with `ParseArena::expanded` where they turn it into a node: the checker
(`typecore.rs`, `typemod.rs`), dependency collection (`deps.rs`), the default
`AstIter::expr` and `UnusedAttributeSweep`, the v0 mapper (`mapper_to0.rs`)
and `Ast_payload.unwrap_braces`. `check::Checker` and the printer read the
tree as written and do not resolve; before the mapper has run, resolving is
the identity.

The table is two parts: a bit per expression beside the two certificate bits
(four bits per expression in `rewrite_free_exprs`, one unused), and the
targets in pages of 64 consecutive expressions, allocated when a page gets
its first expansion (`expansion_pages`, `expansion_targets`). Resolving a node
without an expansion is one bit test; with one, two more indexed loads. There
is no hashing.

A node gets an expansion in two cases:

- a rewrite of the inventory applies to it (the pipe, `let?`, the record
  `let`, the boolean match, `async` and `@this` functions, `await`, an awaited
  local module, raw, ffi, regexp, todo, an `l` integer, braces whose location
  follows a rewritten operand or that forward `@this`);
- a child that is not an expression changed its handle: a pattern
  (`rewrite_pat_idx`), a core type (`rewrite_core_type_idx`), a module
  expression, a value binding that was flattened or carries a locally
  abstract constraint, or the node's attributes (`rewritten_attributes`). The
  expansion is then a copy of the node that refers to the changed child.
  Patterns, core types, module expressions and structure items are still
  rebuilt by their own mappers; `pattern_needs_no_rewrite` keeps the handle
  of a pattern that has no attribute, `l` integer, type or extension below
  it, so that a `switch` or a function does not get an expansion for its
  patterns alone.

No rewrite of the inventory had to stay a rebuild: every one of them is read
only by readers that resolve.

## Validation traversals

The three traversals have different inputs and observable scheduling. None is
merged here: sharing their recursion would require replaying separate event
streams, retaining the original and rewritten trees, and reproducing the
mapper's early exits. Skipping provably irrelevant subtrees avoids that state.

### `check::Checker` (original tree)

Carries mutable arena access, `async_context` (initially true), the fixed
`let_unwrap` feature setting, and an ordered warning vector. Each expression
saves/restores async state; functions replace it with their own async flag,
`@this` callbacks and functor bodies clear it. Await validation is post-order.
The first error aborts; only warnings preceding it survive.

It follows the builtin mapper, **not** `AstIter`: attributes precede ordinary
expression children; constructor arguments/record fields of the mapper are
evaluated right-to-left, lists left-to-right. Cases visit RHS, guard, pattern;
nonrecursive binding groups visit last binding first. Structure ordering uses
`structure_mapper_order`, including head-first special items and awaited-module
checks; signatures are left-to-right. Boolean matches use false arm, true arm,
scrutinee. Record/unwrap bindings follow their rewritten match order. Object
types visit tagged field types in reverse, excluding inherited types and the
object's own attributes. Attribute payloads recurse through structures,
signatures, types, and pattern guards (guard before pattern). Expression
extensions validate their own payload without traversing it; raw/todo nodes
also have dedicated handling. Integer `l` expressions/patterns now retain their source nodes; the ordinary attribute traversal applies.
`@@config` is not mapped; consumed deriving attributes are omitted.

The diagnostic-producing sites (other nodes only lead to these sites) are:

| Site | Checks and diagnostics |
|---|---|
| Await expressions, `for await`, awaited local/structure modules | Await outside async context error |
| `@this` functions, including forwarding through braces | Non-variable first parameter and optional-argument errors |
| Pipe applications | Labelled arguments and non-binary pipe errors |
| Local/top-level unwrap bindings | Feature disabled, unsupported shape/type, top-level unwrap errors |
| Packed-module record destructuring | Record-rest and invalid field-pattern errors |
| Raw nodes, `%raw`, `%ffi`, `%%raw`, regexp literals | Raw payload kind / non-function FFI errors; JS/regexp parse diagnostics (`BsFfiWarning`) |
| Todo nodes and `%todo` | `BsTodo`, including semantic string escape errors |
| Inline string bindings, payload semantic strings | Invalid template escape errors |
| Last declaration's `@deriving` | Duplicate/configuration/unsupported or removed deriver errors; `BsDeriveWarning`; accessors inline-record constructor errors and abstract/open type warnings |
| ReScript external declarations | `validate_external_attribute_errors`: attribute payload/conflict/name/arity errors, object argument rules, argument/result FFI annotations and return-wrapper rules; associated FFI/unused-attribute warnings |

External validation reads the entire arrow type, argument/result annotations,
primitive and declaration attributes (rewriting their payloads first). Its
helper chain is `validate_external_attribute_payload_errors`,
`parse_external_attrs`, `validate_plain_obj_arg_type_errors` or
`validate_non_obj_arg_type_errors`, plus the remaining checks in
`validate_external_attribute_errors`; it also marks consumed attributes used.
The external attribute inventory above lists the names, including `@as`,
`@string`, `@int`, `@unwrap`, `@ignore` and `@return` on types.

### `NestedExternals` (each expanded item, before rewriting it)

Uses ordinary `AstIter` order, traversing all node children and all four
payload kinds. Its only state is a preorder vector of cloned value
descriptions: `Pstr_primitive` and **every** `Psig_value`, including values
without primitives. The caller starts with `walk_*_item`, so the root item's
external is excluded (validated separately). Descendants include modules,
functors, module types, local modules and payloads. After collection it calls
`validate_external_attribute_errors` in vector order, stopping at the first
error. It has the same external errors and attribute-use effects described
above, but discards the helper's warning vector. Derive expansion precedes
this traversal, so it is not interchangeable with the original-tree Checker.

### `UnusedAttributeSweep` (rewritten tree)

Uses `AstIter` order with an ordered warning vector, `stopped` flag and first
error. This is a later phase: attributes may have been consumed or generated,
externals encoded, and integer `l` suffixes removed. It inspects:

- Attributes: errors for removed `ocaml.deprecated`, `ocaml.unboxed`,
  `ocaml.immediate`, `ocaml.warnerror`, `ocaml.boxed`,
  `ocaml.deprecated_mutable`, `ocaml.text`, `ocaml.warning`,
  `ocaml.ppwarning`; `BsUnusedAttribute` for non-ghost, unused `as`, `config`,
  `ignore`, `int`, `optional`, `res.hoistedFunction`, `string`, `unwrap`.
  **Attribute payloads are not traversed.**
- Extensions: removed `ocaml.error` error, then payload traversal otherwise.
- Expression and pattern constants: unsuffixed integer overflow warning
  (`BsIntegerLiteralOverflow`), then attributes only.
- Type declarations: built-in rank-zero type redefinition error before children.
- Value descriptions: `%identity`/`%component_identity` arity-one error;
  unsafe primitive names (not starting `%`, `#`, `?`) emit `BsFfiWarning`
  and skip children. Other descriptions recurse normally.
- Label declarations: semantic string `@as` marks usage before children;
  invalid string escapes raise an error.
- Constructors: `process_constructor_tag` errors (invalid/duplicate `@as`
  and invalid runtime tags), then redefinition of `false`, `true`, `()`;
  otherwise children are visited.

The first raised error stops subsequent emission; earlier warnings are kept.
Keeping the phase and traversal order unchanged preserves this behavior.

### Certificates

The existing rewrite whitelist excludes every Checker and NestedExternals
trigger: even ordinary applications exclude pipes. Both can return immediately
when bit 0 is set. It is **not** sufficient for UnusedAttributeSweep: ordinary
unsuffixed integers can overflow. Bit 1 excludes those literals as well,
without parsing their text during allocation. Both bits share the packed side
table (two bits per expression) and are computed in one bottom-up immediate-
child pass. Intersection propagates both proofs; unknown kinds, attributes,
patterns, types and modules remain conservative. Mutable access and reserved
slot initialization invalidate both bits at that index and every later index.
There is no cached diagnostic or change to warning state at a skipped node.

## Measurements

Baseline: `ba94d6ef7`. Linux x86-64, pinned nightly-2026-11-10, ordinary
fat-LTO `cargo build --release --manifest-path rewatch/Cargo.toml` (not PGO).
The clean single-thread `tests/tests` build parses 711 source files and compiles
711 modules. Set `RESCRIPT_RUNTIME` to `packages/@rescript/runtime` and
`RAYON_NUM_THREADS=1`; build the runtime with each executable first, then run:

```sh
rescript clean tests/tests
valgrind --tool=callgrind --callgrind-out-file=profile rescript build tests/tests
callgrind_annotate --inclusive=yes --threshold=100 profile
callgrind_annotate --inclusive=no --threshold=100 profile
```

Warm each executable's identity cache before measuring: the initial candidate
run accidentally included a cold executable hash, adding about 81 million
instructions in `blake3_hash_many_avx2`. That run is excluded. Building the
runtime first warms the cache without retaining any project build output.

| Instructions (Ir) | Before | After | Change |
|---|---:|---:|---:|
| Whole clean build, warmed identity | 4,621,362,409 | 4,597,734,644 | -0.51% |
| Builtin structure + signature entry paths, inclusive | 239,328,915 | 211,079,466 | -11.80% |
| Share of whole build | 5.18% | 4.59% | -0.59 percentage points |

The pass count is the inclusive cost of the outer `rewrite_structure_impl`
plus `rewrite_signature_with_warnings`; do **not** add the recursive `'2`
structure entries again. It includes nested mapping, checks, allocation and
helper calls, but not separate JSX lowering or later unused-attribute sweeps.
A second baseline run gave 4,612,524,592 instructions; neither local sample is
a substitute for CI's five-run instruction-count comparison.

### Visits and structural changes

A separate, unoptimized instrumentation run counted entry calls and
`result != input` at `rewrite_expression`, `rewrite_pattern`,
`rewrite_core_type`, `rewrite_module_expr`, `rewrite_module_type`, and
`rewrite_attribute`. Counters were stored per arena, emitted once at each
public structure/signature entry, and summed over 1,016 entries, including
interfaces and runtime. Baseline mode used the original `rewrite_child` leaf
predicate; candidate mode used certificates. The temporary instrumentation
was removed before instruction measurement and is not in production code.

These are **structural changes**, including rebuilt child handles, not counts
of semantically changed source constructs. They deliberately expose the waste
in the mapper; an unchanged semantic tree can still allocate new handles.
Visits include repeated traversal, not distinct arena nodes. The six mapper
families do not count structure/signature items or individual list elements.

| Mapper family | Before visits | Before changed | After visits | After changed |
|---|---:|---:|---:|---:|
| Expressions (full mapper) | 67,455 | 56,156 | 33,613 | 28,492 |
| Patterns | 33,016 | 3,382 | 33,016 | 3,382 |
| Core types | 15,554 | 4,480 | 15,554 | 4,480 |
| Module expressions | 1,423 | 982 | 1,423 | 981 |
| Module types | 451 | 293 | 451 | 293 |
| Attributes | 6,122 | 208 | 6,122 | 75 |
| Total full mapper entries | 124,021 | 65,501 | 90,179 | 37,703 |
| `rewrite_child` requests | 121,580 | — | 52,362 | — |
| Requests retained by index | 70,618 | 0 | 35,242 | 0 |

Fewer retained-by-index requests after the change is expected: retaining an
entire subtree prevents requests for its descendants. Adding retained requests
to full expression entries gives 138,073 before and 68,855 after expression
visits. Expression full-mapper calls drop 50.2%.

### Instruction attribution by family

The following is **self** cost of symbols containing `binary_ast::ppx::`,
including generic instantiations naming PPX visitors. It is a non-overlapping
attribution of 100,517,132 before / 90,465,187 after instructions, not a sum of
inclusive family costs. Inlined transformations inside
`rewrite_expression_generic` remain in traversal/other; allocator, JS parser,
Spice and other out-of-module callees are not attributed to these families.
Consequently it is not valid to read, for example, the tiny raw row as the full
cost of parsing raw JavaScript.

| Family (symbol grouping) | Before Ir | Before share | After Ir | After share |
|---|---:|---:|---:|---:|
| Diagnostics/validation (`Checker`, `validate_*`, `UnusedAttributeSweep`, `NestedExternals`, warning helpers) | 49,705,118 | 49.45% | 50,146,254 | 55.43% |
| Traversal/other | 42,778,433 | 42.56% | 32,048,045 | 35.43% |
| External FFI | 3,864,076 | 3.84% | 3,965,336 | 4.38% |
| Async/await | 2,105,086 | 2.09% | 2,124,811 | 2.35% |
| Binding flattening | 1,471,332 | 1.46% | 1,535,710 | 1.70% |
| Pipes | 269,498 | 0.27% | 314,542 | 0.35% |
| Inline constants | 156,589 | 0.16% | 156,589 | 0.17% |
| Accessors | 124,467 | 0.12% | 126,564 | 0.14% |
| Raw/regexp/todo | 33,416 | 0.03% | 37,614 | 0.04% |
| Method callbacks/object fields | 9,117 | 0.01% | 9,722 | 0.01% |

### Wall time

`hyperfine --runs 5 --warmup 1`, preparing each run with `rescript clean
tests/tests`, using the same environment as above:

| | Mean ± standard deviation | Min–max |
|---|---|---|
| Before | 626.2 ± 28.9 ms | 605.4–675.6 ms |
| After | 579.5 ± 23.2 ms | 552.1–606.2 ms |

This short local timing sample is supporting evidence, not a performance
promise. The CI instruction gate remains authoritative.

### Validation subtree skipping

Baseline `8a19c272c`, same Linux x86-64 toolchain, fat-LTO release,
single-thread clean `tests/tests` build and warmed executable identity protocol
as above. Both builds parsed/compiled 711 modules. These are new measurements,
not a continuation of the earlier baseline/candidate sample.

| Instructions (Ir) | Before | After | Change |
|---|---:|---:|---:|
| Checker self | 25,524,372 | 12,465,060 | -51.16% |
| NestedExternals self | 9,297,545 | 5,493,386 | -40.92% |
| UnusedAttributeSweep self | 13,095,539 | 8,503,068 | -35.07% |
| Three validation families self | 47,917,456 | 26,461,514 | -44.78% |
| All PPX-named symbols self | 90,457,455 | 69,181,839 | -23.52% |
| Builtin structure + signature entry paths inclusive | 211,395,554 | 175,553,776 | -16.95% |
| Whole clean build | 4,522,664,496 | 4,480,699,379 | -0.93% |

The three self-cost rows sum all symbols naming the corresponding visitor
(including generic AstIter instantiations), using `callgrind_annotate
--inclusive=no --threshold=100`. They do not include out-of-module callees or
shared `validate_*` helpers, unlike the earlier Diagnostics/validation row.
The pass row again adds only the outer `rewrite_structure_impl` and
`rewrite_signature_with_warnings`, not recursive entries. UnusedAttributeSweep
is outside those entry paths and is included in the whole-build count.

Hyperfine, five runs with one warmup and a clean before each run:

| | Mean ± standard deviation | Min–max |
|---|---|---|
| Before | 512.0 ± 13.5 ms | 502.8–535.6 ms |
| After | 669.8 ± 311.2 ms | 505.2–1225.7 ms |

The candidate timing sample has a large outlier; it does **not** demonstrate a
wall-time improvement. Instruction counts, rather than this noisy timing,
are the performance evidence. CI's repeated instruction-count gate is the
acceptance check.

CI Instruction count (five runs, minimum of each side): **4,508,872,410 →
4,464,721,357**, a reduction of **44,151,053 instructions (0.979%)** across
711 modules. [Comparison run](https://github.com/jfrolich/rescript-rust/actions/runs/43125250180).

### Expansions instead of rebuilt ancestors

Baseline `2979e7f97`, Linux x86-64, fat-LTO release with one codegen unit,
single-thread clean `tests/tests` build (727 modules), the runtime built
first. Callgrind for the breakdown, cachegrind for the totals (the smallest of
three and of five runs).

Before the change, one profile of 4,070.1 M instructions:

| Instructions (Ir) | | Share of build |
|---|---:|---:|
| Builtin structure + signature entry paths, inclusive | 183.0 M | 4.50% |
| Self cost of the expression mapper's functions (visit, clone, push and drop, inlined) | 109.0 M | 2.68% |
| Their callees outside the expression mapper (patterns, types, attributes, allocator, the visited-location set) | 52.9 M | 1.30% |

The profile cannot separate the rebuild from the visit: both are inlined into
the same functions. The change does: the same entry paths cost 154.3 M after
it, so **rebuilding was 28.7 M (0.70% of the build)**, and visiting, the three
other mappers, the checks and the structure items are the remaining 3.8%.

On the 720 implementation files of `tests/tests` that the mapper accepts
without the JSX transform: 83,113 expressions, 15,489 without a certificate
(each was cloned and pushed again), **2,053 with an expansion** after the
change, for which 3,895 expression nodes are appended. So about 13,400
expressions were rebuilt whose own construct no rewrite applies to.

| Instructions (Ir) | Before | After | Change |
|---|---:|---:|---:|
| Clean build of `tests/tests`, local, 727 modules | 4,073,542,665 | 4,034,320,027 | -0.963% |
| The same, CI instruction count, 735 modules | 4,078,163,440 | 4,038,720,685 | -0.967% |
| of which the visited-location set as a bit vector instead of a hash set | | | -0.17% |
| Clean build of a 3,735-module application, one run each | 69,574,364,296 | 69,092,936,764 | -0.692% |

The saving is below the 1% that THREE_TREES section 11 expected of this
slice: the rebuilt spine was 0.70% of the build, not the 4.13% of the two
entry paths. What is left in those paths is not rebuilding.


### T7 pre-change inventory

Baseline: `3fa9eb29e` (includes T2). Line numbers below refer to that commit.
These are shared functions, not four independently removable passes.

| Row | Implementation in `binary_ast/ppx.rs` | What must remain |
| --- | --- | --- |
| A, `l` integer | `rewrite_expr:7173` constant arm at 7190; `rewrite_pattern:6670` constant arm at 6676; `pattern_needs_no_rewrite:7082` certificate test | The expression/pattern traversals serve all other rewrites. Remove their integer arms, not these shared functions. Patterns are rebuilt, not entered in the expression expansion table. |
| B, boolean match | `boolean_match_arms:7728`, called by `rewrite_expr:7346` | Ordinary match case traversal remains. Recognition requires exactly two unguarded nullary unqualified constructors, in either order. |
| C, record/dictionary let | `rewrite_single_binding_let:7761`, record arm after the unwrap arm | The same function implements `let?`, which stays an expansion. Includes one alias wrapper; excludes recursive/grouped bindings and packed-module RHS. |
| D, async/await | `rewrite_fun:7901`, `wrap_with_unsafe_async:5575`, `transform_await:5536`; `rewrite_expr:7552` | `transform_await` is also called by `create_await_module_expression:5787`; the async wrapper is also called by `rewrite_method_callback_expression:6923`. Module await and method callbacks are separate expansion rows. |

#### Readers of the compiled form

Audit command: `rg -n 'expanded\(|get_expanded_expr' compiler-rust/src`.
At the baseline this returns 207 lines. Three `types/ctype.rs` hits are
`has_constr_row_expanded`, unrelated to parse expansions. The parse-arena
hits include accessor definitions and tests, not independent consumers.

| Reader | A: integer | B: boolean match | C: record let | D: async/await |
| --- | --- | --- | --- | --- |
| `types/typecore.rs` (143 hits), `types/typemod.rs` (12 hits) | `convert_constant` must accept the digits without treating `l` as an unknown modifier; both expression and pattern consumers use it | Dispatch to the existing conditional rule, preserving `IfCondition`/`IfReturn` and boolean arm order; shape-sensitive diagnostic/nonexpansiveness readers also need auditing | Dispatch to `type_match` with one borrowed case, not ordinary let typing; preserve merged attributes and the packed-module exclusion | Build the same primitive identifier/application typed nodes, with the same type instantiation, locations and attributes; the existing `type_await:17138` is an incomplete stub, not an implementation to reuse |
| `binary_ast/deps.rs:137` | No dependencies in the digits | Same source children; boolean constructors add no module dependency | Same RHS, pattern and body; preserve module-unpack scope | The generated identifier supplies `Primitive_promise`; original async/await nodes must contribute that implicit dependency explicitly |
| `binary_ast/ast_iter.rs:38`, used by `UnusedAttributeSweep` | `check_constant:1219` currently warns only on suffix-free integers; it must recognize `l` through the same digit accessor | Expansion discards the case patterns; walking originals must not introduce warnings for their attributes | Expansion merges binding attributes onto the match; preserve sweep ordering and warning locations | Expansion drops await-node attributes, uses a ghost operand location, and wraps async bodies at parameter location; walking original nodes must preserve that attribute policy |
| `binary_ast/mapper_to0.rs:233` | Can encode the original suffix; any compiled-value consumer needs the digit accessor | Original match is representable in v0 | Original let is representable in v0 | Original await is encoded with `res.await`; original async with the function marker. This is not the same v0 shape as the primitive expansion |
| `binary_ast/writer.rs` | Uses `mapper_to0` and dependency collection, not a separate expansion lookup | Same | Same | Same; artifact usability must be verified, not inferred from changed bytes |
| `binary_ast/ppx.rs` (32 hits) | Inline implementation/signature constants currently match `Integer(_, None)`; these consumers must also use the accessor | Pipe and payload readers inspect expanded shapes; removal must not change their classification | Same; retain the separate unwrap and packed-module rules | Braces copy an expanded inner location; removing await also affects the braces expansion count. Method callbacks and module await share the primitive helpers |
| `ast_payload.rs:14` | String-only extraction does not consume integer values | Unwraps braces; no boolean-specific need | Unwraps braces; no let-specific need | Unwraps braces; location/attribute policy belongs to callers |
| genType | Reads typed constants, not parsed digits | Reads the resulting typed conditional | Reads the resulting typed match | Reads the resulting primitive application/function; no parse-expansion lookup found |
| Editor analysis | Reads typed constants and original source locations | Reads typed conditional and source | Reads typed match and source | Reads typed applications/function and source; no parse-expansion lookup found |

The binary writer's module comment still promises byte-identical `.ast`
files, whereas the correctness contract requires usable artifacts, not
identical intermediate representations. A direct implementation must check
usability explicitly. In particular, simply deleting an await expansion is
not sufficient: the checker stub neither constrains the operand to a promise
nor constructs the primitive application used today.

#### Baseline instruction profile

One clean, single-worker `tests/tests` build, Linux x86-64, normal fat-LTO
release, Callgrind `--dump-instr=yes`: **4,043,070,987 Ir**, 735 modules.
The runtime was built before measurement. Inclusive attribution from
`callgrind_annotate --inclusive=yes --threshold=100`:

| Function | Ir (inclusive, recursion contexts combined) |
| --- | ---: |
| `rewrite_expr` | 124,080,794 |
| `rewrite_pattern` | 1,970,655 |
| `rewrite_single_binding_let` | 382,901 |
| `rewrite_fun` | 22,323,820 |
| `transform_await` | 157,831 |
| `wrap_with_unsafe_async` | 120,476 |

These are overlapping inclusive costs, not additive row savings.
`boolean_match_arms` has no separate symbol in this optimized profile; its
instructions are charged to `rewrite_expr`. The shared functions include
other rewrites and child visits, so none of these numbers is an exclusive
cost of a direct row. No performance saving is claimed by this inventory.

#### Baseline rewrite counts

A temporary, uncommitted `eprintln!` probe at each direct rewrite arm, and
at `expand`, was compiled into a second release executable. A clean
single-worker build of `tests/tests` (735 compiled modules, the runtime
already built) produced:

```text
      3 T7 A-expression
      0 T7 A-pattern
      2 T7 B
     15 T7 C
    171 T7 D-async
    167 T7 D-await
   3400 T7 expansion
```

The four direct arms fire **358** times. `expand` counts expression
expansions through that helper, not calls to `set_expansion` made directly
by the unwrap binding or extension paths. The async count excludes the
separate method-callback rewrite, and the await count excludes module
await. The probes were removed after measurement. Additional expansions
caused by changed brace locations or pattern handles are not attributed by
these probes; the end-state exact-delta gate needs those accounted for,
not silently included in the 358.

#### T7 row D: direct promise typing and immutable ghost views

The initial location-ownership blocker is resolved in `a2873133f`.
`ParseArena::ghost_location` sets an existing index bit; `get_location`
returns a 12-byte value with that bit applied. A source location and its
immutable ghost view share coordinates, without a new pool row, allocation,
lock, atomic or thread-local access. Pool limits reserve the bit. Tests pin
the returned location to 12 bytes and prove that 10,000 ghost views leave the
location count unchanged.

The two primitive longidents are allocated once per arena. The checker
supplies their handles and a borrowed one-element argument slice to the same
identifier and application rules used by explicit calls. The borrowed callee
view is 16 bytes (size pinned); nothing is stored per syntax node. Async body
typing occurs after parameter module unpacks are in scope. Dependency
collection likewise adds the implicit primitive dependency inside that scope.

`wrap_with_unsafe_async` and the dormant `type_await` stub are deleted.
`transform_await` remains with exactly one caller,
`create_await_module_expression`; awaited-module expansion is a separate
rewrite. Neither ordinary await nor async functions reaches it. The mapper
only visits their existing children; the unused-attribute sweep preserves the
old await attribute-discard policy. A 10,000-function test proves that ordinary
async/await functions append no expression nodes.

#### Same-base expansion census (all four rows)

A temporary, uncommitted probe at `ParseArena::set_expansion` counted every
entry during clean single-worker `tests/tests` builds, with the runtime
already built. Both builds compiled 735 modules, including location retries.
Base is `10227bc20`; head includes direct typing for all four rows. Probes
were removed after measurement. Counts grouped by the original expression:

| Original expression / reason | Base | Direct typing | Removed |
| --- | ---: | ---: | ---: |
| `l` integer | 3 | 0 | 3 |
| Two boolean cases | 2 | 0 | 2 |
| Single record/dictionary let | 21 | 18 | 3 |
| Async function | 172 | 25 | 147 |
| Await expression | 167 | 0 | 167 |
| Braces whose location changed | 7 | 0 | 7 |
| Every other expression | 3,038 | 3,038 | 0 |
| **Total** | **3,410** | **3,081** | **329** |

The retained record-let entries are six packed-module bindings (outside row
C) and twelve record-rest pattern/type rewrites. The retained async entries
are one method-callback rewrite and twenty-four parameter/type rewrites.
These are independent rewrites of non-expression children, not record-let or
promise desugaring, and still produce the same shapes they produced before.
The ordinary direct rules never record an expansion.

**Correction to the initial inventory:** the 358 direct-arm hits were not
358 independently removable expansion entries. Twelve record lets and
twenty-four async functions also needed those independent rewrites; seven
brace copies existed only to propagate the old await ghost location. Thus
`358 - 12 - 24 + 7 = 329`, exactly the observed reduction. No unrelated
expression expansion count changes. The earlier eight-entry reduction for
A–C was the same overlap effect (`20 - 12`), not an upstream change.

#### Historical T7 A–C measurements

The saved release binaries at `3fa9eb29e` and `655dfcbf2` isolate A–C
before integrating subsequent trunk changes. Linux x86-64, ordinary fat-LTO
release, one worker; runtime preparation is outside the measurements.

| Corpus | Base instructions | A–C instructions | Change |
| --- | ---: | ---: | ---: |
| `tests/tests`, minimum of three Cachegrind runs | 4,048,215,873 | 4,049,924,082 | +0.0422% |
| 3,735-module application, one Cachegrind run each | 67,588,537,024 | 67,625,184,174 | +0.0542% |

The three `tests/tests` counts were 4,049,932,181 / 4,048,215,873 /
4,049,320,612 at base and 4,049,924,082 / 4,050,498,052 / 4,050,144,472
after A–C. These small increases are below the 0.1% instruction gate but
are **not instruction savings**. No individual-row saving was measured.
Hyperfine (two warmups, ten clean builds each) measured base 566.8 ± 40.4 ms
(range 504.3–615.5) and A–C 558.9 ± 19.6 ms (535.3–591.0). The ranges overlap;
there is no established speedup.

`compare_checker_builds.py` found no differences on either corpus: 735
signatures and 729 generated files on `tests/tests`, and all signatures,
diagnostics and generated files on the 3,735-module application.

The later same-base census above resolves the initial expansion-count
attribution. The A–C figures remain measurements of those saved binaries,
not claims about the completed four-row implementation.

After merging trunk at `88ca1bd53`, both Rust crates build, rewatch tests and
strict all-features clippy pass. The local compiler unit run reports 1,937
passed, 50 failed and 25 ignored in the checkout without OCaml reference
artifacts; it is not a passing full-suite gate. Baseline/head comparisons
pass for all 745 single-file and 79 multi-file error fixtures. Local JS
snapshot comparison passes 729/729, but the complete JS/stdlib/genType parity
scripts remain blocked by missing reference/package prerequisites. CI is
the reference-compiler gate. These are historical A–C validation results;
the completed implementation is checked again on the final head.

#### Completed four-row validation

At `9d6235b9a`, against `10227bc20`, all 745 single-file and 79 multi-file
diagnostic fixtures match. The checker comparison reports 735 matching
signatures, one matching diagnostic and 729 matching generated files.
The compiler unit suite locally has 1,973 passes and 48 missing-reference
artifact failures; the reference-enabled CI compiler suite is the gate.

The first completed implementation exceeded the CI instruction threshold:
4,018,024,706 versus 4,023,019,518 (minimum of five), **+0.124%**. That result
is not a performance improvement. The profile identified empty attribute
slice-to-vector conversions in the extracted identifier rule and out-of-line
location-value copies. The follow-up keeps the original compact `Attributes`
clone and inlines the location getter so field-only readers do not copy unused
coordinates. The final instruction check must pass without a waiver; its
results are reported on pull request #206. Historical A–C application
measurements above remain separately attributable to those saved binaries.
