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
| Integer expression with `l` suffix | Integer without suffix; original attributes retained | `rewrite_expression` | None | Parser literal completion |
| Integer pattern with `l` suffix | Pattern constant without suffix | `rewrite_pattern` | None | Parser pattern completion |
| Binary `a -> f` | Application, constructor/variant application or tuple pipe, with temporary binding when needed | `desugar_pipe`, `rewrite_pipe_rhs`, `pipe_tuple_map`, `pipe_bound`, `fresh_bound_name` | Names in RHS, evaluation count/order | Parser completed pipe or checker expression entry |
| Single nonrecursive record/dictionary-pattern local binding (including alias), except packed module RHS | One-case match with merged expression/binding attributes | `rewrite_expression_generic` (`Pexp_let`) | Binding group and RHS shape | Parser completed local binding |
| Supported `let?`/unwrap binding | Match with early-return and continuation cases | `classify_let_unwrap_pattern`, `rewrite_expression_generic` | Experimental-feature setting, top-level vs local context | Checker binding entry |
| Simple tuple binding with matching tuple RHS (possibly under opens) | Separate bindings, preserving opens | `flatten_value_binding`, `destruct_open_tuple`, `restore_exp` | Complete pattern/RHS; recursive bindings excluded; value-constraint side data | Parser completed binding group or checker binding entry |
| Record pattern binding to packed module identifier | Separate bindings referring to module fields | `flatten_value_binding` | Complete RHS and unqualified field patterns | Checker binding entry |
| Two unguarded true/false match cases | If/then/else with arms in boolean order | `rewrite_expression_generic` (`Pexp_match`) | Both cases | Parser completed match |
| `async` function | Function body wrapped with promise/unsafe-async operations | `add_promise_to_fun_body`, `wrap_with_unsafe_async` | N-ary parameter/default/newtype side tables, parameter location | Checker function entry |
| `await e` | `Primitive_promise.unsafe_await` application | `transform_await` | Validation needs enclosing async function; generated ghost location comes from operand | Checker expression entry |
| Awaited module alias, with optional module-type constraint | Dynamic import expression, module unpack and module type declaration | `transform_module_await`, `create_await_module_expression`, `local_module_type_decl` | Per-structure module-type-name deduplication | Checker module entry; not node-local parser work |
| Local awaited module inside a value binding | Hoisted module type declarations plus rewritten local module | `spelunk_value_bindings_for_await_module_types`, `spelunk_expression_for_await_module_types`, `rewrite_expression_generic` (`Pexp_letmodule`) | Enclosing structure, deduplication, original binding before rewriting | Checker structure/binding entry |
| `@this` function | Method callback record/constrained callback/unsafe-to-method application | `rewrite_method_callback_expression`, `split_this_attrs` | Function arity, async body and parameter shape | Checker function entry |
| `@this` on braces around function | Attribute forwarded through braces to function; unrelated attributes retained | `add_this_to_braced_function`, `rewrite_expression_generic` (`Pexp_braces`) | Braced descendant shape; rewritten inner location | Parser completed braced expression or checker expression entry |
| `@this` arrow type | `Js.OO.Callback.arityN<...>` type | `rewrite_core_type` | N-ary arrow side table or recorded arity | Checker type entry |
| Object type field attributes | Last `@this` forwarded to field type; other attributes reversed; `@set` retained for checker | `rewrite_object_fields`, `process_attributes_rev` | Field type | Checker object type entry |
| `%raw` / `Pexp_raw` expression | Local raw external application, with function-literal information | `handle_raw`, `handle_raw_node`, `raw_expression`, `raw_local_external_apply` | JS parser classification, payload and source locations | Checker expression entry |
| `%ffi` / raw FFI node | FFI raw expression with literal function arity | `handle_ffi`, `ffi_expression`, `detect_js_function_arity` | JS source classification | Checker expression entry |
| Regexp literal | Constrained raw expression of `RegExp.t` | `rewrite_expression_generic` (`Pexp_regexp`) | Separate regexp validation/warnings | Parser completed regexp or checker expression entry |
| `%todo` / `Pexp_todo` | `Stdlib_JsError.throwWithMessage` with source position and optional message | `handle_extension`, `todo` | Source filename, line, columns; separate warning | Checker expression entry |
| `%%raw` / `Pstr_raw` | Evaluation of raw-statement external | `handle_raw_structure`, `handle_raw_structure_node`, `raw_structure` | Payload/source location, JS statement validation | Checker structure item entry |
| Consecutive `%%private` items | Local module and overriding open | `private_extension_structure_items`, `wrap_in_local_module`, `rewrite_structure_impl` | Adjacent items, local-name counter, mapper order | Checker structure entry; not node-local |
| `@deriving(accessors)` type group | Type declarations and generated record getters / variant constructors in constrained includes | `handle_deriving_type`, `generate_accessor_include`, `generate_record_accessors_and_sigs`, `generate_variant_accessors_and_sigs` | Whole mutually recursive type group; gentype attributes; structure/signature distinction | Checker type-group entry |
| Spice derive attributes | Encoder/decoder declarations and signatures | `derive::expand_structure_item_with_mapper`, `derive::expand_signature_item_with_mapper`, `spice_ppx::map_type_decl_structure`, `spice_ppx::generate_sig_decls` | Mapper activation over containing structure/signature; derive configuration, type group | Checker type-group entry; preserve activation semantics |
| Attributes and extension payloads traversed by the mapper | Recursively rewritten payload AST | `rewrite_attribute`, `rewrite_payload`, `rewrite_attributes` | Payload kind; `PTyp` is retained; unknown expression extensions are retained without descending | Parser payload completion or checker attribute consumer |
| JSX component annotations on bindings/descriptions | Annotation round-trip through attributes and dedicated component side data | `rewrite_value_binding_without_flattening`, `rewrite_structure_item_no_spice`, `rewrite_signature_item_no_spice`, `ast_jsx_component::take` | Binding/description representation | Checker binding/description entry |
| JSX elements/fragments and component declarations (separate mapper) | React/JSX runtime calls, props records and component wrappers/signatures | `parser::jsx_ppx::{transform_jsx_element,transform_jsx_fragment,mk_react_jsx,make_props_record_type,make_props_record_type_sig}` | JSX version/module/mode configuration and component scope | Parser completion with explicit configuration, or checker component entry |

Many comments still describe string-delimiter normalization from an older
representation. The current `rewrite_expression`/`rewrite_pattern` constant
branches do not rewrite every string: do not infer a trigger from those comments.
Likewise, `@get`/`@set` object fields are not expanded here; the checker consumes
them. Unknown attributes still matter because their payloads can contain real
rewrite targets.

## Safe subtree skipping

`ParseArena::push_expr` computes a bottom-up certificate using existing child
certificates. `rewrite_free_exprs` holds one bit per expression, not a field on
each node. `expr_needs_no_rewrite` is an O(1) lookup used by `rewrite_child`.
The whitelist contains attribute-free ordinary applications (not pipes),
constants except `l` integers, identifiers, break/continue, tuples, arrays,
constructors/variants, field access, assertions, sequences, while loops,
ternaries, if expressions and records, provided every expression child is also
certified. New/unknown expression variants default to the full mapper.

Functions, patterns, types, braces, modules, bindings, extensions, JSX and all
attributes remain conservative. In particular, braces must not be skipped based
only on their own attributes: an enclosing `@this` can be forwarded through them.
No checker/warning sweep is skipped. The marshal location marker is retained for
the skipped root; attribute-free descendants do not require attribute-wrapper
sharing markers. This does not claim byte-identical intermediate AST encoding.

`get_expr_mut` and `initialize_expr` invalidate the changed index and all later
certificates. Certified parents are allocated after their certified children;
reserved slots are never certified. This deliberately sacrifices some skip
opportunities rather than keeping stale proofs after mutation. Shared synthetic
expressions have no certificate. No new global state or unsafe code is used.

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

