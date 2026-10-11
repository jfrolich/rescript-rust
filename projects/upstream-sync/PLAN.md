# Upstream master sync

Merge `upstream/master` (rescript-lang/rescript) into this branch step by
step, porting each step's compiler changes to the Rust compiler so the
parity gates stay green against the new OCaml reference.

The upstream range is 204 first-parent commits (merge-base `9e7c571e9`,
target `8c3fecc56`). Each step merges an upstream commit with
`git merge --no-commit <sha>`, adapts the fork-only OCaml debug printers
(`compiler/ml/sexp_typedtree.ml`, `compiler/core/sexp_lambda.ml`,
`compiler/syntax/src/res_ast_debugger.ml`, `compiler/ml/ffi_debug.ml`), ports
the change to `compiler-rust/`, reruns the gates and commits the merge.

## Steps

| Step | Upstream range | Content | Status |
|------|----------------|---------|--------|
| 1 | 98e4a6613..0f66af5fa (commits 1-20) | structural optional defaults, structured FFI (`primitive_repr`, `external_decl`), externals expanded at translation, dynamic import resolved at translation | done |
| 2 | ..84bed4dda (21-28) | vendored Flow parser, OCamlformat 0.29, OCaml 5.5 | done |
| 3 | ..055e9e091 (29-49) | object representation cleanup (field mutability, Stage 0-E) | done |
| 4 | ..ebc61dd5b (50-110) | Lambda/Lam merge, curried application removal | done |
| 5 | ..7875e74f9 (111-117) | string literal normalization, formatter | done |
| 6 | ..0aa58d8aa (118-148) | scalar replacement, @as in the AST, sharing passes | done (Tella blocked, see log) |
| 7 | ..1cec5eb9e (149-162) | constructor argument lists, parser modes removed, coercions, untagged blocks | done (Tella blocked, see step 6) |
| 8 | ..8c3fecc56 (163-204) | parser token inspection, regexp/ternary/braces nodes, cleanup | done (Tella blocked, see step 6) |

## Debug-printer conventions

`Ffi_debug.primitive_repr` renders a value description's primitive for the
typedtree/parsetree sexp printers; the Rust printers must produce the same
strings (`compiler-rust/src/types/external_ffi_types.rs`).

## Step log

### Step 1 (`0f66af5fa`)

Ported to Rust:

- Structural optional defaults: the typechecker names the optional
  parameter `<label>Opt` and records it on the function parameter; the
  Rust-only `rename_optional_parameters` lowering pass is gone.
- `pval_prim`/`val_prim` are `Option<PrimitiveRepr>`; the builtin PPX
  digests externals into `PrimFfi { name, spec }` / `PrimInlineConst`
  (`types/external_ffi_types.rs` mirrors `External_arg_spec` and
  `External_ffi_types`). `Primitive.description` carries `prim_kind`.
- Externals are expanded at translation (`transl_external_application`,
  `lambda_of_inline_const`, unit-return replacement from the declared
  type); `Pjs_call` carries an `external_decl` and the backend compiles it
  per `Lam_compile_external_call.translate_ffi`.
- Dynamic import resolves to `Pimport(ImportSource)` at translation; the
  backend registers the module and emits `import(...)[.then(...)]`.
  `Lglobal_module` and the external arity/inline lookups lost their
  dynamic-import flag.
- `.cmi`/`.cmj` readers decode the new layouts (`cmi/ffi_decode.rs`); the
  binary AST writer marshals digested externals
  (`binary_ast/ffi_types.rs`); the old string-encoded FFI blobs are gone.
- Magic numbers: `Caml1999I025`, `ResImpl01301`/`ResIntf01301`.

Gates (release): JS output parity 626/626, typedtree parity 626/626,
error output parity green, syntax tests 572/572, compiler lib tests
1350/1350, rewatch unit tests and `rewatch/tests/suite.sh` green.
`tests/comptime_tests.rs::parse_inline_for` fails independently of this
step (experimental comptime syntax).

After a `.cmi` format change, rebuild the runtime, `tests/dependencies/rescript-react`
and `tests/tests` with the reference compiler, and delete stale ignored
`.cmi`/`.cmj`/`.cmt` artifacts under `tests/build_tests` and
`tests/error_output_parity`, before running the gates.

### Step 2 (`84bed4dda`)

Upstream vendored and upgraded the Flow parser (used for `%raw` checks and
warning 103), reformatted the OCaml sources with OCamlformat 0.29 and moved
the development toolchain to OCaml 5.5 (5.0 stays the minimum; the local
5.3 switch builds it). The only output change is `Pprintast`'s object-field
layout without attributes (`@;<2 0>`), ported to `parser/ml_printer.rs`.
Rust keeps its OXC-based `%raw` checker with Flow-style messages.

Gates (release): JS output parity 626/626, typedtree parity 626/626, error
output parity green (including the new `warning_103_flow_parser` fixture),
syntax tests 572/572.

### Step 3 (`055e9e091`)

Upstream removed the object-method remnants (`Pexp_send`, `##`/`#=`,
`%obj`, `@get`/`@set` getter-setter rewriting, `Lsend`,
`Pjs_unsafe_downgrade`) and typed objects directly: `Pexp_object_get`,
`Pexp_object_set` and `Pexp_object_literal` in the parsetree, the matching
`Texp_object_*` typedtree forms, and `Pjs_object_get`/`Pjs_object_set`
primitives. `Tobject` lost its name and `Tfield` carries a
`field_mutability ref` instead of a `field_kind`; `@set` on an object field
type makes it settable.

Ported to Rust:

- Parse tree, parser, printers, comment table, PPX passes and the v0
  mappers use the three object forms; the binary AST tags shifted.
- `Tfield { name, mutability, typ, rest }` with `MutabilityRef` cells
  (`TypeContext` arena, persistent cells for shared/store graphs, journaled
  `set_mutability`), copy sessions (`with_copy_session`,
  `dup_mutability`, `row_terminator_generic`) in every graph copier,
  unification/moregen/eqtype/variance/inclusion on mutability, and
  `filter_method`/`filter_object_field_for_write`.
- Typecore: object literal, get and set typing with
  `object_field_use_type`/`type_object_field_value` and the
  `Object_field_not_mutable` error; `@set` read from object type
  annotations; `Typetexp.find_value`'s `check_value_name` before value
  lookup.
- Coercion now follows OCaml's two paths: `enlarge_type`
  (`build_subtype`, newly ported) under a snapshot, then subtyping.
- Unification and subtyping use `enter_poly`/`unify_univar` with
  `univar_pairs` (constraints carry their pairs into `force_subtype`)
  instead of pairwise binder unification.
- Interface graphs serialize mutability classes; the `.cmi` reader decodes
  `field_mutability ref` blocks. Magic numbers: `Caml1999I029`,
  `ResImpl01303`/`ResIntf01303`.
- Printtyp prints `@set` fields; gentype reads mutability from the type.

Gates (release): JS output parity 628/628, typedtree parity 628/628, error
output parity 1881/1881, syntax tests green, compiler tests 1366/1367
(`parse_inline_for`, independent), rewatch unit tests 147/147 and
`rewatch/tests/suite.sh` green.

`make test-analysis` rebuilds the runtime and belt in-process, which writes
no interfaces and cleans the reference-built `lib/ocaml`; rebuild them with
the reference compiler afterwards. The analysis test projects still fail
until the editor tooling commands are ported into the watcher.

### Step 4 (`ebc61dd5b`)

Upstream merged the `Lam` IR into `Lambda` (one private, normalized
representation built through smart constructors), deleted the
curried-application machinery and moved several rewrites from Lambda-to-Lam
conversion to where the terms are produced. Rust keeps its raw-lambda and Lam
layers; the port reproduces the producer-side behavior and the removed
primitives.

Ported to Rust:

- `Typecore.check_polyvar_name`: a numeric polymorphic variant name outside
  the int32 range is a type error in expressions and patterns (the frontend
  check is gone).
- Match-action sharing treats string constants as immutable (`make_key`), and
  switch locations no longer take part in action keys (the raw `Lswitch`
  carries no location). The raw switch records `sw_consts_full` /
  `sw_blocks_full` like OCaml instead of case counts.
- `Pisout`, `Poffsetint` and `%succint`/`%predint` are gone. The switcher
  emits range tests directly (`Switch.out_of_range`/`emit_if_out`/
  `emit_if_in`) and folds a guard whose table covers the range into the
  switch's failaction; `Lam.if_` lost that arm.
- Translation-time builtins (`Lambda.mk_builtin`): `%identity`/`%ignore` are
  erased, `%null`/`%undefined` are constants, and `%incr`/`%decr` expand to
  the field write, binding the reference unless it is a variable.
- Recursive modules with an empty signature keep their right-hand side
  (`Transl_recmodule.shape_is_empty`).
- `Lambda_scc.bind_rec` splits `let rec` groups at translation
  (`raw_lambda/lambda_scc.rs`, with one dependency row per binding); lowering
  no longer reorders recursive bindings.
- The `.cmj` reader decodes `Lambda.t` (lfunction without arity, `ap_info`
  without status, the new constant, tag and primitive layouts).
- The OCaml debug printers follow `Lambda.t`
  (`compiler/core/sexp_lambda.ml`).

Gates (release): JS output parity 628/628, typedtree parity 628/628, error
output parity 1884/1884, syntax tests green, compiler tests 1346/1347
(`parse_inline_for`, independent), rewatch unit tests 147/147 and
`rewatch/tests/suite.sh` green. The runtime and Belt built by the Rust
compiler match the checked-in JavaScript.

### Step 5 (`7875e74f9`)

Upstream replaced string delimiters with `String_literal`: a string constant
keeps its source spelling and its decoded (semantic) value, `json` literals
and raw sources are separate constants, and backquoted templates are their
own parsetree, typedtree and lambda nodes (`Pexp_template`,
`Pexp_tagged_template`, `Ptemplate`, `Ptagged_template`). The JS printer
escapes semantic strings itself.

Ported to Rust:

- `string_literal.rs` and `ast_payload.rs` (semantic payload readers); the
  scanner, parser, printers, JSX ppx and FFI attribute readers use them.
- `ast_mapper_to0`/`ast_mapper_from0`: templates round-trip through the v0
  `^` chain and `res.template`/`res.taggedTemplate` attributes, with the
  upstream errors for invalid escapes, interpolated `json` literals and tagged
  templates in patterns.
- Typing of the template nodes, the `InvalidStringEscapeSequence` and
  `JsonLiteralOutsideExternal` errors, and UTF-16 lengths in `parmatch`.
- Lambda: `Const_string` without a delimiter, the template primitives, and
  UTF-16 based `String.length`/`String.get` folding. The `.cmj` reader decodes
  the new layouts.
- JS IR: `Str`, `TemplateLiteral`, `JsonLiteral` and `InterpolatedTemplate`
  replace the delimiter-carrying string node; the printer ports
  `Js_dump_string.escape_to_buffer`.
- `.cmi` attribute strings are read through `String_literal.payload`.
- `matching.ml`'s `approx_present` treats `Lglobal_module` as present, as
  OCaml does (it is not a constant), so an alias binding is not sunk into a
  branch past a global module access.

Rewatch: in-process builds now copy `.res`/`.resi` sources into `lib/bs` and
`lib/ocaml` like the subprocess build. The runtime precompile reads
`lib/ocaml/*.res`, so before this a clean runtime build left Belt unable to
find `Stdlib`.

Gates (release): JS output parity 631/631 and Tella 3205/3205, typedtree
parity 630/630 (`string_unicode_test` takes longer than the 10s limit in both
compilers; its 138 MB sexp matches byte for byte), error output parity
1893/1893, syntax tests 580/580, compiler tests green except
`parse_inline_for` (independent), rewatch unit tests and `tests/suite.sh`
green. `make test-analysis` stops at `no-watcher.sh` (editor-tooling port in
progress).

### Step 6 (`0aa58d8aa`)

Upstream decides a field's runtime name and a constructor's runtime tag once,
in the AST: `@as` moves out of the attributes into `pld_runtime_name` and
`pcd_runtime_tag` (built by `Ast_helper.Type.field`/`constructor`), and from
there into `ld_runtime_name`, `cd_runtime_tag` and `lbl_runtime_name`. The
variant tag type splits into literal tags and the `Untagged` block types. On
the Lambda side, scalar replacement (`Lam_pass_sroa`) replaces ref
elimination, `%incr`/`%decr`/`%refget` and `Int.Ref` are gone, the passes
rebuild only what changed (`Lambda_traverse.shallow_map_sharing`), match
guards are kept as data until the fallthrough is known, and builtins are
built through the folding `Lambda.prim`.

Ported to Rust:

- `ast_helper_type.rs`, the new `ast_payload` readers, the parsetree fields
  and their marshalling (`ResImpl01306`/`ResIntf01306`), printers that put
  `@as` back from the fields, and the mapper and ppx builders.
- `.cmi` decoding of the new label and constructor layouts (`Caml1999I032`),
  `record_runtime.rs` (duplicate runtime names, extra `@as` on a field), the
  typedecl tag decoding with `VariantAsIntegerOutOfRange`, and consumers
  reading the declared names instead of attributes (typecore, includemod,
  ctype, convert, matching, gentype's `declared_field_name`).
- `bs_ast_invariant`: a field's leftover `@as` warns only when its payload is
  a name; a constructor runs `process_constructor_tag`.
- `lambda_traverse.rs` (`shallow_exists`, `shallow_map_sharing`, with a
  changed flag standing in for physical equality), `lam_pass_sroa.rs` after
  `simplify_lets`, `lets_dce` without the ref arms and with `refine_let
  ~original`, removal of `lam_pass_eliminate_ref.rs` and `Poffsetref`.
- Effect analysis: `**` on BigInt, checked array and string reads, and the JS
  `Bin (Pow|Div|Mod)` rule.
- The raw match-compiler input is built through the folding `prim` and the
  constant arms of `if_` (on lowered constants), so the switcher sees merged
  arms as OCaml does.
- `lam_compile`: an assignment is a statement in every continuation, so a
  unit-returning `if` with an assignment flips into an early return.
- Includemod: `@as` no longer inflates the marshalled declaration, so the
  `Module_types` elision keeps only the `@tag` case.

Tella: upstream deleted `Int.Ref`, and Tella's own sources still call
`Int.Ref.increment` (`tella-std/src/ArrayExt.res` and
`chrome/src/ExtensionIcon.res`), so the OCaml reference build of Tella fails.
Tella parity cannot run against this step until those calls change.

Error parity needed the ignored `.cmi`/`.cmj`/`.cmt` files written next to
the fixtures by earlier runs removed: they were in the old format and the
OCaml reference rejected them.

Gates (release): JS output parity 637/637, typedtree parity 636/636
(`string_unicode_test` exceeds the 10s limit in both compilers), error output
parity 1895/1895, syntax tests 583/583, compiler tests green except
`parse_inline_for` (independent), rewatch unit tests 147/147 and
`tests/suite.sh` green. `make test-analysis` stops at `no-watcher.sh`
(editor-tooling port in progress).

### Step 7 (`1cec5eb9e`)

- Constructor and polymorphic variant arguments are lists located at the
  parentheses (`Pexp_construct`/`Ppat_construct`/`Pexp_variant`/
  `Ppat_variant`), and `Rtag` payloads are located type groups. The parser,
  sexp printers, marshalling (`ResImpl01307`/`ResIntf01307`), the iterators,
  the ML and ReScript printers (`print_expression_args`,
  `print_pattern_args`, grouped `Rtag` payloads), the comment table
  (`walk_row_field` no longer walks payload types) and every builder were
  moved over. The expression side tables for constructor/variant arguments
  are gone.
- The v0 PPX bridge encodes several arguments as a tuple with the
  `_res.constructor_args` marker and decodes them with `decode_args`. The
  internal Spice PPX builds its arguments the way that bridge decodes them.
- `ParserMode` and the `-typechecker` flag are removed.
- Typing: `normalize_constructor_pat_args`/`normalize_constructor_expr_args`
  after disambiguation; `type_construct` types each argument with
  `type_argument` instead of typing a synthetic tuple; polymorphic variant
  payload groups become a tuple only in the type checker (shared arena
  storage for the rebuilt core types); `Texp_coerce` carries the
  head-expanded source and target types.
- `Variant_runtime.block` is `Tagged | Untagged {tag; block_type}`:
  `Blk_constructor` holds a tagged block, untagged constructors are erased
  to their payload in translation, `get_block_type` rejects multi-argument
  untagged constructors, `.cmi`/`.cmj` decoders follow the new layout
  (`Caml1999I034`), and `Lambda.switch` decides a constant scrutinee of an
  untagged switch by its runtime value.
- Bigint tags print through `Bigint_utils.parse_bigint` (`@as(1_0n)` emits
  `10n`), and `%raw` templates go through `decode_raw_template_source`.
- Frontend: `ast_exp_apply` gives a piped constructor argument its own
  location, `ast_derive_projector` passes one argument per parameter.

Gates (release): JS output parity 640/640, typedtree parity 639/639
(`string_unicode_test` exceeds the 10s limit in both compilers), error output
parity 1898/1898, syntax tests 588/588, compiler tests green except
`parse_inline_for`, rewatch unit tests 147/147, `cargo fmt` clean and
`tests/suite.sh` green. `make test-analysis` stops at `no-watcher.sh`.

### Step 8 (`8c3fecc56`)

- New Parsetree nodes `Pexp_braces {expr; braces_loc}` (tag 0, so every
  later `expression_desc` tag moved up), `Pexp_ternary` and
  `Pexp_regexp {pattern; flags}` replace the `res.braces`/`res.ternary`
  attributes and `%re`; `Ppat_open`/`Tpat_open` and `pat_record_label` are
  gone; type declarations carry `ptype_origin`. The AST, sexp printers,
  iterators, dependency walk, marshalling (`ResImpl01311`/`ResIntf01311`),
  the v0 PPX bridge and every consumer that looked at the old attributes
  (printer, parens, JSX PPX, builtin PPX, let? and Spice PPX, type checker,
  payload readers, `.cmi` attribute decoding) were moved over. Payload
  readers look through braces (`Ast_payload.unwrap_braces`).
- Parser: diamond scanner mode removed, binary operators assembled on
  demand (`peek_binary_operator`), regexp literals rescanned from the `/`,
  type-constructor arguments written with parentheses are recovered with a
  diagnostic, comma-delimited regions recover paired delimiters, and
  lookahead/snapshots roll back error-region state.
- Pipes bind their left side when the right side is a block, open, let or
  sequence (`desugar_pipe`).
- Backend: exports left unbound by a toplevel throw are declared after it
  (`declare_undeclared_exports`). GenType keeps inline-record cases of
  untagged variants as objects. Magics `Caml1999I035`/`Caml1999T039`.
- Rust's module-inclusion elision is still its own size approximation; the
  error gate shows it matches upstream's word-count `is_big` on every
  fixture.

Gates (release): JS output parity 635/635, typedtree parity 634/634
(`string_unicode_test` exceeds the 10s limit in both compilers), error output
parity 1896/1896, syntax tests all green, compiler tests green except
`parse_inline_for`, rewatch unit tests 150/150, `cargo fmt` clean and
`tests/suite.sh` green. `make test-analysis` stops at `no-watcher.sh`.
