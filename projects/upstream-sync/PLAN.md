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
| 4 | ..110 | Lambda/Lam merge, curried application removal | |
| 5 | ..117 | string literal normalization, formatter | |
| 6 | ..148 | scalar replacement, @as in the AST, sharing passes | |
| 7 | ..162 | parser modes removed, coercions, reanalyze | |
| 8 | ..204 | parser token inspection, regexp/ternary/braces nodes, cleanup | |

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
