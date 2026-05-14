# JS Output Parity Fixtures

This corpus compares JavaScript emitted by the OCaml compiler and the Rust
compiler byte for byte. The fixtures are intentionally small, compiling
ReScript programs that isolate code-generation shapes. Generated `.js`, `.mjs`,
`.cmi`, `.cmj`, and `.cmt` files are written under `.parity-cache/` and must
not be checked in. A fixture can include a sibling `.resi`; the runner compiles
that interface before the implementation for each compiler. A fixture entry can
also be a directory; the runner builds the copied directory as a tiny project
with the OCaml compiler and debug rewatch `--in-process`, then compares every
generated JS output.

Run the focused fixture gate with the debug Rust compiler and debug rewatch:

```bash
./scripts/test_js_output_parity_fixtures.sh -v
```

Run the broader local JS output gate, which includes these fixtures first and
then the 660 snapshot files:

```bash
./scripts/test_js_output_parity.sh --skip-spice-ppx
```

Each source listed in `cases.tsv` is compiled in these fixture modes:

- ES module output
- CommonJS output
- debug output (`-bs-g`)
- no-assert output (`-noassert -bs-noassertfalse`)
- unsafe output (`-unsafe -bs-no-check-div-by-zero`)
- no-version-header output (`-bs-no-version-header`)
- cross-module optimization output (`-bs-cross-module-opt`)
- no cross-module optimization output (`-bs-no-cross-module-opt`)

Current focused coverage:

- `core_patterns.res`: literals, tuples, arrays, lists, records, objects,
  labelled/optional functions, pipe calls, loops, assertions, options,
  polymorphic variants, unboxed variants, and nested modules.
- `ffi_patterns.res`: `@obj`, `@send`, `@get`, `@set`, index get/set,
  ignored GADT arguments, raw JavaScript, and array/string FFI calls.
- `js_expression_patterns.res`: reserved property names, scoped/default
  externals, variadic `@new`/`@send`, optional external args, object literals,
  dict-pattern lowering, and index mutation.
- `function_call_patterns.res`: uncurried direct calls, partial application,
  labelled/default calls, pipes, callback arity wrappers, `@ignore`, and
  constant `@as` arguments.
- `match_lowering_patterns.res`: list/array/record destructuring, nested
  constructor patterns, literal payload patterns, guards, tuple or-patterns,
  aliases, and exception payload matching.
- `advanced_output_patterns.res`: variadic constructors, imported modules with
  attributes, unwrap externals, escaped record fields, unboxed constructors,
  exceptions, async/await, includes, functors, and assertions.
- `control_module_patterns.res`: `for`, `for...of`, `for await...of`,
  `continue`, `break`, mutually recursive functions, recursive modules,
  functors, lazy values, directives, extensible variants, and exception payload
  patterns.
- `module_pack_patterns.res`: first-class module packing/unpacking,
  package-returning functions, package arrays, `let module` bindings, local
  module aliases, and functor application over unpacked modules.
- `external_edge_patterns.res`: nested scopes, nullable/null-undefined returns,
  `@string`/`@int` marshalling, tagged templates, `@this` callbacks, constant
  args, property get/set, dynamic import, and module-await lowering.
- `variant_representation_patterns.res`: string/int/float/bigint constructor
  coercions, unboxed nullish variants, variant spreads, `jsConverter`,
  tagged inline records, unboxed widening, and Tella-derived named
  polymorphic-variant widening.
- `tella_sparse_record.res`: a minimized Tella-derived large sparse record
  shape without depending on the external Tella repository.
- `interface_patterns.res`: a minimized interface-backed case covering `.resi`
  CMI flow, abstract implementation types, nested module signatures, and named
  polymorphic-variant widening.
- `module_boundary_patterns/`: a multi-source fixture covering local module
  artifacts, `.resi` plus `.res` provider compilation, consumer imports, module
  aliases, abstract exported values, and cross-module optimization reads.
- `jsx_transform_patterns.res`: JSX v4 transform output for DOM elements,
  components, fragments, keys, spread props, escaped prop names, optional
  children, and memoed components.
- `jsx_preserve_minimal.res`: JSX v4 preserve output for DOM elements, nested
  children, and spread props.
