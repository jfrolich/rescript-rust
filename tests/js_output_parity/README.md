# JS Output Parity Fixtures

This corpus compares JavaScript emitted by the OCaml compiler and the Rust
compiler byte for byte. The fixtures are intentionally small, compiling
ReScript programs that isolate code-generation shapes. Generated `.js`, `.mjs`,
`.cmi`, `.cmj`, and `.cmt` files are written under `.parity-cache/` and must
not be checked in. A fixture can include a sibling `.resi`; the runner compiles
that interface before the implementation for each compiler. A fixture entry can
also be a directory; the runner builds the copied directory as a tiny project
with the OCaml compiler (through the hidden
`rescript build-reference --bsc`) and with an in-process `rescript build`,
then compares every generated JS output. Directory fixtures can include `rescript.extra.json` for
extra project-level config such as namespace settings.

See `COVERAGE.md` for the compiler-output surface checklist that maps language
features and Tella-minimized patterns to concrete fixtures.

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
- `numeric_primitive_patterns.res`: integer division/modulo flag-sensitive
  lowering, bitwise operators, overflow coercions, float arithmetic,
  comparisons, assertions, and int/float conversions.
- `runtime_primitive_alias_patterns.res`: aliases for runtime-backed
  `compare`/`min`/`max` across primitive/object types plus checked
  string/array access and update primitives.
- `ffi_patterns.res`: `@obj`, `@send`, `@get`, `@set`, index get/set,
  ignored GADT arguments, raw JavaScript, and array/string FFI calls.
- `js_expression_patterns.res`: reserved property names, scoped/default
  externals, variadic `@new`/`@send`, optional external args, object literals,
  dict-pattern lowering, and index mutation.
- `uncurried_external_edge_patterns.res`: uncurried external edge output for
  object builders with constant JSON args, scoped constant-arg calls, ignored
  GADT witness get/set/index accessors, unit-send forms, `@this` setters, and
  bare `@module` constructor imports.
- `uncurried_optional_external_patterns.res`: uncurried external calls with
  trailing optional arguments omitted, earlier optional slots preserved when a
  later optional label is supplied, optional `@send`, and optional `@new`.
- `function_call_patterns.res`: uncurried direct calls, partial application,
  labelled/default calls, pipes, callback arity wrappers, `@ignore`, and
  constant `@as` arguments.
- `higher_order_eta_patterns.res`: higher-order unary/binary function wrapper
  output, nested wrappers, and wrappers around record/object-selected
  callbacks.
- `async_this_callback_patterns.res`: async lowering for `@this` methods,
  async record callbacks, inline async callbacks, async closures captured inside
  loops, nested async callbacks, and React-hook-shaped callback wrappers.
- `mutable_uncurry_patterns.res`: mutable-ref parameter destructuring,
  generated parameter-name stability, multi-arity tuple functions, and nested
  functions over ref payloads.
- `match_lowering_patterns.res`: list/array/record destructuring, nested
  constructor patterns, literal payload patterns, guards, tuple or-patterns,
  aliases, and exception payload matching.
- `local_exception_scope_patterns.res`: local exception declarations, nested
  exception shadowing, record-payload local exceptions, and `exception` switch
  patterns.
- `js_exception_rethrow_patterns.res`: JS exception packing/destructuring,
  `JsExn` catch patterns, rethrow paths, and exception switch patterns.
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
- `module_value_patterns.res`: module-value destructuring, private module
  destructuring, first-class module parameters/results, `module type of`
  values, and module-typed external arguments.
- `external_edge_patterns.res`: nested scopes, nullable/null-undefined returns,
  `@string`/`@int` marshalling, tagged templates, `@this` callbacks, constant
  args, property get/set, dynamic import, and module-await lowering.
- `import_binding_patterns.res`: same-source and same-member `@module`
  imports, tuple module paths, `@val` plus `@module`, `@new` imports,
  variadic module imports, node-style module names, relative imports, and
  Tella-derived bare `@module` asset/default/class imports.
- `variant_representation_patterns.res`: string/int/float/bigint constructor
  coercions, unboxed nullish variants, variant spreads, `jsConverter`,
  tagged inline records, unboxed widening, and Tella-derived named
  polymorphic-variant widening.
- `unboxed_recursive_output_patterns.res`: recursive unboxed unknown and
  existential payload representations, polymorphic unboxed record fields, and
  recursive unboxed record aliases inside polymorphic-variant rows.
- `tella_sparse_record.res`: a minimized Tella-derived large sparse record
  shape without depending on the external Tella repository.
- `tella_scoped_send_patterns.res`: minimized Tella binding output for
  Stripe/Notion-style `@send @scope` methods, nested send scopes, imported
  constructors, escaped record fields, and optional nested payload records.
- `tella_aws_binding_patterns.res`: minimized Tella AWS/Shaka binding output
  for `@new @module` command constructors, `@as` record fields, `@send`
  methods with inserted constant event names, and tuple `@scope` module values.
- `tella_chrome_svix_binding_patterns.res`: minimized Tella Chrome/Svix
  binding output for scoped global event registries, `@get` option accessors,
  Promise wrappers around callback APIs, `@val @scope(("process", "env"))`
  nullable reads, and `@send @scope` webhook client methods.
- `tella_json_decode_patterns.res`: minimized Tella JSON decoder output for
  exception-wrapping array/dict loops, unsafe array allocation, recursive
  field-path decoding, optional decoder fallback, and one-of error folding.
- `tella_json_encode_patterns.res`: minimized Tella JSON encoder output for
  `%identity` JSON externals, dict pair mapping, object construction from
  property lists, recursive list-to-array filling, and tuple encoders.
- `tella_dexie_binding_patterns.res`: minimized Tella Dexie binding output for
  indexed table access, fluent `@send` chains, raw store-schema helpers,
  labelled promise-returning sends, and `%identity` primary-key encoders.
- `tella_directive_import_patterns.res`: minimized Tella/Next client-module
  directive output for file-level and nested `@@directive` items combined with
  emitted imports, hook-shaped externals, and `@send` navigation methods.
- `tella_raw_function_patterns.res`: minimized Tella raw-function output for
  typed `%raw` constructors, multiline raw helpers, raw promise factories, and
  try/catch wrappers around `@send` calls.
- `interface_patterns.res`: a minimized interface-backed case covering `.resi`
  CMI flow, abstract implementation types, nested module signatures, and named
  polymorphic-variant widening.
- `module_boundary_patterns/`: a multi-source fixture covering local module
  artifacts, `.resi` plus `.res` provider compilation, consumer imports, module
  aliases, abstract exported values, and cross-module optimization reads.
- `namespace_project_patterns/`: a multi-source namespaced project covering
  project-level namespace module aliases across output modes.
- `config_output_patterns.res`: file-level `@@config(no_export)` output with
  retained local bindings and side effects.
- `deriving_output_patterns.res`: builtin deriving output for accessors,
  abstract records, optional fields, and light abstract records.
- `uncurried_deriving_output_patterns.res`: generated accessor and constructor
  helper arity from `@deriving(accessors)` under `@@uncurried`, including
  composed calls through derived helpers.
- `attribute_codegen_patterns.res`: inline constants/functions/modules,
  `%%private` extension output, tuple `@module` externals, legacy and direct
  `null_to_opt` returns, and named/optional `@unwrap` arguments.
- `external_arity_patterns.res`: uncurried external arity inference from type
  aliases and type constructors, optional external arity, and JSX v4 external
  component arity through `@react.component @module`.
- `jsx_transform_patterns.res`: JSX v4 transform output for DOM elements,
  components, fragments, keys, spread props, escaped prop names, optional
  children, and memoed components.
- `jsx_external_component_patterns.res`: Tella-derived JSX v4 output for
  scoped external React component bindings using `@module`, `@scope`,
  escaped prop names, optional callback props, polymorphic event details,
  array props, fragments, and default imports.
- `react_component_edge_patterns.res`: Tella/test-suite-derived React
  component output for aliased/default props, module-typed props,
  `forwardRef`, `memo`, `cloneElement`, and hook-shaped external calls.
- `jsx_preserve_minimal.res`: JSX v4 preserve output for DOM elements, nested
  children, and spread props.
