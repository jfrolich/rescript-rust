# JS Output Parity Coverage

This checklist maps ReScript-to-JavaScript output surfaces to concrete focused
fixtures. The fixture runner compares OCaml and Rust output byte-for-byte across
ES module, CommonJS, debug, assertion, unsafe, version-header, and
cross-module optimization modes.

## Expression Translation

- Constants, tuples, arrays, lists, records, optional fields, object literals:
  `core_patterns.res`, `js_expression_patterns.res`.
- Value paths, primitive paths, runtime primitive aliases, specialized
  comparison/arithmetic primitives: `numeric_primitive_patterns.res`,
  `runtime_primitive_alias_patterns.res`.
- Function translation, labelled/default/optional arguments, partial
  application, pipe calls, callback wrappers, eta wrappers:
  `function_call_patterns.res`, `higher_order_eta_patterns.res`.
- Let, recursive let, module-local let, nested functions, mutable refs:
  `core_patterns.res`, `mutable_uncurry_patterns.res`,
  `control_module_patterns.res`.
- Match, try, guards, or-patterns, tuple/list/array/record destructuring,
  exception cases: `match_lowering_patterns.res`,
  `local_exception_scope_patterns.res`, `js_exception_rethrow_patterns.res`.
- Constructors, polymorphic variants, extensible variants, unboxed variants,
  inline records, tagged records, spreads, `jsConverter`:
  `variant_representation_patterns.res`,
  `unboxed_recursive_output_patterns.res`,
  `control_module_patterns.res`.
- Record create/update/access/set, sparse large records, extension records:
  `core_patterns.res`, `tella_sparse_record.res`,
  `variant_representation_patterns.res`.
- Control flow: `if`, `if` without else, sequence, assert, while, for,
  downto, `for...of`, `for await...of`, break, continue:
  `core_patterns.res`, `control_module_patterns.res`.
- Async/await, async callbacks, scoped async closures, Promise wrappers:
  `advanced_output_patterns.res`, `async_this_callback_patterns.res`,
  `tella_chrome_svix_binding_patterns.res`.
- First-class modules, package arrays, pack/unpack, module values:
  `module_pack_patterns.res`, `module_value_patterns.res`.
- Raw expressions and typed raw functions:
  `import_binding_patterns.res`, `tella_raw_function_patterns.res`.

## Module Translation

- Structure values, eval items, primitives, type extensions, exceptions:
  `advanced_output_patterns.res`, `control_module_patterns.res`,
  `local_exception_scope_patterns.res`.
- Modules, recursive modules, functors, functor application, module aliases,
  module type of, includes, local modules:
  `control_module_patterns.res`, `module_pack_patterns.res`,
  `module_value_patterns.res`, `module_boundary_patterns/`.
- Interface-backed compilation and CMI flow:
  `interface_patterns.res`, `module_boundary_patterns/`.
- Namespaced projects and project-level output configuration:
  `namespace_project_patterns/`, `config_output_patterns.res`.
- File-level and nested directives:
  `control_module_patterns.res`, `tella_directive_import_patterns.res`.

## FFI And Imports

- `@obj`, `@get`, `@set`, `@get_index`, `@set_index`, `@send`, `@scope`,
  ignored GADT witness args: `ffi_patterns.res`,
  `uncurried_external_edge_patterns.res`.
- `@module`, `@val`, default imports, same-source imports, tuple module paths,
  node-style names, relative imports, asset imports, import attributes:
  `import_binding_patterns.res`, `advanced_output_patterns.res`.
- `@new`, variadic calls, variadic constructors, constant `@as` args,
  `@string`, `@int`, tagged templates, `@this`, `@return` nullability:
  `advanced_output_patterns.res`, `external_edge_patterns.res`,
  `attribute_codegen_patterns.res`.
- Optional external arguments and uncurried external calls:
  `uncurried_optional_external_patterns.res`,
  `external_arity_patterns.res`.
- Left-to-right argument and literal-element evaluation when a later one
  compiles to statements (held field, global and assignable reads, JS method
  objects kept as `this`, property reads of objects with statements, dict
  rows, `for` bounds): `argument_evaluation_order_patterns.res`.
- Tella-derived binding families:
  `tella_scoped_send_patterns.res`, `tella_aws_binding_patterns.res`,
  `tella_chrome_svix_binding_patterns.res`,
  `tella_dexie_binding_patterns.res`.

## JSX And React

- JSX v4 transform: DOM elements, components, fragments, keys, spread props,
  escaped prop names, optional children, memoed components:
  `jsx_transform_patterns.res`.
- JSX preserve output: `jsx_preserve_minimal.res`.
- External React components with `@module`, `@scope`, default imports,
  callback props, polymorphic event details, arrays, fragments:
  `jsx_external_component_patterns.res`.
- React component edge cases: aliased/default props, module-typed props,
  `forwardRef`, `memo`, `cloneElement`, hook-shaped calls:
  `react_component_edge_patterns.res`.

## Derived And Attribute Codegen

- Builtin deriving for accessors, abstract records, optional fields, light
  abstract records: `deriving_output_patterns.res`.
- Deriving under `@@uncurried`: `uncurried_deriving_output_patterns.res`.
- Inline constants/functions/modules, `@inline` modes, `%%private`,
  legacy/direct null-to-option returns, `@unwrap`:
  `attribute_codegen_patterns.res`.

## Tella-Minimized Data Paths

- Large sparse JSX-style records: `tella_sparse_record.res`.
- JSON decode loops, row/path error wrapping, one-of fallbacks:
  `tella_json_decode_patterns.res`.
- JSON encode dict/list/object/tuple paths:
  `tella_json_encode_patterns.res`.
- Typed raw TextDecoder/Blob/Math-style helpers:
  `tella_raw_function_patterns.res`.

## Non-Focused Gates

- Local JS snapshot corpus: `./scripts/test_js_output_parity.sh --skip-spice-ppx`.
- Runtime/stdlib output corpus: `./scripts/test_stdlib_output_parity.sh`.
- External Tella output corpus, used as a mining and regression signal:
  `./scripts/test_tella_output_parity.sh --quick`.

## Out Of Scope

- Source forms that the ReScript parser/typechecker does not accept as
  compiling ReScript programs.
- Parser AST, typedtree, lambda, and diagnostic parity. Those have their own
  gates and are only used here as regression checks around output fixture work.
