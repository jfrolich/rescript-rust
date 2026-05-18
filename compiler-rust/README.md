# Rust Compiler Architecture

This document describes the Rust ReScript compiler implementation in
`compiler-rust/` and the build-system integration in `rewatch/`. It is written
as a source map and algorithm guide for people changing the compiler.

The Rust compiler is a port of the OCaml/ReScript compiler. The default rule is
that behavior must match the OCaml reference: traversal order, identifier
allocation, lazy forcing, physical type-node sharing, warning order, diagnostic
text, binary artifacts, Lambda shape, JavaScript output, and metadata all matter.
If Rust intentionally uses a different representation or execution mode, this
README calls it out as a Rust-specific diversion.

## Contents

- [Reference Source Map](#reference-source-map)
- [End-To-End Pipeline](#end-to-end-pipeline)
- [Observable Invariants](#observable-invariants)
- [Stage 0: Project Loading And Build Graph](#stage-0-project-loading-and-build-graph)
- [Stage 1: Compiler Entrypoints And Options](#stage-1-compiler-entrypoints-and-options)
- [Stage 2: Source Text, Lexing, And Locations](#stage-2-source-text-lexing-and-locations)
- [Stage 3: Parsing Into Parsetree](#stage-3-parsing-into-parsetree)
- [Stage 4: Binary ASTs And Dependency Extraction](#stage-4-binary-asts-and-dependency-extraction)
- [Stage 5: Frontend Rewrites, Built-In PPX, And File Directives](#stage-5-frontend-rewrites-built-in-ppx-and-file-directives)
- [Stage 6: Initial Typing Environment](#stage-6-initial-typing-environment)
- [Stage 7: Lazy Module Components And Substitution](#stage-7-lazy-module-components-and-substitution)
- [Stage 8: Core Type Engine](#stage-8-core-type-engine)
- [Stage 9: Expression, Pattern, And Type Syntax Checking](#stage-9-expression-pattern-and-type-syntax-checking)
- [Stage 10: Module And Signature Typing](#stage-10-module-and-signature-typing)
- [Stage 11: Diagnostics And Warnings](#stage-11-diagnostics-and-warnings)
- [Stage 12: Interface And Backend Metadata Artifacts](#stage-12-interface-and-backend-metadata-artifacts)
- [Stage 13: Typedtree To RawLambda](#stage-13-typedtree-to-rawlambda)
- [Stage 14: Pattern-Matching Compilation](#stage-14-pattern-matching-compilation)
- [Stage 15: RawLambda To Lambda](#stage-15-rawlambda-to-lambda)
- [Stage 16: Lambda Simplification](#stage-16-lambda-simplification)
- [Stage 17: Lambda To JavaScript IR](#stage-17-lambda-to-javascript-ir)
- [Stage 18: JavaScript IR Passes, Dependencies, And Metadata](#stage-18-javascript-ir-passes-dependencies-and-metadata)
- [Stage 19: JavaScript Printing And Output](#stage-19-javascript-printing-and-output)
- [Direct, Subprocess, And In-Process Modes](#direct-subprocess-and-in-process-modes)
- [Rust-Specific Diversions](#rust-specific-diversions)
- [Performance Instrumentation](#performance-instrumentation)
- [Optimization Map](#optimization-map)
- [Workflow For Architecture Changes](#workflow-for-architecture-changes)

## Reference Source Map

The OCaml reference is still the primary algorithm spec. When changing Rust
code, read the matching OCaml source first.

| Area | OCaml reference | Rust implementation | Notes |
| --- | --- | --- | --- |
| Main implementation driver | `compiler/core/js_implementation.ml` | `src/driver.rs` | OCaml `implementation` parses, applies external PPX, runs `Ppx_entry`, then `after_parsing_impl`. Rust direct source mode mirrors that order in `compile_source_to_js_with_options`. |
| Interface driver | `compiler/core/js_implementation.ml`, `compiler/ml/typemod.ml` | `src/driver.rs` | Interfaces parse as signatures, run signature PPX/config/warnings, typecheck, then publish `.cmi`-like data. |
| ReScript syntax parser | `compiler/syntax/`, `compiler/ml/parsetree.ml` | `src/parser/*`, `src/parse_arena.rs` | Rust parser uses arena indices instead of OCaml heap records, but output shape and locations must match. |
| Frozen PPX AST boundary | `compiler/ml/parsetree0.ml`, `ast_mapper_to0.ml`, `ast_mapper_from0.ml`, `binary_ast.ml` | `src/binary_ast/parsetree0.rs`, `mapper_to0.rs`, `mapper_from0.rs`, `writer.rs`, `marshal.rs` | `parsetree0` is a compatibility wire format. Do not evolve it for new syntax. |
| Frontend and PPX rewrites | `compiler/frontend/*`, `compiler/core/cmd_ppx_apply.ml`, `compiler/frontend/ppx_entry.ml` | `src/binary_ast/ppx.rs`, `src/parser/jsx_ppx.rs`, `src/parser/let_unwrap_ppx.rs`, `src/driver.rs` | Order is observable through warnings, errors, AST dumps, and generated code. |
| Initial environment | `compiler/core/res_compmisc.ml`, `compiler/ml/env.ml` | `src/types/predef.rs`, `src/types/env.rs`, `src/cmi/persistent_env.rs`, `src/driver.rs` | Pervasives/Stdlib loading and implicit opens must preserve OCaml lookup and force order. |
| Persistent environment | `compiler/ml/env.ml`, `compiler/ml/cmi_format.ml`, `compiler/ml/cmi_format.mli` | `src/cmi/persistent_env.rs`, `src/cmi/cmi_format.rs`, `src/cmi/sig_reader.rs`, `src/cmi/portable_types.rs` | Rust has disk-backed and registry-backed modes. Both expose the same logical signatures/metadata. |
| Lazy module components | `compiler/ml/env.ml` (`EnvLazy` module), `compiler/ml/subst.ml` | `src/types/env_lazy.rs`, `src/types/env.rs`, `src/types/context.rs` | This is a high-risk parity area. Rust must preserve OCaml API boundaries such as `find_module_descr` versus `find_module`. |
| Core type operations | `compiler/ml/ctype.ml`, `compiler/ml/btype.ml` | `src/types/ctype.rs`, `src/types/btype.rs`, `src/types/type_expr.rs` | Physical sharing created by `instance`, `copy`, `link_type`, `unify`, generalization, and row mutation is observable in typedtree sexp parity. |
| Type declarations and data representation | `compiler/ml/typedecl.ml`, `compiler/ml/datarepr.ml`, `compiler/ml/typetexp.ml` | `src/types/typemod.rs`, `src/types/typecore.rs`, `src/types/decl.rs` | Constructors, labels, records, variants, objects, externals, and type attributes must build equivalent declarations. |
| Expression and pattern typing | `compiler/ml/typecore.ml`, `compiler/ml/typeopt.ml`, `compiler/ml/parmatch.ml` | `src/types/typecore.rs`, `src/raw_lambda/typeopt.rs` | Includes expression inference, pattern typing, labels, application, rows, warnings, and error messages. |
| Module and signature typing | `compiler/ml/typemod.ml`, `compiler/ml/includemod.ml`, `compiler/ml/mtype.ml` | `src/types/typemod.rs`, `src/types/includemod.rs` | Includes structures, signatures, functors, includes, opens, recursive modules, interface inclusion, delayed checks, and signature simplification. |
| Typedtree definitions and dumps | `compiler/ml/typedtree.ml`, `compiler/ml/sexp_typedtree.ml` | `src/types/typedtree.rs`, `src/types/sexp_typedtree.rs` | Serializer must reflect typechecker output. It must not normalize content to hide typechecker differences. |
| Typedtree to first Lambda representation | `compiler/ml/translcore.ml`, `compiler/ml/translmod.ml`, `compiler/ml/matching.ml`, `compiler/ml/typeopt.ml`, `compiler/ml/lambda.ml` | `src/raw_lambda/convert.rs`, `src/raw_lambda/matching.rs`, `src/raw_lambda/typeopt.rs`, `src/raw_lambda/mod.rs` | Rust `RawLambda` is the counterpart of OCaml `Lambda.lambda`. |
| First Lambda to JS-backend Lambda, then optimization | `compiler/core/lam_convert.ml`, `compiler/core/lam_compile_main.ml`, `compiler/core/lam_pass_*.ml` | `src/raw_lambda/lower.rs`, `src/lambda/lam_compile_main.rs`, `src/lambda/lam_pass_*.rs` | OCaml also has this second Lambda-level representation: `Lam_convert.convert` converts `Lambda.lambda` into backend `Lam.t`. Pass order is fixed by the OCaml backend. |
| JavaScript backend | `compiler/core/lam_compile.ml`, `compiler/core/js_*.ml`, `compiler/core/j.ml` | `src/lambda/lam_compile.rs`, `src/lambda/js_*`, `src/js_ir/*` | Includes JS IR, externals, primitives, module paths, exports, side effects, and printer behavior. |
| Build system integration | OCaml `bsb`/legacy build behavior plus compiler artifact contracts | `rewatch/src/build/*` | Rewatch is Rust-specific, but artifact semantics and compiler invocation semantics must stay compatible. |

## End-To-End Pipeline

At the highest level, a `.res` implementation follows this pipeline:

```text
rescript.json + source graph
  -> rewatch package/source discovery
  -> parse .res/.resi into Parsetree nodes stored in ParseArena
  -> dependency extraction and optional binary .ast/.iast writing
  -> external PPX plus built-in frontend rewrites
  -> TypeContext + Env + PersistentEnv setup
  -> module/expression/pattern/type checking into Typedtree
  -> interface inclusion, signature simplification, and signature publishing
  -> Typedtree to RawLambda (OCaml Lambda.lambda equivalent)
  -> RawLambda to JS-backend Lambda (OCaml Lam.t equivalent)
  -> Lambda simplification and JS-backend optimization
  -> Lambda to JavaScript IR
  -> JS IR passes, dependency collection, and backend metadata
  -> JavaScript printing and artifact writing
```

The OCaml implementation path is:

```text
js_implementation.implementation
  -> Res_compmisc.init_path
  -> parser
  -> Cmd_ppx_apply.apply_rewriters
  -> Ppx_entry.rewrite_implementation
  -> dump parsetree/source when requested
  -> after_parsing_impl
  -> Ast_config.process_str
  -> optional no_export/binary_ast/as_pp/syntax_only handling
  -> Res_compmisc.initial_env
  -> Typemod.type_implementation_more
  -> typedtree dumps
  -> Translmod.transl_implementation
  -> Lam_compile_main.compile
  -> Lam_compile_main.lambda_as_module
  -> GenType processing
```

The Rust direct source path is:

```text
driver::compile_source_to_js_with_options
  -> parser::module::parse_structure
  -> apply_external_structure_ppxs
  -> config/warning/directive extraction
  -> JSX and let-unwrap transforms
  -> built-in extension and expression rewrites
  -> TypeContext/TypeCheckContext/Env/PersistentEnv setup
  -> typemod::type_structure
  -> moregen/interface inclusion checks
  -> signature simplification/normalization/publishing
  -> typedtree dumps when requested
  -> RawLambdaConverter::convert_structure_with_coercion
  -> raw_lambda::lower::lower_to_lambda_with_start_stamp
  -> LambdaCompiler::compile_deps_program_with_possible_required_modules
  -> print_deps_program_with_directives_and_options
```

The Rust in-process path has the same logical compiler stages, but rewatch
splits them:

```text
rewatch parse step
  -> StoredAst in BuildCommandState
  -> compile_preprocessed_structure_in_process_until_js
  -> publish signature early when allowed
  -> return InProcessPreJsCompileResult
  -> scheduler waits for backend-visible dependency metadata
  -> finish_preprocessed_structure_in_process_from_js_boundary_with_metadata_hook
  -> publish JS metadata
  -> write JS outputs
```

The interface path is the same idea, but it parses a signature, typechecks it as
a module type, saves/publishes the signature, and produces `.cmti`/`.cmi`-like
data instead of Lambda/JS.

## Observable Invariants

These details are not implementation trivia; tests and users can observe them.

- Identifier stamps are part of compiler output. Typedtree sexps, Lambda dumps,
  generated JS names, export identifiers, and module metadata all depend on
  stamp allocation order.
- Type expression identity is physical identity. OCaml typedtree sexp dedup is
  based on `type_expr.id`, not structural equality. Rust must preserve the same
  sharing through `TypeExprRef`.
- Lazy environment force order is semantic for parity. Forcing a component table
  can allocate paths, substitute declarations, copy type nodes, and cache child
  components in an order that later dumps expose.
- Path spelling is observable. `Pident`, `Pdot`, `Papply`, flattened module names,
  generated nested module names, and alias paths must be produced by the same
  declaration/substitution flow as OCaml.
- Location and position accounting is user visible. Parser errors, type errors,
  warning ranges, AST dumps, and source maps must agree with the reference.
- Warning order is observable. PPX warnings, parse diagnostics, type warnings,
  delayed unused checks, warning-as-error, and fatal errors must be emitted in the
  same order and with the same failure behavior as the OCaml compiler.
- Binary artifacts are compatibility boundaries. `.ast`, `.iast`, `.cmi`, and
  `.cmj`-like data must carry the same logical information in subprocess and
  in-process modes.
- JavaScript output is byte-level observable. Small changes in Lambda shape,
  export coercion, module ordering, identifier allocation, or printer formatting
  can be user-visible even if runtime behavior is unchanged.

## Stage 0: Project Loading And Build Graph

`rewatch` is the build-system front end for the Rust compiler. It reads project
configuration, discovers source files, computes dirty state, schedules work, and
writes artifacts.

Important files:

- `rewatch/src/project_context.rs`
- `rewatch/src/build/packages.rs`
- `rewatch/src/build/read_compile_state.rs`
- `rewatch/src/build/parse.rs`
- `rewatch/src/build/deps.rs`
- `rewatch/src/build/compile.rs`
- `rewatch/src/build/clean.rs`

Algorithm:

1. Find the nearest project root and read `rescript.json`.
2. Resolve package configuration, dependencies, dev dependencies, source
   directories, namespace settings, output module format, and feature flags.
3. Build a module table from source files. A module can have an implementation
   file (`.res`) and an optional interface file (`.resi`).
4. Read prior compile state and compare timestamps/content state to determine
   parse dirty and compile dirty modules.
5. Parse dirty files and extract module dependencies from the parsetree or
   binary AST dependency section.
6. Validate that each dependency is available through package dependencies and
   source directories.
7. Schedule ready modules according to the dependency graph. Interfaces are
   typechecked before implementations when present.
8. Publish interface or implementation signatures as soon as they are available
   in in-process mode.
9. Finish JS after backend-visible dependency metadata is available.
10. Write JS, interface, and build-state artifacts.

OCaml reference alignment:

- The compiler artifact contract follows the OCaml/ReScript compiler: `.ast` and
  `.iast` carry parsed ASTs; `.cmi` carries signatures; `.cmj` carries backend
  metadata used by JavaScript generation.
- The build scheduler itself is Rust-specific. Its job is to preserve the same
  module dependency semantics while reducing process and artifact overhead.

In-process scheduler detail:

- Type dependencies gate typechecking.
- Backend-visible dependencies gate JS finalization.
- Implementation signatures for modules without `.resi` are published early,
  matching OCaml's "save inferred signature before translation" behavior in
  `Typemod.type_implementation_more`.
- JS metadata such as purity, export constants, export arities, and cross-module
  inlineable Lambda is published after JavaScript lowering has inspected the
  simplified module.
- The ready queue uses critical-path priority and a bounded Rayon pool so large
  projects do not submit all work at once and lose scheduling control.

## Stage 1: Compiler Entrypoints And Options

The direct compiler entrypoint is `compile_source_to_js_with_options` in
`src/driver.rs`. The in-process entrypoints are
`compile_preprocessed_structure_in_process_until_js` and
`finish_preprocessed_structure_in_process_from_js_boundary_with_metadata_hook`.
The CLI binary is `src/bin/bsc.rs`.

Compiler options affect every later stage:

- Source and output paths select module names, output prefixes, load paths, and
  artifact names.
- `-I`, package config, runtime path, and module format affect persistent
  environment loading and JS module path resolution.
- `-nopervasives`, implicit opens, `-bs-jsx`, debug flags, warning flags, and
  file-level `@@config` affect frontend and typechecker behavior.
- Dump flags such as `-dtyped-sexp`, `-drawlambda`, and `-dlambda-sexp` expose
  intermediate representations and can short-circuit downstream work in parity
  scripts.
- In-process options can skip JS rendering, capture intermediates, publish
  signatures through hooks, or compile multiple JS targets from one Lambda tree.

OCaml reference alignment:

- OCaml stores many options in global modules such as `Clflags`, `Js_config`,
  `Config`, and `Location`.
- Rust threads most option state through `CompilerOptions`, `TypeCheckContext`,
  `PersistentEnv`, and backend compiler structs. This is a representation
  difference; the observable option semantics should match.

## Stage 2: Source Text, Lexing, And Locations

The Rust parser lives under `src/parser/`. It is a hand-written parser with a
byte-oriented scanner.

Important files:

- `src/parser/scanner.rs`
- `src/parser/token.rs`
- `src/parser/state.rs`
- `src/parser/grammar.rs`
- `src/parser/code_frame.rs`
- `src/source_text.rs`
- `src/location.rs`
- `src/parse_arena.rs`

Algorithm:

1. `Parser::new` creates parser state for a filename and source string.
2. The scanner reads bytes and emits tokens with source locations.
3. ASCII paths are fast; non-ASCII text is decoded as UTF-8 only when needed.
4. The scanner tracks byte offsets, character positions, UTF-16 code-unit
   offsets, line starts, and line numbers.
5. Comments and doc comments are captured instead of discarded.
6. The parser maintains lookahead, error-recovery state, region state, and the
   current `ParseArena`.
7. Diagnostics are accumulated with precise locations and later rendered by the
   driver.

Context-sensitive lexer behavior:

- Type-parameter diamond parsing uses scanner/parser mode state.
- JavaScript-like regular-expression literals need previous-token context.
- Comments and documentation comments must remain attached enough for printers,
  AST tooling, and diagnostics.
- Some token classifications depend on expression, pattern, type, structure, or
  signature context.

Rust-specific diversion:

- OCaml ASTs are ordinary heap-allocated values with source locations embedded in
  records. Rust stores positions, locations, strings, longidents, and recursive
  AST nodes in `ParseArena` and passes compact indices through the parsetree.
  This is intended as a representation-only diversion.

## Stage 3: Parsing Into Parsetree

The parser builds a ReScript parsetree for either an implementation (`.res`) or
a signature (`.resi`).

Important files:

- `src/parser/module.rs`
- `src/parser/expr.rs`
- `src/parser/pattern.rs`
- `src/parser/typ.rs`
- `src/parser/ast.rs`
- `src/parser/comment_table.rs`
- `src/parser/printer.rs`
- `src/parser/ml_printer.rs`
- `src/parser/formatter.rs`

Implementation parsing algorithm:

1. `module::parse_structure` parses top-level structure items until EOF.
2. Module items parse into module declarations, includes, opens, imports,
   exports, type declarations, value bindings, externals, extensions, and
   attributes.
3. Expressions parse with explicit precedence and associativity handling.
4. Patterns parse with their own grammar so binding forms, constructor payloads,
   record patterns, arrays, variants, aliases, or-patterns, and constraints have
   the correct AST shape.
5. Core types parse separately from expressions and patterns, including arrows,
   tuples, variants, objects, polytypes, type variables, module paths, and
   attributes.
6. The parser records comments and doc comments for later tooling.
7. Recovery points limit cascaded parse errors inside damaged regions.

Signature parsing algorithm:

1. `module::parse_signature` parses signature items until EOF.
2. It accepts value declarations, type declarations, module declarations,
   module type declarations, includes, opens, externals, extensions, and
   attributes.
3. Module expressions are not accepted where module types are required, and vice
   versa. Error recovery still tries to continue to later signature items.

Syntax-level ReScript work:

- Inline record declarations inside variants can generate nested type
  declarations with dotted names.
- Import/export surface syntax is mapped into parsetree forms consumed by later
  frontend/typechecker code.
- JSX syntax remains syntax until the JSX PPX transform stage.
- Let-unwrap syntax is accepted by the parser but rejected or transformed later
  depending on flags.

OCaml reference alignment:

- The Rust parser mirrors the ReScript surface parser, not upstream OCaml
  syntax. The downstream parsetree is still consumed by OCaml-derived typing and
  backend algorithms, so parsetree shape, locations, and attributes must match
  what the OCaml/ReScript compiler expects after parsing.

## Stage 4: Binary ASTs And Dependency Extraction

`src/binary_ast/` supports the historical `.ast` and `.iast` artifact format
and the PPX compatibility boundary.

Important files:

- `src/binary_ast/mod.rs`
- `src/binary_ast/writer.rs`
- `src/binary_ast/deps.rs`
- `src/binary_ast/mapper_to0.rs`
- `src/binary_ast/mapper_from0.rs`
- `src/binary_ast/parsetree0.rs`
- `src/binary_ast/current_marshal.rs`
- `src/binary_ast/parsetree0_marshal.rs`
- `src/binary_ast/marshal.rs`

Binary AST algorithm:

1. Walk the current parsetree and extract a dependency section.
2. Map the current parsetree to frozen `parsetree0` when writing the PPX wire
   format.
3. Serialize the dependency section and OCaml marshal-compatible AST payload.
4. In subprocess mode, rewatch or the compiler can write `.ast`/`.iast` files
   for later compiler invocation.
5. External PPX processes read and write the marshal-compatible payload.
6. When necessary, map `parsetree0` back into the current parsetree after PPX.

Dependency extraction algorithm:

- The dependency walker records module references that can affect build order.
- It distinguishes references in implementation and interface files.
- It must agree with the module dependency semantics used by the legacy build
  system, including namespace and generated module-name behavior.

OCaml reference alignment:

- `parsetree0` corresponds to the frozen OCaml/ReScript PPX boundary. New syntax
  should change the current parsetree and mapper modules, not mutate
  `parsetree0`.
- OCaml marshal compatibility is required because external PPX tools are outside
  the Rust compiler.

Rust-specific diversion:

- In in-process mode, rewatch can skip writing `.ast`/`.iast` files and keep
  `StoredAst` values in memory. This removes serialization/process overhead but
  does not change the logical stage boundary.

## Stage 5: Frontend Rewrites, Built-In PPX, And File Directives

The frontend rewrite layer runs between parsing and typechecking. In OCaml it is
spread across `compiler/frontend/`, `compiler/syntax/`, `Cmd_ppx_apply`, and
`Ppx_entry`. In Rust it is called from `src/driver.rs`,
`src/binary_ast/ppx.rs`, `src/parser/jsx_ppx.rs`, and
`src/parser/let_unwrap_ppx.rs`.

Direct source order in Rust:

1. Parse the structure.
2. Apply external structure PPXs.
3. Reject invalid polymorphic variant integer literals.
4. Collect leading built-in warning attributes.
5. Validate and extract file `@@config`.
6. Build the effective warning config from CLI options, leading attributes, and
   file config.
7. Emit PPX/config warnings with the correct warning state.
8. Extract file directives for output printing.
9. Compute debug and JSX-preserve flags.
10. Validate let-unwrap availability and malformed let-unwrap syntax.
11. Run JSX transform if the file/options select a JSX version.
12. Collect raw JS warnings.
13. Expand built-in extension points such as raw JS/private payloads.
14. Rewrite expressions and module forms for pipes, setters, property access,
    await, tagged templates, externals, and mapper/spice-style rewrites.
15. Reserve parser arena capacity for synthetic typecheck nodes.

OCaml reference order:

- `js_implementation.implementation` runs `Cmd_ppx_apply.apply_rewriters` before
  `Ppx_entry.rewrite_implementation`.
- `after_parsing_impl` then runs `Ast_config.process_str`, optional `no_export`,
  binary AST writing, `as_pp`, `syntax_only`, environment initialization, and
  typechecking.

Why order matters:

- Warning attributes must be collected before generated warnings are emitted.
- File directives must be preserved until final JS printing.
- JSX and let-unwrap rewrites must happen before general built-in rewrites.
- External PPX output must be seen by built-in processing.
- `@@no_export` changes the structure shape before typechecking and export
  coercion.

## Stage 6: Initial Typing Environment

Typechecking starts with fresh compiler state, an initial local environment, and
a persistent environment view.

Important files:

- `src/types/context.rs`
- `src/types/type_expr.rs`
- `src/types/env.rs`
- `src/types/env_lazy.rs`
- `src/types/predef.rs`
- `src/types/path.rs`
- `src/cmi/persistent_env.rs`
- `src/driver.rs`

Algorithm:

1. Reset the OCaml-compatible identifier stamp state.
2. Create an `IdGenerator` starting at the non-predef stamp start.
3. Consume the stamp that OCaml's `Parmatch.extra_pat` consumes at module
   initialization.
4. Create `TypeContext` from the generator.
5. Create `TypeCheckContext` for this module and parser arena.
6. Apply command-line, leading-attribute, and file-config warning options.
7. Create the initial `Env` with predefined types, constructors, exceptions,
   primitives, and builtin module paths.
8. Create `PersistentEnv`.
9. Configure load paths, displayed load paths, open modules, JSX version,
   `-nopervasives`, and current compiling module.
10. Load Pervasives/Stdlib unless disabled.
11. Install implicit opens through the same lookup/open machinery as ordinary
    opens.
12. Attach `PersistentEnv` to `TypeCheckContext`.

OCaml reference alignment:

- `Res_compmisc.initial_env` and `Env.set_unit_name` set up the OCaml initial
  environment before `Typemod.type_implementation_more`.
- Rust keeps this state explicit in `TypeContext`, `TypeCheckContext`, `Env`,
  and `PersistentEnv`, but stamp order and lookup semantics must match.

Local `Env` model:

- Values, types, constructors, labels, modules, and module types are stored in
  identifier tables.
- Opens are symbolic layers, not eager flattening of every declaration into the
  current scope.
- Included signatures extend the environment in source order.
- Module aliases and paths are retained so later lookup, error reporting, and
  backend translation can recover the same paths as OCaml.

Persistent environment model:

- Disk mode searches load paths and reads `.cmi`/`.cmj` artifacts.
- In-process mode reads signatures and backend metadata from `ModuleRegistry`.
- The current compiling unit is hidden or exposed at precise points to match
  OCaml's save-before-translation behavior without letting JS dependency probing
  import the current unit as a normal dependency.

## Stage 7: Lazy Module Components And Substitution

Module lookup is one of the highest-impact and highest-risk parity areas.

OCaml reference algorithm:

1. `Env.components_of_module` creates an `EnvLazy` thunk from `(env, sub, path,
   module_type)`.
2. `Env.components_of_module_maker` forces the thunk.
3. It calls `scrape_alias env mty`.
4. For a signature module type, it creates empty component tables for values,
   constructors, labels, types, modules, module types, and child components.
5. It calls `prefix_idents path sub sg`, which assigns `Pdot(root, name, pos)`
   paths and extends the substitution for types, modules, and module types.
6. It walks the signature with `List.iter2` over items and prefixed paths.
7. `Sig_value` substitutes the value description, stores it with the current
   runtime position, and increments position unless the value is `Val_prim`.
8. `Sig_type` substitutes the type declaration, sets row names through
   `Datarepr.set_row_name`, derives constructors and labels, stores type info,
   and does not increment the runtime position.
9. `Sig_typext` substitutes the extension constructor, derives the extension
   descriptor, stores it in constructor tables, and increments position.
10. `Sig_module` creates a lazy substituted module declaration, stores it with
    the current position, creates child components through
    `components_of_module`, stores the module in the running environment, and
    increments position.
11. `Sig_modtype` substitutes the module type declaration, stores it with
    `nopos`, and stores the module type in the running environment.
12. For functors, OCaml stores the parameter, substituted argument/result module
    types, and caches for applications/substitutions.
13. For aliases or unresolved identifiers, the component maker can return no
    structure components.

Rust implementation:

- `QualifiedModuleComponents` represents a signature viewed through a selected
  access path.
- Component tables are shared behind `Arc` and interior-mutability cells so
  repeated lookups reuse forced state.
- Stored module components use `OnceCell` so a forced component view is reused.
- Values, types, modules, module types, constructors, labels, and child
  components can be built lazily by bucket instead of materializing every table.
- Child module components are lazy per child name, so looking up `A.B` should not
  force all siblings under `A`.
- Functor result substitutions are cached because repeated functor applications
  can otherwise rebuild equivalent component views.
- `TypeContext` caches shared qualified views so repeated opened-module lookups
  can reuse the same component table.

API-boundary rules:

- `find_module_descr`, `find_module`, `find_type`, constructor lookup, label
  lookup, and component-table forcing are distinct OCaml APIs. They may force
  different thunks at different times.
- Rust should not compensate by suppressing a force, rewriting a path, or
  guessing alias equivalence after lookup. The fix should move behavior into
  the same lazy thunk or lookup boundary as OCaml.
- Runtime positions are computed by the same rules as OCaml: ordinary values,
  type extensions, and modules affect runtime positions; primitive values,
  types, and module types do not.

Current Rust-specific risk:

- `src/types/env_lazy.rs` is OCaml-inspired and much closer to the reference than
  earlier eager component-table code, but it is not yet a trivial line-for-line
  port of `Env.components_of_module_maker`. Any performance or parity work here
  should cite the exact OCaml reference path and avoid adding a Rust-only
  compatibility layer.

## Stage 8: Core Type Engine

The core type engine corresponds primarily to OCaml `ctype.ml` and `btype.ml`.

Important files:

- `src/types/ctype.rs`
- `src/types/btype.rs`
- `src/types/type_expr.rs`
- `src/types/context.rs`
- `src/types/path.rs`
- `src/types/variance.rs`

Core data model:

- `TypeExprRef` is the Rust handle for mutable type nodes.
- Type descriptions include variables, arrows, tuples, constructors, objects,
  variants/rows, links, substitutions, polymorphic types, packages, and
  univar/non-generic state.
- Type nodes have levels, scopes, IDs, and mutable descriptions.
- Rows contain present/absent/either fields, row variables, closed/open state,
  and metadata needed for polymorphic variants and objects.

OCaml algorithm:

1. `begin_def` raises the current level before typing a definition.
2. Fresh type variables are allocated at the current level.
3. `end_def` leaves the definition level.
4. `generalize` marks eligible variables as generic.
5. `instance` copies polymorphic schemes into fresh type nodes.
6. `repr` follows `Tlink` chains to the current representative.
7. `unify` mutates type nodes by linking representatives, lowering levels, and
   recursively unifying descriptions.
8. Occurs checks reject infinite types.
9. Expansion functions such as `expand_head` reveal abbreviations and manifests
   when required by the typing algorithm.
10. Row operations merge fields and row variables while preserving OCaml's
    mutation and sharing behavior.

Rust alignment requirements:

- Do not replace physical sharing with structural equality.
- Do not normalize rows or paths in serializers to hide typechecker differences.
- Preserve when `instance` copies and when it returns shared nodes.
- Preserve level lowering during unification and generalization.
- Preserve link direction where OCaml's representative choice is observable.
- Preserve expansion order, because expansion can force modules and allocate
  substituted type declarations.

Performance sensitivity:

- Type allocation and copying is often hot in large projects.
- Any arena or allocation optimization must preserve `TypeExprRef` identity
  semantics and OCaml-like mutation points.

## Stage 9: Expression, Pattern, And Type Syntax Checking

This stage corresponds mainly to OCaml `typecore.ml`, `typetexp.ml`,
`typeopt.ml`, and parts of `parmatch.ml`.

Important files:

- `src/types/typecore.rs`
- `src/types/typemod.rs`
- `src/types/decl.rs`
- `src/types/typedtree.rs`
- `src/raw_lambda/typeopt.rs`

Expression typing algorithm:

1. Parse nodes are typed in source traversal order.
2. Identifiers are resolved through `Env`, opened layers, and `PersistentEnv`.
3. Expected-type information flows into expressions through `type_expect`-style
   calls.
4. Applications instantiate the function type, type arguments in order, handle
   labelled/optional arguments, and unify the result with the expected type.
5. Let-bindings type patterns and expressions, enforce recursive binding rules,
   run value restriction, and generalize eligible variables.
6. Records resolve labels, build field typing information, handle punning,
   optional fields, updates, and missing/extra-field diagnostics.
7. Variants resolve constructors, build payload types, handle unboxed/untagged
   encodings, and enforce arity.
8. Polymorphic variants update row fields and constraints.
9. Objects and object field accesses update object rows.
10. Control-flow expressions such as `if`, `switch`, `try`, loops, and sequence
    forms type subexpressions in OCaml order and unify branch/result types.
11. Externals, raw JS, JSX output, optional values, promises, and ReScript
    primitives attach backend attributes and typedtree metadata.

Pattern typing algorithm:

1. Allocate pattern type variables at the current level.
2. Resolve constructors, labels, variants, arrays, tuples, records, aliases, and
   or-patterns.
3. Bind value identifiers with their inferred types in the pattern environment.
4. Unify constructor/label payloads with pattern subnodes.
5. Track pattern modes and usage information needed for warnings.
6. Preserve OCaml's order for binding allocation and error reporting.
7. Produce typed patterns consumed by expression typing and later matching
   compilation.

Type-syntax translation algorithm:

- Core type syntax is translated into type expressions in the current
  environment.
- Type constructors are resolved through paths and persistent environment lookup.
- Type variables are scoped and reused according to OCaml's rules.
- Package types, object types, polymorphic variants, aliases, private rows,
  labelled arrows, optional arrows, and unboxed annotations build the same
  internal type descriptions as the reference.

Warnings and delayed checks:

- Unused values, unused opens, fragile patterns, partial matches, deprecated
  items, ignored attributes, and warning-as-error state are collected while
  typing.
- Some checks are delayed until after interface inclusion so exported values are
  not reported as unused merely because they are not used inside the module.

## Stage 10: Module And Signature Typing

This stage corresponds mainly to OCaml `typemod.ml`, `includemod.ml`,
`mtype.ml`, and declaration checking modules.

Important files:

- `src/types/typemod.rs`
- `src/types/includemod.rs`
- `src/types/typecore.rs`
- `src/types/decl.rs`
- `src/types/env.rs`
- `src/types/typedtree.rs`

Structure typing algorithm:

1. Type structure items in source order.
2. Each item returns typedtree nodes, signature items, and an updated environment.
3. `let` bindings extend values.
4. Type declarations check parameters, constraints, manifests, variants, records,
   externals, private/public flags, recursive groups, unboxed attributes, and
   representation details, then store type, constructor, and label information.
5. Module bindings type module expressions and store lazy module components.
6. Opens add symbolic opened layers and warning state.
7. Includes check included module types, compute inclusion/coercion information,
   and extend the environment with included signature items.
8. Exceptions/type extensions extend constructor tables and runtime positions.
9. Attributes and extension nodes are validated or passed through according to
   their meaning.
10. The final typed structure carries a signature and final environment.

Module expression algorithm:

- Identifiers resolve to module paths and module declarations.
- Structures type recursively through the structure algorithm.
- Functors type the parameter module type, extend the environment with the
  parameter, then type the body.
- Functor applications check argument module types against parameter module
  types and substitute the result.
- Constraints run inclusion checks and compute coercions.
- Unpacks and first-class modules preserve package typing rules.

Signature typing algorithm:

- Value descriptions translate core types and attributes.
- Type declarations are checked similarly to implementation type declarations,
  but produce signature declarations.
- Module declarations type module types and register lazy components.
- Module type declarations store aliases or signatures.
- Includes expand/check included signatures.
- Opens affect following signature items.

Implementation/interface algorithm:

OCaml `Typemod.type_implementation_more` does the following:

1. Clear CMT state and delayed checks.
2. Call `type_structure initial_env ast`.
3. Compute `simple_sg = simplify_signature sg`.
4. If an interface exists, find the `.cmi`, read the declared signature, run
   `Includemod.compunit initial_env sourcefile sg intf_file dclsig`, force
   delayed checks, save CMT, and return the declared signature.
5. If no interface exists, run `Includemod.compunit` against the inferred simple
   signature, run `check_nongen_schemes`, run `normalize_signature`, force
   delayed checks, save `.cmi` and CMT, and return the simple signature.
6. On error, save a partial CMT before re-raising.

Rust mirrors this behavior in `src/driver.rs` around typechecking:

- Typecheck the structure through `typemod::type_structure`.
- Apply moregen/interface constraints before typedtree sexp output when a `.resi`
  exists.
- Run inclusion checks.
- If no `.resi` exists, simplify the inferred signature, check non-generalized
  schemes, normalize signature types, prepare the signature for saving, and
  publish it before Lambda conversion.
- If a `.resi` exists, keep the declared interface as the target signature and
  do not replace it with the implementation signature for export coercion.

## Stage 11: Diagnostics And Warnings

Diagnostics are a first-class compiler output. Parse and compiler errors must
match the OCaml compiler byte for byte where parity is the goal.

Important files:

- `src/parser/diagnostics.rs`
- `src/parser/code_frame.rs`
- `src/diagnostics.rs`
- `src/driver.rs`
- `src/types/typecore.rs`
- `src/types/typemod.rs`
- `src/types/includemod.rs`
- `src/cmi/persistent_env.rs`

Diagnostic flow:

1. Parser diagnostics are accumulated while parsing.
2. Fatal parse failures are rendered by the driver with source code frames or
   reference-compatible fatal syntax output as required.
3. PPX/config/frontend warnings are collected and emitted after the effective
   warning configuration is known.
4. Typechecker functions return structured errors such as typecore, typemod,
   includemod, or persistent-env errors.
5. The driver checks persistent-env errors at the same points where OCaml would
   raise them.
6. Type warnings are emitted before errors when the reference does so.
7. Delayed checks are flushed after interface inclusion.
8. Warning-as-error converts otherwise successful compilation into failure.
9. Backend diagnostics are rendered with locations after RawLambda or JS lowering.

Parity rules:

- Do not normalize diagnostic output in parity tests.
- Do not special-case Rust messages to pass a fixture if the check belongs in
  the parser/typechecker/backend algorithm.
- Parse diagnostics should be generated at the same parser decision point as the
  OCaml/ReScript parser.
- Type diagnostics should come from the same `Typecore`, `Typemod`, `Ctype`,
  `Env`, or `Includemod` check as the reference.

## Stage 12: Interface And Backend Metadata Artifacts

The compiler publishes cross-module information for later units.

Important files:

- `src/cmi/persistent_env.rs`
- `src/cmi/cmi_format.rs`
- `src/cmi/sig_reader.rs`
- `src/cmi/portable_types.rs`
- `src/types/includemod.rs`
- `src/driver.rs`
- `rewatch/src/build/compile.rs`

Interface metadata:

- Module signatures.
- Type declarations.
- Value declarations.
- Module and module type declarations.
- Paths, identifiers, stamps, attributes, and deprecation metadata.
- Data needed to reconstruct environment components lazily.

Backend metadata:

- Package and source path information.
- Output module format.
- Purity/side-effect status.
- Export constants.
- Export arities.
- Export Lambda values used for cross-module inlining when enabled.

OCaml reference behavior:

- For modules without `.mli`/`.resi`, `Typemod.type_implementation_more` saves
  the inferred `.cmi` before `Translmod.transl_implementation`.
- JavaScript generation later reads `.cmj` metadata for dependency paths,
  side-effect checks, arities, constants, and inlineable Lambda.

Rust behavior:

- Disk/subprocess mode uses file artifacts.
- In-process mode publishes equivalent logical data through `ModuleRegistry`.
- The in-process pre-JS stage can publish signatures early, then the JS finish
  stage publishes backend metadata.
- Before JS dependency probing, the current unit is hidden again so it is not
  treated as an importable dependency.

## Stage 13: Typedtree To RawLambda

RawLambda is the first Rust backend IR. It corresponds to OCaml
`Lambda.lambda`, the representation produced by `Translcore` and `Translmod`
before the JS backend calls `Lam_convert.convert`.

Important files:

- `src/raw_lambda/mod.rs`
- `src/raw_lambda/convert.rs`
- `src/raw_lambda/typeopt.rs`
- `src/raw_lambda/print.rs`
- `src/types/typedtree.rs`

OCaml reference:

- `Translmod.transl_implementation module_name (str, coercion)` creates a
  persistent module identifier, translates the typed structure with module
  coercion, records exported identifiers, and returns `Lambda.lambda` plus
  exports.
- `Translcore.transl_exp` translates typed expressions to Lambda.
- `Typeopt` queries type information to choose optimized primitive and runtime
  representations.
- `Lam_compile_main.compile` receives this `Lambda.lambda` and then calls
  `Lam_convert.convert` before running backend Lambda passes.

Rust algorithm:

1. Synchronize the Lambda start stamp from the type context.
2. Compute the implementation coercion from the typed structure and interface
   state.
3. Create `RawLambdaConverter` with parser arena, type context, environment,
   start stamp, and unit name.
4. Configure options such as sparse-record preservation for dumps,
   `no_assert_false`, `noassert`, warning config, and persistent environment.
5. Convert structure items with coercion into RawLambda.
6. Record RawLambda warnings and diagnostics.
7. Flush delayed value-usage checks in the same logical region as OCaml delayed
   checks.
8. Capture possible required modules that later simplification may erase.
9. Print `-drawlambda` output when requested.

RawLambda covers:

- Constants, identifiers, lets, functions, applications, sequences, conditionals,
  loops, exceptions, static catches, switches, records, variants, arrays,
  modules, functors, includes, externals, optional values, unboxed/untagged
  encodings, dynamic imports, and primitive operations.

Representation mapping:

- OCaml has two Lambda-level representations: `Lambda.lambda` from
  `compiler/ml/lambda.ml`, then backend `Lam.t` after
  `compiler/core/lam_convert.ml`.
- Rust mirrors that split with `raw_lambda::RawLambda`, then `lambda::Lambda`
  after `raw_lambda::lower`.
- The names differ, but this is not meant to be a semantic extra stage.

## Stage 14: Pattern-Matching Compilation

Pattern matching spans typechecking and backend translation. The Rust matching
compiler is in RawLambda because it lowers typed pattern matrices into control
flow.

Important files:

- `src/raw_lambda/matching.rs`
- `src/raw_lambda/switch.rs`
- `src/raw_lambda/convert.rs`
- `src/raw_lambda/typeopt.rs`

OCaml reference:

- `compiler/ml/matching.ml`
- `compiler/ml/translcore.ml`
- `compiler/ml/parmatch.ml`
- `compiler/ml/typeopt.ml`

Algorithm:

1. Typed patterns and guarded actions enter as a match matrix.
2. The compiler analyzes constructors, constants, arrays, variants, records,
   exceptions, aliases, or-patterns, and default cases.
3. It chooses tests and switch forms while preserving evaluation order.
4. It shares actions when OCaml would share them.
5. It introduces static exits/catches for fallthrough and failure paths.
6. It preserves null/undefined and optional-value runtime encodings.
7. It uses type information to choose block tags, variant tags, record fields,
   unboxed representation checks, and special primitive paths.
8. It emits RawLambda switches, conditionals, lets, static raises, and handlers.

Why this stage is sensitive:

- Match compilation affects generated JS shape and performance.
- It affects warning behavior through partial/fragile match analysis.
- Static-exit shape affects later Lambda simplification and output byte parity.
- Typeopt lookups can force environment components, so matching can affect
  typedtree/lambda parity indirectly when it queries declarations.

## Stage 15: RawLambda To Lambda

The lowered Lambda IR lives in `src/lambda/mod.rs`. It corresponds to OCaml's
JS-backend `Lam.t`, the representation produced by `Lam_convert.convert`. The
Rust RawLambda boundary is implemented in `src/raw_lambda/lower.rs`.

Algorithm:

1. Consume RawLambda and the converter's current stamp.
2. Convert Raw constants, identifiers, functions, applications, lets, switches,
   catches, loops, modules, globals, primitives, and blocks into Lambda.
3. Rewrite predefined exceptions and runtime names where required.
4. Remap static exits and static catches.
5. Apply alias tables introduced by lowering.
6. Rename optional parameters where backend conventions require fresh names.
7. Preserve subexpression evaluation order.
8. Convert dynamic imports and module references into Lambda module references
   with metadata.
9. Convert property send/setter forms into primitive operations understood by
   JS lowering.

The result is still language-shaped. It has lets, functions, switches, primitive
operations, global module references, static catches, exceptions, loops, and
module-export blocks.

OCaml reference alignment:

- This boundary should match the semantics of `Lam_convert.convert`: convert the
  first Lambda representation into the JS-backend Lambda representation, record
  required modules, and preserve the shape expected by `Lam_compile_main`.
- Any lowering change should be checked against the reference Lambda dump and JS
  output, not only runtime behavior.

## Stage 16: Lambda Simplification

Before JS IR generation, Lambda goes through the JS backend simplification
pipeline in `src/lambda/lam_compile_main.rs`. This is intentionally aligned with
`compiler/core/lam_compile_main.ml`.

Pipeline order:

```text
RawLambda lowering has already performed the Lam_convert.convert-equivalent step
dump lambda sexp when requested
deep_flatten
collect_info
simplify_exits
collect_info
simplify_alias
deep_flatten
collect_info
simplify_alias
deep_flatten
collect_info
alpha_conversion
simplify_exits
collect_info
simplify_alias
alpha_conversion
simplify_lets
simplify_exits
export coercion / grouping
```

Important files:

- `src/lambda/lam_compile_main.rs`
- `src/lambda/lam_pass_deep_flatten.rs`
- `src/lambda/lam_pass_collect.rs`
- `src/lambda/lam_pass_exits.rs`
- `src/lambda/lam_pass_remove_alias.rs`
- `src/lambda/lam_pass_alpha_conversion.rs`
- `src/lambda/lam_pass_lets_dce.rs`
- `src/lambda/lam_coercion.rs`
- `src/lambda/lam_beta_reduce.rs`
- `src/lambda/lam_analysis.rs`
- `src/lambda/lam_free_variables.rs`
- `src/lambda/lam_arity.rs`

Pass responsibilities:

- `deep_flatten` flattens nested lets, sequences, and groups.
- `collect_info` records usage, arity, side effects, export information, and
  facts used by later passes.
- `simplify_exits` simplifies static exits and catches.
- `simplify_alias` removes aliases and performs inlining decisions using the
  collected metadata.
- `alpha_conversion` renames identifiers to avoid capture and collisions.
- `simplify_lets` removes dead lets and simplifies let structure.
- `lam_coercion` shapes top-level exports and module export groups.

Parity rule:

- The pass order is not an optimization knob. Changing it can alter identifiers,
  static exits, export shape, and JS output. Optimize inside a pass or by moving
  data more efficiently through the same pass order.

## Stage 17: Lambda To JavaScript IR

`src/lambda/lam_compile.rs` lowers simplified Lambda to `src/js_ir`.

Important files:

- `src/lambda/lam_compile.rs`
- `src/lambda/lam_compile_const.rs`
- `src/lambda/lam_compile_external.rs`
- `src/lambda/lam_compile_primitive.rs`
- `src/lambda/lam_compile_variant.rs`
- `src/lambda/js_exp_make.rs`
- `src/lambda/js_stmt_make.rs`
- `src/js_ir/mod.rs`

Algorithm:

1. Collect possible required modules from Lambda and combine them with modules
   captured before simplification.
2. Run Lambda simplification through `lam_compile_main`.
3. Collect CMJ export constants and arities from the simplified Lambda.
4. Seed the JS-lowering identifier generator past every existing Lambda stamp,
   matching OCaml `Ext_ident.create` behavior.
5. Compile Lambda expressions into JS expressions plus prelude statements.
6. Compile constants and blocks into JS runtime representations.
7. Compile primitives into JS operators, helper calls, runtime functions, or
   explicit control flow.
8. Compile externals using FFI metadata, module import metadata, arity, and
   dynamic-import state.
9. Compile variants and switches into JS tags, blocks, arrays, if/switch forms,
   and helper calls.
10. Extract top-level exports from module-export blocks.
11. Coerce exports to the expected runtime shape.
12. Rewrite top-level variable initializers through rewriteable aliases.
13. Resolve export aliases.
14. Compute side-effect status from Lambda.
15. Produce `DepsProgram { program, modules, side_effect }`.

JavaScript IR model:

- `Program` contains a block and exports.
- `Expression` and `Statement` represent JS syntax after ReScript backend
  lowering.
- `ModuleId`, `ModulePathResolver`, and `DepsProgram` carry dependency and module
  path information.
- Name reservations prevent the printer from reusing identifiers needed for
  exports or runtime bindings.

OCaml reference alignment:

- This corresponds to `compiler/core/lam_compile.ml` and related `js_*` modules.
- Cross-module inline decisions must follow `.cmj` metadata semantics.
- Identifier allocation must be seeded to match the global OCaml identifier
  counter behavior through Lambda and JS lowering.

## Stage 18: JavaScript IR Passes, Dependencies, And Metadata

After initial JS IR generation, several JS-level passes run.

Important files:

- `src/lambda/js_pass_flatten_and_mark_dead.rs`
- `src/lambda/js_pass_external_shadow.rs`
- `src/lambda/js_pass_tailcall_inline.rs`
- `src/lambda/js_shake.rs`
- `src/js_ir/mod.rs`
- `src/js_ir/program_printer.rs`

JS pass order in Rust:

1. Flatten JS blocks.
2. Rewrite or shadow external bindings where required.
3. Inline tail-call helper shapes.
4. Flatten again while marking dead code.
5. Shake unused declarations.
6. Collect required modules from the final JS block.
7. Add possible required modules that may have been erased by simplification but
   are still needed for dependency semantics.
8. Sort modules with OCaml-compatible ordering.
9. Update side-effect status based on required modules if the module body itself
   has no side-effect reason.

Module path resolution:

- Runtime modules can resolve through runtime paths.
- Local modules can resolve relative to the output path.
- Package modules resolve through package metadata.
- Dynamic imports keep dynamic import metadata.
- In-process mode can resolve module paths and metadata through `ModuleRegistry`.
- `.cmj` metadata provides side-effect, arity, constant, and inlineable Lambda
  information.

Metadata output:

- `cmj_export_constants` records constant exports for later modules.
- `cmj_export_arities` records function arities for later call optimization.
- Cross-module inlineable Lambda may be read when cross-module inlining is on.
- `is_pure` is derived from final program side-effect state.

## Stage 19: JavaScript Printing And Output

The final stage prints JavaScript text and writes generated files.

Important files:

- `src/js_ir/printer.rs`
- `src/js_ir/program_printer.rs`
- `src/driver.rs`
- `rewatch/src/build/compile.rs`

Printer algorithm:

1. Build the file-level output with directives first.
2. Print the generated header unless disabled.
3. Print `"use strict"` for CommonJS output when required.
4. Print static imports or `require` statements from sorted required modules.
5. Filter dynamic imports from static import lists.
6. Print the program body.
7. Print exports in CommonJS or ES module shape.
8. Print side-effect or purity comments when required.
9. Handle empty modules and modules with only directives/imports/exports.
10. Allocate JS names while avoiding reserved words, globals, name reservations,
    and local collisions.

OCaml reference alignment:

- This corresponds to `compiler/core/js_dump_program.ml`, `js_dump.ml`, and
  related JS printer modules.
- Output format is byte-level observable. Formatting-only differences are still
  regressions unless intentionally accepted.

Output targets:

- Direct source mode can return a JS string.
- Subprocess rewatch mode writes the output path selected by compiler args.
- In-process mode can render zero, one, or multiple JS targets from the same
  lowered Lambda depending on `CompilerOptions`.
- Post-build commands are run by rewatch after writing outputs when configured.

## Direct, Subprocess, And In-Process Modes

The compiler has three practical execution modes.

Direct source mode:

- Entry: `driver::compile_source_to_js_with_options`.
- Parses source text and runs all stages in one Rust call.
- Useful for tests, playground-style calls, and direct compiler invocations.
- Cross-module state comes from disk-backed `PersistentEnv`.

Rewatch subprocess mode:

- Rewatch parses or writes `.ast`/`.iast` artifacts.
- Compilation invokes a compiler process with compiler args.
- Cross-module state moves through file artifacts.
- This mode is closest to the historical process boundary.

Rewatch in-process mode:

- Rewatch parses once and stores ASTs/dependencies in memory.
- Interfaces are typechecked first when present.
- Implementations run to the pre-JS boundary as soon as type dependencies are
  ready.
- Signatures are published early to `ModuleRegistry`.
- JS finalization waits for backend-visible metadata dependencies.
- The pre-JS result carries lowered Lambda, possible required modules, current
  identifier stamp, directives, debug flags, JSX-preserve state, signature,
  optional registry updates, and captured intermediates.

The in-process split is a Rust-specific execution-mode diversion. It must
preserve OCaml's logical ordering:

- Save/publish the current unit's inferred signature before Lambda translation
  when there is no interface.
- Keep that signature visible during RawLambda conversion when OCaml would have
  it visible.
- Hide the current unit again before JS dependency probing.
- Carry the identifier stamp across the split because OCaml has one mutable
  global stamp through translation and JS compilation.

## Rust-Specific Diversions

Rust-specific diversions fall into two groups: representation-only differences
that should not affect behavior, and known algorithmic risk areas that require
extra care.

Representation-only diversions:

- `ParseArena` stores recursive AST nodes, strings, longidents, positions, and
  locations by index instead of OCaml heap records.
- `TypeContext` owns type nodes, predef state, lazy component caches, persistent
  environment views, and counters explicitly instead of using OCaml global
  mutable modules.
- `TypeCheckContext` threads warning state, feature flags, persistent env, and
  typechecker side effects explicitly.
- `PersistentEnv` can be disk-backed or registry-backed.
- `RawLambda` and `lambda::Lambda` make the OCaml `Lambda.lambda` to backend
  `Lam.t` split explicit in Rust naming.
- Lambda passes often have owned variants so Rust can move trees instead of
  cloning them.
- Performance counters and tracing spans are Rust-only instrumentation.
- Rewatch in-process scheduling is Rust-specific and should preserve artifact
  semantics without requiring process boundaries.

Known algorithmic risk areas:

- Lazy module components are not a simple mechanical port of OCaml `env.ml`.
  Keep moving them toward the OCaml `components_of_module_maker` and lookup API
  boundaries.
- Force/no-force behavior must follow OCaml APIs, not output-mode flags or
  post-hoc path rewrites.
- Alias identity should come from declarations, substitutions, and component
  lookup, not string spelling equivalence.
- Signature-content scans should not decide forcing if OCaml would force through
  lookup/normalization.
- Stdlib/Pervasives special cases should be justified by the implicit-open path
  in `res_compmisc.ml` and `env.ml`, not by a single observed parity fixture.
- Serializer-level normalization is not a valid typedtree parity fix. The
  serializer should faithfully emit the typechecker result.

When a Rust implementation does something different from OCaml:

1. Decide whether the difference is representation-only or semantic.
2. If representation-only, document the invariant that keeps behavior identical.
3. If semantic, either remove it or document the exact intended ReScript language
   change.
4. Add tests for the behavior that would diverge.

## Performance Instrumentation

The Rust compiler has timing and counter hooks for architecture work.

Important files:

- `src/timing.rs`
- `src/perf_counters.rs`
- `rewatch/src/build/compile.rs`

Useful environment variables:

- `RESCRIPT_PHASE_TIMINGS=1` prints aggregate compiler phase timings.
- `RESCRIPT_MODULE_TIMINGS=1` prints per-module wall time and compiler phase time.
- `RESCRIPT_RUNTIME_TIMINGS=1` times runtime compilation in rewatch.
- `RESCRIPT_COMPILER_COUNTERS=1` enables hot-path counters from
  `perf_counters.rs`.
- `RESCRIPT_SCHEDULER_COUNTERS=1` prints in-process scheduler queue/capacity
  counters.

Useful dump flags:

- `-dtyped-sexp`
- `-dtyped-sexp-locs`
- `-drawlambda`
- `-dlambda-sexp`
- `-dlambda-sexp-locs`

Measurement rules:

- Use debug builds for iteration speed while developing.
- Use release builds for wall-clock performance numbers.
- Keep direct, subprocess, and in-process numbers separate.
- Clear parity caches before authoritative parity baselines.
- Attribute time to parse, typecheck, Lambda, Lambda optimization, codegen, and
  scheduler overhead before choosing an optimization.

## Optimization Map

Good compiler optimizations reduce work at an OCaml-aligned boundary without
changing observable compiler products.

High-impact candidates:

- Lazy module components and signature qualification. Repeated component-table
  construction, path substitution, type freshening, and child module forcing can
  dominate large projects.
- Persistent environment loading. Repeated `.cmi`/`.cmj` reads or repeated
  registry internalization can multiply with dependency fanout.
- Type expression allocation and copying. `Subst.signature`, `instance`, row
  operations, unification, and declaration copying are hot and parity-sensitive.
- Constructor and label lookup. Large signatures should not derive every
  constructor/label table when one lookup needs one bucket.
- RawLambda conversion and matching. Pattern compilation shape affects both
  output and downstream optimization work.
- Lambda optimization. Pass order is fixed, but pass internals can often move
  less data, reuse analyses, or avoid avoidable clones.
- JS IR generation and printing. Generated text must remain byte-identical, but
  name-scope structures, module-path resolution, and printer allocation can be
  optimized.
- Rewatch scheduling. In-process builds benefit when signatures are published
  early, JS waits only on backend-visible dependencies, and ready work follows
  the critical path.

Optimization workflow:

1. Pick one stage and one metric.
2. Add or reuse a counter that proves the work is hot.
3. Read the OCaml reference implementation for the same stage.
4. Simplify Rust toward the OCaml boundary rather than adding a compatibility
   layer.
5. Check typedtree parity, Lambda parity when relevant, JS output parity, and
   error-output parity before committing source changes.
6. For docs-only README changes, parity is not required.

## Workflow For Architecture Changes

Use this process for compiler behavior changes:

1. Identify the compiler stage and the matching OCaml reference files.
2. Read the OCaml implementation enough to know the control flow, mutation
   points, lazy force points, and traversal order.
3. Inspect the Rust implementation and decide whether the difference is
   representation-only or semantic.
4. Implement the OCaml-aligned behavior in the Rust stage that corresponds to
   the reference stage.
5. Avoid serializer normalization, output-mode branches, path-spelling
   equivalence, and fixture-specific logic.
6. Add or update focused tests for the behavior.
7. Run focused parity first, then full non-tella parity, then tella parity when
   the change affects typedtree/Lambda/output behavior.
8. For performance work, run release measurements after correctness is stable.

Use this process for documentation changes:

1. Update this README in `compiler-rust/`.
2. Keep root README focused on project-level user/contributor information.
3. No parity run is required for README-only changes.
