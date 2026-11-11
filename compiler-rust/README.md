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
- [OCaml Typechecker Algorithm Map](#ocaml-typechecker-algorithm-map)
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
- [Possible Algorithmic Gaps With OCaml](#possible-algorithmic-gaps-with-ocaml)
- [Performance Improvements Versus OCaml](#performance-improvements-versus-ocaml)
- [Performance Instrumentation](#performance-instrumentation)
- [Optimization Map](#optimization-map)
- [Workflow For Architecture Changes](#workflow-for-architecture-changes)

## Reference Source Map

The OCaml reference is still the primary algorithm spec. When changing Rust
code, read the matching OCaml source first.

| Area | OCaml reference | Rust implementation | Notes |
| --- | --- | --- | --- |
| Main implementation driver | `compiler/core/js_implementation.ml` | `src/driver.rs` | OCaml `implementation` parses, applies external PPX, runs `Ppx_entry`, then `after_parsing_impl`. Rust direct source mode follows the same broad stage order in `compile_source_to_js_with_options`, but intentionally rejects external PPXs. |
| Interface driver | `compiler/core/js_implementation.ml`, `compiler/ml/typemod.ml` | `src/driver.rs` | OCaml interfaces parse as signatures, run signature PPX/config/warnings, typecheck, self-check, force delayed checks, and write `.cmi`/`.cmti`. Rust in-process mode publishes a registry signature; direct Rust helpers currently typecheck/dump but do not write OCaml-compatible interface artifacts. |
| ReScript syntax parser | `compiler/syntax/`, `compiler/ml/parsetree.ml` | `src/parser/*`, `src/parse_arena.rs` | Rust parser uses arena indices instead of OCaml heap records, but output shape and locations must match. |
| Former PPX AST boundary | `compiler/ml/parsetree0.ml`, `ast_mapper_to0.ml`, `ast_mapper_from0.ml`, `binary_ast.ml` | `src/binary_ast/parsetree0.rs`, `mapper_to0.rs`, `mapper_from0.rs`, `writer.rs`, `marshal.rs` | PPX is not supported going forward; `parsetree0` is not frozen and not compared with OCaml. |
| Frontend and PPX rewrites | `compiler/frontend/*`, `compiler/core/cmd_ppx_apply.ml`, `compiler/frontend/ppx_entry.ml`, `compiler/frontend/ast_config.ml` | `src/binary_ast/ppx.rs`, `src/parser/jsx_ppx.rs`, `src/driver.rs`, `rewatch/src/build/parse.rs` | Order is observable through warnings, errors, AST dumps, and generated code. Rust has several mode-specific caveats listed below. |
| Initial environment | `compiler/core/res_compmisc.ml`, `compiler/ml/env.ml` | `src/types/predef.rs`, `src/types/env.rs`, `src/cmi/persistent_env.rs`, `src/driver.rs` | Pervasives/Stdlib loading and implicit opens must preserve OCaml lookup and force order. |
| Persistent environment | `compiler/ml/env.ml`, `compiler/ml/cmi_format.ml`, `compiler/ml/cmi_format.mli`, `compiler/core/js_cmj_format.ml` | `src/cmi/persistent_env.rs`, `src/cmi/cmi_format.rs`, `src/cmi/sig_reader.rs`, `src/cmi/portable_types.rs` | Rust reads OCaml `.cmi`/`.cmj` data and has an in-memory registry mode. Disk writing of `.cmi`/`.cmj` is not currently equivalent to OCaml. |
| Lazy module components | `compiler/ml/env.ml` (`EnvLazy` module), `compiler/ml/subst.ml` | `src/types/env_lazy.rs`, `src/types/env.rs`, `src/types/context.rs` | This is a high-risk parity area. Rust must preserve OCaml API boundaries such as `find_module_descr` versus `find_module`. |
| Core type operations | `compiler/ml/ctype.ml`, `compiler/ml/btype.ml` | `src/types/ctype.rs`, `src/types/btype.rs`, `src/types/type_expr.rs` | Physical sharing created by `instance`, `copy`, `link_type`, `unify`, generalization, and row mutation decides what unifies and how types print; the typed tree's own sharing need not match OCaml. |
| Type declarations and data representation | `compiler/ml/typedecl.ml`, `compiler/ml/datarepr.ml`, `compiler/ml/typetexp.ml` | `src/types/typemod.rs`, `src/types/typecore.rs`, `src/types/decl.rs` | Constructors, labels, records, variants, objects, externals, and type attributes must build equivalent declarations. |
| Expression and pattern typing | `compiler/ml/typecore.ml`, `compiler/ml/typeopt.ml`, `compiler/ml/parmatch.ml` | `src/types/typecore.rs`, `src/raw_lambda/typeopt.rs` | Includes expression inference, pattern typing, labels, application, rows, warnings, and error messages. |
| Module and signature typing | `compiler/ml/typemod.ml`, `compiler/ml/includemod.ml`, `compiler/ml/mtype.ml` | `src/types/typemod.rs`, `src/types/includemod.rs` | Includes structures, signatures, functors, includes, opens, recursive modules, interface inclusion, delayed checks, and signature simplification. |
| Typedtree definitions and dumps | `compiler/ml/typedtree.ml`, `compiler/ml/sexp_typedtree.ml` | `src/types/typedtree.rs`, `src/types/sexp_typedtree.rs` | Debugging dumps only; they are not compared with OCaml's. |
| Typedtree to first Lambda representation | `compiler/ml/translcore.ml`, `compiler/ml/translmod.ml`, `compiler/ml/matching.ml`, `compiler/ml/typeopt.ml`, `compiler/ml/lambda.ml` | `src/raw_lambda/convert.rs`, `src/raw_lambda/matching.rs`, `src/raw_lambda/typeopt.rs`, `src/raw_lambda/mod.rs` | Rust `RawLambda` is the counterpart of OCaml `Lambda.lambda`. |
| First Lambda to JS-backend Lambda, then optimization | `compiler/core/lam_convert.ml`, `compiler/core/lam.ml`, `compiler/core/lam_compile_main.ml`, `compiler/core/lam_pass_*.ml` | `src/raw_lambda/lower.rs`, `src/lambda/mod.rs`, `src/lambda/lam_compile_main.rs`, `src/lambda/lam_pass_*.rs` | OCaml also has this second Lambda-level representation: `Lam_convert.convert` converts `Lambda.lambda` into backend `Lam.t`. Pass order is fixed by the OCaml backend. |
| JavaScript backend | `compiler/core/lam_compile.ml`, `compiler/core/js_*.ml`, `compiler/core/j.ml`, `compiler/core/js_cmj_format.ml` | `src/lambda/lam_compile.rs`, `src/lambda/js_*`, `src/js_ir/*`, `src/cmi/persistent_env.rs` | Includes JS IR, externals, primitives, module paths, exports, side effects, printer behavior, and `.cmj` metadata reads. |
| Build system integration | OCaml `bsb`/legacy build behavior plus compiler artifact contracts | `rewatch/src/build/*` | Rewatch is Rust-specific, but artifact semantics and compiler invocation semantics must stay compatible. |

## End-To-End Pipeline

At the highest level, a `.res` implementation follows this pipeline:

```text
rescript.json + source graph
  -> rewatch package/source discovery
  -> parse .res/.resi into Parsetree nodes stored in ParseArena
  -> dependency extraction and optional binary .ast/.iast writing
  -> built-in frontend rewrites and spice derives
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

The interface path is the same idea, but it parses a signature and typechecks it
as a module type instead of producing Lambda/JS. OCaml's file-backed interface
path then runs a self-inclusion check, forces delayed checks, writes `.cmi`,
writes `.cmti`, and can run GenType. Rust's in-process path publishes the
signature into `ModuleRegistry`; Rust's direct interface helper currently
typechecks and dumps typed output but does not write OCaml-compatible `.cmi` or
`.cmti` files.

## Observable Invariants

These details are not implementation trivia; tests and users can observe them.

Only the generated JavaScript (with gentype output and source maps), the
ReScript the parser and printer emit, and the type system's results (accepted
programs, inferred and printed types, errors and warnings) are compared with
OCaml. Intermediate representations (parse tree, parsetree0, `.ast` files,
typed tree, Lambda) and identifier stamps are not; they may differ freely.

- Identifier stamps matter only where they reach that output, for example the
  names and order of generated JS bindings.
- Lazy environment force order matters only where it changes types, paths or
  diagnostics.
- Path spelling is observable. `Pident`, `Pdot`, `Papply`, flattened module names,
  generated nested module names, and alias paths must be produced by the same
  declaration/substitution flow as OCaml.
- Location and position accounting is user visible. Parser errors, type errors,
  warning ranges, AST dumps, and source maps must agree with the reference.
- Warning order is observable. PPX warnings, parse diagnostics, type warnings,
  delayed unused checks, warning-as-error, and fatal errors must be emitted in the
  same order and with the same failure behavior as the OCaml compiler.
- Binary artifacts are compatibility boundaries. `.ast`, `.iast`, `.cmi`, and
  `.cmj`-like data should carry the same logical information in subprocess and
  in-process modes; current in-process backend metadata still has narrower CMJ
  coverage for closed Lambda exports.
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
- JS metadata is published after JavaScript lowering has inspected the
  simplified module. In-process registry metadata currently covers purity,
  export constants, and export arities; disk `.cmj` reading also supports
  closed Lambda exports for cross-module inlining.
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
  intermediate representations for debugging and skip the work after the
  dumped stage.
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
- `src/parser/utf8.rs`
- `src/source_text.rs`
- `src/location.rs`
- `src/parse_arena.rs`

Algorithm:

1. File-based entrypoints read source bytes through
   `source_text::latin1_bytes_to_string`: ASCII inputs become UTF-8 strings
   directly, and non-ASCII inputs map each original byte to one `char` in
   `0..=255`.
2. `Parser::new` creates parser state for a filename and source string.
3. The scanner reads bytes from that string and emits tokens with source
   locations.
4. ASCII paths are fast. For raw `&str` callers, non-ASCII text can go through
   the UTF-8 decoder; for normal file input, the Latin-1 byte-string model is
   used to match OCaml's byte-oriented source strings.
5. The scanner tracks byte offsets, character positions, UTF-16 code-unit
   offsets, line starts, and line numbers.
6. Comments and doc comments are captured instead of discarded.
7. The parser maintains lookahead, error-recovery state, region state, and the
   current `ParseArena`.
8. Diagnostics are accumulated with precise locations and later rendered by the
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
- The Rust scanner has a UTF-8 slow path, but OCaml parity for files relies on
  the Latin-1 byte-string conversion before scanning. Position bugs often come
  from accidentally reasoning about Unicode scalar positions when the reference
  path is byte-oriented.

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
2. Map the current parsetree to `parsetree0` when writing the PPX wire
   format.
3. Serialize the dependency section and OCaml marshal-compatible AST payload.
4. In subprocess mode, rewatch or the compiler can write `.ast`/`.iast` files
   for later compiler invocation.
5. Tools and conversion tests can read and write the frozen v0 payload.
6. A complete PPX round trip maps `parsetree0` back into the current parsetree
   after PPX. OCaml does this before later frontend processing; current Rust
   direct paths do not yet consume the transformed tree.

Dependency extraction algorithm:

- The dependency walker records module references that can affect build order.
- It distinguishes references in implementation and interface files.
- It must agree with the module dependency semantics used by the legacy build
  system, including namespace and generated module-name behavior.

OCaml reference alignment:

- External PPXs are no longer supported. `parsetree0` is not a frozen boundary
  and its bytes are not compared with OCaml. The conversion modules remain
  available for tooling, but built-in spice derives operate directly on the
  current AST without a version-0 round trip.

Rust-specific diversion:

- In in-process mode, rewatch can skip writing `.ast`/`.iast` files and keep
  `StoredAst` values in memory. This removes serialization/process overhead but
  does not change the logical stage boundary.
- External PPX execution is no longer supported. Package configuration rejects
  every non-spice `ppx-flags` entry, even when its source marker is absent.
- Spice derives run directly on the current AST, without a version-0 round trip.
  `src/binary_ast/derive.rs` is the single seam between frontend rewrites and
  the removable built-in spice implementation.

## Stage 5: Frontend Rewrites, Built-In PPX, And File Directives

The frontend rewrite layer runs between parsing and typechecking. In OCaml it is
spread across `compiler/frontend/`, `compiler/syntax/`, `Cmd_ppx_apply`, and
`Ppx_entry`. In Rust it is called from `src/driver.rs`,
`src/binary_ast/ppx.rs`, and `src/parser/jsx_ppx.rs`.

Direct source order in Rust:

1. Parse the structure.
2. Run external structure PPX commands and validate their output magic. Current
   Rust direct compilation does not consume the transformed AST yet.
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
- `Ppx_entry.rewrite_implementation` and `rewrite_signature` run invariant
  warning collection, `Ast_config.process_*`, JSX, and then the built-in mapper
  unless `-bs-no-builtin-ppx` is set.
- `after_parsing_impl` then runs `Ast_config.process_str`, optional `no_export`,
  binary AST writing, `as_pp`, `syntax_only`, environment initialization, and
  typechecking.
- `after_parsing_sig` runs `Ast_config.process_sig`, optional binary AST
  writing, `as_pp`, `syntax_only`, signature typechecking, signature
  self-inclusion, delayed checks, fatal-warning checks, `.cmi` save, `.cmti`
  save, and GenType.

Mode-specific caveats:

- Rust direct source mode collects file config and warning attributes before
  JSX and built-in rewriting, then runs `expand_extensions` before the full
  built-in structure rewrite. This should stay aligned with OCaml warning and
  rewrite observability, but it is not a literal function-by-function clone of
  `Ppx_entry`.

Why order matters:

- Warning attributes must be collected before generated warnings are emitted.
- File directives must be preserved until final JS printing.
- JSX and let-unwrap rewrites must happen before general built-in rewrites.
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
- `TypeContext` keeps side caches for qualified component views, flattened alias
  component paths, forced normalized paths, and forced type-path comparisons.
  The qualified-component cache matches OCaml lazy sharing intent; the alias and
  forced-path caches are higher-risk and should only memoize effects already
  produced by the OCaml-aligned lookup path.
- `PersistentEnv` and `env_lazy` contain flattened alias prefix rewrites for
  names such as `Stdlib_JSON` versus `Stdlib.JSON`. Treat these as current Rust
  compatibility machinery to shrink, not as a substitute for declaration,
  substitution, and component lookup identity.
- Explicit `Stdlib`/`Pervasives` handling remains in several Rust typing and
  persistent-environment paths. Each instance must be justified by OCaml's
  `Res_compmisc.initial_env`, implicit-open setup, and `Env` lookup behavior.

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

Rust aligns with the typechecking and ordering parts of this behavior in
`src/driver.rs`:

- Typecheck the structure through `typemod::type_structure`.
- Apply moregen/interface constraints before typedtree sexp output when a `.resi`
  exists.
- Run inclusion checks.
- If no `.resi` exists, simplify the inferred signature, check non-generalized
  schemes, normalize signature types, and prepare the signature for the same
  stamp/shape effects as saving before Lambda conversion.
- If a `.resi` exists, keep the declared interface as the target signature and
  do not replace it with the implementation signature for export coercion.
- The main in-process compile path also publishes the inferred signature before
  RawLambda conversion when there is no interface.
- Rust direct interface helpers and `typecheck_preprocessed_signature_in_process`
  do not currently run the whole OCaml `after_parsing_sig` artifact contract in
  every mode: direct helpers typecheck and dump, while in-process helpers publish
  an in-memory signature instead of writing `.cmi`/`.cmti`.

## OCaml Typechecker Algorithm Map

This section is a source-oriented map of the OCaml typechecker files that define
the behavior Rust must match. It is intentionally more detailed than the stage
overview above. When optimizing or fixing parity in Rust, use this as the
checklist for control flow, mutation points, environment forcing, and type-node
sharing.

Core OCaml files covered:

- `compiler/ml/btype.ml`: low-level mutable type-node operations, traversal,
  marks, snapshots, backtracking, row helpers, and copy helpers.
- `compiler/ml/ctype.ml`: levels, instantiation, abbreviation expansion,
  unification, subtyping, generalization, equality, non-dependency, and type
  normalization.
- `compiler/ml/typetexp.ml`: translation of parsed core type syntax into
  `Types.type_expr`, plus lookup/error narrowing for types, values,
  constructors, labels, modules, and module types.
- `compiler/ml/typedecl.ml`: type declaration, extension, exception, value
  declaration, `with`-constraint, variance, immediacy, and recursion checking.
- `compiler/ml/typecore.ml`: expression typing, pattern typing, application,
  records, variants, let-binding generalization, match typing, delayed checks,
  and core-language diagnostics.
- `compiler/ml/typemod.ml`: module type translation, signature translation,
  module expression typing, structure typing, recursive module checking,
  implementation/interface checking, and save-time signature normalization.
- `compiler/ml/includemod.ml`: module/signature inclusion and coercion
  construction.
- `compiler/ml/mtype.ml`: module-type scraping, strengthening, non-dependency,
  enrichment, alias removal, and nongen lowering.

### High-Level Call Graph

The implementation-file path is:

```text
Typemod.type_implementation_more
  -> Typemod.type_structure
     -> Typecore.type_binding / type_expression
     -> Typedecl.transl_type_decl / transl_type_extension / transl_exception
     -> Typemod.type_module / transl_modtype / transl_signature
  -> Typemod.simplify_signature
  -> Includemod.compunit
  -> Typemod.check_nongen_schemes
  -> Typemod.normalize_signature
  -> Delayed_checks.force_delayed_checks
  -> Env.save_signature + Cmt_format.save_cmt, when files are written
```

The core expression path is:

```text
Typecore.type_expression
  -> Typetexp.reset_type_variables
  -> Ctype.begin_def
  -> Typecore.type_exp
     -> Typecore.type_expect
        -> Typecore.type_expect_
           -> Typetexp lookup/translation helpers
           -> Ctype.instance / unify / subtype / filter_arrow / filter_method
           -> Typecore.type_pat / type_cases / type_let / type_application
  -> Ctype.end_def
  -> Ctype.generalize_expansive, when expression is expansive
  -> Ctype.generalize
```

The top-level binding path is:

```text
Typecore.type_binding
  -> Typetexp.reset_type_variables
  -> Typecore.type_let
     -> Ctype.begin_def
     -> Typecore.type_pattern_list
     -> recursive approximation with Typecore.type_approx, when recursive
     -> delayed pattern forces
     -> expression typing under env or recursive env
     -> partial-match checks for let patterns
     -> Ctype.end_def
     -> expansive-value restriction
     -> Ctype.generalize over pattern types
```

The signature path is:

```text
Typemod.transl_signature
  -> Env.in_signature true
  -> source-order recursive transl_sig loop
     -> Typedecl.transl_value_decl
     -> Typedecl.transl_type_decl
     -> Typedecl.transl_type_extension / transl_exception
     -> Typemod.transl_modtype / transl_recmodule_modtypes
     -> Typemod.type_open
     -> Env.add_signature for includes
  -> Typemod.simplify_signature
```

The module expression path is:

```text
Typemod.type_module
  -> Pmod_ident: lookup_module, find_module, strengthen or alias coercion
  -> Pmod_structure: type_structure, simplify_signature, possible implicit coercion
  -> Pmod_functor: transl_modtype, Env.enter_module, type_module body
  -> Pmod_apply: type argument before functor, scrape_alias, Includemod.modtypes,
     substitute result when argument is a path, otherwise nondep_supertype
  -> Pmod_constraint: type module, transl_modtype, Includemod.modtypes
  -> Pmod_unpack: Typecore.type_exp, package type extraction, package constraints
```

### `btype.ml`: Mutable Type-Node Substrate

`btype.ml` is not just utility code. It defines the mutable graph discipline
the type checker's results depend on.

- Every type node has `desc`, `level`, and `id`. `id` is allocated by `newty2`
  from a mutable counter. Rust need not reproduce OCaml's ids or sharing; only
  what they decide (unification, generalization, printed types) must match.
- `generic_level`, `lowest_level`, and `pivot_level` are special marker levels.
  `pivot_level - level` is used to mark nodes during traversals without
  side tables. Rust can use side tables internally, but the observable order and
  mutation effects must match the traversal.
- `repr` follows `Tlink` chains and also skips object fields whose kind has
  become `Fabsent`. Path compression is logged through the backtracking trail.
  A Rust shortcut that follows only `Tlink` misses an OCaml representative case.
- Row helpers such as `row_field_repr`, `row_repr`, `row_field`, `row_more`,
  `row_fixed`, and `static_row` normalize chained rows and row fields lazily.
  They are used by typing, unification, subtyping, printing, and declaration
  checks, so row order and row sharing cannot be treated as presentation detail.
- `iter_type_expr`, `iter_row`, `iter_type_expr_kind`, and the `type_iterators`
  record define the canonical structural traversal over types, signatures, and
  module types. `Typemod`, `Mtype`, `Ctype`, and `Typedecl` reuse these
  traversals for marking, variance, non-dependency, normalization, and alias
  analysis.
- Backtracking is implemented by logging changes to type descriptions,
  compressed links, levels, row fields, field kinds, commutability cells,
  univar cells, and type sets. `snapshot`, `backtrack`, and `undo_compress`
  matter in pattern backtracking, coercion fallback, subtyping, and equality.
- `copy_type_desc` is the base copy function. It deliberately allocates fresh
  abbreviation refs for `Tconstr`, preserves `Tunivar` names, shares field kind
  variables in specific cases, and refuses to copy raw `Tvariant` there because
  row copying needs special handling.
- Mark/unmark functions mutate levels in place. A failed pass must unmark or
  backtrack exactly where OCaml does, otherwise later traversals see different
  levels and produce different sharing.

Rust parity implications:

- Any arena optimization must keep type-node identity stable and must not turn
  OCaml's mutating mark/unmark/backtrack pattern into structural rebuilding.
- Row helpers are algorithmic operations, not serializer conveniences.

### `ctype.ml`: Levels, Instantiation, Expansion, And Unification

`ctype.ml` is the central type engine.

Level state:

- `current_level`, `nongen_level`, `global_level`, and `saved_level` are mutable
  global state in OCaml. Rust stores equivalent state in context objects, but
  the nesting behavior must match.
- `init_def` sets both `current_level` and `nongen_level`.
- `begin_def` saves both levels, increments `current_level`, and sets
  `nongen_level` to the new current level.
- `begin_class_def` increments only the current level.
- `raise_nongen_level` saves levels and raises `nongen_level`.
- `end_def` restores the saved pair.
- `reset_global_level`, `increase_global_level`, and `restore_global_level` are
  used by `Typetexp` to scope explicit type variables and package translation.

Creation and representation:

- `newty`, `newvar`, `newvar2`, `new_global_var`, `newobj`, and `newconstr`
  allocate nodes at the active level. A call moved across `begin_def` or
  `end_def` changes later generalization.
- `simple_abbrevs` memoizes parameterless abbreviation expansions until the next
  generalization. This is part of sharing, not just caching.
- `proper_abbrevs` avoids sharing simple abbreviations when tracing GADT
  instances, when the constructor has parameters, or when the path is an object
  type.

Generalization and level lowering:

- `generalize` walks nodes whose level is above `current_level`, marks them
  generic, traverses abbreviation caches for constructors, and resets
  `simple_abbrevs`.
- `generalize_structure` lowers variables to a chosen level but generalizes
  structure above `current_level`; it clears abbreviation caches for most
  constructors.
- `update_level` enforces the invariant that constructor levels cannot escape
  the binding time of their paths. It first tries without expansion, backtracks
  on failure, then retries while expanding abbreviations.
- `generalize_expansive` implements the relaxed value restriction. It follows
  variance: covariant/weak branches can be generalized structurally, while
  contravariant branches are made non-generalizable.
- `limited_generalize` builds an inverse graph of type dependencies and
  generalizes only the reachable parents from selected roots.

Instantiation:

- `instance`, `instance_def`, `generic_instance`, and `instance_list` all go
  through `copy` plus `cleanup_types`.
- `copy` temporarily rewrites generic nodes to `Tsubst` stubs, copies through
  the graph, then restores the original descriptions. This is why OCaml can
  preserve recursive sharing while still allocating fresh instances.
- Non-generic nodes are shared in ordinary instantiation. With partial
  instantiation, non-generic nodes may become fresh variables or keep their
  level depending on the `partial` flag and free-univar analysis.
- Variant row copying is special: OCaml encodes the copied row variable and
  copied variant in a temporary `Tsubst (Ttuple [more'; t])` so later visits can
  reuse the same copied row.
- `instance_constructor` creates local abstract types for existentials in GADT
  patterns by adding local types to the environment before linking copied
  existential variables.
- `instance_label` treats polymorphic label arguments with `instance_poly`.

Abbreviation expansion:

- Expansion is environment-sensitive. `check_abbrev_env` flushes expansion
  caches when the environment object changes.
- `expand_abbrev_gen` checks the constructor's expansion cache, then calls
  `Env.find_type_expansion` or `Env.find_type_expansion_opt`, substitutes
  parameters with `subst`, records GADT ambiguity chains when needed, and may
  normalize paths if no expansion is found.
- `expand_head`, `expand_head_opt`, `try_expand_once`, and `full_expand` differ
  in privacy and failure behavior. Optimizations that use private manifest
  information must go through the `_opt` path, not ordinary typing expansion.
- Expansion can force environment components, allocate type nodes, rewrite
  abbreviation caches, and link types. It is not a pure query.

Unification:

- `unify` is intentionally staged:
  1. Fast cases handle identical nodes, variables, univars, and some equal
     zero-argument constructors.
  2. `unify2` expands both heads, lowers levels, updates GADT ambiguity chains,
     and chooses which side controls the trace direction.
  3. `unify3` performs structural unification and rolls back `t1'` on failure.
- `unify1_var` performs occurs check, free-univar check, links the variable,
  then lowers levels in the linked type. If lowering fails, it restores the
  original variable description.
- Expression mode links representatives. Pattern mode records equalities and
  can generate local GADT equations instead of eagerly linking everything.
- GADT unification uses `unify_gadt`, `newtype_level`, `reify`,
  `add_gadt_equation`, local constraints in `Env`, and an equality set.
- Object field unification flattens and sorts fields, associates matching
  labels, creates a shared row variable with `make_rowvar`, then unifies missing
  and present fields while restoring row descriptions on error.
- Variant row unification merges sorted row fields, computes closed/fixed/name
  state, updates row-more variables through `set_more`, then unifies each
  matching row field. `Reither` cases can force unification, split shared row
  refs, or keep passive variants for exhaustiveness checking.
- Package unification builds missing package type constraints with
  `complete_type_list`, compares normalized package paths, and delegates module
  package subtyping back to `Typemod` through `Ctype.package_subtype`.

Subtyping, equality, and non-dependency:

- `moregeneral`, `matches`, and `equal` are implemented by instantiating,
  rigidifying, temporarily unifying/equating, then backtracking. They are not
  structural equality checks.
- `subtype` first accumulates constraints in a stable traversal order, then
  returns a thunk that enforces them later. This is why coercion typing can bind
  variables before final subtype constraints are applied.
- ReScript-specific subtype cases for variant/record coercion and primitive
  coercion are implemented here, after ordinary abbreviation/private expansion
  cases.
- `nondep_type`, `nondep_type_decl`, and `nondep_extension_constructor` copy
  types while removing references to a module identifier, expanding
  abbreviations when necessary and preserving row-variable sharing through a
  separate variant cache.
- `normalize_type` rewrites row names, sorts row fields, compacts equivalent
  `Reither` alternatives, normalizes object names, and rebuilds object field
  chains. It runs before saving/printing signatures and therefore affects
  interface artifacts and parity.

Rust parity implications:

- Do not move a `newvar`, `instance`, `generalize`, `expand_head`, or `unify`
  call across a level boundary unless OCaml does.
- Do not replace `moregeneral`, `matches`, `equal`, or subtype checks with
  content comparisons; they rely on mutation plus backtracking.
- Expansion and lookup are linked. If Rust avoids a force in `Ctype`, it may be
  moving both type allocation and environment side effects.

### `typetexp.ml`: Type Syntax Translation

`typetexp.ml` translates parsed core types and performs narrowed lookup errors.

Lookup behavior:

- `find_component` wraps `Env.lookup_*` functions and calls
  `narrow_unbound_lid_error` when lookup fails.
- `narrow_unbound_lid_error` recursively checks module prefixes, distinguishes
  unbound modules from inaccessible functor applications, reports attempts to
  access functors as structures, and reports aliases whose target cannot be
  scraped.
- `find_type`, `find_value`, `find_constructor`, `find_all_constructors`,
  `find_all_labels`, `lookup_module`, `find_module`, and `find_modtype` each
  call the corresponding `Env` API. Their force/load behavior differs.

Variable state:

- `type_variables` stores explicit type parameters already in scope.
- `univars` stores explicitly quantified universal variables.
- `pre_univars` stores variables created before final universal checking.
- `used_variables` stores named type variables encountered in a type expression
  before they are globalized.
- `reset_type_variables` resets `Ctype` global level state and the reified
  variable counter.
- `narrow`/`widen` save and restore the `Typetexp` type-variable context around
  module type translation inside package types.

Translation policy:

- `Fixed`: unbound `_` is rejected and unbound variables must be already known.
- `Extensible`: ordinary type syntax can create fresh variables.
- `Univars`: syntax creates pre-universal variables for later quantification.

Core translation rules:

- `Ptyp_any` creates a fresh variable according to policy.
- `Ptyp_var` reuses a univar, reuses a previously used variable, or creates a
  fresh variable and records it in `used_variables`. Names beginning with `_`
  are rejected for explicit variables.
- `Ptyp_arrow` translates the argument and return, wraps optional arguments in
  `option`, then creates `Tarrow` with the source arity.
- `Ptyp_constr` resolves the type path, handles the one-`_` shorthand for
  multi-parameter constructors, checks arity, translates arguments, instantiates
  declaration parameters, unifies them with arguments, builds `Tconstr`, and
  enforces constraints.
- `Ptyp_alias` unifies the alias variable with the inner type and may write the
  alias name back into a `Tvar` or `Tunivar` proxy.
- `Ptyp_variant` accumulates fields in a hash table, checks duplicate tags by
  type equivalence/unification, expands inherited variant types, checks present
  tags, creates a row, and chooses `Tnil`, a fresh variable, or a pre-univar for
  `row_more`.
- `Ptyp_object` uses `transl_fields`, rejects opened inherited objects where
  required, and builds a `Tobject`.
- `Ptyp_poly` opens a definition level, creates named univars, translates the
  body, generalizes it, converts occurring generic variables to `Tunivar`, then
  wraps the body in `Tpoly`.
- `Ptyp_package` builds a fake package module type with `with type`
  constraints, translates it via `Typemod`, restores the variable context, then
  produces `Tpackage`.

Finalization:

- `make_fixed_univars` marks variant rows fixed when row variables are
  universal.
- `globalize_used_variables` creates global variables for used type variables,
  unifies them with existing parameters when possible, and returns a delayed
  force function for later consistency checks.
- `transl_simple_type` translates and immediately globalizes variables.
- `transl_simple_type_delayed` returns both the typed core type and the delayed
  globalize function.
- `transl_type_scheme` resets variables, opens a definition, translates,
  closes the definition, and generalizes the result.

Rust parity implications:

- Type-variable tables and global-level state are part of the algorithm.
- Package type translation crosses into module-type translation and back.
- Delayed type-variable globalization is observable because forcing it can
  raise errors after other typing work has occurred.

### `typedecl.ml`: Declarations, Recursion, Variance, And Data Shape

`typedecl.ml` translates source declarations into `Types.type_declaration`,
constructors, labels, extensions, exceptions, and value declarations.

Declaration entry:

- `enter_type` pre-enters recursive type declarations as abstract stubs. For
  nonrecursive declarations it still pre-enters row helper types and rejects
  GADT constructor syntax.
- `update_type` later unifies recursive stubs with their final manifest.
- Fixed private row types create an extra `#row` type, and `set_fixed_row`
  rewrites the row variable to a constructor for that row type.

`transl_declaration` order:

1. Validate declaration attributes such as `@notUndefined`, `@boxed`, and
   `@unboxed`.
2. Reset type variables and open a definition level.
3. Translate type parameters with duplicate-parameter detection.
4. Translate explicit constraints.
5. Determine unboxed/untagged status and reject invalid unboxed shapes.
6. Translate the declaration kind:
   - abstract type,
   - variant constructors,
   - record labels,
   - open type.
7. ReScript additions such as variant spreads, record type spreads, optional
   inline record fields, object-spread fallback, `@tag`, untagged variants, and
   inline-record metadata are handled here before the final `Types` declaration
   is built.
8. Translate the manifest with fixed-row awareness.
9. Build the provisional `type_declaration`.
10. Unify explicit constraints.
11. Close the definition level.
12. Set fixed row variables if needed.
13. Check cyclic abbreviations.
14. Return a typedtree `type_declaration`.

`transl_type_decl` group order:

1. Add synthetic fixed-row helper declarations.
2. Expand ReScript variant spreads, or report variant-spread errors.
3. Allocate all identifiers.
4. Initialize the Ctype definition level to `Ident.current_time`.
5. Pre-enter declarations into a temporary environment.
6. Translate all declarations under the temporary environment.
7. Attach inline-record metadata to declarations.
8. Check duplicate constructor/label names and warning behavior.
9. Build the final environment from provisional declarations.
10. For recursive declarations, update stubs against the final environment.
11. End the definition level and generalize every declaration.
12. Check well-founded manifests and declarations.
13. Check regular recursive abbreviation use.
14. Check closed type variables.
15. Run delayed untagged-variant well-formedness checks.
16. Check constraints using source locations from the original declaration.
17. Force private recursive row aliases through the type name when needed.
18. Compute variance and immediacy to a fixpoint.
19. Check re-export/coherence against manifest record/variant definitions.
20. Return typed declarations and the final environment.

Variance and immediacy:

- `compute_variance` traverses type bodies with `Btype` iterators and respects
  constructor variance from the environment.
- GADT constructors are handled with `compute_variance_gadt`; anonymous
  varying parameters can be rejected.
- `compute_properties_fixpoint` repeatedly adds candidate variances and
  immediacy flags to a temporary environment until both stabilize, then performs
  final required-variance checks.
- `compute_immediacy` looks through unboxed single-field records/variants and
  manifest types using `Ctype.maybe_pointer_type`.

Extensions, exceptions, and values:

- `transl_type_extension` resolves the extended type, checks it is open and not
  illegally private, translates extension parameters, unifies them with the
  original declaration parameters, translates constructors, generalizes, checks
  closed variables, checks variance, and adds extensions to the environment.
- `transl_exception` is the same constructor translation specialized to
  `Predef.path_exn`.
- Rebound extension constructors instantiate the original constructor, check
  result type compatibility, preserve inlined-record payloads, and reject
  privacy escapes.
- `transl_value_decl` translates a type scheme, accepts plain values only in
  signatures, parses primitives/externals in structures, rejects null-arity
  externals, and enters the value with the correct unused warning callback.
- `transl_with_constraint` is a constrained subset of type declaration
  translation for module type `with` constraints.

Rust parity implications:

- Type declaration translation is a group algorithm, not independent per
  declaration. Temporary env, final env, stub update, and fixpoint ordering all
  affect sharing and errors.
- ReScript-specific declaration features should still be placed at the same
  conceptual points: before declaration construction, before final env, or after
  final env depending on which OCaml check they interact with.
- Variance and immediacy are fixpoint properties. One-pass shortcuts are likely
  wrong for recursive groups.

### `typecore.ml`: Pattern Typing

Pattern typing uses mutable global side state in OCaml:

- `pattern_variables` stores value bindings discovered while typing a pattern.
- `pattern_force` stores delayed type-variable force functions from annotated
  patterns.
- `pattern_scope` controls annotation recording.
- `allow_modules` gates unpack patterns.
- `module_variables` stores unpacked module bindings.
- `reset_pattern` clears all of this before each pattern group.

Backtracking and modes:

- `save_state` captures a `Btype` snapshot, `Ctype` levels, and the current
  environment. `set_state` restores all three.
- `type_pat_mode` controls or-pattern behavior:
  - `Normal`,
  - `Splitting_or`,
  - `Inside_or`,
  - `Split_or`.
- `Need_backtrack` tells pattern typing to retry an or-pattern branch under
  Parmatch-generated constructor/label information.
- Pattern typing can update the environment through local GADT constraints, so
  the environment is passed as `Env.t ref`.

Core pattern flow:

- `type_pat` applies attribute warning scope, expands variant-spread patterns
  when necessary, then delegates to `type_pat_aux`.
- Wildcard patterns may be exploded by `Parmatch.ppat_of_type` for GADT
  exhaustiveness checking.
- Variable patterns call `enter_variable`; duplicate names are rejected before
  the variable reaches the environment.
- Explicit polymorphic variable constraints translate with
  `Typetexp.transl_simple_type_delayed`, unify with the expected type, delay the
  force, instantiate the poly body, and generalize the variable type.
- Alias patterns type the inner pattern first, then build the alias type with
  `build_as_type`, generalize it, and bind the alias variable.
- Constructor patterns resolve candidates, disambiguate through expected type,
  mark usage, reject unqualified GADT patterns where needed, instantiate
  constructor arguments and result, perform ordinary or GADT unification, check
  inlined-record escape rules, then type each subpattern.
- Polymorphic variant patterns create a row with `Reither`, unify it with the
  expected type, and type the payload under the payload type.
- Record patterns choose a record path from the expected type when possible,
  disambiguate labels, sort by label position, instantiate labels, type
  subpatterns, check polymorphic labels, check duplicate/missing labels, and
  finally unify the record type with the expected type.
- Or-patterns first try typing both sides without splitting; they sort and
  unify bound variables by name, alpha-rename the second side, and fall back to
  split mode under Parmatch when necessary.
- Open patterns type under the opened environment, then copy local additions
  back to the outer environment.
- Exception patterns are only accepted at the top match-case split point, not
  below arbitrary pattern positions.

Post-pattern functions:

- `type_pattern` resets pattern state, types one pattern with existentials
  allowed, adds pattern variables to the environment, and returns delayed force
  functions plus unpacked modules.
- `type_pattern_list` types parallel binding patterns against preallocated
  expected types and only then adds variables to the environment.
- `partial_pred`, `check_partial`, and `check_unused` call back into pattern
  typing under snapshots and passive variants for exhaustiveness/redundancy.

Rust parity implications:

- Do not add pattern variables to the environment as soon as a subpattern is
  seen if OCaml waits until the whole pattern group is typed.
- Or-pattern backtracking must restore both type graph and Ctype levels.
- GADT local constraints are environment mutations; they must occur at the same
  pattern typing points.

### `typecore.ml`: Expression Typing And Let Generalization

Expression typing centers on `type_expect`.

Expected-type discipline:

- `type_exp` is just `type_expect ... (newvar ())`.
- `type_expect` wraps attribute warning scope and records the typed expression
  in CMT state.
- `type_expect_` constructs expressions and uses `rue` to unify the expression's
  type with an instance of the expected type after recording the expression
  type. This "record before final unification" behavior matters for typedtree
  shape and error locations.

Important expression rules:

- Identifiers call `Typetexp.find_value`, check deprecation, instantiate the
  value type, and enforce inlined-record escape rules through the `recarg`
  mode.
- Let expressions delegate to `type_let`, then type the body under the new
  environment and run recursive binding checks afterward.
- Functions use `type_function`: optionally unify the expected type with an
  uncurried arity arrow, instantiate and filter an arrow with `filter_arrow`,
  generalize argument/result shapes when local constraints exist, type match
  cases, warn for unerasable optional arguments, and build a single-case
  `Texp_function`.
- Applications type the function before the arguments under one definition
  level, instantiate its type, lower unused arguments, then type arguments under
  a new definition level. `type_application` handles labelled/optional
  arguments, ignored optional arguments, arity, uncurried total application,
  `ignore`, partial application warnings, and label-order diagnostics.
- ReScript unified operators are a deliberate special path before ordinary
  application argument typing.
- Match expressions type and generalize the scrutinee before typing cases, split
  exception cases, and pass call-context information for error text.
- Tuple, array, if/else, sequence, loop, break/continue, for-of, constraint,
  coercion, send, let-module, let-exception, newtype, pack, open, and extension
  forms all thread expected-type information in specific places. Moving the
  expected-type unification earlier or later changes diagnostics and sharing.
- Record expressions infer or select a record type from the expected type,
  disambiguate labels, type fields, perform final record-type unification,
  check duplicates/missing labels, fill omitted optional fields with `None`,
  and build `Texp_record`.
- Record updates type the base expression first, infer record type from expected
  type or base type, disambiguate fields, unify kept fields against the base,
  and warn about useless record-with.
- Field access and setfield go through `type_label_access` and
  `type_label_exp`; dict field access has a ReScript-specific rejection path.
- Constructors are disambiguated from expected type, instantiated, optionally
  separated under local constraints, and only then are payload expressions typed
  with paired original/fresh argument types.

Match cases:

- `type_cases` detects polymorphic variants and GADTs before typing patterns.
- GADT cases copy argument/result types and duplicate environment value types.
- Pattern typing happens for all cases before case bodies are typed.
- The first pass instances the argument type per pattern, collects delayed
  pattern forces, and unifies all pattern types against a fresh `ty_arg'`.
- Polymorphic variant rows are finalized before delayed pattern forces run.
- If propagation is needed, OCaml re-instances and re-unifies pattern types,
  then generalizes pattern nodes after closing the propagation definition level.
- Bodies are typed afterward under each pattern environment. Guards are typed
  before the body.
- Exhaustiveness and unused checks may be delayed when polymorphic variants or
  GADTs are involved.
- Existential escape is checked by unifying the result type with a fresh
  variable after closing the GADT level.

Let bindings:

- `type_let` opens a definition level, preallocates one expected type per
  pattern, types all patterns as a group, and only later adds variables to the
  environment.
- Recursive lets first unify each pattern against `type_approx` of the
  corresponding expression.
- Variant rows in patterns are pressure-finalized before expressions are typed.
- Delayed pattern forces run before expression typing.
- Recursive expression bodies type under the new environment; nonrecursive
  bodies type under the old environment.
- Polymorphic pattern annotations instantiate their universal variables,
  type the expression against the instantiated body, then run `check_univars`.
- Unused-recursive-binding analysis installs value-used callbacks during
  expression typing and replays dependency slots later.
- Let-pattern exhaustiveness checks run before closing the definition level.
- After `end_def`, expansive right-hand sides trigger
  `generalize_expansive` on each pattern type; then every pattern type is
  generalized.
- Recursive lets reject complex patterns after typing, so the error happens
  after the type effects OCaml has already performed.

Nonexpansive/value restriction:

- `is_nonexpansive` is a typedtree predicate, not a parsetree predicate.
- ReScript partial applications are treated as nonexpansive.
- Empty arrays are expansive.
- Records are nonexpansive only when mutable fields are not overridden and the
  extension expression is nonexpansive.
- Exceptions/rebindings/type extensions have module-level nonexpansive rules
  used by module non-generalization checks.

Rust parity implications:

- The order "type patterns, run delayed forces, type expressions, check
  let-pattern partiality, close level, value restriction, generalize" decides
  generalization and warnings; change it only where types and diagnostics stay
  the same.
- Record typing is highly sensitive to expected-type propagation and final
  `instance env ty_expected` calls. Sparse record representations must lower
  to the same JavaScript.
- Application typing has nested definition levels. Collapsing them can change
  level numbers and generalization.

### `typemod.ml`: Modules, Signatures, And Implementation Checking

`typemod.ml` ties the core checker to the module language.

Module types and signatures:

- `type_open_` uses `Typetexp.lookup_module ~load:true`, then
  `Env.open_signature`; if opening fails it finds the module and checks that
  scraping its alias yields a signature.
- `transl_modtype` translates identifiers, aliases, signatures, functors,
  `with` constraints, `module type of`, and extension errors.
- Functor module types enter the parameter module before translating the result
  and call `Ctype.init_def (Ident.current_time ())` before the body.
- `transl_signature` runs under `Env.in_signature true`, checks uniqueness of
  type/module/module-type/extension names, translates items in source order,
  extends the environment after each item, expands includes by adding their
  signatures, and simplifies duplicate value specifications at the end.
- Recursive module signatures are translated by approximation first, then two
  real passes, with recursive type declaration checks after each real pass.

`with` constraints:

- `merge_constraint` descends into a signature by name path.
- Type constraints call `Typedecl.transl_with_constraint`, then
  `Includemod.type_declarations`, then `Typedecl.check_coherence`.
- Module constraints find and strengthen the replacement module.
- Destructive substitutions build a substitution over all real paths removed
  from the signature and check applicative functor uses/aliases that would
  become ill-typed.
- Fixed private row constraints create and thread the synthetic `#row`
  declaration.

Module expressions:

- `Pmod_ident` looks up the module path. In alias mode it avoids loading unless
  required; otherwise aliases can be normalized, expanded through
  `Includemod.expand_module_alias`, and wrapped in an implicit alias coercion.
  Non-alias paths are strengthened when `sttn` asks for strengthening.
- `Pmod_structure` types the nested structure, produces `Mty_signature`, then
  wraps an implicit coercion if signature simplification drops duplicate values.
- `Pmod_functor` translates the optional parameter module type, enters the
  parameter, resets the Ctype definition level to the current identifier time,
  then types the body.
- `Pmod_apply` types the argument first, records its path when possible, types
  the functor with strengthening only if the argument has a path, checks
  inclusion against the parameter module type, and computes the result by
  substitution for path arguments or `Mtype.nondep_supertype` for non-path
  arguments.
- Generative functors can only be applied to `()` and are disallowed in
  applicative functor bodies when the functor result can create types.
- `Pmod_constraint` wraps the module expression with an explicit inclusion
  coercion.
- `Pmod_unpack` types the expression, extracts a package type, rejects
  incomplete packages, and rejects type-creating unpack in functor bodies.

Structures:

- `type_structure` processes items in source order and returns typedtree items,
  signature items, and the final environment.
- Each structure item calls `Ctype.init_def (Ident.current_time ())` before
  typing the item. This is a major stamp/level synchronization point.
- Value items call `Typecore.type_binding`; the signature exposes the final
  `Env.find_value` entries without triggering value-used callbacks.
- Type items call `Typedecl.transl_type_decl` and then `Mtype.enrich_typedecl`
  when an anchor path exists.
- Module bindings type the module expression before entering the declaration,
  enrich anchored module types, lower non-generalizable variables below the
  binding time, then add the module to the environment.
- Recursive modules require explicit module types, translate recursive module
  types first, type all bodies under the recursive environment, then run the
  recursive inclusion unrolling algorithm.
- Includes type the module, extract/simplify the included signature, check
  name uniqueness, and extend the environment with those signature items.
- Items marked `internal.local` are hidden from the produced signature.

Implementation checking:

- `type_implementation_more` clears CMT state, resets delayed checks, types the
  structure, and computes `simple_sg = simplify_signature sg`.
- With an interface, it locates the `.cmi`, reads the declared signature, runs
  `Includemod.compunit initial_env sourcefile sg intf_file dclsig`, forces
  delayed checks, saves CMT, and returns the declared signature.
- Without an interface, it includes the inferred signature against the simplified
  signature, checks non-generalized schemes, normalizes the signature, forces
  delayed checks, saves `.cmi`/`.cmt` when file writing is enabled, and returns
  the simplified signature.
- On error, it saves a partial CMT before re-raising.

Rust parity implications:

- Structure typing is a recursive source-order fold. Parallelizing inside a
  module would need to reproduce all environment, stamp, level, warning, and
  delayed-check effects.
- In-process signature publication must correspond to the no-interface branch
  after simplification/non-generalization/normalization effects that OCaml
  performs before Lambda translation.
- The `.resi` path must keep the declared signature as the export target after
  inclusion; replacing it with the implementation signature changes coercion and
  JS exports.

### `includemod.ml`: Inclusion And Coercion

`includemod.ml` implements module/signature inclusion and produces module
coercions used by later translation.

- Inclusion is directional: `mty1` is the implementation/actual module type and
  `mty2` is the expected/specification module type.
- Value inclusion marks the implementation value as used and delegates to
  `Includecore.value_descriptions` after substituting the expected description.
- Type inclusion marks the implementation type as used and delegates to
  `Includecore.type_declarations`.
- Module-type inclusion handles aliases first, module type identifiers through
  expansion, signatures through `signatures`, and functors contravariantly on
  arguments plus covariantly on results.
- Alias inclusion can return `Tcoerce_alias` when the implementation alias is
  absent but the expected alias is present.
- Signature inclusion builds a component table from the implementation
  signature, matches each expected component by kind/name, builds a substitution
  from expected ids to implementation ids, accumulates missing fields, then
  checks paired components in expected-signature order.
- Runtime positions only count runtime components. Primitive values, types,
  module types, and class types do not increment runtime position; ordinary
  values, type extensions, modules, and classes do.
- Structure coercions are simplified to `Tcoerce_none` only if runtime positions
  form the identity coercion.
- Module declarations are strengthened with `Mtype.strengthen ~aliasable:true`
  before inclusion.
- `compunit` wraps signature inclusion and prepends the implementation/interface
  mismatch context on failure.

Rust parity implications:

- Inclusion is both a check and an effect: it marks values/types/modules as
  used, builds substitutions, and computes runtime coercion positions.
- A name-based export filter is not equivalent to `Includemod.compunit`; it can
  miss coercions, alias coercions, runtime positions, and use-marking effects.

### `mtype.ml`: Strengthening, Non-Dependency, And Alias Removal

`mtype.ml` is small but central for module path shape.

- `scrape` expands module type identifiers through `Env.find_modtype_expansion`
  until it reaches a non-identifier.
- `freshen` is `Subst.modtype Subst.identity`; it copies a module type through
  the standard substitution machinery.
- `strengthen` turns abstract type components into manifest paths rooted at a
  module path and recursively strengthens applicative functor results as
  `Papply (p, Pident param)`.
- `strengthen_sig` tracks runtime position exactly like `EnvLazy` and
  `Includemod`: primitive values/types/module types do not increment; runtime
  values/type extensions/modules do.
- `strengthen_decl` either keeps module aliases, turns aliasable declarations
  into `Mty_alias (Mta_present, p)`, or strengthens the module type.
- `nondep_supertype` removes references to a module id from a module type,
  using covariance/contravariance/strictness to decide when removal can abstract
  components.
- `enrich_typedecl` adds a manifest path to abstract type declarations when the
  original environment has a matching type at that path and arity.
- `type_paths` extracts type paths from module types for recursive-module
  declaration checks.
- `contains_type` detects module types whose evaluation can create fresh types;
  `Typemod` uses it to reject some functor-body operations.
- `remove_aliases` collects argument paths used in applicative functors, keeps
  aliases that are needed for those paths, and scrapes/removes other aliases.
- `lower_nongen` traverses module types and lowers non-generalizable variables
  above a threshold.

Rust parity implications:

- Strengthening and alias removal are the source of many path spelling and
  manifest-type shapes. Do not repair path spelling after the fact if the
  strengthening/nondep step is where OCaml creates it.
- Runtime position accounting must match across `Mtype`, `EnvLazy`, and
  `Includemod`.

### Source-Derived Audit Points

These are the concrete questions to ask before changing Rust typechecker code:

- Is this call inside the same `begin_def`/`end_def` region as OCaml?
- Does Rust allocate a type node where OCaml reuses a non-generic node, or reuse
  one where OCaml's `copy` allocates a `Tsubst`-backed instance?
- Does the call use the same `Env` API as OCaml (`lookup_module ~load:true`,
  `find_module`, `find_module_descr`, `find_type_expansion`,
  `find_type_expansion_opt`, `open_signature`)?
- If the operation can fail and retry, does Rust restore the type graph,
  levels, environment, and delayed side state like OCaml snapshots do?
- Is a row or object helper being replaced by structural normalization?
- Is a module path produced by `Mtype.strengthen`, `Subst`, `Env.normalize_path`,
  `Includemod`, or `Ctype.expand_abbrev`, or is Rust inventing the spelling
  later?
- Does a delayed force from `Typetexp.transl_simple_type_delayed` run at the
  same point?
- Does inclusion mark values/types/modules as used before delayed unused checks
  are forced?
- Does a performance representation expand to the OCaml shape before any
  observable boundary: typedtree dump, RawLambda conversion, Lambda dump, JS
  output, `.cmi`/registry signature, or error text?

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
- Export Lambda values used for cross-module inlining when enabled in
  file-backed `.cmj` mode.

OCaml reference behavior:

- For modules without `.mli`/`.resi`, `Typemod.type_implementation_more` saves
  the inferred `.cmi` before `Translmod.transl_implementation`.
- JavaScript generation later reads `.cmj` metadata for dependency paths,
  side-effect checks, arities, constants, and inlineable Lambda.

Rust behavior:

- Disk/subprocess mode reads file artifacts through `PersistentEnv` and
  `cmi_format`. Full Rust writing of OCaml-compatible `.cmi`/`.cmj` artifacts is
  not implemented in the direct Rust CLI path.
- In-process mode publishes logical signature data and JS metadata through
  `ModuleRegistry`.
- The in-process pre-JS stage can publish signatures early, then the JS finish
  stage publishes purity, export constants, and export arities.
- In-process `PersistentEnv` treats the registry as authoritative and does not
  fall back to disk `.cmj` data. Closed Lambda export metadata for
  cross-module inlining is currently available through disk `.cmj` reads, not
  through the in-process registry.
- Before JS dependency probing, the current unit is hidden again so it is not
  treated as an importable dependency.
- Rust `PersistentEnv` also has a source-fallback path that can typecheck
  dependency source signatures on demand, bounded by a depth limit. That is a
  Rust-specific fallback for missing registry/file artifacts, not the normal
  OCaml driver contract.

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
- File-backed `.cmj` metadata provides side-effect, arity, constant, and
  inlineable Lambda information. In-process metadata currently provides
  side-effect, arity, and constant information only.

Metadata output:

- `cmj_export_constants` records constant exports for later modules.
- `cmj_export_arities` records function arities for later call optimization.
- Cross-module inlineable Lambda may be read from file-backed `.cmj` artifacts
  when cross-module inlining is on; it is not currently published through the
  in-process registry.
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
- Returns JavaScript text or typed/intermediate dumps. It does not write
  OCaml-compatible `.cmi`/`.cmj` artifacts.

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
- Only built-in spice derives are supported; external PPXs are rejected.

The in-process split is a Rust-specific execution-mode diversion. It must
preserve OCaml's logical ordering:

- Save/publish the current unit's inferred signature before Lambda translation
  when there is no interface.
- Keep that signature visible during RawLambda conversion when OCaml would have
  it visible.
- Hide the current unit again before JS dependency probing.
- Carry the identifier stamp across the split because OCaml has one mutable
  global stamp through translation and JS compilation.

Detailed in-process algorithm:

1. The parse phase runs `generate_ast_with_rust_parser` for `.res` and `.resi`
   files. It reads source bytes through the Latin-1-compatible path, parses into
   a `ParseArena`, applies per-file config, JSX, let-unwrap, built-in PPX unless
   disabled, applies `@@no_export` for structures, extracts dependencies, then
   stores `StoredAst` and dependency payloads in memory. It does not run or
   consume external PPX output.
2. The scheduler snapshots the stored AST table and a `ModuleRegistry` template
   once for the compile wave. The registry snapshot shares Arc-backed maps so
   worker-local registries can read published dependency signatures and metadata
   without a global mutable `PersistentEnv`.
3. Ready typecheck work is held in a priority heap and bounded by the current
   Rayon pool size. This keeps critical-path ordering meaningful instead of
   submitting the whole graph to Rayon at once.
4. `compile_module_in_process_to_js_boundary` builds compiler options, inserts
   provisional module metadata into a local registry, and typechecks the stored
   `.resi` first when one exists. The interface result is registered locally so
   the implementation can run the same `.resi` constraints OCaml would read from
   `.cmi`, and a `SignatureReady` message can unblock dependents.
5. The implementation path calls
   `compile_preprocessed_structure_in_process_until_js`. It creates a fresh
   `TypeContext`, `TypeCheckContext`, local `Env`, and registry-backed
   `PersistentEnv`, then runs `type_structure`.
6. With an interface, Rust applies the moregen constraints before typedtree
   capture and keeps the declared interface as the export target. With no
   interface, it simplifies the inferred signature, checks non-generalized
   schemes, normalizes signature types, prepares save-time stamp/shape effects,
   registers the signature in the local registry, and publishes the signature
   through the scheduler hook before RawLambda conversion.
7. The current unit's just-published signature remains visible through RawLambda
   conversion, matching OCaml's save-before-translation behavior. The pre-JS
   result contains the lowered Lambda, possible required modules, the identifier
   stamp at the JS boundary, directives, debug/JSX-preserve flags, the signature,
   optional registry updates, and captured intermediates.
8. The scheduler converts the possible required module set into backend-visible
   dependencies and waits for those modules' JS metadata before finalizing JS.
   Type dependents can start after signature publication; JS finalization waits
   only for backend-visible metadata.
9. `finish_preprocessed_structure_in_process_from_js_boundary_with_metadata_hook`
   creates a fresh registry-backed `PersistentEnv` for JS, unregisters the
   current unit so dependency probing cannot import it as a normal dependency,
   restores the carried identifier stamp, runs the JS backend, publishes
   `is_pure`, `cmj_export_constants`, and `cmj_export_arities`, then renders zero,
   one, or many JS outputs.
10. In-process mode writes JS outputs and build-state data, but it does not write
    `.ast`, `.iast`, `.cmi`, `.cmj`, `.cmt`, or `.cmti` artifacts for ordinary
    source modules. Those artifact contracts are represented by `StoredAst`,
    `ModuleRegistry`, `PortablePersStruct`, and backend metadata.

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

Current semantic and coverage caveats:

- Rust direct interface helpers typecheck and dump signatures but do not write
  `.cmi`/`.cmti`; in-process interface helpers publish registry signatures
  instead of running every OCaml file-artifact step.
- Rust can read OCaml `.cmi`/`.cmj` artifacts, but direct Rust compilation does
  not yet write full OCaml-compatible interface and backend metadata artifacts.
- In-process backend metadata covers purity, constants, and arities. Closed
  Lambda exports for cross-module inlining are decoded from disk `.cmj` files
  only.
- Source-fallback signature typechecking in `PersistentEnv` is Rust-specific and
  should not be treated as OCaml's normal compiled-interface lookup behavior.
- Several lazy-environment side caches and explicit mode splits remain in the
  Rust typechecker. They are debt unless each call site is proven to correspond
  to an OCaml lookup or forcing boundary.

When a Rust implementation does something different from OCaml:

1. Decide whether the difference is representation-only or semantic.
2. If representation-only, document the invariant that keeps behavior identical.
3. If semantic, either remove it or document the exact intended ReScript language
   change.
4. Add tests for the behavior that would diverge.

## Possible Algorithmic Gaps With OCaml

These are the main areas where the current Rust implementation is known or
suspected to differ from the OCaml reference algorithm. Some are intentional
execution-mode differences, but each one needs care when claiming byte-for-byte
parity.

- Interface artifact behavior is not a full `after_parsing_sig` port. OCaml
  self-checks the signature, forces delayed checks, checks fatal warnings, saves
  `.cmi`, saves `.cmti`, and can run GenType. Rust direct helpers typecheck and
  dump; in-process helpers publish a registry signature instead of writing those
  files.
- Rust reads OCaml `.cmi`/`.cmj` files but does not yet write full
  OCaml-compatible `.cmi`/`.cmj` artifacts from the direct Rust CLI path.
  Rewatch in-process replaces them with registry data, so bugs can hide at the
  file artifact boundary until subprocess/file-backed mode is tested.
- In-process CMJ metadata currently publishes purity, constant exports, and
  arities. OCaml `.cmj` can also carry non-constant closed Lambda exports when
  `cross_module_inline` is enabled; Rust can decode those from disk `.cmj` but
  does not publish them through `ModuleRegistry`.
- The lazy module environment is not yet a mechanical port of `env.ml`.
  `ComponentLookupCacheMode`, flattened-alias side tables, forced path caches,
  and explicit `Stdlib`/`Pervasives` handling should be treated as audit points
  until each call site is proven to correspond to an OCaml lookup or forcing
  boundary.
- Source-fallback signature typechecking in `PersistentEnv` is Rust-specific.
  It can recover missing registry/file artifacts by typechecking source up to a
  depth limit; OCaml's normal driver expects compiled interfaces.
- Implementation coercion for a `.resi` path is recomputed at RawLambda
  conversion time. If `Includemod.compunit` fails there, Rust currently falls
  back to `build_name_based_coercion` so exports are filtered by name. That is
  not OCaml's algorithm and should be treated as a temporary compatibility
  fallback because it can hide real inclusion failures if used too broadly.
- Rust direct source mode follows the same broad frontend stage order as OCaml,
  but it is not a function-by-function clone of `Ppx_entry` and
  `after_parsing_impl`. Warning order, config timing, JSX, extension expansion,
  and built-in rewrite ordering should be checked against OCaml before changing
  this area.

## Performance Improvements Versus OCaml

Rust can use different storage and scheduling strategies as long as the
observable compiler products remain aligned with OCaml. These are current
performance-oriented differences and near-term candidates.

Current Rust performance-oriented differences:

- `ParseArena` stores positions, locations, longidents, recursive AST nodes, and
  strings behind compact typed indices. OCaml uses ordinary heap records and
  pointers. The Rust representation reduces pointer-heavy AST allocation and
  makes common handles four bytes while preserving OCaml-facing identity where
  binary AST and dumps need it.
- `TypeContext` stores type expressions in a per-compilation `typed_arena`
  allocation with stable addresses and `TypeExprRef` indices. This keeps OCaml's
  mutable type-node model while avoiding global type storage and allowing one
  independent type arena per concurrently compiled module.
- Parse-time sparse side tables keep uncommon expression payloads out of the
  main `Expression` enum. Function defaults, case guards, constructor payloads,
  variant payloads, record spreads, else branches, and coercion source types are
  keyed by stable `ExprIdx` instead of inflating every expression node.
- Typed expressions and patterns keep their extras and attributes in a
  `TypedArena` side table behind an optional 4-byte handle, so the common case
  of neither costs no allocation and no inline empty vectors.
- `Texp_record_sparse` is an internal representation for large closed regular
  records with many omitted optional fields, especially JSX prop bags. OCaml
  materializes one field entry per label from `lbl_all`; Rust stores explicit
  fields plus a shared `Arc<Vec<LabelDescription>>`, then expands or compacts at
  typedtree, RawLambda, and Lambda boundaries so output remains equivalent.
- In-process compilation avoids subprocess startup, marshal I/O, `.ast`/`.iast`
  write/read cycles, and local `.cmi`/`.cmj` write/read cycles. `StoredAst`,
  `ModuleRegistry`, `PortablePersStruct`, and backend metadata replace those
  file artifacts inside one build wave.
- The in-process scheduler publishes signatures before JS finalization, so
  dependent typechecking can overlap with upstream Lambda/JS work while still
  waiting for backend-visible metadata before JS dependency probing.
- Registry snapshots and stored AST snapshots share Arc-backed payloads across
  workers. Workers get local registry views for provisional module/interface
  entries instead of contending on one mutable persistent environment.
- Lazy module component views, stored component `OnceCell`s, child-component
  laziness, qualified component caches, and qualified record-label caches reduce
  repeated signature qualification, substitution, and constructor/label table
  work. These optimizations must still follow OCaml lazy lookup boundaries.
- The JS finish path consumes the lowered Lambda tree for the common single
  output target, avoiding extra clones. It keeps a shared lowered tree only when
  multiple JS targets must be rendered from one pre-JS result.
- ASCII and Latin-1 source handling keeps the file path byte-oriented like OCaml
  while giving the scanner a fast ASCII path and avoiding Unicode decoding work
  for the common case.

Candidate improvements that still need proof:

- Replace selected short-lived typechecker or parser temporaries with
  thread-local bump allocation, or `bumpalo`, after proving that physical
  `TypeExprRef` identity, arena indices, and mutation points remain unchanged.
  The current type-expression arena uses `typed_arena`; the current
  `ParseArena` is a typed-index `Vec` arena.
- Reduce or remove flattened-alias and forced-path side caches by moving more
  behavior into the OCaml-aligned lazy `Env`/`Ctype` boundaries. This is both a
  correctness simplification and likely a performance improvement if it removes
  duplicate lookup work.
- Publish closed Lambda exports through `ModuleRegistry` when
  `cross_module_inline` is enabled, matching disk `.cmj` capability without
  reintroducing file I/O.
- Keep extending counters around signature copy/freshen, qualified component
  cache hits, sparse records, and registry snapshots before committing
  performance changes. The right optimization target should be selected from
  measured hot paths, not intuition.

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
5. Check JS output parity and error-output parity before committing source
   changes.
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
   the change can affect output.
8. For performance work, run release measurements after correctness is stable.

Use this process for documentation changes:

1. Update this README in `compiler-rust/`.
2. Keep root README focused on project-level user/contributor information.
3. No parity run is required for README-only changes.

## Whole-project build benchmark

Compare two release `rescript` binaries on a disposable copy of any project:

```sh
scripts/bench_project.sh PROJECT_DIR BASE_RESCRIPT CANDIDATE_RESCRIPT \
  --runtime-from COMPILER_CHECKOUT
# Without Valgrind (output identity and wall time only):
scripts/bench_project.sh PROJECT_DIR BASE_RESCRIPT CANDIDATE_RESCRIPT --no-instructions
python3 scripts/test_bench_project.py rewatch/target/release/rescript
```

Requires Python 3 and, for instruction counting, Valgrind. The runtime checkout
(default: this checkout) supplies fresh runtime and Belt copies under the
project's `.rescript-pkgs`; the script replaces those copies and the
`node_modules/@rescript/belt` symlink. An existing real Belt directory must be
moved aside first. Use a disposable project: clean/build change its outputs.
Each binary first builds the runtime to populate `lib/ocaml` sources; Belt
builds with the project's dependencies. Runtime preparation is not timed,
instruction-counted, or included in the project's output digest.

The script compares sorted project-relative paths and SHA-256 content hashes
of `.js`, `.mjs`, `.cjs`, `.ts`, and `.tsx` files created or rewritten during
the project build (stat metadata before/after detects writes, excluding unchanged
handwritten files). Linked dependencies are followed, visiting each physical
directory once to avoid duplicate counts and symlink cycles. A mismatch lists
the first 20 differing paths.

Each binary then gets one clean, single-worker Cachegrind run with CI's
`--tool=cachegrind --cache-sim=no` flags. Instructions per line count **all**
physical `.res`/`.resi` files under the project, including dependencies and
build-directory source copies, rather than only compiled modules. Normal build
wall time uses the caller's thread setting (set `RAYON_NUM_THREADS=8` for eight
workers); Cachegrind always uses one. This is a comparison report, not a
statistical regression gate. Exit status is 0 for identical output, 1 for
different output, and 2 for usage/build errors. The final `BENCH_PROJECT ` line
contains a JSON summary, including counts, digests, seconds and instructions.

## Parse-only instruction benchmark

Run `scripts/bench_parse.sh` from a checkout with Cargo on `PATH`. It builds
`examples/parse_bench.rs` in release mode and benchmarks `tests/tests/src` and
`packages/@rescript/runtime` in `scan` and `parse` modes. With Valgrind installed
it uses the instruction-count CI flags (`--tool=cachegrind --cache-sim=no`)
and reports instructions per source line; otherwise it reports timing only.
Set `ITERATIONS=N` to repeat the corpus (default 1). To select other inputs:

```sh
cargo run --release --manifest-path compiler-rust/Cargo.toml --example parse_bench -- \
  --mode parse --iterations 1 tests/tests/src packages/@rescript/runtime
```

Files are recursively collected, canonicalized, sorted and deduplicated; symlinks
are skipped. All input is read and decoded using the build's Latin-1 conversion
before timing starts. A line is an LF-terminated line or a final nonempty line
without LF (empty files have zero lines). Files, lines and bytes describe one
corpus pass; diagnostics count all iterations, and nanoseconds/instructions per
line divide by `lines * iterations`. The timed region includes allocation and
AST destruction, but no I/O, printing, frontend rewrites, JSX transform or type
checking. Parsing uses `Parser::new` (locations enabled), `parse_structure` for
`.res` and `parse_signature` for `.resi`, just like the compiler before its
frontend. Scanner mode repeatedly calls `Scanner::scan` to EOF; it deliberately
has no parser context for JSX, templates or regexes, so its lexical diagnostics
can differ from parse mode. The `parse_errors` field counts diagnostics (lexical
ones in scan mode), not files with errors; errors do not fail the benchmark.

Cachegrind counts the **whole process**, including startup, discovery, loading
and output; timing measures only the in-memory loop. Compare the same corpus,
iterations, checkout path, toolchain and machine. This is an instruction-work
metric, not hardware retired instructions or a timing measurement under Valgrind.

Initial x86-64 Linux measurements, Valgrind 3.22.0, release fat LTO, one iteration,
894 files / 67,935 lines / 1,745,497 bytes:

| Mode | Run 1 instructions | Run 2 instructions | Run 1 instructions/line | Run 2 instructions/line |
| --- | ---: | ---: | ---: | ---: |
| scan | 192,651,045 | 192,651,164 | 2835.814308 | 2835.816059 |
| parse | 632,055,990 | 631,790,848 | 9303.834401 | 9299.931523 |

Parse mode reported zero errors; scanner mode reported 210 lexical diagnostics.
**Repeatability limitation:** scan differed by 0.000062%, but parse differed by
0.04195%, exceeding a 0.01% comparison threshold. The parser still constructs
randomly seeded hash tables, a likely source of this noise. Increasing to 20 iterations did not reliably remove
this variation. Do not use this benchmark to gate changes at 0.01% until that
noise is resolved; the benchmark does not substitute a different parser or
change production hashing just to improve its scores.
