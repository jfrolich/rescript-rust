# Compile-time macros: the compiler side

How the design in [README.md](README.md) is implemented in the Rust
compiler. Read that first.

## Where things are

| Path | What |
| --- | --- |
| `compiler-rust/src/macros/mod.rs` | The `MacroHost` trait (the JavaScript engine), `MacroExpansionRequired`, and where compiler text and engine text are converted. |
| `compiler-rust/src/macros/expand.rs` | The expansion of one file: the pass loop, `%Macro.eval`, position mapping. |
| `compiler-rust/src/macros/discover.rs` | The type checker's hooks: recognizing macro uses, running the macro, recording edits, instances of generics. |
| `compiler-rust/src/macros/quote.rs` | Lowering `%code`, `%type` and `%pat` in a macro's own file. |
| `compiler-rust/src/macros/reflect.rs` | Answers about types: `Type.info`, printing a type as source, the literal shape of a `%Macro.eval` value. |
| `compiler-rust/src/macros/edit.rs` | `SourceText`: text that knows where each character comes from, and edits on it. |
| `compiler-rust/src/macros/report.rs` | What a diagnostic says about generated code. |
| `compiler-rust/src/macros/host.js` | The engine side: module loader, sandbox, call entry point. The same script in QuickJS and in the browser. |
| `compiler-rust/src/macros/quickjs.rs` | The engine of native builds (feature `macro-quickjs`, part of `native`). |
| `packages/@rescript/runtime/Macro.res` | The API macros are written against. |
| `compiler-rust/src/parser` | `${...}` holes, the payloads of quotes, macro arguments. |
| `compiler-rust/tests/macros.rs` | End-to-end tests: small projects, the JavaScript and the expanded source. |
| `compiler-rust/tests/macro_errors.rs` | The diagnostics of broken programs, compared with `tests/macro_errors/*.txt`. |
| `playground/` | The browser playground and its host. |

## Parsing

- `${` is a token (`Token::DollarLbrace`). `${expr}` parses to the extension
  `res.hole` with the expression as payload, where an expression, a type or
  a pattern is expected. The scanner did not accept `$` outside template
  strings before, so no existing source changes meaning.
- `${...expr}` is a splice hole, the extension `res.hole.splice`. It parses
  where a hole does, and in two places of its own: as a row of a record
  (`{a: 1, ${...rest}}`, a field named `res.hole.splice` whose value is the
  extension) and as a case of a switch (a case without a bar, with the
  pattern `_` and the extension as its right-hand side). A block does not continue into a splice
  hole, so one after a case is the next case and not an expression of that
  case's body.
- `%code(...)` has the ordinary payload of an extension: an expression or
  structure items. `%type(...)` takes a type and `%pat(...)` a pattern.
- An extension whose name starts with an uppercase letter takes
  comma-separated arguments: expressions in expression, item and module
  position, types in type position. One argument is kept as itself, several
  as a tuple.
- The parser has a mode for expanded text (`Parser::for_expanded_source`):
  identifiers may contain `$`, and `Position::cnum` counts characters, which
  is what `SourceText` maps.

## One file, start to finish

`driver::compile_source_in_process` compiles the file as it always did. The
type checker runs with `MacroMode::Off`: at a macro use it sets
`macro_expansion_required` and fails the item, and the driver returns
`MacroExpansionRequired`. Only then does expansion run:

```mermaid
sequenceDiagram
  participant D as driver
  participant X as expand_source
  participant T as type checker (discover)
  participant E as engine (host.js)
  D->>X: source text
  loop until a pass records no edit
    X->>X: parse; lower quotes; frontend
    X->>T: type check with MacroMode::Discover
    T->>E: call Json.encode with {code, type handle}
    E-->>T: need info:3
    T->>E: call again, with the answer
    E-->>T: code as text
    T-->>X: edits, errors, %Macro.eval sites
    X->>X: apply edits
  end
  X-->>D: expanded text + origin map
  D->>D: parse expanded text, remap positions, compile
```

The final compile is the ordinary pipeline on the expanded text. It also
returns the text (`InProcessCompileResult::expanded_source`).

### Why text

A macro's result is source text, and expansion is edits of the file's text
followed by a new type check. The alternative is splicing parse trees and
typing only the new piece.

Text was chosen because it makes generated code go through exactly what
written code goes through (the parser, the frontend passes, inference, later
macro uses inside it) without a second path for any of them, and because the
expanded file is a thing a person can read. Its cost is a type check of the
file per pass. Changing it later does not change the language: the surface
(`code<'a>`, quotes, `Macro`) does not say how code is represented.

`SourceText` keeps, for every character, where it comes from:

- a character of the file as written has its offset in that file, also when
  it is an argument that a macro put in its result;
- a generated character has the macro use it was generated for, and, when it
  was written in a quote, the file, line and column of that quote. A
  function generated for a `@generic` is generated for the call that needed
  it and has a description, "`Json.encode` for `user`". Code generated
  inside generated code belongs to the use in the file as written.

`expand::remap_positions` rewrites every position in the parse arena of the
expanded text through that map, so everything after parsing sees original
positions. It goes by location: one that starts or ends in generated code
covers the macro use, one inside an argument stays where the argument is.
The arena keeps the expansion (`ParseArena::expansion`): the text, and the
offset each position had in it.

## Diagnostics

A diagnostic in generated code is reported at the macro use. When the driver
prints the frame of a location (`push_generated_code_note` in `driver.rs`,
for errors and warnings), it asks the expansion what is at the location's
offsets in the expanded text. For generated code, `report.rs` adds a note
after the frame: the lines of the quote the code was written in, read from
the macro's file, or, for code that is not from a quote (`Code.raw`, the
builders), the lines of the expanded source.

Errors of expansion itself (a macro that reports or raises, generated code
that does not parse, passes that run out) go through `expand::diagnostic`,
which places and annotates them the same way.

The final compilation of an expanded file runs with
`MacroMode::Expanded`. A macro use that is still there is typed by its
declared type instead of stopping the compilation: it is there because
something near it has an error, and that error is the one to report.

## Quotes

`quote::lowering_edits` rewrites the quotes of a file as text:

```rescript
%code(JSON.Encode.string(${value}))
// becomes
(Macro.__quoteCode(
  [[("JSON.Encode.string(", 9, 20)], [(")", 9, 48)]],
  [Macro.__holeCode(value)],
  "Json.res",
))
```

The pieces are the source text around the holes, each with the line and
column it has in the macro's file. A code value is `{c: text, m: spans}`:
`m` lists which parts of the text are a piece of a quote or an argument of
the macro (an argument arrives with `$o`, the compiler's name for its range).
`Macro` keeps the spans when it builds code from parts (`cat` in
`Macro.res`), and the engine returns them with the code. That is how a
character of the expanded text gets its origin. `__holeCode`, `__holeType`
and `__holePat` are identity functions whose types make the hole's
expression check as `code<'a>`, `typ` or `pat`; `__holeItem` is for a hole
that stands where a whole declaration does. A quote of declarations lowers
to `__quoteDecls`. At run time a quote is string concatenation, with
parentheses around each filled hole except a declaration.

A splice hole is lowered by the list it is an item of, which the scan of a
quote records for each one (`SplicePlace`):

| The list | The hole becomes | Its argument |
| --- | --- | --- |
| Arguments of a call or a constructor, items of an array or a tuple | `Macro.__spliceItems(items, trailing)` | `array<code<'a>>` |
| Fields of a record | `Macro.__spliceEntries(entries, trailing)` | `array<Code.entry>` |
| Cases of a switch | `Macro.__spliceCases(cases)` | `array<(pat, code<'a>)>` |

The operands of an operator are an application as well, and are not a list:
`1 + ${...xs}` is not a place for a splice. The comma after a hole of items
or entries belongs to the hole (`trailing`), which writes it when it has
items: a hole with none leaves no comma in the text. A splice hole in any
other place is left in the lowered code, where `quote::stray_splice` finds
it and expansion reports it at its position, as it does for one outside a
quote.

A record value is built from entries (`Code.entry`, `Code.entryOf`,
`Code.spread`): `Code.record` and a splice hole in a record both take them,
and both put a spread before the fields, where the syntax wants it.

While it copies a piece, the lowering puts the file's module name in front
of the top-level value and module names of the macro's own file, so that
`encode(v)` inside a quote in `Json.res` reads `Json.encode(v)` at the use.
This is the only hygiene there is so far.

## The type checker's hooks

`TypeCheckContext::macro_mode` is `Off` or `Discover(Discovery)`. The hooks
are called from `typecore.rs` and `typemod.rs`:

| Hook | Called at | Does |
| --- | --- | --- |
| `expression_extension` | `Pexp_extension` | `%M.f(...)`, `%Macro.eval`, leftover quotes and holes |
| `type_extension`, `pattern_extension` | `Ptyp_extension`, `Ppat_extension` | macros in type and pattern position |
| `declarations_extension` | `Pstr_extension`, `Pmod_extension` | macros that return declarations |
| `type_item`, `value_item` | a `type` or `let` item with a macro attribute | derive on a type, rewrite of a `let` |
| `generic_use`, `note_application` | an identifier, an application | notes a use of a `@generic` |
| `begin_item`, `end_item` | around each top-level item | resolves the noted generics once the item is inferred |

In a discovery pass a hook runs the macro and pushes an `Edit`. The item
then fails with a marker error and the pass goes on with the next item: a
failed item is skipped in discovery, so one pass expands every macro it can
reach. Real type errors are left for the final compile to report.

`typemod.rs` copies `@macro` and `@generic` from a `let` to the value
description of the exported value (`mark_macro_values`), which is how a use
in another file knows the value is a macro.

### Arguments

A macro's parameter types decide what each argument becomes
(`signature`/`ParamKind`): `code<'a>` gets `{c: <source text>, t: <type>}`,
where the type comes from typing the argument on its own; `typ` gets a type,
`{c: <printed type>, id: <handle>}`; any other type gets the JSON value of a
literal
(`literal`). `Type.decl` and `Decl.value` are built from the item the
attribute is on.

### Generics

A `@generic` used in another file is typed as a function at its erased type
(`code<t>` read as `t`), and the use is noted with its environment and type.
At `end_item` the types are final. For each use, `resolve_generic`:

1. prints the argument and result types. A type that still has an unknown
   part is an error asking for an annotation;
2. looks up the instance by key: macro, argument types, compile-time values,
   result type;
3. if there is none, runs the macro with parameters named `a$`, `b$`, ...
   and adds `name = (a$: t): r => <result>` to the instance group of the
   current top-level item;
4. replaces the callee, or the whole call when there are compile-time
   arguments, with the instance name.

Instance groups are `let rec` items marked `@res.macroInstances`, inserted
before the top-level item that needed them. `typemod.rs` leaves them out of
the signature and `raw_lambda/convert.rs` out of the exports. An instance
that an earlier item turns out to need moves to that item's group, with the
instances it calls (`Discovery::finish`). `InstanceTable` lives across the
passes of a file.

The calls a generated instance makes to the generic (the `encode(...)` on
each field) are ordinary uses, found by the next pass.

### `%Macro.eval`

`%Macro.eval(expr)` is known by its name (`macros::EVAL_MACRO`); the module
`Macro` has no value `eval`. It parses as any macro use does, with the
expression as its argument, and in a place other than an expression it is
an error.

A discovery pass types the expression and records the site with the shape
of its type (`reflect::value_shape`). After the pass,
`expand::evaluate` compiles `opens + let value = <expr>` as a
module of its own in memory, sends its JavaScript to the engine (`kind:
"eval"`), and `host.js` writes the value as a literal by the shape.

## The engine

`MacroHost::call(request) -> response` is the whole interface, JSON both
ways. The embedder provides `__rescript_macro_source(moduleName)`, which
returns the compiled JavaScript of a module; `host.js` loads modules through
it, turning ES module output into CommonJS by text when needed.

```json
{"kind": "call", "module": "Json", "name": "encode",
 "args": [{"c": "alice", "t": {"c": "user", "id": 1}}],
 "expected": {"c": "JSON.t", "id": 2},
 "answers": {"info:1": {"TAG": "Record", "name": "user", "fields": []}}}
```

The response is `{"ok": "<code>", "spans": [...]}`, `{"error": "..."}` (with
`"exception": true` when the macro raised instead of reporting) or
`{"need": "<question>"}`. A question is `info:<handle>`,
`companion:<handle>:<name>`, `readFile:<path>` or `env:<name>`. On `need`
the compiler adds the answer and calls again (`Discovery::run`). Answers
are in the layout the compiled `Macro.Type.info` variant has at run time,
so the macro reads them without decoding.

The compiler keeps source text as one `char` per byte of the file.
`macros::call_host` converts requests to real text and responses back.

`host.js` gives macro modules a `Math` without `random`, a `Date` without
the current time, and no `fetch`, timers or other input and output of the
embedder.

**QuickJS** (`quickjs.rs`): one runtime per thread that expands macros,
created on first use, with a 512 MB memory limit and an interrupt handler
that stops a call after 20 seconds. `QuickJsHost::invalidate` makes engines
drop the modules they loaded, for when compiled JavaScript changes.

**Browser** (`playground/crate/src/lib.rs`): the host calls
`__rescript_macro_call` of the page, which evaluated `host.js`. The compiler
runs in a worker; the page replaces the worker when a build takes more than
20 seconds.

## The runtime as source

The tests and the playground have no compiled standard library: modules of
`@rescript/runtime` are type checked from source on demand.
`ModuleRegistry::set_source_fallback_is_runtime` says that those modules are
the runtime: they are checked with the runtime package's flags
(`-nopervasives -open Pervasives`) and imported from
`@rescript/runtime/lib/...`.

## Tests

`cargo test --manifest-path compiler-rust/Cargo.toml --test macros` compiles
small projects, with QuickJS as the engine, and checks the JavaScript and
the expanded source. One test compiles every example of the playground.
`--test macro_errors` compiles broken programs and compares what the
compiler says with `tests/macro_errors/*.txt`; `UPDATE_EXPECTED=1` rewrites
those files. `playground/scripts/smoke.mjs` builds and runs the same examples
with the compiler in WebAssembly.

## Next steps

In the order that seems right:

1. **Build system.** In `rewatch`: treat a macro name in an extension or
   attribute as a reference to its module (`binary_ast/deps.rs`), create one
   `QuickJsHost` per build whose source function reads the compiled
   JavaScript of a module, and on `MacroExpansionRequired` expand from the
   source file and compile the result. Then measure a large project.
2. **Cache.** Store `(macro module digest, request, answers) -> result` in
   `lib/bs/rescript.sqlite`, and record the files `readFile` read and the
   interfaces `Type.info` looked at as inputs of the module, next to the
   `reads` the build already tracks.
3. **Hygiene.** Rename the binders a quote introduces per expansion.
4. **Check a quote where it is written.** A quote is text until a use
   expands it, so `%code(${e} + 1)` returned as `code<string>` is found at
   the use, not in the macro's file. Typing a quote's content against its
   holes at definition would catch it there.
5. **`rescript expand <file>`** and the editor: show the expansion; hover
   and definitions inside macro arguments.
6. **Port ppx-spice** to a library of macros, with the Rust port as the
   oracle, and delete `binary_ast/spice_ppx.rs`.
7. **Trees instead of text**, if the measurements of step 1 ask for it.
