# Importing TypeScript into ReScript

Status: draft, implemented on the branch `ts-import` of the Rust port of the compiler.

## In short

Using a TypeScript module from ReScript means writing bindings: an `external` for every function, a record for every interface, by hand, and again when the TypeScript changes. Nothing checks that the bindings are right.

With this change you name the module and what you want from it:

```rescript
let {getUser, rename} = %ts("./users.ts")
```

The compiler asks the TypeScript checker for the types of `getUser` and `rename` and declares them as ReScript types. `%ts` is replaced by ordinary `type` and `external` declarations before type checking, so everything after it (inference, errors, the JavaScript that is generated) is what you would get from bindings written by hand.

The checker is [tsrs](https://github.com/oxc-project/tsrs), a port of the TypeScript compiler to Rust, linked into the ReScript compiler. There is no Node process, no `tsc` run and no generated file.

<!-- example: values -->
```rescript
let {add, formatPrice, average, taxRate} = %ts("./math.ts")

let total = add(19.99, 5.)
let inDollars = formatPrice(total, ~currency="USD")
```
<!-- /example -->

In each example the left side is editable: change the TypeScript and watch the ReScript declarations follow, or change the ReScript and see what the type checker says. "As ReScript" shows the file with its imports written out.

## The import forms

There are five, all built from syntax ReScript already has. The string is a module specifier, resolved the way TypeScript resolves it from the importing file; `#Name` selects one export.

| Form | Imports |
|---|---|
| `let {a, b: c} = %ts("./m.ts")` | The values `a` and `b` (as `c`), and every type they mention. |
| `let main = %ts("./m.ts#default")` | One value under a name of your choice. |
| `type user = %ts("./m.ts#User")` | One type. |
| `module Api = %ts("./m.ts")` | Every export, as a module. |
| `module Counter = %ts("./m.ts#Counter")` | A class: `Counter.t`, `Counter.make` and the static members. |

Types are declared where they are first needed and once per file, so two imports that mention `User` share one `user`.

<!-- example: records -->
```rescript
let {getUser, rename} = %ts("./users.ts")

let ada = rename({id: "1", name: "ada", email: Null.null, tags: [], address}, "Ada")
```
<!-- /example -->

<!-- example: module -->
```rescript
module Api = %ts("./api.ts")
type todo = %ts("./api.ts#Todo")
```
<!-- /example -->

<!-- example: classes -->
```rescript
module Counter = %ts("./counter.ts#Counter")

let a = Counter.make(10.)
let next = a.increment(~by=2.)
```
<!-- /example -->

## How types are translated

The translation starts from the checker's types, not from the syntax of the declaration. Aliases are followed, generics applied, utility and mapped types evaluated, and results that were never annotated are inferred, before anything is turned into ReScript.

| TypeScript | ReScript |
|---|---|
| `string`, `boolean`, `bigint`, `void` | `string`, `bool`, `bigint`, `unit` |
| `number` | `float` |
| `T[]`, `readonly T[]`, `[A, B]` | `array<t>`, `array<t>`, `(a, b)` |
| `T \| undefined`, `T \| null`, both | `option<t>`, `Null.t<t>`, `Nullable.t<t>` |
| `interface`, object type | record; methods are fields of function type |
| instance of a class the module exports | private record with `@instanceOf`, and `@extends` for its superclass |
| optional property `p?: T` | optional field `p?: t` |
| `Record<string, T>`, `{[key: string]: T}` | `dict<t>` |
| `"a" \| "b"`, `1 \| 2` | `[#a \| #b]`, `[#1 \| #2]` |
| objects sharing a literal property (`kind: "circle"`) | `@tag("kind")` variant with inline records |
| `string \| number`, `number \| "auto"`, `T[] \| Date`, `string \| symbol` | `@unboxed` variant |
| `Car \| Vehicle`, `Readable \| Writable`, `URL \| Headers \| string` | `@unboxed` variant with one case per class |
| `enum` | variant with `@as` |
| type parameters, on types and functions | type variables |
| generic method | field with a polymorphic type (`'u. ...`) |
| optional parameter | optional labelled argument `~name=?` |
| rest parameter of the imported function | `@variadic` |
| `Promise`, `Map`, `Set`, `Date`, `RegExp`, `Error`, typed arrays | `promise`, `Map.t`, `Set.t`, `Date.t`, `RegExp.t`, `JsError.t`, ... |
| library classes (`URL`, `Headers`, `Element`) | an abstract type with `@instanceOf`; a subclass abbreviates its superclass |
| other library types (DOM option objects, iterables) | an abstract type per type |
| `unknown` | `unknown` |

Object types without a name get one from where they are used (`loadResult`, `updatePatch`), and two with the same shape share a declaration. Types that refer to each other become one `type rec` group.

<!-- example: unions -->
```rescript
let {area, scale, place} = %ts("./shapes.ts")

let circle = Circle({radius: 2.})
let placed = place(circle, #center, Auto)
```
<!-- /example -->

A class that something names at run time (an export of the module, a class of a Node module, a global such as `URL`) is declared with that class, so that it can be a member of a union. This uses a language change that is part of this branch, described under [Classes on records](#classes-on-records).

<!-- example: instances -->
```rescript
module Garage = %ts("./garage.ts")

let describe = (what: Garage.parkWhat) =>
  switch what {
  | String(plate) => plate
  | Car(car) => car.honk()
  | Vehicle(vehicle) => Float.toString(vehicle.wheels)
  }
```
<!-- /example -->

<!-- example: generics -->
```rescript
let {parseNumber, first, mapPage} = %ts("./result.ts")
```
<!-- /example -->

<!-- example: resolved -->
```rescript
let {update, setters, snapshot} = %ts("./settings.ts")
```
<!-- /example -->

A package is found through `node_modules`, `package.json` and its declaration files, with the options of the nearest `tsconfig.json` (or strict, `esnext`, bundler resolution when there is none).

<!-- example: package -->
```rescript
let {money, plus, format} = %ts("tiny-money")
```
<!-- /example -->

## Only what is imported is checked

A TypeScript program is type checked lazily: asking for the type of one symbol resolves that symbol and what its type mentions, nothing else. The import uses this. It builds a program with one root, a file of a few lines that imports the modules named by `%ts`, and asks for the types of the requested exports. Function bodies are only looked at when a result type has to be inferred. The rest of the module, and the rest of the project, is parsed but not checked.

The consequences:

- The cost of an import follows the size of the types you import, not the size of the project they live in.
- A type error somewhere else in the TypeScript does not stop the ReScript build. It is not reported either: this is not a replacement for running `tsc`.

<!-- example: lazy -->
```rescript
let {invoiceTotal} = %ts("./billing.ts")
```
<!-- /example -->

Measured with a release build on an Apple M-series machine:

| | Types resolved | Time |
|---|---|---|
| Import one function from a 402-line module | 87 | 2.0 ms |
| Full check of the same module | 9,311 | 12.6 ms |
| First import in a compiler process (parses TypeScript's library files) | | about 9 ms |
| Every later import in that process | | about 0.7 ms |
| `module Vite = %ts("vite")`: 105 values, 1,353 types | | 62 ms |

The declaration files of the TypeScript standard library are parsed once per process and shared by every import after that.

## Errors

Because an import becomes declarations, using it wrongly is an ordinary type error, at the place of the mistake.

<!-- example: mismatch -->
```rescript
let {distance} = %ts("./geometry.ts")

let d = distance(origin, {x: "3"})
```
<!-- /example -->

A module that cannot be found, or an export that does not exist, is an error at the `%ts`, and lists what the module does export.

## What TypeScript can say that ReScript cannot

Not every TypeScript type has a ReScript form. When one does not, the import still compiles, with the closest type that is sound to use (often `unknown`, which you have to check or cast before using), and the compiler records a note: which import, where in its type, the TypeScript type, and what was lost. The "TypeScript" tab of each example lists the notes.

<!-- example: gaps -->
```rescript
let {parse, resolve, log, byId, debounce} = %ts("./loose.ts")
```
<!-- /example -->

To see which gaps matter, every export of twelve modules was imported: `react`, `react-dom`, `semver`, `chalk`, `vite` and seven Node built-ins (`fs`, `path`, `url`, `child_process`, `os`, `events`, `http`). That is 585 values and 2,292 types, and all twelve compile. 66% of the declarations have an exact ReScript type. The other 34% carry at least one note:

| Gap | Declarations affected | Imported as | What would close it |
|---|---|---|---|
| Union whose members cannot be told apart at run time | 18.1% | `unknown` | See below: these are four different problems. |
| `any` | 9.9% | A type variable as an argument, `unknown` as a result | Nothing: `any` is a hole in the TypeScript, not in ReScript. |
| Overloads | 6.9% | The first signature | Converter: one external per signature (`parse`, `parse2`). Language: an external with several types, chosen by the arguments. |
| Constraint on a type parameter (`T extends U`) | 3.8% | An unconstrained type variable | Language: bounded type variables. For object bounds the open object type `{.. "id": string}` already exists, but not for records. |
| Rest parameter in a callback type | 3.5% | One array argument | Language: `@variadic` on function types, not only on externals. |
| Constructor types, classes as values | 2.8% | `unknown` | Language: a function type that is called with `new`. |
| Conditional, mapped and indexed types over a type parameter | 2.8% | The constraint, or `unknown` | Converter: import at an instantiation, `%ts("./m.ts#Pick<User, 'id'>")`, which TypeScript can evaluate. |
| Enum and namespace objects as values | 2.5% | Skipped (the enum's type is imported) | Converter: a module with one value per member. |
| Tuples with optional or rest elements | 2.3% | `array` | Language: optional tuple elements. |
| Generic function type nested in a type | 2.1% | `unknown` for its own type parameters | Language: polymorphic function types anywhere, not only as record fields. |
| Type parameter out of scope where the type is declared | 2.1% | `unknown`, or the constraint | The same. |
| Explicit `this` parameter | 1.1% | Dropped | Converter: `@this` already expresses it. |
| `object` and `{}` | 1.0% | `unknown` | Converter: `{..}` for `object`. |
| Functions with properties | 1.0% | The function | Converter: an abstract type with a `call` external and one getter per property. |
| Named properties next to an index signature | 0.7% | The named properties | Language: a record with a `dict` remainder. |
| `never` outside a result | 0.6% | `unknown` | Language: an empty variant type. |
| Branded primitives (`string & {__brand: "Id"}`) | 0.3% | The primitive | Converter: `type id = private string`. |

Two kinds of union that used to be in the first row are imported exactly now: `string | symbol` (124 declarations, all event names and property keys) and unions of classes such as `Readable | Writable` or `Car | Vehicle`. What is left, 522 declarations, is not one problem:

- **Tagged unions that share a tag** (about 180). The syntax tree `Node` of vite's parser is a union of interfaces tagged by `type`, where six of them say `type: "Literal"` and six more `type: "Identifier"`. A `@tag` variant needs distinct tags.
- **More than one plain object.** React's `ReactNode` (about 70), `{result} | {error}`, `AddressInfo | {}`. Nothing at run time tells two plain objects apart unless a field does; the upstream proposal for that is objects told apart by a field they share (rescript-lang/rescript issue 7988).
- **Library interfaces** (about 140). `NodeJS.ReadableStream | WritableStream`, `EventEmitter | EventTarget`, `EventListener | EventListenerObject`, `boolean | AddEventListenerOptions`, `T | PromiseLike<T>`. TypeScript declares these as interfaces, so nothing says which class to test for, and the import makes a library interface an abstract type. The DOM option objects could be records; the converter does not do that yet.
- **Unions of tuples** (about 40): the arguments of an event listener, `[] | [err: Error] | [chunk: any]`.

For arguments none of this needs solving: a function that accepts `A | B` can be given an `A`. A union type that can be built from any member but not matched on would make every union importable in argument position, which is where most of them are.

## Classes on records

The unions of classes are imported through a change to the language, which is part of this branch and implemented in the Rust compiler only.

An untagged variant tells a class case apart with `instanceof`. Before, the class could be declared on an abstract type only (`@instanceOf("Blob") type blob`), which has no fields, and the class had to be a global. Now:

```rescript
@instanceOf("Blob")
type blob = private {
  size: float,
  @as("type") type_: string,
}

@instanceOf("File") @extends(: blob)
type file = private {
  ...blob,
  name: string,
}

@unboxed
type part = Text(string) | Blob(blob) | File(file)

let name = part =>
  switch part {
  | Text(text) => text
  | File(file) => file.name // tested before Blob
  | Blob(blob) => blob.type_
  }

let asBlob = (file: file) => (file :> blob)

@module("three") @instanceOf("Mesh")
type mesh // part instanceof Three.Mesh, with the import
```

- **`@instanceOf` on a record** makes the record a class: its values are the instances. The record must be `private`, so that a record literal cannot pass for an instance; the fields are read as on any record.
- **`@extends(: parent)`** names the superclass. The parent must be a class, and the record must have the parent's fields at types that coerce to the parent's. A method that returns its own class is fine: `rename: string => dog` in the subclass, `string => animal` in the superclass.
- **A subclass coerces to its superclass** with `:>`, and to nothing else: a record with the same fields that is not a declared subclass does not coerce to a class.
- **In a variant the subclass is tested first**, whatever the order of the cases. A variant with two classes where neither is declared a subclass of the other tests them in the order written.
- **`@module("m")` beside `@instanceOf`** imports the class from `m`. Classes of the same name from two modules are two classes.

This follows the upstream RFC "Class hierarchies in WebAPI" (rescript-lang/rescript issue 9058, proposals A and B) and fixes what issue 9239 reports for `@module`. `@instanceOf` on abstract types and `@typeOf` were already in the compiler; the import now uses them too. Not implemented: `@scope` beside `@instanceOf` (write a dotted class name), and the OCaml compiler, which rejects these declarations.

The remaining table is the proposed order of work: the converter-only rows first, since they need no design.

## How it works

1. The file is parsed as usual. Before the built-in PPXs run, the compiler looks for `%ts` at the top level of the structure and of nested modules.
2. All imports of the file are answered by one TypeScript program. Its only root is a virtual file next to the importing file that imports each named module. TypeScript loads those modules and what they import, and its own library declarations.
3. For every requested export the compiler asks the checker for its type and walks it: signatures, properties, union members, type arguments. Each type it meets becomes a ReScript type expression or a declaration, and a note where it does not fit.
4. The declarations are printed as ReScript source, parsed into the same syntax tree as the file, and take the place of the `%ts` item. Locations point at the `%ts`, so an error in generated code is reported there.
5. Compilation continues as for any file. The generated externals use `@module`, so the JavaScript imports the TypeScript module by the specifier you wrote.

The implementation is the crate `ts-import/` (TypeScript types to ReScript declarations; it does not depend on the compiler) and `compiler-rust/src/ts_import.rs` (finding `%ts`, splicing the declarations). The Cargo feature `ts-import` of the compiler is on by default; without it `%ts` is an unknown extension.

The catalog `ts-import/tests/fixtures/features.ts` has about 140 exports, one per TypeScript feature, with the expected ReScript next to it in `features.res.txt`. A compiler test type checks every declaration in it, and another imports every export of the twelve modules of the survey and compiles the result, where they are installed.

## Limitations and open questions

- **Incremental builds do not watch TypeScript files.** A module is recompiled when its `.res` changes, not when a `.ts` it imports changes. The build system needs the list of files an import read; the import already produces it.
- **The JavaScript imports the specifier as written.** `%ts("./api.ts")` compiles to `import ... from "./api.ts"`, which a bundler resolves. Without a bundler the specifier has to name a JavaScript file.
- **Numbers are `float`.** TypeScript does not distinguish integers.
- **Records are closed.** A TypeScript function that takes `{id: string}` accepts any object with an `id`; the imported one takes exactly that record. Pass a record of the declared type.
- **Names are adapted.** Types and values become lower case identifiers (`User` is `user`, `URL` is `url`), reserved words get an underscore (`type_`), and the original name is kept with `@as` or the external's string.
- **Importing every export of `typescript` itself does not finish** in reasonable time: its API is one very large mutually recursive graph. Named imports from it are fine.
- **tsrs keeps a program alive for the life of the process.** One program is made per importing file. In a long-running watch process this adds up and needs a cache keyed by the TypeScript files.
- **tsrs is young** (it tracks TypeScript 7's Go implementation) and is pinned to a commit. It needs a recent nightly Rust, which the repository already uses.
- Should a note be a warning? Today notes are only visible in tooling; a build is silent about an import that became `unknown`.

## Trying it

```sh
cargo test --manifest-path compiler-rust/Cargo.toml --test ts_import
cargo test --manifest-path ts-import/Cargo.toml

# What an import expands to, with its notes:
cargo run --manifest-path ts-import/Cargo.toml --example show -- /abs/path/Importer.res ./api.ts getUser

# The survey above:
cargo run --release --manifest-path ts-import/Cargo.toml --example survey -- /abs/project/Importer.res react node:fs

# This page:
cd ts-import/site && npm ci && npm run build:wasm && npm run build
```
