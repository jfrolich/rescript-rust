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

To see which gaps matter, every export of twelve modules was imported: `react`, `react-dom`, `semver`, `chalk`, `vite` and seven Node built-ins (`fs`, `path`, `url`, `child_process`, `os`, `events`, `http`). That is 603 values and 3,075 types (react 19.3, vite 8.3), and all twelve compile. 78% of the declarations have an exact ReScript type. The other 22%, 808 declarations, carry at least one note.

### The gaps and how to close them

One row per gap, with the solution this document proposes, what it needs, and where it stands. *Converter* is work in the import alone: the ReScript it would generate compiles today. *Language* is a change to ReScript, described under [language changes](#language-changes). A declaration can have several gaps, so the shares add up to more than 22%. The unions are split by cause, because each cause has its own solution. Each of the 305 union declarations that remain is counted under one cause, by the TypeScript type its note quotes.

| Gap | Declarations | Imported today as | Solution | Needs | Status |
|---|---|---|---|---|---|
| **Unions** | **8.3%** | | | | |
| Members share a tag: vite's syntax tree, where six members say `type: "Literal"` | closed | A variant | [Each member a case](#members-that-share-a-tag); another field tells apart the members that share a tag | language: object cases, then converter | done |
| Library interfaces: `EventEmitter \| EventTarget`, `boolean \| AddEventListenerOptions`, `EventListener \| EventListenerObject`, `ArrayBufferLike` | 2.4% | `unknown` | [Import the interfaces as records and function types](#library-interfaces); object cases then tell them apart | converter | not started |
| React's own types: `ReactNode`, in 70 declarations | 2.1% | `unknown` | [A table of known React types](#library-interfaces): `React.element` | converter | not started |
| Plain objects without a tag: `{result} \| {error}`, `{value: string} \| {value: number}` | closed | A variant | Object cases, told apart by a field that is present or by its kind | language: object cases | done |
| Arguments of an event listener: `[] \| [err: Error] \| [chunk: Buffer]` | 1.1% | `unknown` | [A GADT of the event names](#event-maps): each name fixes the arguments | converter | not started |
| Nothing tells the members apart: `T \| PromiseLike<T>`, `U \| readonly U[]`, two function types | 1.2% | `unknown` | [An opaque type](#nothing-tells-the-members-apart) with a conversion to and from each member | converter | not started |
| Members merged into one case disagree on a field's type | 0.5% | A variant; the field is `unknown` | The join of the types: `string` for a literal and a string, a variant where one exists | converter | done for literals and nullable types; the rest not started |
| `object` or `{}` as a member: `object \| RuleProps`, `AddressInfo \| {}` | 0.2% | `unknown` | An open object case, tested last | converter | not started |
| Others: CSS property types of React's `style`, merged members whose fields mention a type variable | 0.8% | `unknown` | Not examined one by one | | |
| `string \| symbol`, unions of classes (`Car \| Vehicle`, `Readable \| Writable`) | | | `@typeOf("symbol")`; [classes on records](#classes-on-records) | language | done |
| **Other gaps** | | | | | |
| `any` | 9.1% | A type variable as an argument, `unknown` as a result | None. `any` is a hole in the TypeScript, not in ReScript. | | stays |
| Overloads | 5.9% | The first signature | [One external per signature](#overloads), named after what it adds | converter | not started |
| Constraint on a type parameter (`T extends U`) | 3.2% | An unconstrained type variable | [The bound](#type-parameters) when the parameter is in one argument only; otherwise a bounded type variable | converter, then language | not started |
| Rest parameter in a callback type | 3.4% | One array argument | [A wrapper type](#standard-library-types) that turns the arguments into an array | standard library | not started |
| Constructor types, classes as values | 2.2% | `unknown` | [A constructor type](#standard-library-types) with `Reflect.construct` | standard library | not started |
| Conditional, mapped and indexed types over a type parameter | 2.4% | The constraint, or `unknown` | A GADT of keys where the parameter ranges over the keys of a known type ([event maps](#event-maps)); the rest stays | converter | not started |
| Enum and namespace objects as values | 2.0% | Skipped | [A module](#namespaces-and-enum-objects) with one value per member | converter | not started |
| Tuples with optional or rest elements, one-element tuples | 2.2% | `array` | Most are the arguments of event listeners: [event maps](#event-maps). One-element tuples stay arrays. | converter | not started |
| Generic function type inside another type | 1.8% | `unknown` for its own type parameters | [An unboxed record](#generic-function-types) with a polymorphic field | converter | not started |
| Type parameter out of scope where the type is declared | 1.8% | `unknown`, or the constraint | Mostly the event name of an event map: [event maps](#event-maps). The rest as generic function types. | converter | not started |
| Explicit `this` parameter | 1.2% | Dropped | `@this` | converter | not started |
| `object` and `{}` | 1.2% | `unknown` | The open object type `{..}` for `object`; `{}` (any value but `null` and `undefined`) stays `unknown` | converter | not started |
| Functions with properties | 0.9% | The function | [A module](#functions-with-properties) with the call and one accessor per property | converter | not started |
| Named properties next to an index signature | 0.7% | The named properties | [A record with a `dict` remainder](#a-record-with-a-dict-remainder) | language | not designed |
| `never` outside a result | 0.5% | `unknown` | [A type without values](#standard-library-types) | standard library | not started |
| Branded primitives (`string & {__brand: "Id"}`) | 0.3% | The primitive | [A single-case unboxed variant](#branded-primitives) | converter | not started |

If every row but `any` and the types TypeScript cannot compute is closed, about 89% of the declarations would be exact, against 78% today. The 89% is an estimate from an earlier run of the survey, in which each note was assigned to the solution that would remove it.

Two things the survey does not measure come before any of these rows, because they decide whether an import can be trusted at all: [type parameters](#type-parameters) that let a caller choose a result type silently, and [names](#stable-names) that can change between two versions of a library.

## Language changes

Five of the solutions need a change to ReScript. Everything else in the table is converter or standard-library work.

| Change | Status | What it closes |
|---|---|---|
| [Classes on records](#classes-on-records) | implemented, Rust compiler only | Unions of classes, with the fields of the class readable. Together with `symbol` cases, 39 fewer unions with a note in the survey. |
| [Object cases told apart by their fields](#object-cases-told-apart-by-their-fields) | implemented, Rust compiler only | Unions of plain objects and of members that share a tag. Measured: the declarations with a union note went from 535 to 305, and vite's syntax tree is a variant of 165 cases. Library interfaces follow once they are records. |
| [Shared tags on tagged variants](#shared-tags-on-tagged-variants) | specified, being implemented | The same unions as object cases, without the tag written as a field of every case. It changes no count; it changes what the imported type looks like. |
| [Bounded type variables](#bounded-type-variables) | specified | Constraints where the parameter also decides the result, such as `pipe<T extends Writable>(destination: T): T`. Part of the 3.2%. |
| [A record with a `dict` remainder](#a-record-with-a-dict-remainder) | not designed | Named properties next to an index signature, 0.7%. |

These were considered and are not needed, because the converter or the standard library covers them with ReScript that compiles today: two record fields with one JavaScript name (overloaded methods become `@send` externals), polymorphic function types outside record fields (an unboxed record with one field), a constructor type and an empty type (standard-library types), and `@variadic` on function types (a wrapper; the language change would only save the wrapper's closure at run time).

### Classes on records

Status: implemented, in the Rust compiler only.

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

### Object cases told apart by their fields

Status: implemented, in the Rust compiler only. The OCaml compiler rejects a variant with two object cases.

An `@unboxed` variant can have one case whose payload is a plain object, because `typeof` answers `"object"` for all of them. This change allows several, when a field shows which one a value is.

```rescript
@unboxed
type outcome =
  | Ok({result: string})
  | Failed({error: string, code?: int})

let message = outcome =>
  switch outcome {
  | Ok({result}) => result
  | Failed({error}) => error
  }
```

```js
function message(outcome) {
  if ("result" in outcome) {
    return outcome.result;
  } else {
    return outcome.error;
  }
}
```

**Object cases.** A case whose payload is a record or an inline record is a *closed* object case: its fields are known. Its *required* fields are the ones that are not optional. A case whose payload is a `dict`, an object type `{"x": int}` or a type declared `@typeOf("object")` is an *open* object case. A variant may have any number of closed object cases and at most one open one.

**Checks.** A check looks at one field `f` of the value `x`. A case *passes* a check when every value of the case does, and *fails* it when no value of the case does.

| Check | JavaScript | A case passes when | A case fails when |
|---|---|---|---|
| presence | `"f" in x` | `f` is required | it does not declare `f` |
| literal | `x.f === "circle"` | `f` is required and its type has only that literal | it does not declare `f`, or the type of `f` cannot be that literal |
| kind | `typeof x.f === "string"`, `Array.isArray(x.f)` | `f` is required and every value of its type has that kind | it does not declare `f`, or no value of the type of `f` has that kind |

The literals of a type are those of a polymorphic variant without payloads (`[#circle | #square]`), of a variant without payloads, and `true` and `false` for `bool`. A literal check tests every literal of the field's type: `x.kind === "a" || x.kind === "c"` for `kind: [#a | #c]`. The kind of a field is the set of answers `typeof` can give for its values. `string` has one answer. `Null.t<string>` has two, `"object"` for `null` and `"string"`; `option<string>` has `"undefined"` and `"string"`; an `@unboxed` variant has those of its cases. Arrays are kept apart from other objects, for `Array.isArray`. A case passes a kind check when its field has that one answer, and fails it when the answer is not among its field's. A type variable, an abstract type and `unknown` have no known answers and take no part in kind checks. An optional field gives its own case no check, but a case that declares it does not fail a presence check on it.

**Order.** The compiler picks a case that has a test every other remaining case fails, tests it first, and goes on with the rest. A test is one check, or several joined with `&&` when no single one is enough; a joined test keeps only the checks it needs. The last case is not tested. Where there is a choice: the earlier case in the declaration, then a literal check before a presence check before a kind check, then the earlier field. An open case declares no fields, so it fails every presence check and is always last.

| Declaration | Tests, in order |
|---|---|
| `Ok({result: string}) \| Failed({error: string})` | `"result" in x` |
| `Text({value: string}) \| Number({value: float})` | `typeof x.value === "string"` |
| `Maybe({value: option<string>}) \| Number({value: float})` | `typeof x.value === "number"`: `Maybe` has no test of its own |
| `Named({name: string}) \| Person({name: string, age: float})` | `"age" in x`: the case with more fields first |
| `Element(element) \| Portal(portal) \| Other(dict<unknown>)` with `portal` = `element` plus `children` | `"children" in x`, then `"props" in x` |
| `A({kind: [#a], x: int}) \| B({kind: [#b], x: int})` | `x.kind === "a"` |

**No order.** Two cases with the same fields at the same kinds cannot be told apart: `A({x: int}) | B({x: int})`. The declaration is rejected with the message both compilers already give for two object cases: "At most one case can be an object type." Two open cases are rejected the same way.

**Where the tests go.** Where the test of the single object case is today: after the literal cases, the primitive kinds and the class instances, and guarded against `null` as it is today. A `switch` that does not name every case tests only the ones it names.

**Many cases.** When one field's literals tell most of the cases apart, the tests are a `switch` on that field. The field is the one that is a set of literals in the most cases, and the switch is used when those cases have at least four different literals on it. Cases that share a literal are told apart inside its arm, with their other checks; cases without a literal on the field are tested under `default`. Smaller variants keep the `if` chain.

```js
function name(node) {
  switch (node.type) {
    case "Literal":
      if (typeof node.value === "string") {
        return node.value; // StringLiteral
      } else if ("raw" in node) {
        return node.value.toString(); // NumericLiteral
      } else {
        return node.regex.pattern; // RegExpLiteral
      }
    case "Identifier":
      return node.name;
    case "ThisExpression":
      return "this";
    case "Super":
      return "super";
    default:
      return "..." + name(node.argument); // SpreadElement, the last case
  }
}
```

A `switch` over all 165 cases of vite's syntax tree is one `switch (node.type)` with 165 labels. The longest `if` chain inside an arm has five tests, for the six kinds of `"Literal"`.

**What is trusted.** A record built in ReScript has its declared fields and no others, so for those values the tests are exact. A value that comes from JavaScript can carry more: an object that TypeScript calls `{error: string}` may also have a `result`. TypeScript's own `in` narrowing makes the same assumption. As everywhere in untagged variants, recognition trusts the type.

**Interfaces.** The tests follow from the declaration alone, so an interface and its implementation agree on them when they agree on the cases, as they must already. A `switch` in another module works out the same tests from the declaration.

**In the import.** A union of object types becomes one case per member when an order exists. A named interface is a case with that record (`Done(done)`). An unnamed member is an inline record, named after its tag literal when it has one (`{type: "Empty"}` is `Empty`), and else after its first required field that no other member has: `{result: string} | {error: string}` is `Result({result: string}) | Error({error: string})`. Members with the same fields are one case. Members that no check separates are merged into one case when they share a tag (see [members that share a tag](#members-that-share-a-tag)); a union whose members all merge is that one record. A union with no order is still `unknown`; the [opaque type](#nothing-tells-the-members-apart) for it is not built.

<!-- example: shapes -->
```rescript
module Jobs = %ts("./jobs.ts")

let message = job =>
  switch Jobs.run(job) {
  | Done({result}) => result
  | Failed({error, ?code}) =>
    switch code {
    | Some(code) => `${error} (${Float.toString(code)})`
    | None => error
    }
  }
```
<!-- /example -->

**Measured.** On the twelve surveyed modules, without and with object cases in the import: the declarations with a union note go from 535 to 305, and the declarations with any note from 1,003 to 808. The number of types goes from 2,419 to 3,075, because the members of a union that was `unknown` are now declared. Converting vite takes as long as before within the noise of the runs: 0.27 to 0.43 s with, 0.26 to 0.43 s without, in runs taken one after another.

### Shared tags on tagged variants

Status: specified, being implemented in the Rust compiler only.

With object cases, a union whose members share a tag is an `@unboxed` variant, and the tag is an ordinary field of every case: `StringLiteral({@as("type") type_: [#Literal], value: string})`. The field has to be written again wherever a value is built: `Super({type_: #Super, start: 3})`. A `@tag` variant writes the tag for you, but rejects two cases with the same tag ("Duplicate literal Literal."). This change allows them.

```rescript
@tag("type")
type node =
  | @as("Literal") StringLiteral({value: string})
  | @as("Literal") NumericLiteral({value: float})
  | @as("ThisExpression") This({start: int})
  | @as("Super") Super({start: int})

let name = node =>
  switch node {
  | StringLiteral({value}) => value
  | NumericLiteral({value}) => Float.toString(value)
  | This(_) => "this"
  | Super(_) => "super"
  }

let made = Super({start: 3}) // {type: "Super", start: 3}
```

```js
function name(node) {
  switch (node.type) {
    case "Literal":
      if (typeof node.value === "string") {
        return node.value;
      } else {
        return node.value.toString();
      }
    case "ThisExpression":
      return "this";
    case "Super":
      return "super";
  }
}
```

- **Which cases.** Cases whose payload is an inline record may share a tag. A case without a payload is the tag itself at run time (`"Super"`, not an object), and a case with a tuple payload keeps its values under `_0`, `_1`; neither can share a tag.
- **Telling them apart.** The cases that share a tag are object cases among themselves: the compiler finds an order and tests by the [rules above](#object-cases-told-apart-by-their-fields), on the fields other than the tag. The last one is not tested.
- **No order.** Two cases with the same tag and the same fields at the same kinds are rejected, with the message for a duplicate tag that both compilers give today.
- **Dispatch.** The tag is tested first, as for any tagged variant; the tests on fields run inside the arm of a shared tag. A `switch` that names some of the cases of a tag tests only those.
- **Everything else is unchanged**: building a value, exhaustiveness, a variant where no tag is shared.

**In the import.** A union of objects that all have one property holding a literal is a `@tag` variant, as before; members with the same literal become cases with the same `@as`, named after their interfaces. A member with no other property is a case with an empty record, `Point({})`, which is the object `{kind: "point"}`; a case without a payload would be the bare string.

One thing is lost against the `@unboxed` form. There a case holds the member's own record (`Identifier(identifier)`), which can be passed to a function that takes that member. The fields of a tagged case are an inline record, which cannot leave the `switch` as a value.

### Bounded type variables

Status: specified, not implemented. The syntax is `@bound(: type as 'variable)` on an external; it may change once it is used.

```ts
function pipe<T extends Writable>(source: Readable, destination: T): T
```

This is imported as `(readable, 'destination) => 'destination`, which ReScript lets you call with anything. The bound is checked by TypeScript and assumed by the JavaScript, so it should be checked here too, without giving up the precise result type.

The smallest version is a bound on a type variable of an `external`, checked where the external is used:

```rescript
@bound(: writable as 'destination)
external pipe: (readable, 'destination) => 'destination = "pipe"

let socket = pipe(file, socket) // 'destination is the socket's class; it extends writable
let wrong = pipe(file, "text")  // error: string is not a writable
```

- At each use, the type the variable was given must coerce to the bound, by the rules of `:>`. With classes on records that includes a declared subclass.
- A variable that nothing else decides is the bound.
- A bound that is an object type needs none of this: `({.. "id": string} as 'item)` exists.

The converter closes most constraints without it: a bounded type parameter that occurs in one argument and not in the result is imported as its bound (see [type parameters](#type-parameters)). This change is for the rest, where the parameter also decides the result.

### A record with a `dict` remainder

Status: not designed.

`{[header: string]: string; accept?: string}` has named properties and an index signature. It is imported today with the named properties only. It needs a record type whose other fields are a `dict`. Node's HTTP headers are the main case.



## Converter and standard-library work

Every encoding in this section was compiled with the current compiler. Apart from [members that share a tag](#members-that-share-a-tag), none of it is implemented in the import yet. Several of the ideas come from [rescript-bindgen](https://github.com/juspay/rescript-bindgen), a generator of ReScript bindings for React component packages that also reads types through the TypeScript checker: the rule for type parameters, names of overloads, conversions in both directions on opaque types, functions with properties as modules, branded types, a table of known React types, stable names and a corpus of pinned packages.

### Type parameters

Today every type parameter becomes a type variable. That is wrong in two places.

**Only in the result.** `json<T>(): Promise<T>` is imported as `unit => promise<'t>`. ReScript infers `'t` from the use, so `let user: user = await json()` compiles, and nothing at the call shows that the type was chosen there. TypeScript lets the caller choose `T` too, but writes it at the call (`json<User>()`). In an earlier run of the survey, 24 of 585 functions had a type variable only in their result. Most are constructors and hooks, where choosing is the point (`new EventEmitter<Events>()`, `createRef<T>()`): there the variable is a type argument of the returned type. The rule: a variable that is a type argument of the returned type stays a variable; a variable that is the result, or the element of a promise, an array or a tuple in it, becomes `unknown`, with a note.

**With a bound, in one argument.** `greet<T extends string>(name: T): void` is imported as `'t => unit`, which accepts anything. A bounded parameter that occurs in one argument and not in the result is its bound: `string => unit`. Where it also occurs in the result, the variable is kept with a note until [bounded type variables](#bounded-type-variables) exist.

### Stable names

Generated types are named after where they are first met (`parkWhat`, `refAttributesRef`) and get a number on a collision (`dict2`, `ref2`). A new version of a library can change the order of conversion and so rename a type that user code refers to. A name should depend on the TypeScript declaration alone: the declaration's own name, else the path from the nearest named declaration (`socket.on.listener`), and on a collision the module it comes from, never a counter. rescript-bindgen keeps a committed file of the names it gave out; an import inside the compiler has no such file, so the scheme itself has to be stable.

### Members that share a tag

The syntax tree of vite's parser is a union of 183 interfaces tagged by `type`, and several tags are used by more than one interface. A `@tag` variant needs one case per tag, so it cannot hold this union. Without a type for it, the `parent` of every node is `unknown` too.

```ts
interface StringLiteral { type: "Literal"; value: string; raw: string | null }
interface NumericLiteral { type: "Literal"; value: number; raw: string | null }
interface RegExpLiteral { type: "Literal"; value: RegExp | null; regex: Regex }
interface IdentifierName { type: "Identifier"; name: string }
type Node = StringLiteral | NumericLiteral | RegExpLiteral | IdentifierName // and 179 more
```

With object cases, every member is a case. The tag is a literal check, and where members share a tag another field decides:

```rescript
@unboxed
type node =
  | StringLiteral({@as("type") type_: [#Literal], value: string, raw: Null.t<string>})
  | NumericLiteral({@as("type") type_: [#Literal], value: float, raw: Null.t<string>})
  | RegExpLiteral({@as("type") type_: [#Literal], value: Null.t<RegExp.t>, regex: regex})
  | IdentifierName({@as("type") type_: [#Identifier], name: string})
```

```js
if (typeof x.value === "string") { /* StringLiteral */ }
else if ("raw" in x) { /* NumericLiteral */ }
else if (x.type === "Literal") { /* RegExpLiteral */ }
else { /* IdentifierName */ }
```

That is what the compiler generates. Building and reading are both exact, and the cases keep their TypeScript names.

Some members that share a tag differ in no field a check can see. `ArrayPattern` and `ArrayAssignmentTarget` are both `{type: "ArrayPattern", elements: [...]}`; only the types of the elements differ. They become one case. A field every member has is required, and a field only some have is optional. A field whose types differ gets their join where there is one: `string` for `"width" | "height"` and `string`, `Null.t<float>` for `number` and `number | null`. Without a join it is `unknown`, with a note.

The import does this. The 183 members of vite's tree become the variant `node` with 165 cases, 11 of them merged from several members, and `parent` has that type. A merged case is named after the tag its members share (`ArrayPattern`) and takes the type variables its fields mention as parameters. The string, number, boolean and null literals stay four cases, because `value: null` has a kind too.

### Library interfaces

Three kinds of type from declaration files come out as an abstract type or as `unknown` today, and take every union they are in with them:

- Interfaces of the DOM library that only carry data (`AddEventListenerOptions`) or are a function (`EventListener`). Imported as records and function types, `boolean | AddEventListenerOptions` is an ordinary variant.
- Interfaces that a class implements (`NodeJS.ReadableStream`, `WritableStream`). Imported as records, object cases tell them apart by a method one has and the other does not (`read`, `write`).
- A class that is also a namespace, such as `EventEmitter` of `node:events`, the superclass of every stream and server.

React's types are a case of their own. A user of `@rescript/react` expects `React.element`, `ReactEvent.Mouse.t`, `React.ref<Nullable.t<Dom.element>>`, `JsxDOM.style` and `Dom.element`, not a structural import of `@types/react`. A table maps those TypeScript types to the existing ReScript types before the converter walks them. The survey cannot show what this is worth, but for React code it matters more than any single row.

### Event maps

```ts
interface SocketEvents { close: []; data: [chunk: Buffer]; error: [err: Error] }
class Socket {
  on<E extends keyof SocketEvents>(event: E, listener: (...args: SocketEvents[E]) => void): this
}
```

`SocketEvents[E]` has no value before `E` is known, so today the listener takes `array<unknown>`, with several notes. But `E` ranges over three names, and each name fixes the listener. That is a GADT whose constructors are the names:

```rescript
type rec socketEvent<_> =
  | @as("close") Close: socketEvent<unit => unit>
  | @as("data") Data: socketEvent<buffer => unit>
  | @as("error") Error: socketEvent<JsError.t => unit>

type rec socket = {on: 'listener. (socketEvent<'listener>, 'listener) => socket}

socket.on(Data, chunk => Console.log(chunk)) // socket.on("data", chunk => ...)
```

This is the `on`, `once` and `emit` of every stream, socket and server of Node: 3,434 of the 11,014 notes of the survey, almost a third. It changes few declarations from inexact to exact, because the same methods also take `any`. The same encoding covers `get<K extends keyof T>(key: K): T[K]` and overloads that differ only in a literal first argument.

### Nothing tells the members apart

Where no check separates the members, as in `T | PromiseLike<T>`, the union is an abstract type with a conversion from each member, for values ReScript passes in, and a reader to each member, for values the library hands back. The caller uses a reader after establishing which member it has, as in TypeScript after a type guard.

```rescript
module Awaitable = {
  type t<'t>
  external fromValue: 't => t<'t> = "%identity"
  external fromPromise: promise<'t> => t<'t> = "%identity"
  external asValue: t<'t> => 't = "%identity"
  external asPromise: t<'t> => promise<'t> = "%identity"
}
```

With this fallback no union is imported as `unknown`.

### Overloads

Each signature becomes an external. The first keeps the name; the others are named after what they add: a parameter (`parseWithRadix`), or, for signatures of the same length, the first parameter whose type differs (`wrapForCount`). An overloaded method becomes `@send` externals next to the record, because a record cannot have two fields with one JavaScript name.

```rescript
@module("./api.ts") external parse: string => float = "parse"
@module("./api.ts") external parseWithRadix: (string, float) => float = "parse"
@send external write: (writable, string) => bool = "write"
@send external writeWithEncoding: (writable, string, string) => bool = "write"
```

### Functions with properties

i18next's `t` and an axios instance are functions with properties. Today the properties are dropped. Instead the type is a module with the call as a conversion and one accessor per property:

```rescript
module Translator = {
  type t
  external asFn: t => (string => string) = "%identity"
  @get external locale: t => string = "locale"
  @send external setLocale: (t, string) => unit = "setLocale"
}

let hello = Translator.asFn(t)("hello") // t("hello")
```

### Generic function types

A function type with type parameters of its own can only be a record field in ReScript. An unboxed record with one field is that function at run time:

```rescript
@unboxed type eachVisit = {call: 'item. array<'item> => array<'item>}
external each: eachVisit => unit = "each"

each({call: items => items->Array.toReversed}) // each(items => items.toReversed())
```

### Namespaces and enum objects

`export namespace constants { ... }`, `fs.promises` and the object of an `enum` are values. Each becomes a module whose members are externals with `@scope`:

```rescript
module Promises = {
  @module("node:fs") @scope("promises") external readFile: string => promise<string> = "readFile"
}
```

### Branded primitives

`type UserId = string & {__brand: "user"}` is imported as `string`, so any string is a user id. A single-case unboxed variant keeps it distinct at no cost:

```rescript
@unboxed type userId = UserId(string)

let UserId(raw) = lookup(UserId("u1")) // lookup("u1")
```

### Standard-library types

```rescript
// `typeof EventEmitter`: a value that is called with `new`.
type constructor<'args, 'instance>
@val @scope("Reflect")
external construct: (constructor<'args, 'instance>, 'args) => 'instance = "construct"

// `(...args: string[]) => void` as a callback: JavaScript passes any number
// of arguments, ReScript receives them as one array.
type variadic<'arg, 'result>
let variadic: (array<'arg> => 'result) => variadic<'arg, 'result> // f => (...args) => f(args)

// `never`
type never
```

`variadic` is the only solution here that adds code at run time, a wrapper around the callback.

### Order of work

1. **Library interfaces as records and the table of React types.** Together 4.6% of the declarations, more than half of the unions that remain.
2. **Type parameters and stable names.** They change no count, but today an import can be wrong without a note, and a library upgrade can rename a type.
3. **Event maps.** A third of all notes.
4. **Overloads, namespaces and constructors**: about 10% of the declarations touched, all converter or standard-library work.
5. **A corpus of pinned packages** with their output and notes kept as a baseline, so that a change which stops one compiling, or adds notes, fails a test. Today the survey runs on whatever is installed.
6. The remaining rows, then bounded type variables and the `dict` remainder.

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
