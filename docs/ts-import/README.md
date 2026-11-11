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
| Union whose members cannot be told apart at run time | 18.1% | `unknown` | Steps 1 to 3 of the [plan](#plan-bridging-the-rest). |
| `any` | 9.9% | A type variable as an argument, `unknown` as a result | Nothing: `any` is a hole in the TypeScript, not in ReScript. |
| Overloads | 6.9% | The first signature | Step 5: one external per signature (`parse`, `parse2`). |
| Constraint on a type parameter (`T extends U`) | 3.8% | An unconstrained type variable | Step 13: bounded type variables. For object bounds the open object type `{.. "id": string}` already exists, but not for records. |
| Rest parameter in a callback type | 3.5% | One array argument | Step 11: a wrapper type in the standard library, or `@variadic` on function types. |
| Constructor types, classes as values | 2.8% | `unknown` | Step 10: a constructor type in the standard library. |
| Conditional, mapped and indexed types over a type parameter | 2.8% | The constraint, or `unknown` | Step 8 where the parameter is a key of a known object type. Otherwise import at an instantiation, `%ts("./m.ts#Pick<User, 'id'>")`, which TypeScript can evaluate. |
| Enum and namespace objects as values | 2.5% | Skipped (the enum's type is imported) | Step 4: a module with one value per member. |
| Tuples with optional or rest elements, one-element tuples | 2.3% | `array` | Step 8 for a tuple that is a rest parameter: its elements become the arguments. Step 14 for the rest. |
| Generic function type nested in a type | 2.1% | `unknown` for its own type parameters | Step 9: an unboxed record with a polymorphic field. |
| Type parameter out of scope where the type is declared | 2.1% | `unknown`, or the constraint | Steps 8 and 9. |
| Explicit `this` parameter | 1.1% | Dropped | Step 7: `@this` already expresses it. |
| `object` and `{}` | 1.0% | `unknown` | Step 14. |
| Functions with properties | 1.0% | The function | Step 6: an abstract type that converts to the function and to a record of its properties. |
| Named properties next to an index signature | 0.7% | The named properties | Step 14. Language: a record with a `dict` remainder. |
| `never` outside a result | 0.6% | `unknown` | Step 12: a type without values in the standard library. |
| Branded primitives (`string & {__brand: "Id"}`) | 0.3% | The primitive | Converter: `type id = private string`. |

Two kinds of union that used to be in the first row are imported exactly now: `string | symbol` (124 declarations, all event names and property keys) and unions of classes such as `Readable | Writable` or `Car | Vehicle`. What is left, 522 declarations, is not one problem:

- **Tagged unions that share a tag** (about 180). The syntax tree `Node` of vite's parser is a union of interfaces tagged by `type`, where six of them say `type: "Literal"` and six more `type: "Identifier"`. A `@tag` variant needs distinct tags.
- **More than one plain object.** React's `ReactNode` (about 70), `{result} | {error}`, `AddressInfo | {}`. Nothing at run time tells two plain objects apart unless a field does; the upstream proposal for that is objects told apart by a field they share (rescript-lang/rescript issue 7988).
- **Library interfaces** (about 140). `NodeJS.ReadableStream | WritableStream`, `EventEmitter | EventTarget`, `EventListener | EventListenerObject`, `boolean | AddEventListenerOptions`, `T | PromiseLike<T>`. TypeScript declares these as interfaces, so nothing says which class to test for, and the import makes a library interface an abstract type. The DOM option objects could be records; the converter does not do that yet.
- **Unions of tuples** (about 40): the arguments of an event listener, `[] | [err: Error] | [chunk: any]`.

None of the four needs a new language feature to be imported: steps 1 to 3 and 8 of the [plan](#plan-bridging-the-rest) cover them with ReScript that compiles today.

## Plan: bridging the rest

66.5% of the surveyed declarations are imported exactly today. This is a plan to reach about 89.5%. What stays out is `any` (9.9% of the declarations: a hole in the TypeScript, not in ReScript) and types computed from a type parameter that TypeScript cannot evaluate before the parameter is known (0.6%).

Most of the distance is converter work. Seventeen of the twenty-three points need no change to the language or the standard library: the ReScript to generate exists, and every encoding shown below compiles with the current compiler. None of the steps is implemented yet.

| # | Step | Needs | Declarations made exact | Exact after |
|---|---|---|---|---|
| | Today | | | 66.5% |
| 1 | Members of a union that share a tag become one case | converter | 182 | 72.8% |
| 2 | Library types that are imported as nothing today | converter | 84 | 75.7% |
| 3 | Members that cannot be told apart become one opaque case | converter | 78 | 78.4% |
| 4 | Namespaces and enum objects as modules | converter | 72 | 80.9% |
| 5 | One external per overload | converter | 50 | 82.7% |
| 6 | Functions with properties | converter | 20 | 83.4% |
| 7 | `this` parameters as `@this` | converter | 10 | 83.7% |
| 8 | Generics over the keys of an object type as a GADT of keys | converter | 3 | 83.8% |
| 9 | Generic function types as unboxed records | converter | 0 | 83.8% |
| 10 | Constructors as values | standard library | 77 | 86.5% |
| 11 | Callbacks with a rest parameter | standard library | 15 | 87.0% |
| 12 | A type without values for `never` | standard library | 4 | 87.1% |
| 13 | Bounded type variables | language | 22 | 87.9% |
| 14 | `{}` and `object`, index signatures beside named properties, one-element tuples, deeper nesting | language and converter | 46 | 89.5% |

A step's count is the number of declarations whose last note it removes, in this order. That understates steps 8, 9 and 11, which share declarations with each other and with `any`. Counted by notes (the places in a type where something is lost) step 8 removes 3,434 of the 11,014 notes, almost a third: they are the `on`, `once` and `emit` methods of every stream, socket and server of Node.

The counts are estimates. Each note of the survey was assigned to the step that would remove it, by its kind and the TypeScript type it quotes. Step 2 is the least certain, because its causes have not been looked at one by one.

### 1. Members that share a tag

The syntax tree of vite's parser is a union of 183 interfaces tagged by `type`. Thirteen tags are used by more than one interface, 37 interfaces in all, and that is enough to make the whole union `unknown`, and with it the `parent` of every node.

```ts
interface StringLiteral { type: "Literal"; value: string; raw: string | null }
interface NumericLiteral { type: "Literal"; value: number; raw: string | null }
interface IdentifierName { type: "Identifier"; name: string }
type Node = StringLiteral | NumericLiteral | IdentifierName // and 180 more
```

Members with the same tag become one case. A field they all have gets the union of its types, a field only some have is optional:

```rescript
@unboxed type literalValue = String(string) | Number(float)

@tag("type")
type node =
  | @as("Literal") Literal({value: literalValue, raw: Null.t<string>})
  | @as("Identifier") Identifier({name: string})
```

Every value TypeScript allows has this type, so reading is exact. Building is not quite: the merged case also accepts a literal whose fields belong to two different members.

### 2. Library types

Three kinds of type from declaration files come out as an abstract type or as `unknown` today, and take every union they are in with them:

- A class that is also a namespace, such as `EventEmitter` of `node:events`, the superclass of every stream and server.
- Interfaces of the DOM library that only carry data (`AddEventListenerOptions`) or are a function (`EventListener`). They should be records and function types; `boolean | AddEventListenerOptions` is then an ordinary variant.
- Interfaces that a class implements (`NodeJS.ReadableStream`). Where nothing names the class they fall under step 3.

### 3. One opaque case

`ReactNode` has two members that are plain objects and one that is any iterable. JavaScript cannot tell them apart, so neither can a variant. Today the whole union is `unknown`. Instead, the members that share a runtime test become one case with an abstract payload, and each of them converts to it:

```rescript
@typeOf("object") type reactNodeObject
external element: reactElement => reactNodeObject = "%identity"
external iterable: iterable<'node> => reactNodeObject = "%identity"

@unboxed
type rec reactNode =
  | String(string)
  | Number(float)
  | BigInt(bigint)
  | Boolean(bool)
  | Promise(promise<reactNode>)
  | Object(reactNodeObject)
  | @as(null) Null

let child = Object(element(someElement))
```

Building a value is exact, and a `switch` tells apart everything JavaScript can. It stops at `Object`, as JavaScript does. A union with a bare type parameter (`T | PromiseLike<T>`) is opaque as a whole: an abstract type with one conversion per member. With this step no union is imported as `unknown` any more.

### 5. Overloads

Each signature becomes an external: `write` and `write2`. For an overloaded method they are `@send` externals next to the record, because a record cannot have two fields with one JavaScript name.

### 8. Generics over the keys of an object type

```ts
interface SocketEvents { close: []; data: [chunk: Buffer]; error: [err: Error] }
class Socket {
  on<E extends keyof SocketEvents>(event: E, listener: (...args: SocketEvents[E]) => void): this
}
```

`SocketEvents[E]` has no value before `E` is known, so today the listener takes `array<unknown>` and the method carries several notes. But `E` ranges over three names, and each name fixes the listener. That is a GADT whose constructors are the keys:

```rescript
type rec socketEvent<_> =
  | @as("close") Close: socketEvent<unit => unit>
  | @as("data") Data: socketEvent<buffer => unit>
  | @as("error") Error: socketEvent<JsError.t => unit>

type rec socket = {on: 'listener. (socketEvent<'listener>, 'listener) => socket}

socket.on(Data, chunk => Console.log(chunk)) // socket.on("data", chunk => ...)
```

The same covers `get<K extends keyof T>(key: K): T[K]` and overloads that differ only in a literal first argument.

### 9. Generic function types

A function type with type parameters of its own can only be a record field in ReScript. An unboxed record with one field is that function at run time:

```rescript
@unboxed type eachVisit = {call: 'item. array<'item> => array<'item>}
external each: eachVisit => unit = "each"

each({call: items => items->Array.toReversed}) // each(items => items.toReversed())
```

### 10 to 12. The standard library

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

`variadic` is the only step that adds code at run time, a wrapper around the callback. The alternative is in the language: `@variadic` on a function type, with the compiler emitting the rest parameter.

The language steps are specified in the next section.

## Language changes

The plan needs three changes to the language. One is implemented, one is specified here in full and is next, one is a sketch.

| Change | Status | What it covers |
|---|---|---|
| [Classes on records](#classes-on-records) | implemented | Unions of classes: `Car \| Vehicle \| string`, `Readable \| Writable`, with the fields of the class still readable. |
| [Object cases told apart by their fields](#object-cases-told-apart-by-their-fields) | specified, not implemented | Unions of plain objects: `{result} \| {error}`, React's `ReactNode`, same-tag members that differ in one field. About 85 declarations become cases a `switch` can open instead of one opaque case (step 3), and step 1 becomes exact for building too. |
| [Bounded type variables](#bounded-type-variables) | sketch | `T extends Writable`: 86 declarations have a constraint, and for 22 it is the last thing missing (step 13). |

The counts for the two that are not implemented are estimates from the survey's notes; they are measured once the import uses the change.

Three things the earlier version of this document listed as language changes turn out not to need one:

- **Overloaded methods.** A record cannot have two fields with one JavaScript name, but `@send` externals next to the record can: `write` and `write2` (step 5).
- **Generic function types and constructor types.** An unboxed record with a polymorphic field (step 9), and a type in the standard library (step 10).
- **Rest parameters in callbacks.** A wrapper in the standard library (step 11).

Named properties beside an index signature (`{[header: string]: string; accept?: string}`, 20 declarations) would need a record with a `dict` remainder. It is not designed here.

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

Status: specified, not implemented.

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
| kind | `typeof x.f === "string"`, `Array.isArray(x.f)` | `f` is required and its type has that kind | it does not declare `f`, or the type of `f` has another kind |

The literals of a type are those of a polymorphic variant without payloads (`[#circle | #square]`), of a variant without payloads, and `true` and `false` for `bool`; a check may test several of them. The kinds are the ones an untagged variant already tells apart for a payload: string, number, bigint, boolean, function, array, object. A field whose type is none of these (an option, a type variable, an abstract type) takes no part in literal or kind checks.

**Order.** The compiler picks a case that has a test every other remaining case fails, tests it first, and goes on with the rest. A test is one check, or several joined with `&&` when no single one is enough. The last case is not tested. Where there is a choice: the earlier case in the declaration, then a literal check before a kind check before a presence check, then the earlier field. An open case declares no fields, so it fails every presence check and is always last.

| Declaration | Tests, in order |
|---|---|
| `Ok({result: string}) \| Failed({error: string})` | `"result" in x` |
| `Text({value: string}) \| Number({value: float})` | `typeof x.value === "string"` |
| `Named({name: string}) \| Person({name: string, age: float})` | `"age" in x`: the case with more fields first |
| `Element(element) \| Portal(portal) \| Other(dict<unknown>)` with `portal` = `element` plus `children` | `"children" in x`, then `"props" in x` |
| `A({kind: [#a], x: int}) \| B({kind: [#b], x: int})` | `x.kind === "a"` |

**No order.** Two cases with the same fields at the same kinds cannot be told apart: `A({x: int}) | B({x: int})`. The declaration is rejected, with the message the compiler has today for two object cases.

**Where the tests go.** Where the test of the single object case is today: after the literal cases, the primitive kinds and the class instances, and guarded against `null` as it is today. A `switch` that does not name every case tests only the ones it names.

**What is trusted.** A record built in ReScript has its declared fields and no others, so for those values the tests are exact. A value that comes from JavaScript can carry more: an object that TypeScript calls `{error: string}` may also have a `result`. TypeScript's own `in` narrowing makes the same assumption. As everywhere in untagged variants, recognition trusts the type.

**Interfaces.** The tests follow from the declaration alone, so an interface and its implementation agree on them when they agree on the cases, as they must already.

**In the import.** A union of object types becomes one case per member when an order exists. The members that still cannot be told apart share one opaque case (step 3), which is then the exception: a bare type parameter, or two types with the same fields.

### Bounded type variables

Status: a sketch. The syntax is open.

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

The converter closes two cases without it: a type parameter that occurs once, as the type of an argument, is imported as its bound; and a bounded method of a record becomes an external, where the bound can be written.

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
