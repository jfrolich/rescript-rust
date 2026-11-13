# Class types that packages can share

Status: draft, not implemented. It builds on the class records of the branch `ts-import` and on the upstream RFC "Class hierarchies in WebAPI" ([rescript-lang/rescript issue 9058](https://github.com/rescript-lang/rescript/issues/9058)).

## In short

The DOM types are moving out of the compiler's standard library and into a package, `@rescript/webapi`. A type belongs to the module that declares it, so from then on every package that mentions an `Element` has to depend on that one package: the React bindings, the JSX runtime, every binding to a library that takes a DOM node.

This RFC removes the need for an owner. A type declared with `@instanceOf` already names a JavaScript class. The proposal is that the class, not the declaration, decides what the type is compatible with:

```rescript
// @rescript/react declares the little it needs. It does not depend on WebAPI.
@instanceOf("Element") type element
external createRoot: element => Root.t = "createRoot"

// @rescript/webapi declares the whole interface.
@instanceOf("Element")
type element = private {tagName: string, mutable id: string /* ... */}

// An application uses both.
let mount = (container: WebAPI.element) => ReactDOM.createRoot(container)
```

Both declarations say "an instance of `Element`", so a value of one is accepted where the other is expected. Each package declares the slice of a class it uses. Nothing about the DOM has to be in the compiler.

An untagged variant already goes by the class: it orders and tests its cases by class, whatever declarations the cases come from. The proposal extends that to coercion.

## The problem

### The DOM types are leaving the standard library

The standard library has a module `Dom` with 261 types, all without fields, and a few more web types such as `Blob` and `File`. The upstream plan is to deprecate them and let [`@rescript/webapi`](https://github.com/rescript-lang/experimental-rescript-webapi) take their place.

The types are used outside the DOM bindings. The JSX runtime names seven of them (`eventTarget`, `element`, `event`, `window`, `touchList`, `dataTransfer`, `eventPointerId`), and the React bindings add `history` and `location`.

### A type has one owner

Two declarations are two types, also when they describe the same values. Today's compiler refuses the last line of this program, with the error shown beside it:

<!-- example: class-today -->
```rescript
// Two packages, each with its own declaration of the class Element.
module ReactDOM = {
  @instanceOf("Element") type element
  @val external querySelector: string => Null.t<element> = "document.querySelector"
}

module WebAPI = {
  @instanceOf("Element")
  type element = private {tagName: string, mutable id: string}
  @send external focus: element => unit = "focus"
}

// Both types say "an instance of Element". They are still two types.
let focus = (el: ReactDOM.element) => WebAPI.focus(el)
```

```
This has type: ReactDOM.element
But this function argument is expecting: WebAPI.element
```
<!-- /example -->

With the proposal the program is accepted, and `focus` compiles to `el.focus()`.

The examples on this page are compiled by the Rust compiler of the branch `ts-import`, which has class records. They show what the compiler does today, so this one shows an error. The proposal itself is not implemented, and its code is not live.

So that packages agree on `element`, one package has to declare it and all others have to depend on that package. That has four costs.

- **Everything depends on one package.** The React DOM bindings would depend on WebAPI. React Native has its own `Element` and no `window`, so core React must not. A binding to a charting library that takes a container element has to pick the DOM package for its users.
- **The owner is not small.** WebAPI models an interface as a record, and a record lists all its fields. In `@rescript/webapi`, `element` is declared in one recursive group of nine records with 382 fields (`DOMTree.res`), and the part of the package it is in requires four others: the DOM platform, animation, CSSOM and geometry. There is no small package that has only `Element`.
- **One version for the whole build.** A package has one version per build, so a breaking change to any type of the owner reaches every package that depends on it.
- **Generated declarations cannot agree.** `%ts` declares the classes an import mentions in the file that imports. Two files that each import a function taking a `URL` get two `URL` types.

The upstream RFC answers the first two by vendoring a WebAPI base subset into the compiler repository, sized to what React DOM needs. That works for React. It keeps one owner, and the subset is fixed by one consumer.

### Only classes have this problem

Most of what the DOM bindings declare is not a class. An options object is a record and an enumeration is a variant, and both already go from one declaration to another when the declarations agree:

<!-- example: class-crossing -->
```rescript
// Two packages, each with its own declaration of an options object
// and of an enum.
module A = {
  type options = {capture: bool, once: bool}
  type mode = | @as("open") Open | @as("closed") Closed
}

module B = {
  type options = {capture: bool}
  type mode = | @as("open") Open | @as("closed") Closed
  external listen: (options, mode) => unit = "listen"
}

// The declarations describe the same values, so `:>` goes from one to
// the other.
let listen = (options: A.options, mode: A.mode) =>
  B.listen((options :> B.options), (mode :> B.mode))
```
<!-- /example -->

A class type is different. It is abstract or a private record, and nothing may be coerced into a private type, because the module that declares it is the only one that may build its values. That is the right rule for a type that guards an invariant. A class type guards one fact, and the compiler knows which: its values are instances of the class.

## What the compiler already knows

`@instanceOf` declares the class of a type. A private abbreviation of a class type is a subclass. On the branch `ts-import`, a private record can carry a class as well, with `@extends` for its superclass, and `@module` beside `@instanceOf` imports the class from a module:

```rescript
@instanceOf("Node") type node
@instanceOf("Element") type element = private node       // a subclass of Node

@instanceOf("Blob") type blob = private {size: float}
@instanceOf("File") @extends(: blob)
type file = private {size: float, name: string}           // a subclass of Blob

@module("three") @instanceOf("Mesh") type mesh           // the class Mesh of "three"
```

From these the compiler keeps, for every class type, the name of its class and the names of its ancestors.

### A variant already goes by the class

An untagged variant tests a subclass before its superclass. It finds the order in the class names, so it works when the cases come from two packages:

<!-- example: class-order -->
```rescript
module Forms = {
  @instanceOf("Element") type element
  @instanceOf("HTMLInputElement") type input = private element
}

module WebAPI = {
  @instanceOf("Element") type element = private {tagName: string}
}

// The cases come from two packages. `Forms.input` says its class has
// Element as an ancestor, so it is tested first.
@unboxed type target = Element(WebAPI.element) | Input(Forms.input)

let describe = (target: target) =>
  switch target {
  | Element(el) => el.tagName
  | Input(_) => "input"
  }
```
<!-- /example -->

### And it already converts between declarations

A constructor of an untagged variant does not decide which case a value matches: the value is tested again when it is matched. So a variant with one case for each package's type converts from one to the other:

<!-- example: class-bridge -->
```rescript
module ReactDOM = {
  @instanceOf("Node") type node
  @instanceOf("Element") type element = private node
}

module WebAPI = {
  @instanceOf("Element")
  type element = private {tagName: string, mutable id: string}
  @send external focus: element => unit = "focus"
}

// A variant with a case for each package's type.
@unboxed type bridge = Theirs(WebAPI.element) | Mine(ReactDOM.node)

// Wrap React's element in its own case, match it in the other one.
let focus = (el: ReactDOM.element) =>
  switch Mine((el :> ReactDOM.node)) {
  | Theirs(el) => WebAPI.focus(el)
  | Mine(_) => ()
  }
```
<!-- /example -->

The JavaScript is `if (!(el instanceof Element)) return; el.focus();`. The compiler takes `instanceof Element` as proof that the value is a `WebAPI.element`. It also knows, from the type of `el`, that the test cannot fail. Today that knowledge costs a variant, a `switch`, a branch that is never taken and a test at run time. The proposal lets the type checker use it directly.

## The proposal

### Definitions

- A **class type** is a type whose declaration has `@instanceOf`.
- Its **class** is the name in `@instanceOf`, with the module of a `@module` beside it. `Element` is a global class; `Mesh` of `"three"` is a different class from `Mesh` of another module.
- Its **ancestors** are the classes of the types its declaration names as superclass, and theirs: the type a private abbreviation abbreviates, or the type `@extends` names.
- Two class types are **the same class** when their classes are equal and neither has type parameters.
- `A` is a **subclass** of `B` when the class of `B` is one of the ancestors of `A`.

Whether two types are the same class or subclass and superclass is read from their declarations only. The compiler has no table of JavaScript classes.

### Rule 1: a class type coerces to the same class and to a superclass

`(a :> B.t)` is accepted when the type of `a` is the same class as `B.t`, or a subclass of it. The declarations may be in different modules or packages. No fields are compared.

```rescript
let a = (el: ReactDOM.element) => (el :> WebAPI.element)          // the same class
let b = (input: WebAPI.htmlInputElement) => (input :> ReactDOM.element)  // a subclass
let c = (el: ReactDOM.element) => (el :> WebAPI.htmlInputElement) // an error: not an ancestor
```

Inside other types the rule follows variance, as `:>` does for every other subtype: `array<WebAPI.htmlInputElement>` coerces to `array<ReactDOM.element>`.

### Rule 2: the same class counts as equal where types must be equal

A mutable field and the parameter of a type such as `ref` require equal types on both sides of `:>`. Two types of the same class are equal there. A subclass is not.

```rescript
let d = (ref: React.ref<Nullable.t<ReactDOM.element>>) =>
  (ref :> React.ref<Nullable.t<WebAPI.element>>)
```

### Rule 3: the coercion is written for you where the expected type is known

Where an expression is checked against a type that is already known (an argument of a function, a JSX prop, a field of a record that is built, the payload of a constructor), and the two types do not unify, the compiler tries rules 1 and 2. If they apply, the expression is typed as if `:>` were written.

```rescript
let mount = (container: WebAPI.element) => ReactDOM.createRoot(container)

let focus = (ref: React.ref<Nullable.t<ReactDOM.element>>) =>
  switch ref.current {
  | Value(el) => el->WebAPI.Element.focus
  | Null | Undefined => ()
  }

// A subclass of one package, where another package expects the superclass.
let attach = (input: WebAPI.htmlInputElement) => Charts.attach(input)
```

Two limits keep this narrow:

- **The same class is accepted anywhere in the type.** A listener of type `WebAPI.event => unit` is accepted where `ReactDOM.event => unit` is expected.
- **A subclass is accepted only as the argument's own type.** `array<htmlInputElement>` where `array<element>` is expected stays an error with a `:>` to write, as it is today within one package.

The second limit is what the discussion of the upstream RFC proposed for upcasts within one package. Rule 3 covers that case too.

### What does not change

- **Type inference.** Unification is not touched. Rule 3 runs only after unification has failed, so a program that compiles today gets the same types and the same JavaScript.
- **Two declarations stay two types.** `el.tagName` is looked up in the declaration of the type of `el`. Which fields a value has never depends on the order in which types were unified.
- **The JavaScript.** A coercion compiles to nothing.
- **Declarations.** A class record must be private, and `@extends` still checks, within its package, that the record has the fields of its superclass.

## What it looks like for the packages

### React and the JSX runtime

They declare the classes they name, as abstract types, with the chain above each:

```rescript
@instanceOf("EventTarget") type eventTarget
@instanceOf("Node") type node = private eventTarget
@instanceOf("Element") type element = private node
@instanceOf("Window") type window = private eventTarget
```

That is the whole dependency on the DOM. Core React declares none of it and stays usable from React Native, which declares its own.

### WebAPI

It keeps its records and becomes the package for people who want to use the DOM, not a package that others must build on. It can change a field or split a module without breaking a package that only names a class.

### A binding to a library

```rescript
@instanceOf("Node") type node
@instanceOf("Element") type element = private node
@module("charts") external attach: element => chart = "attach"
```

Its users pass the element they have, from React, from WebAPI or from their own bindings.

### Imports from TypeScript

A `%ts` import declares each class it mentions, with the ancestors TypeScript knows. With rule 1 the `URL` of an import in one file, the `URL` of an import in another and WebAPI's `URL` are compatible, and the import does not have to guess which ReScript package the reader uses.

### The standard library

It has 30 class types today (`Date`, `Map`, `Blob`, `File`, the typed arrays). They stay, and are compatible with a package that declares the same class with more detail. `Dom` can be removed without a replacement that everything depends on.

## Why this is sound

It relies on what the compiler relies on today. A class type makes two promises:

1. **Every value of the type is an instance of the class.** A variant tests `instanceof` and expects it to succeed for the values of the case.
2. **Every instance of the class may be used at the type.** A match gives a value that passes `instanceof` the type of the case, wherever the value came from.

The bridge above uses both: promise 1 for `ReactDOM.element`, promise 2 for `WebAPI.element`. Rule 1 is those two steps without the test. An upcast adds the declared ancestry, which is trusted within a package today.

What stays trusted, not checked:

- **The fields of a record.** They are a claim about the class, as the type of an `external` is a claim about a function. Two packages can describe one class differently, and each reader gets the description of the type they hold. A wrong description is wrong for the package's own values too.
- **The ancestry.** A false `@extends` or abbreviation lets a value pass as a class it is not. Today that stays inside the package; with rule 1 it reaches the packages that declare the ancestor.
- **Realms.** `instanceof` fails for a value of another frame. That is unchanged.

One thing follows for authors: a type that is narrower than its class must not have `@instanceOf`. A module that hands out only the elements it created, and relies on that, declares `type root = private element` without the attribute. Rule 1 looks at the declaration that has `@instanceOf`, so nothing coerces into `root`.

## Limits

- **A slice has to declare the chain it is used with.** Ancestors come from the declaration of the type that is coerced. A package that declares `@instanceOf("HTMLElement") type htmlElement` with no parent cannot pass it where an `Element` is expected.
- **A missing chain also misorders a variant.** In `Element(A.element) | Input(B.input)`, where `B.input` declares no parent, `instanceof Element` is tested first and takes every input. This happens today, within one package too. It becomes more likely when slices are small. A warning for two unrelated classes in one variant whose order matters is possible, but the compiler cannot know the chain that was left out.
- **Classes with type parameters** keep today's rules. `element<'native>` of one package and `element` of another are not the same class, because nothing says how the parameters correspond.
- **A relative `@module`** (`"./mesh.js"`) names a file relative to the declaring file. Two declarations in different directories are the same class only if the compiler resolves the specifiers; until it does they are different classes, which is the safe answer.
- **Mixins** (`ParentNode`, `GlobalEventHandlers`) have no class and are not covered. They do not need to be: no value has a mixin as its type.

## Alternatives considered

| Alternative | What it gives | Why not |
|---|---|---|
| One package owns the types, vendored into the compiler repository (the upstream RFC) | Works with today's compiler | Everything that names a DOM class depends on it; the subset follows React DOM |
| Keep `Dom` in the standard library | No dependency | The DOM stays in the compiler; abstract types have no fields; the compiler's releases decide what the web looks like |
| Phantom types (`Dom.element_like<'a>`, as `Dom` does today) | Equal types across packages, no compiler change | No fields, no `instanceof` dispatch, and errors that print the encoding |
| Object types (`{"tagName": string}`) | Structural, no owner | Any object literal is an element; no class to dispatch on |
| The same class is the same type in the unifier | No coercion at all, also in results and branches | The fields of `el` would depend on which declaration unification met first; equality of types is used throughout the type checker (module inclusion, GADTs, interfaces) |
| Compare the fields of the two records on coercion | Finds packages that disagree | The error is reported to the one person who wrote neither declaration, and stops the two packages from working together |
| A table of DOM classes and their ancestors in the compiler | Complete chains | The DOM is in the compiler again |

The fifth row is the closest. It is a later step if rule 3 turns out to leave too many places where `:>` has to be written.

## Implementation

The parts are small, because a class type already carries its class and its ancestors by name (`Instance::Class` in [`variant_runtime.rs`](../../compiler-rust/src/types/variant_runtime.rs); the name of an imported class includes its module), also for a type of another module.

1. **Rule 1** in `subtype_rec` of [`ctype.rs`](../../compiler-rust/src/types/ctype.rs): two type constructors with different paths are subtypes when `is_declared_subclass` holds or the classes are equal. `coerces_into_private_type`, which refuses coercion into a private record, already makes an exception for a declared subclass; the exception gets the same-class case and stops comparing fields for class records of different declarations.
2. **Rule 2** where `subtype_rec` falls back to unification for invariant positions: try the same-class test first.
3. **Rule 3** in the typing of arguments, record fields and constructor payloads in `typecore.rs`: on a unification error, run the subtype check restricted to class steps, and wrap the expression in the coercion node that `:>` produces.
4. **Errors.** A failed coercion between two class types says which class each is and which ancestors the source declares.
5. **The OCaml compiler** has the same structure (`Ctype.subtype`, `Typecore.type_argument`), so the rules can be ported once they are agreed on.

Rule 3 costs nothing for code that type checks today: it runs on the path that would report an error.

Tests: two packages with different slices of one class (abstract and record), each direction of rule 1, the invariant positions of rule 2, each site of rule 3, the errors, and the variant examples of this page.

## Open questions

1. **Where rule 3 applies.** Arguments, JSX props, record fields and constructor payloads are proposed. Annotated `let` bindings and function results could follow. Branches of an `if` or a `switch` have no expected type and stay explicit.
2. **Upcasts in rule 3.** The same class is the case that sharing needs. Accepting a subclass as an argument is the convenience the upstream discussion asked for. They can land separately.
3. **Classes with type parameters.** Is "same number of parameters, compared in order" good enough, or should the correspondence be declared?
4. **Disagreeing descriptions.** Should a build that contains two records for one class with a field at incompatible types get a warning, reported at the second declaration?
5. **Refinements.** `type root = private element` without `@instanceOf` is still tested with `instanceof Element` in a variant, so a variant can hand any element to it. Should a refinement be refused as a case?

## Order of work

1. Rules 1 and 2, with the two-package tests. This is enough for React DOM to stop depending on a DOM package, with `:>` written where two packages meet.
2. Rule 3 for the same class.
3. Rule 3 for a subclass as an argument.
4. The React bindings and the JSX runtime declare their classes; `Dom` is deprecated.
5. Tests for `%ts` across files: a class that two files import is one class.
