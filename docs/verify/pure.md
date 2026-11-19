# RFC: `@pure`

Status: proposed, implemented in the Rust compiler (`compiler-rust/src/verify/purity.rs`).

## Summary

`@pure` on a `let` is a promise the compiler checks: the binding reads
nothing that can change and changes nothing its caller can see.

```rescript
@pure
let total = items => items->Array.reduce(0, (sum, item) => sum + item.price * item.qty)
```

`@mutates` marks the other kind of function the check has to know about: one
that changes its first argument and does nothing else.

The generated JavaScript does not change. A file that uses neither attribute
is not looked at.

## Motivation

A reducer that pushes onto the state it was given, a render function that
reads the clock, a comparison function that logs: each type checks, and each
is a bug that shows up far from where it was written.

ReScript has no way to say "this function only computes". Other parts of a
program rely on exactly that:

- React calls render functions and reducers more than once and expects the
  same answer.
- Memoization and caching are only correct for functions without effects.
- A property of a function, or a model of a state machine, can only be
  checked by running the function many times, which is meaningless when a
  run changes the next one. The two RFCs that follow this one rely on it.

## Guide

### What a pure function may do

Compute. Call other pure functions, build and take apart data, raise and
catch exceptions, loop, recurse.

<!-- example: pure-compute -->
```rescript
type shape = Circle(float) | Rect(float, float)

@pure
let area = shape =>
  switch shape {
  | Circle(r) => Math.Constants.pi *. r *. r
  | Rect(w, h) => w *. h
  }
```
<!-- /example -->

It may also change values it creates itself. Nobody else can see them until
the function returns them:

<!-- example: pure-local -->
```rescript
@pure
let evens = xs => {
  let out = []
  xs->Array.forEach(x =>
    if mod(x, 2) == 0 {
      out->Array.push(x)
    }
  )
  out
}
```
<!-- /example -->

### What it may not do

Change something it was given:

<!-- example: pure-argument -->
```rescript
@pure
let addItem = (items, item) => {
  items->Array.push(item)
  items
}
```

```
  We've found a bug for you!
  src/Cart.res:8:10-19

   6 │ @pure
   7 │ let addItem = (items, item) => {
   8 │   items->Array.push(item)
   9 │   items
  10 │ }

  This changes `items`, and `addItem` did not create it.

  `addItem` is @pure, so it can only change values it creates itself: a `let`
  bound to a literal (`[]`, `{...}`, `dict{}`), to `ref(...)`, or to a call of
  a @pure external that returns a new value.
```
<!-- /example -->

Read or change state outside itself, or call something that does:

<!-- example: pure-state -->
```rescript
let counter = ref(0)

@pure
let next = () => counter.contents + 1 // `counter` ... its type lets it change

@pure
let stamp = text => `${text} at ${Date.now()->Float.toString}` // `Date.now` is not marked @pure
```
<!-- /example -->

Return a function that keeps state:

<!-- example: pure-closure -->
```rescript
@pure
let counter = () => {
  let n = ref(0)
  () => {
    n := n.contents + 1 // This function changes `n`, which was created outside it
    n.contents
  }
}
```
<!-- /example -->

### Functions of the same file

A function of the same file needs no annotation. The compiler looks into it
the first time a pure binding uses it, and reports where it stops being pure:

<!-- example: pure-helpers -->
```rescript
let trace = x => {
  Console.log(x)
  x
}

@pure
let f = x => trace(x)
```

```
  `trace` is not pure, and `f` is @pure.

  Line 2: The external `Console.log` is not marked @pure.
```
<!-- /example -->

Only what crosses a file needs an annotation: a pure binding can use a value
of another file when its declaration there (in the interface, when the file
has one) says `@pure`.

### Function arguments

A pure function may call a function it is given. It is then as pure as that
function:

<!-- example: pure-arguments -->
```rescript
@pure
let twice = (f, x) => f(f(x))

// The argument is checked here, where it is written.
@pure
let fourth = x => twice(n => n * n, x)
```
<!-- /example -->

Called from a pure binding, the argument is checked there, so the whole call
is pure. Called from ordinary code with a function that logs, `twice` logs.
`@pure` says that `twice` adds no effect of its own.

### `@mutates`

A `@mutates` function is checked like a pure one, except that it may change
its first argument. A pure function may call it on a value it created:

<!-- example: pure-mutates -->
```rescript
type buffer = {mutable items: array<string>, mutable size: int}

@mutates
let add = (buffer, item) => {
  buffer.items = buffer.items->Array.concat([item])
  buffer.size = buffer.size + 1
}

@pure
let fromArray = items => {
  let buffer = {items: [], size: 0}
  items->Array.forEach(item => buffer->add(item))
  buffer
}
```
<!-- /example -->

The standard library's mutating functions are marked this way
(`Array.push`, `Array.sort`, `Dict.set`, `Map.set`, `Set.add`, ...), which is
how the compiler knows that `xs->Array.push(x)` changes `xs`.

### Externals and `%raw`

The compiler cannot see JavaScript. An external is taken to have an effect
unless its declaration says otherwise, and then it is taken on trust:

<!-- example: pure-externals -->
```
<!-- /example -->rescript
@pure @val external parseFloat: string => float = "parseFloat"
@mutates @send external reverse: array<'a> => unit = "reverse"
```

The same holds for a binding whose value is `%raw(...)`. For ReScript code
the check cannot follow, `@pure(unchecked)` and `@mutates(unchecked)` skip
it; the standard library needs this once, for `Dict.delete`.

### Interfaces and module types

An annotation in a signature is a requirement on whatever is matched against
it. The implementation needs no annotation of its own; it is checked as if it
had one:

<!-- example: pure-interface -->
```rescript
module Counter: {
  @pure
  let next: int => int
} = {
  let calls = ref(0)
  let next = n => {
    calls := calls.contents + 1 // This changes `calls`, and it is defined outside this function
    n + 1
  }
}
```
<!-- /example -->

It is one rule for interface files (`.resi`), signatures written on a module,
module types and functor arguments:

<!-- example: pure-functor -->
```rescript
module type Ord = {
  type t
  @pure
  let compare: (t, t) => Ordering.t
}

module Max = (O: Ord) => {
  @pure
  let max = (a, b) => Ordering.isGreater(O.compare(a, b)) ? a : b
}

module StringMax = Max(String) // String.compare is @pure
```
<!-- /example -->

## Reference

A binding is checked when it has `@pure` or `@mutates`, or when a signature
requires one of them of it. Inside a checked binding:

1. **A value from outside the binding** must be one of
   - a value whose declaration is `@pure` (or `@mutates`, see 3);
   - a compiler primitive without effects (arithmetic, comparison, field and
     element reads, `raise`, ...);
   - a function of the same file that passes this check itself;
   - a value whose type is immutable data: no mutable field, array, dict,
     ref, function, object, promise or abstract type anywhere in it.
2. **A change** (assigning a mutable field, calling a `@mutates` function,
   `:=`) must have as its target a name the binding bound with `let` to a
   value it created: a record, array, dict or object literal, `ref(...)`, a
   call of a `@pure` external whose declared result is not a type variable,
   or a call of a function of the same file that always returns such a value.
   In a `@mutates` binding the first parameter is such a name too.
3. **A `@mutates` function** can only be called directly, and its first
   argument is then a change (2). It cannot be used as a value.
4. **A function that changes a value created outside it** must not outlive
   the call that created the value. It may be written as an argument of a
   call whose result cannot hold a function, or bound with `let` and then
   only called or passed to such a call.
5. `async` functions, `await`, `for await`, dynamic `import` and `%raw` are
   not allowed.

A recursive use of the binding being checked counts as pure.

### What `@pure` does not promise

- **Termination.** A pure function may loop forever.
- **No exceptions.** Raising is allowed; the same arguments raise the same
  exception.
- **Identity.** `@pure let make = () => []` returns a new array each time.
  Two results are equal with `==`, not with `===`.
- **Anything about JavaScript taken on trust**: externals and `%raw`
  bindings marked `@pure`, `@pure(unchecked)`, and conversions with
  `%identity` (which can turn any value into a function).
- **Purity of function arguments**, as described above.

### Cost

A file with no `@pure` or `@mutates`, matched against no signature that has
one, is not looked at: the parser records whether it saw the attribute.
Otherwise the check is one walk of the typed tree to index the file's
bindings and one walk of each checked binding.

## The standard library

More than 500 declarations of `Stdlib` are annotated, in 38 files, among them
`Array`, `List`, `String`, `Int`, `Float`, `BigInt`, `Math`, `Option`,
`Result`, `Dict`, `Map`, `Set`, `JSON`, `Null`, `Nullable`, `Bool`,
`Ordering`, `Pair`, `Type` and `JsError`. Their implementations pass the
check, and their generated JavaScript is unchanged.

Left without annotation, on purpose: `Math.random`, `Array.shuffle` and
`toShuffled`, `Date` (the clock, and setters), `Console`, `Promise`, timers,
`RegExp` (a global or sticky expression keeps `lastIndex`), iterators,
`Lazy`, `Symbol`, typed arrays and `Belt`.

## Alternatives

- **An effect system** (Koka, Flix): effects in function types, inferred and
  polymorphic. It answers the function-argument question precisely, and
  changes every function type in the language. Too large a change for what
  ReScript code needs from it.
- **Inferring purity for every function** and storing it with the module.
  No annotations, but purity then is not part of an interface: a change in
  an implementation would silently change what its users may do.
- **Pure by default**, with effects marked. Not compatible with existing
  code.
- **A table in the compiler** for the standard library instead of
  attributes in its sources. The attributes are where the documentation is,
  work the same way for every library, and are checked.

## Open questions

- Type-directed freshness: `List.toArray(xs)` returns a new array, but it is
  a ReScript function of another file, so a pure binding cannot change the
  result without `->Array.copy` first. A `@fresh` declaration could say so.
- Whether `@pure` on a `let` that is not a function should require an
  immutable type.
- Belt and the typed arrays are not annotated yet.
- The OCaml compiler does not implement the check.
