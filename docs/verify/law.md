# RFC: `@law`

Status: proposed, implemented in the Rust compiler (`compiler-rust/src/verify/laws.rs`) and the build system (`rescript verify`). Builds on [`@pure`](pure.md).

## Summary

A law is a property of the program: a function that returns `bool` and is
meant to return `true` for every value of its parameters.

```rescript
@law
let totalIgnoresOrder = (items: array<item>) => total(items) == total(items->Array.toReversed)
```

- A build type checks a law, checks that it is pure, and leaves it out of the
  JavaScript.
- `rescript verify` runs every law on values the compiler makes from the
  types of its parameters: all of them when there are few, a thousand random
  ones otherwise. A value that breaks a law is made smaller before it is
  reported.

There is nothing to install and nothing to write besides the law: no
generators, no test file, no test framework.

## Motivation

A test checks the cases someone thought of. The bugs are in the cases nobody
thought of: the empty cart, the negative coupon, the two numbers whose
difference does not fit in an integer.

A law says what holds for every case and lets the machine look for one where
it does not. Property testing libraries do this already, and each asks the
programmer to describe how to make a value of every type involved. The
compiler knows those types. It also knows what the values are at run time: a
constructor's tag, a field's name after `@as`, an unboxed variant. So it can
make them.

A law is also documentation that cannot go stale. It sits next to the code
it describes, in the language of that code, and the build fails when it stops
type checking.

## Guide

### Writing a law

A law is a `let` at the top level of a file (or of a module in it), marked
`@law`, bound to a function that returns `bool`. Its parameters have type
annotations: they say which values to try.

<!-- example: law-first -->
```rescript
type item = {name: string, price: int, qty: int}

let total = items => items->Array.reduce(0, (sum, item) => sum + item.price * item.qty)

@law
let totalIgnoresOrder = (items: array<item>) => total(items) == total(items->Array.toReversed)

@law
let totalOfTwoCarts = (a: array<item>, b: array<item>) =>
  total(Array.concat(a, b)) == total(a) + total(b)
```
<!-- /example -->

```
$ rescript verify
src/Cart.res
  ✓ totalIgnoresOrder  held for 1000 random cases
  ✓ totalOfTwoCarts    held for 1000 random cases

2 checks passed
```

The JavaScript of a build has `total` and nothing else. A law costs the
program nothing.

### Few values: all of them

When the parameters of a law have few values, `rescript verify` does not
sample. It runs the law on every one of them, and the law then holds for all
inputs: that is a proof.

<!-- example: law-exhaustive -->
```rescript
type light = Red | Amber | Green

let next = light =>
  switch light {
  | Red => Green
  | Green => Amber
  | Amber => Red
  }

@law
let deMorgan = (a: bool, b: bool) => !(a && b) == (!a || !b)

@law
let threeStepsComeBack = (light: light) => next(next(next(light))) == light
```
<!-- /example -->

```
  ✓ deMorgan            holds for all 4 values
  ✓ threeStepsComeBack  holds for all 3 values
```

The report says which of the two happened: `holds for all` or `held for`.

### A law that does not hold

<!-- example: law-counterexample -->
```rescript
type coupon = Percent(int) | Fixed(int) | FreeShipping

let apply = (amount, coupon) =>
  switch coupon {
  | Percent(p) => amount - amount * p / 100
  | Fixed(n) => amount - n
  | FreeShipping => amount
  }

@law
let couponNeverRaisesThePrice = (amount: int, coupon: coupon) => apply(amount, coupon) <= amount

@law
let sortTwiceIsSortOnce = (xs: array<int>) => {
  let sort = xs => xs->Array.toSorted((a, b) => Float.fromInt(a - b))
  sort(sort(xs)) == sort(xs)
}
```
<!-- /example -->

```
  ✗ couponNeverRaisesThePrice  fails (case 1, made smaller 9 times)
      amount = 0
      coupon = Fixed(-1)
      the law returned false
      src/Cart.res:10
  ✗ sortTwiceIsSortOnce        fails (case 135, made smaller 3 times)
      xs = [2147483646, -2]
      the law returned false
      src/Cart.res:13
```

The first value found is rarely the one to read. The runner keeps trying
smaller ones (shorter arrays, numbers closer to zero, earlier constructors)
as long as the law still fails, and reports the smallest: a coupon of -1
raises the price.

The second law fails too, on `[2147483646, -2]`: the difference of the two
does not fit in a 32-bit integer, so the comparison function gives the wrong
sign and the array does not get sorted. Nobody writes that test case.

A failing run prints its seed, and `rescript verify --seed <n>` runs the same
cases again.

### Values of your own types

Values are made from the type declarations, recursive ones included. Their
representation at run time is the one the compiler generates code for.

<!-- example: law-recursive -->
```rescript
type rec tree<'a> = Leaf | Node(tree<'a>, 'a, tree<'a>)

let rec mirror = tree =>
  switch tree {
  | Leaf => Leaf
  | Node(left, value, right) => Node(mirror(right), value, mirror(left))
  }

@law
let mirrorTwice = (t: tree<string>) => mirror(mirror(t)) == t
```
<!-- /example -->

| Type | Values |
| --- | --- |
| `int`, `float`, `bigint` | small numbers often, large ones and the limits sometimes, both signs |
| `string`, `char` | short texts of letters, digits, punctuation and a few non-ASCII characters |
| `bool`, `unit` | all |
| `option`, `array`, `list`, `dict`, tuples | of generated parts; collections start short |
| records, variants, polymorphic variants | from the declaration, with `@as`, `@tag`, `@unboxed` and optional fields as declared |
| a type variable (`array<'a>`) | `int` |

### Types whose values cannot be made

The compiler does not make values of an abstract or private type: only its
module can, and a made-up value might be one the module never produces.
Functions, promises, objects and extensible types are not made either.

<!-- example: law-abstract -->
```rescript
@law
let roundTrip = (email: Email.t) => Email.make(Email.toString(email)) == Some(email)
```

```
  No value can be made for `email`: `Email.t` is an abstract type: only its
  module can make its values.

  A law is run on values made from the types of its parameters. Take what
  this value is built from as the parameter, and build the value in the law.
```
<!-- /example -->

The law takes what the value is built from, and builds it. This is also the
better law: it only speaks about values the program can have.

<!-- example: law-built -->
```rescript
@law
let roundTrip = (text: string) =>
  switch Email.make(text) {
  | Some(email) => Email.toString(email) == text
  | None => !String.includes(text, "@")
  }
```
<!-- /example -->

A law that only applies under a condition says so with `||`:
`low > high || ...` holds trivially when the condition is not met.

### Laws are pure, and no part of the program

A law is checked like a [`@pure`](pure.md) binding, without saying so: a law
that logs, reads the clock or changes its argument is rejected. Running it a
thousand times would otherwise mean nothing.

Nothing can refer to a law. Its name is not in scope after it, and it is in
no interface. That is what lets a build leave it out.

## Reference

### What a law is

A value binding is a law when it has the attribute `@law`. It must be

1. a `let` of a single name, not joined to others with `and`,
2. at the top level of a file, or of a module written as
   `module M = { ... }` at such a level (no signature on the module, no
   functor),
3. a function whose result type is `bool`,
4. with parameters whose types the compiler can make values of.

A law is type checked as written and checked as a `@pure` binding. Its name
is not added to the environment. In a build it is left out of the module's
signature and is not translated: the JavaScript, the interface other files
see and the `.cmi`-level artifacts are those of the file without the law.

### `rescript verify`

```
rescript verify [folder] [--seed <n>] [--cases <n>]
```

1. Builds the project, as `rescript build` does.
2. Compiles each file of the project that has a law once more, in memory,
   with its laws exported and the file's interface ignored. The result is
   written next to the file's JavaScript as `<name>.verify<suffix>` and
   removed after the run. Laws of installed dependencies are not run.
3. For each law the compiler writes down a shape for every parameter: what
   its values are and how each is represented in JavaScript.
4. Runs every law under Node and prints the report. The exit code is 1 when
   a law fails.

A law whose parameters have at most 10,000 values in total is run on all of
them. Any other law is run on `--cases` values (1,000 unless given). The
values of case `i` of a law come from the seed, the law's name and `i`, so a
run with the same seed is the same run, and laws do not affect each other.

A law fails when it returns anything but `true`, or raises.

A failing case is a sequence of choices (which constructor, how long, which
number). The runner drops and lowers choices while the law keeps failing,
and reports the values of the shortest, lowest sequence it finds.

### Cost

A file without `@law` pays nothing. A law costs a build its type check and
purity check. `rescript verify` type checks the project a second time, in
memory, and compiles the files that have laws.

## Alternatives

- **A property testing library** (fast-check, or one written in ReScript).
  It works today. Generators are written by hand for every type and kept in
  sync by hand; the test is in another file, in a test framework, and the
  compiler knows nothing about it.
- **Deriving generators with macros.** A macro can read a type declaration
  and write a generator for it. It then needs an attribute on every type a
  law reaches, also those of other packages, and it has to repeat the
  compiler's rules for run-time representation.
- **Proving laws** with an SMT solver or by export to a proof assistant. A
  law states exactly what such a tool would prove, so this is where a later
  proposal would attach. Running the law is the step that needs no
  annotations and no second language.
- **Keeping laws in the JavaScript** and letting a bundler remove them. Then
  purity could not be relied on, and every law would be an export.

## Open questions

- Generators for abstract types: a module could name the function that makes
  its values (`@law.make`), so a law can take an `Email.t`.
- Functions as parameters (a law about `Array.map` wants an arbitrary `f`).
- How many values count as "few": 10,000 is a guess.
- Reporting in CI: a machine-readable report, and whether a build should be
  able to require that every law of a package was run.
- Laws inside functors and modules with a signature.
- The OCaml compiler ignores `@law`: there a law is an ordinary export.
