# RFC: proofs of laws

Status: proposed, implemented in the Rust compiler (`compiler-rust/src/verify/prove.rs`) and `rescript verify`. Builds on [`@law`](law.md).

## Summary

`rescript verify` runs a [law](law.md) on values. With this proposal it first
tries to prove the law: to show, from the law's code, that it is true for
every value of its parameters.

```rescript
@law
let reverseTwice = (xs: list<int>) => reverse(reverse(xs)) == xs
```

```
  ✓ reverseTwice  proved for every value (induction on xs, using reverseAppend)
```

- There is no proof to write. The prover evaluates the law with unknowns
  for its parameters, splits into cases where the code takes an unknown
  apart, uses induction on recursive types, and uses the laws proved
  earlier in the file.
- A law it cannot prove is run on values as before, and the report says
  what stopped the proof.
- `@law(proved)` marks a law that must be proved: a run is not enough.

## Motivation

A thousand lists that satisfy a law are evidence. They are not all lists.
The sample misses the case that needs a list of a particular length, or two
numbers that are exactly equal, and it says nothing about the values it did
not make.

Languages built for proving close that gap by making the programmer write
the proof, in a language made for it: a term or a tactic script for every
law, kept up to date with the code.

Most laws of an application do not need that. They follow from the
definitions by computing, by looking at each case of a variant, and by one
induction on a list. A machine can do those three things without help. So
the law stays what it is, a function that returns `bool`, and the proof is
the compiler's job. What it cannot prove it still tests.

## Guide

### A proof

<!-- example: proof-first -->
```rescript
let rec append = (xs, ys) =>
  switch xs {
  | list{} => ys
  | list{x, ...rest} => list{x, ...append(rest, ys)}
  }

let rec length = xs =>
  switch xs {
  | list{} => 0
  | list{_, ...rest} => 1 + length(rest)
  }

@law
let appendNil = (xs: list<int>) => append(xs, list{}) == xs

@law
let lengthAppend = (xs: list<string>, ys: list<string>) =>
  length(append(xs, ys)) == length(xs) + length(ys)
```
<!-- /example -->

```
  ✓ appendNil     proved for every value (induction on xs)
  ✓ lengthAppend  proved for every value (induction on xs)
```

For `lengthAppend` the prover does what a person would. `append` takes `xs`
apart, so there are two cases.

- `xs` is `list{}`: both sides compute to `length(ys)`.
- `xs` is `list{x, ...rest}`: the left side computes to
  `1 + length(append(rest, ys))`. `rest` is a part of `xs`, so the law may
  be used for it: that is `1 + length(rest) + length(ys)`, which is what the
  right side computes to.

A proved law is run as well. The run cannot add to a proof; it checks the
prover against the JavaScript the compiler generates.

### Laws that build on laws

A proof often needs a fact that is a law in its own right. State it first:
every law that was proved is used, as a rewrite from its left side to its
right, in the proofs after it.

<!-- example: proof-lemmas -->
```rescript
@law
let appendNil = (xs: list<int>) => append(xs, list{}) == xs

@law
let appendAssoc = (xs: list<int>, ys: list<int>, zs: list<int>) =>
  append(append(xs, ys), zs) == append(xs, append(ys, zs))

@law
let reverseAppend = (xs: list<int>, ys: list<int>) =>
  reverse(append(xs, ys)) == append(reverse(ys), reverse(xs))

@law
let reverseTwice = (xs: list<int>) => reverse(reverse(xs)) == xs
```
<!-- /example -->

```
  ✓ appendNil      proved for every value (induction on xs)
  ✓ appendAssoc    proved for every value (induction on xs)
  ✓ reverseAppend  proved for every value (induction on xs, using appendNil, appendAssoc)
  ✓ reverseTwice   proved for every value (induction on xs, using reverseAppend)
```

Take `reverseAppend` away and `reverseTwice` is no longer proved. It is
still run. This is the one place where the programmer helps: by saying what
is true on the way, in the language of the program.

### Cases, arithmetic and order

Most code is not recursive. Its laws are proved by going through the cases
of its variants and the outcomes of its comparisons.

<!-- example: proof-cases -->
```rescript
type coupon = Percent(int) | Fixed(int) | FreeShipping
type order = {amount: int, coupon: coupon, shipping: int}

let total = order => order.amount - discount(order) + shipping(order)

let clamp = (x, low, high) => x < low ? low : x > high ? high : x

@law
let totalAddsUp = (order: order) =>
  total(order) + discount(order) == order.amount + shipping(order)

@law
let clampStaysInRange = (x: int, low: int, high: int) =>
  low > high || {
      let clamped = clamp(x, low, high)
      low <= clamped && clamped <= high
    }
```
<!-- /example -->

```
  ✓ totalAddsUp        proved for every value (3 cases)
  ✓ clampStaysInRange  proved for every value (8 cases)
```

`totalAddsUp` has one case per coupon. In each, the two sides are sums of
the same unknowns, and the prover compares them as polynomials. It does so
modulo 2^32, because that is what `+`, `-` and `*` on `int` compute: the
proof holds for amounts that overflow too.

`clampStaysInRange` has a case for each way the comparisons can turn out.
In each, what is asked follows from what the case assumes, because `<=` is
a total order.

### Your own recursive types

Induction works on any recursive variant, and a proof can use it more than
once.

<!-- example: proof-tree -->
```rescript
type rec tree = Leaf | Node(tree, int, tree)

@law
let mirrorTwice = (t: tree) => mirror(mirror(t)) == t

type rec nat = Zero | Succ(nat)

@law
let addCommutes = (a: nat, b: nat) => add(a, b) == add(b, a)
```
<!-- /example -->

```
  ✓ mirrorTwice      proved for every value (induction on t)
  ✓ mirrorKeepsSize  proved for every value (induction on t)
  ✓ addCommutes      proved for every value (induction on a, b)
```

### What is not proved

<!-- example: proof-false -->
```rescript
// Not true: `+` wraps around at the largest int.
@law
let successorIsLarger = (n: int) => n + 1 > n

// True, and the prover does not find out: it knows `+` and `<=`,
// not how the two go together.
@law
let doubleIsEven = (n: int) => mod(n + n, 2) == 0
```
<!-- /example -->

```
  ✗ successorIsLarger  fails (case 16)
      n = 2147483647
      the law returned false
  ✓ doubleIsEven       held for 1000 random cases (no proof: it could not show a case to be true)
```

The prover never says that a law is false. When it finds no proof, the law
is run, and the run decides: a counterexample, or `held for 1000 random
cases` with the reason there is no proof. The two answers stay apart in the
report: `proved for every value` is never printed for a law that was only
run.

The most common reason is code the prover does not read:

```
  ✓ reverseKeepsLength  held for 1000 random cases (no proof: it uses `List.length`, which is defined in another file)
```

### Asking for a proof

`@law(proved)` says that a run is not good enough for this law.

<!-- example: proof-required -->
```rescript
@law(proved)
let sumAppend = (xs: list<int>, ys: list<int>) => sum(append(xs, ys)) == sum(xs) + sum(ys)

// The standard library is another file: this law can be run, not proved.
@law(proved)
let reverseKeepsSum = (xs: list<int>) => sum(List.reverse(xs)) == sum(xs)
```
<!-- /example -->

```
  ✓ sumAppend        proved for every value (induction on xs)
  ✗ reverseKeepsSum  is not proved
      held for 1000 random cases, which is not a proof
      no proof was found: it uses `List.reverse`, which is defined in another file
```

A law over few values that was run on all of them counts as proved.

## Reference

### What a proof says

`proved for every value` means: for every value of the parameters' types,
the law returns `true`. It does not raise, and it does not run forever.

The prover reasons about the typed program, not about the JavaScript. So
that the two agree, it reads only code whose meaning it knows exactly:

| Read | Not read (the law is then run, not proved) |
| --- | --- |
| `int` with `+`, `-`, `*`, unary minus; `/` and `mod` by a constant other than zero | floats, `bigint`, division by an unknown |
| `bool`, `string` with `++`, `unit` | arrays, dicts, objects, promises |
| tuples, records, variants, options, lists | records with optional fields, inline records, polymorphic variants |
| `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `\|\|`, `!` | `===` on anything but a number, a string or a `bool` |
| `switch` without `when`, `if`, `let`, functions | exceptions, loops, `let rec` inside a function |
| functions of the same file | functions of other files, externals |

Two rules keep a proof true of the program:

- **Recursive functions must be total.** A function that calls itself is
  read only when every such call passes, at one position, a part of the
  argument it got there (found by `switch`). Then every call ends, and the
  function has a value for every argument. Other functions are replaced by
  their bodies, a bounded number of times.
- **No float is ever a value in a proof.** `x == x` is false for NaN, and
  the prover uses that a value equals itself. A law with a `float` in a
  parameter's type is not attempted.

### How a law is proved

The law's body is evaluated with an unknown for each parameter.

1. **Computing.** Calls of non-recursive functions are replaced by their
   bodies. A call of a recursive function is computed when the argument it
   recurses on starts with a constructor, and is otherwise kept as it is.
   `int` terms are kept as polynomials with coefficients modulo 2^32, so
   two sides that differ only in how they are written are the same term.
2. **Cases.** When the code takes apart a term whose constructor is not
   known, the proof splits: one case per constructor for an unknown, with
   new unknowns for its parts; for any other term (a comparison, a call
   that returns an option), one case per constructor with the assumption
   that the term is that constructor. A case whose assumptions contradict
   each other is closed. Facts about `<=` are closed under transitivity.
3. **Induction.** When the unknown split is of a recursive type, the law
   itself may be used for each part of the same type: as a rewrite from its
   left side to its right when it is written `a == b`, and as a fact
   otherwise. The first induction of a proof holds for every value of the
   other parameters; a later one keeps them fixed. Which unknown to split
   is the one most stuck calls wait for.
4. **Lemmas.** Every law proved earlier in the file is a rewrite rule for
   every value of its parameters. A rule whose two sides have one form
   (`add(a, b) == add(b, a)`) is only applied when it makes the term
   smaller, so it cannot go round.
5. The law is proved when every case evaluates to `true`.

The search is bounded (evaluation steps, cases, depth of splitting). When a
bound is reached the law is not proved.

### The report

| Report | Meaning |
| --- | --- |
| `proved for every value (induction on xs, using appendNil)` | proved by the compiler, and also run |
| `holds for all 4 values` | run on every value: also a proof |
| `held for 1000 random cases (no proof: ...)` | run on a sample; the reason no proof was found |
| `is not proved` | a `@law(proved)` that was only run: fails |

The compiler writes the outcome of a proof into what it tells the runner
about each law. A build does not prove: proofs are part of
`rescript verify`.

### What is trusted

The prover is part of the compiler and is not itself verified. It produces
no proof that another program could check. A bug in it could accept a law
that is false; that is why a proved law is still run, and a run that breaks
a proved law is reported as a bug in rescript.

## Alternatives

- **Proof terms written by the programmer**, checked by a dependent type
  checker (Bend 2, Lean, Agda, Idris). The checker is small and what it
  accepts is certain. Every law needs a proof written and maintained, the
  functions must be written the way the checker wants, and it is a second
  type system. This proposal takes the other end: no proofs to write, a
  smaller class of laws proved, a larger thing to trust.
- **An SMT solver** (Z3, as Dafny and Liquid Haskell use). Much stronger on
  arithmetic and on combinations of facts. It is a large dependency that
  cannot run in the browser build of the compiler, its failures are hard to
  explain, and it does not do induction by itself.
- **Only testing.** What laws are without this proposal.
- **Proving in every build.** A proof costs more than type checking, and a
  build should stay fast. `rescript verify` is where the time goes.

## Open questions

- **The standard library.** `List.reverse` is another file, so a law about
  it is not proved. Interfaces could carry the bodies of pure functions, or
  the laws a module has proved, for other files to use as lemmas.
- **Hints.** When the prover picks the wrong induction or needs a lemma it
  was not given, the only help today is another law. `@law(induction(xs))`
  or naming the lemmas to use would be small additions.
- **Arithmetic.** Order and `+` are known separately: `a <= a + 1` under a
  bound is not proved. A decision procedure for linear arithmetic over
  32-bit integers would close most of that.
- **Arrays and dicts**, which have no induction as they are.
- **Functions as parameters.** A law about `map` needs an arbitrary
  function; the run cannot make one, a proof could.
- **Specs.** `always` of a [spec](spec.md) with no end of states could be
  proved by induction on the steps.
- **A proof that can be checked.** The prover could write down the steps it
  took, for a small checker to confirm.
