# RFC: `@spec`

Status: proposed, implemented in the Rust compiler (`compiler-rust/src/verify/specs.rs`) and the build system (`rescript verify`). Builds on [`@pure`](pure.md) and [`@law`](law.md).

## Summary

A spec is a state machine and what must be true of it: where it starts, its
reducer, and properties of its states.

```rescript
@spec
let request: Spec.t<request, event> = {
  init: {status: Idle, attempts: 0},
  step: update,
  always: request => request.attempts <= 3,
  eventually: request => request.status == Done || request.status == GaveUp,
}
```

- A build type checks a spec, checks that it is pure, and leaves it out of
  the JavaScript.
- `rescript verify` goes through every state the machine can get into, in
  every order of actions, and checks the properties. When one does not hold
  it prints the shortest run that shows it.

The machine is the program's own reducer, not a model of it written in
another language. What is checked is what ships.

## Motivation

The state of an application is a reducer: `(state, action) => state`. Its
bugs are rarely in one step. They are in an order of steps: Pay pressed
twice before the answer to the first, a failure while saving, a retry after
giving up. A test follows one order. A [law](law.md) checks one function on
many values, which is one step.

Model checkers find such orders by trying them all. TLA+ is the known one,
and it works on a model: a second description of the system, in a second
language, that someone has to keep true to the code.

A reducer needs no model. It is a pure function over data, so the machine it
describes can be explored as it is: start from the first state, apply every
action, and continue from each state not seen before. For the state of a
dialog, a form, a request or a checkout there are tens or thousands of
states, and all of them are visited in milliseconds.

## Guide

### Writing a spec

A spec is a `let` at the top level of a file (or of a module in it), marked
`@spec`, of type `Spec.t<state, action>`. The two type arguments say what
the machine's states and actions are.

<!-- example: spec-first -->
```rescript
type status = Idle | Loading | Failed | Done | GaveUp
type request = {status: status, attempts: int}
type event = Send | Succeed | Fail | Retry

// A request that is sent again after a failure, three times at most.
let update = (request, event) =>
  switch (request.status, event) {
  | (Idle, Send) => {status: Loading, attempts: 1}
  | (Loading, Succeed) => {...request, status: Done}
  | (Loading, Fail) => {...request, status: request.attempts >= 3 ? GaveUp : Failed}
  | (Failed, Retry) => {status: Loading, attempts: request.attempts + 1}
  | _ => request
  }

@spec
let request: Spec.t<request, event> = {
  init: {status: Idle, attempts: 0},
  step: update,
  always: request => request.attempts <= 3,
  sometimes: request => request.status == GaveUp,
}
```
<!-- /example -->

```
$ rescript verify
src/Request.res
  ✓ request  always, sometimes hold over all 10 states

1 check passed
```

`rescript verify` starts from `init` and applies `step` with every event to
every state it finds. This machine has ten states. `always` was true in each
of them, so no order of events makes a fourth attempt: that is a proof, not
a sample. `sometimes` checks the spec itself: giving up does happen.

The JavaScript of a build has `update` and nothing else.

### `always`: what never goes wrong

<!-- example: spec-always -->
```rescript
type checkout = {pending: int, charges: int}
type event = Pay | Charged

// Pay sends a charge; Charged is its answer.
let update = (checkout, event) =>
  switch event {
  | Pay => checkout.charges > 0 ? checkout : {...checkout, pending: checkout.pending + 1}
  | Charged =>
    checkout.pending > 0
      ? {pending: checkout.pending - 1, charges: checkout.charges + 1}
      : checkout
  }

@spec
let chargedOnce: Spec.t<checkout, event> = {
  init: {pending: 0, charges: 0},
  step: update,
  always: checkout => checkout.charges <= 1,
}
```
<!-- /example -->

```
  ✗ chargedOnce  fails: always
      `always` is false after 4 steps:
        init        {pending: 0, charges: 0}
        Pay      →  {pending: 1, charges: 0}
        Pay      →  {pending: 2, charges: 0}
        Charged  →  {pending: 1, charges: 1}
        Charged  →  {pending: 0, charges: 2}
      src/Checkout.res:14
```

The reducer guards against paying after a charge, not against paying while
one is on its way. States are visited nearest first, so the run that is
printed is the shortest there is: nothing in it is beside the point.

Ignore Pay while a charge is pending (`checkout.charges > 0 ||
checkout.pending > 0`) and the spec holds over all three states.

### `eventually`: what is certain to happen

`always` says nothing bad happens. A machine that does nothing satisfies it.
`eventually` says something good does happen: every run, whatever its
actions, gets to a state where the property is true.

<!-- example: spec-eventually -->
```rescript
  // The attempt is not counted.
  | (Failed, Retry) => {...request, status: Loading}

@spec
let settles: Spec.t<request, event> = {
  init: {status: Idle, attempts: 0},
  step: update,
  always: request => request.attempts <= 3,
  eventually: request => request.status == Done || request.status == GaveUp,
}
```
<!-- /example -->

```
  ✗ settles  fails: eventually
      `eventually` is never true in this run, which can go on forever:
        init      {status: Idle, attempts: 0}
        Send   →  {status: Loading, attempts: 1}
        and then, again and again:
        Fail   →  {status: Failed, attempts: 1}
        Retry  →  {status: Loading, attempts: 1}
      src/Request.res:15
```

`always` still holds here: there are never more than three attempts, because
there is never more than one. Only `eventually` sees that the request can
fail and be retried without end.

A run breaks `eventually` in one of two ways: it goes round, as here, or it
ends in a state where the property is false and no action changes anything.
An action that leaves the state as it is does not count as a step: a user
who presses a button that does nothing has not started a run that goes on
forever.

### `reachable`: what stays possible

`eventually` is often too much to ask: a user may go back and forth between
two screens for as long as they like. `reachable` asks for less: from every
state the machine can get into, some actions lead to a state where the
property is true. There are no dead ends.

<!-- example: spec-reachable -->
```rescript
type dialog = Closed | Editing | Saving | Broken
type event = Open | Save | Saved | SaveFailed | Cancel

let update = (dialog, event) =>
  switch (dialog, event) {
  | (Closed, Open) => Editing
  | (Editing, Save) => Saving
  | (Editing, Cancel) => Closed
  | (Saving, Saved) => Closed
  | (Saving, SaveFailed) => Broken
  | _ => dialog
  }

@spec
let canBeClosed: Spec.t<dialog, event> = {
  init: Closed,
  step: update,
  reachable: dialog => dialog == Closed,
}
```
<!-- /example -->

```
  ✗ canBeClosed  fails: reachable
      `reachable` is out of reach after 3 steps: no actions lead from the last state to one where it is true
        init           Closed
        Open        →  Editing
        Save        →  Saving
        SaveFailed  →  Broken
      src/Dialog.res:14
```

Nothing handles an event in `Broken`. The type checker is content: the
`switch` has a case for everything.

### Saying which actions can happen

Without `actions`, every value of the action type can happen in every state.
That needs an action type with few values. When an action carries a number
or a text, or when some actions cannot happen in some states, the spec says
which ones to try:

<!-- example: spec-actions -->
```rescript
type operation = Deposit(int) | Withdraw(int)

@spec
let neverOverdrawn: Spec.t<int, operation> = {
  init: 0,
  step: apply,
  actions: balance => balance < 100 ? [Deposit(50), Withdraw(30)] : [Withdraw(30)],
  always: balance => balance >= 0,
}
```
<!-- /example -->

`actions` is also what keeps a machine small. This one stops depositing at
100, so it has 15 states. A machine with no end of states is looked at up to
a bound (`--states`, 100,000 unless given), and the report says so: `always
held over the first 100000 states (there are more)`.

Leaving `actions` out when the action type has too many values is an error
of the build, not of the run:

<!-- example: spec-unlisted -->
```
  The actions of the spec `neverOverdrawn` cannot be listed: the type has
  too many values: each would be tried in every state.

  A spec without `actions` tries every value of its action type in every
  state. Give this one `actions: state => [...]`: the actions that can
  happen in a state.
```
<!-- /example -->

### Specs are pure, and no part of the program

A spec is checked like a [`@pure`](pure.md) binding, without saying so, and
with it the reducer it names. A reducer that changes the state it is given
would change the states already visited:

<!-- example: spec-impure -->
```rescript
let update = (cart, event) =>
  switch event {
  | Add =>
    cart.items->Array.push("item")
    cart
  | Clear => {items: []}
  }
```

```
  `update` is not pure, and `cart` is @pure.

  Line 8: This changes a value that `update` did not create itself.
```
<!-- /example -->

This is the bug that React's reducers must not have, found by the build.

Like a law, a spec cannot be referred to, and it is in no interface. A build
leaves it out.

## Reference

### What a spec is

A value binding is a spec when it has the attribute `@spec`. It must be

1. a `let` of a single name, not joined to others with `and`,
2. at the top level of a file, or of a module written as
   `module M = { ... }` at such a level,
3. of type `Spec.t<state, action>`.

`Spec.t` is a record of the standard library:

```rescript
type t<'state, 'action> = {
  init: 'state,
  step: ('state, 'action) => 'state,
  actions?: 'state => array<'action>,
  always?: 'state => bool,
  sometimes?: 'state => bool,
  reachable?: 'state => bool,
  eventually?: 'state => bool,
}
```

A spec written as a record must have at least one of the four properties.
When it has no `actions`, its action type must have at most 10,000 values
that the compiler can make (the rules are those of a [law's
parameters](law.md#values-of-your-own-types)).

A spec is type checked as written and checked as a `@pure` binding. Like a
law, its name is not added to the environment, and a build leaves it out of
the module's signature and of the JavaScript.

### The states of a machine

`rescript verify` compiles each file that has a spec with its specs
exported, as it does for laws, and for each spec:

1. Starts with `init`.
2. For each state not seen before, in the order they were found, takes the
   actions (`actions(state)`, or every value of the action type) and applies
   `step` to each. The results not seen before are new states.
3. Stops when there are no new states, or at the bound of `--states`.

Two states are the same when they are equal as `==` has it: structurally. A
state that holds a function cannot be compared and fails the spec.

Because states are found nearest first, the run to each state is the
shortest there is.

### The properties

| Property | Holds when | Reported when it fails |
| --- | --- | --- |
| `always` | it is true in every state | the shortest run to a state where it is false |
| `sometimes` | it is true in at least one state | the number of states, none of which has it |
| `reachable` | from every state, some run leads to a state where it is true | the shortest run to a state from which none does |
| `eventually` | every run gets to a state where it is true | a run that never does: one that ends, or one that goes round |

For `eventually`, a step is an action that changes the state. A run ends in
a state that no action changes.

When the bound on states was reached, `always` is reported as `held over the
first n states (there are more)`, which is not a proof. `sometimes` holds
when a state with the property was found. `reachable` and `eventually`
cannot be decided on a part of the machine and are reported as not decided,
which fails the spec.

A function of the spec that raises fails it, with the run that led there.

### Cost

A file without `@spec` pays nothing. A spec costs a build its type check and
purity check. `rescript verify` keeps every state of a machine in memory,
with a text made from it to compare states by.

## Alternatives

- **TLA+ or another modelling language.** It can say more: fairness,
  several processes, refinement. It checks a model, which is a second
  description to write and to keep true to the code. A spec checks the
  reducer that ships.
- **A law over a list of actions**: `(actions: array<event>) => ...` folds
  the reducer over generated lists. It needs nothing new and finds what
  breaks `always`. It samples, so it proves nothing, and it cannot say
  `reachable` or `eventually`, which are about all runs.
- **Model-based testing libraries** (XState's, fast-check's commands).
  These need the machine described in the library's own form, beside the
  reducer.
- **Properties as separate bindings** (`@always(machine) let ...`). Each
  property would have a name of its own in the report. It needs attributes
  that refer to values; a record needs nothing the language does not have.

## Open questions

- `Spec` is a new module of the standard library, which every file opens: a
  project's own `Spec.res` would be hidden by it. The record could live
  elsewhere, or `@spec` could give a record literal its type.
- Names for properties: a spec has one `always`. Several, each reported by
  name, would need a different field type.
- Several first states, for a machine that starts from saved data.
- Effects. A reducer that returns commands (a request to send) has their
  answers as actions; a spec could pair each command with the actions it can
  cause, which `actions` does by hand today.
- Fairness for `eventually`: "if the user keeps retrying, it settles" cannot
  be said.
- Larger machines: comparing states by a hash, symmetry, a depth bound.
- Printing only what changed between two states of a long record.
- The OCaml compiler ignores `@spec`: there a spec is an ordinary export.
