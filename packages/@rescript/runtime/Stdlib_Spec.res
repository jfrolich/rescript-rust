/***
A spec says what a state machine does and what must be true of it. Mark a
`let` of this type with `@spec`, and `rescript verify` goes through every
state the machine can get into, in every order of actions, and checks it.

```rescript
type state = {count: int}
type action = Increment | Reset

@spec
let counter: Spec.t<state, action> = {
  init: {count: 0},
  step: (state, action) =>
    switch action {
    | Increment => {count: mod(state.count + 1, 4)}
    | Reset => {count: 0}
    },
  always: state => state.count < 4,
}
```

A build type checks a spec and leaves it out of the JavaScript.
*/

/**
A state machine over `'state`, with what to check about it.

- `init` is the state it starts in.
- `step` gives the state after an action: a reducer.
- `actions` gives the actions that can happen in a state. Without it, every
  value of `'action` can happen in every state.
- `always` must be true in every state the machine can get into.
- `sometimes` must be true in at least one of them.
- `reachable` must stay possible: from every state the machine can get into,
  some actions lead to a state where it is true.
- `eventually` must be certain: whatever actions happen, the machine gets to
  a state where it is true. An action that leaves the state as it is does
  not count as a step.
*/
type t<'state, 'action> = {
  init: 'state,
  step: ('state, 'action) => 'state,
  actions?: 'state => array<'action>,
  always?: 'state => bool,
  sometimes?: 'state => bool,
  reachable?: 'state => bool,
  eventually?: 'state => bool,
}
