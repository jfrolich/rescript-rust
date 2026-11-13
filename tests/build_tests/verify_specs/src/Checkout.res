// Paying: the button can be pressed while a charge is on its way.
type checkout = {pending: int, charges: int}
type event = Pay | Charged

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

module Dialog = {
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
}

// An action type with no end of values: the spec says which can happen.
type operation = Deposit(int) | Withdraw(int)

let apply = (balance, operation) =>
  switch operation {
  | Deposit(amount) => balance + amount
  | Withdraw(amount) => balance >= amount ? balance - amount : balance
  }

@spec
let neverOverdrawn: Spec.t<int, operation> = {
  init: 0,
  step: apply,
  actions: balance => balance < 100 ? [Deposit(50), Withdraw(30)] : [Withdraw(30)],
  always: balance => balance >= 0,
}

// A machine with no end of states is looked at up to a number of them.
@spec
let counts: Spec.t<int, unit> = {
  init: 0,
  step: (count, ()) => count + 1,
  always: count => count >= 0,
}

// A step that raises is a failure of the spec.
@spec
let raises: Spec.t<int, bool> = {
  init: 0,
  step: (count, up) => up ? count + 1 : 10 / count,
  actions: count => count < 2 ? [true, false] : [],
  always: count => count >= 0,
}
