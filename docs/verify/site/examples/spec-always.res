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
