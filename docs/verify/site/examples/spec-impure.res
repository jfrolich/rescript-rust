type cart = {items: array<string>}
type event = Add | Clear

// Changes the cart it was given.
let update = (cart, event) =>
  switch event {
  | Add =>
    cart.items->Array.push("item")
    cart
  | Clear => {items: []}
  }

@spec
let cart: Spec.t<cart, event> = {
  init: {items: []},
  step: update,
  always: cart => Array.length(cart.items) <= 3,
}
