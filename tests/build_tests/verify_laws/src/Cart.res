type item = {name: string, price: int, qty: int}
type coupon = Percent(int) | Fixed(int) | FreeShipping

let total = items => items->Array.reduce(0, (sum, item) => sum + item.price * item.qty)

let apply = (amount, coupon) =>
  switch coupon {
  | Percent(p) => amount - amount * p / 100
  | Fixed(n) => amount - n
  | FreeShipping => amount
  }

// Holds, and is checked on random carts.
@law
let totalIgnoresOrder = (items: array<item>) => total(items) == total(items->Array.toReversed)

// Does not hold: a coupon can be negative.
@law
let couponNeverRaisesThePrice = (amount: int, coupon: coupon) => apply(amount, coupon) <= amount

// Two booleans have four values, so this one is tried on all of them.
@law
let deMorgan = (a: bool, b: bool) => !(a && b) == (!a || !b)
