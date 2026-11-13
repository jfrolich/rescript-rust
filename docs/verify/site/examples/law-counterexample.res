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
