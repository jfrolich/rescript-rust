type coupon = Percent(int) | Fixed(int) | FreeShipping
type order = {amount: int, coupon: coupon, shipping: int}

let discount = order =>
  switch order.coupon {
  | Fixed(n) => n
  | Percent(_) | FreeShipping => 0
  }

let shipping = order =>
  switch order.coupon {
  | FreeShipping => 0
  | Percent(_) | Fixed(_) => order.shipping
  }

let total = order => order.amount - discount(order) + shipping(order)

let clamp = (x, low, high) => x < low ? low : x > high ? high : x

@law
let freeShippingCostsTheAmount = (amount: int, shipping: int) =>
  total({amount, shipping, coupon: FreeShipping}) == amount

@law
let totalAddsUp = (order: order) =>
  total(order) + discount(order) == order.amount + shipping(order)

@law(proved)
let clampStaysInRange = (x: int, low: int, high: int) =>
  low > high || {
      let clamped = clamp(x, low, high)
      low <= clamped && clamped <= high
    }

// Not true: `+` wraps around at the largest int. The run finds it.
@law
let successorIsLarger = (n: int) => n + 1 > n
