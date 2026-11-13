type item = {name: string, price: int, qty: int}

let total = items => items->Array.reduce(0, (sum, item) => sum + item.price * item.qty)

@law
let totalIgnoresOrder = (items: array<item>) => total(items) == total(items->Array.toReversed)

@law
let totalOfTwoCarts = (a: array<item>, b: array<item>) =>
  total(Array.concat(a, b)) == total(a) + total(b)
