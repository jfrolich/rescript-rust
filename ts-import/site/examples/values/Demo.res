// The names are the exports of the module. Their types are
// whatever TypeScript says they are.
let {add, formatPrice, average, taxRate} = %ts("./math.ts")

let total = add(19.99, 5.)
let label = formatPrice(total)
let inDollars = formatPrice(total, ~currency="USD")
let mean = average([1., 2., 3., 4.])
let tax = total *. taxRate

Console.log3(label, inDollars, mean)
