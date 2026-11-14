// A package is resolved as TypeScript resolves it: through node_modules,
// package.json and the declaration file it points to.
let {money, plus, format} = %ts("tiny-money")

let price = money(19.99, #EUR)
let shipping = money(4.5, #EUR)
let label = format(plus(price, shipping), ~locale="nl-NL")
