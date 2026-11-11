// Only `invoiceTotal` is asked for. TypeScript parses billing.ts, then
// resolves the type of that one function and the `Invoice` it mentions.
// The sixty other functions in the file are not checked. See "TypeScript"
// on the right for the numbers.
let {invoiceTotal} = %ts("./billing.ts")

let total = invoiceTotal({id: "2026-001", total: 120.})
