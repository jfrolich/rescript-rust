// error-output-parity: parenthesized arrow return type recovery
let make = (x: 'v): 'b. ('v => 'b) => 'b => f => f(x)
