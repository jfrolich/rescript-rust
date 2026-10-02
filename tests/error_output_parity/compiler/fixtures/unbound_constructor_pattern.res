// error-output-parity: an unknown constructor in a pattern is Unbound_constructor
let f = x =>
  switch x {
  | Reducer(a, b) => a + b
  }
