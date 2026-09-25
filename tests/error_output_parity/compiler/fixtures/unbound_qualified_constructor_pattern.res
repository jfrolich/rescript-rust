// error-output-parity: a qualified unknown constructor in a pattern is reported at the constructor
module M = {}
let f = x =>
  switch x {
  | M.Reducer(a) => a
  }
