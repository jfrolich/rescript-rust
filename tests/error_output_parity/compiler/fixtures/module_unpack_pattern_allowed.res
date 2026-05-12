// error-output-parity: Typecore allows Ppat_unpack module patterns in match cases.

module type S = {}

let f = (x: module(S)) =>
  switch x {
  | module(M) => 0
  }
