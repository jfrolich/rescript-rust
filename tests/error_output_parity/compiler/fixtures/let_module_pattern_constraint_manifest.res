// error-output-parity: a let-module manifest type in a parameter constraint expands instead of escaping.
let value = {
  module M = {
    type t = string
  }
  (x: M.t) => x
}
