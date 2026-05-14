// error-output-parity: local let-module type escape reported through Pattern_type_clash.
let value = {
  module M = {
    type t
  }

  (x: M.t) => x
}
