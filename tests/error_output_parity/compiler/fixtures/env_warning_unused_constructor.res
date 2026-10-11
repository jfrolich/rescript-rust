// error-output-parity: Env emits warning 37 for unused regular constructors.
module type S = {}

module M: S = {
  type t = A | B
}
