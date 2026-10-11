// error-output-parity: Typemod.Not_allowed_in_functor_body
module F = () => {type t}
module G = (X: {}) => {
  module M = F()
}
