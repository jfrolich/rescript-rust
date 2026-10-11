// error-output-parity: Typemod.With_makes_applicative_functor_ill_typed
module type S = {
  module M: {
    module N: {
      type t
    }
  }
  module F: (X: {type t = M.N.t}) => {type u}
  module R: module type of F(M.N)
}

module type T = S with type M.N.t := string
