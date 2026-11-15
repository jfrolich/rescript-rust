// Constructors through an alias of a functor application's result that
// holds an alias, and through an alias of a functor parameter.

module G = (X: {let n: int}) => {
  module R = {
    type t = K | L
    let n = X.n
  }
  module A = R
}
module M = G({
  let n = 1
})
module N = M
let k = N.A.K

module F = (
  X: {
    module R: {
      type t = A | B
      type r = {f: int}
    }
    module A = R
  },
) => {
  module Y = X
  let v = Y.A.A
  let r = {Y.A.f: 1}
  let g = x =>
    switch x {
    | Y.A.B => r.Y.A.f
    | _ => 0
    }
}
module H = F({
  module R = {
    type t = A | B
    type r = {f: int}
  }
  module A = R
})
let h = H.v
