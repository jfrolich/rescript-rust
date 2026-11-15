// A module whose type is a module type abbreviation of a submodule, then
// constrained by the abbreviation's target and by the abbreviation again.

module type S = {let x: int}

module R = {
  module Y = {
    module type T = S
  }
  module type T = Y.T
}

module M: R.T = {
  let x = 2
}

module N: R.Y.T = M

module P: S = N

module Q: R.T = P

// An abstract module type reached through a module alias, as a functor
// parameter (agreed before).
module type A = {module type T}

module B: A = {
  module type T = {let x: int}
}

module R2 = {
  module Y = B
  module type T = Y.T
}

module F = (X: R2.T) => X

module G = (X: B.T) => F(X)

let v = Q.x + N.x
