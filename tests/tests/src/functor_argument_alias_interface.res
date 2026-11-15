// The alias of a functor parameter's module, re-exported by the functor and
// used through an interface that hides the functor.
module N = {
  let x = 1
}

module F = (
  X: {
    module N: {
      let x: int
    }
    module M = N
    module L = M
  },
) => {
  module Z = X.L
  let v = Z.x
}

module R = F({
  module N = N
  module M = N
  module L = M
})

let y = R.Z.x + R.v
