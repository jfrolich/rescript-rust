// `module Z = X.M` for an alias `M` declared in the parameter's signature
// keeps the alias: Z is absent at run time, in the functor and in its
// applications.
module N = {
  let x = 1
}

module F = (
  X: {
    module N: {
      let x: int
    }
    module M = N
  },
) => {
  module Z = X.M
}

module R = F({
  module N = N
  module M = N
})

let y = R.Z.x

// A submodule of the parameter that is not an alias keeps its strengthened
// type: Z.K is reached through Z, and the result eliminates the parameter.
module G = (
  X: {
    module N: {
      module K: {
        let x: int
      }
    }
  },
) => {
  module Z = X.N
  let v = Z.K.x
}

module S = G({
  module N = {
    module K = {
      let x = 2
    }
  }
})

let w = S.v

// The alias accessed as a value agreed before.
module H = (
  X: {
    module N: {
      let x: int
    }
    module M = N
  },
) => {
  let v = X.M.x
}

module T = H({
  module N = N
  module M = N
})

let u = T.v
