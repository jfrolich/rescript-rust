// A functor that includes its parameter re-exports the parameter's alias.
// Applied to a structure, the parameter is eliminated from the result by
// replacing the alias of a parameter module with that module's type.
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
  include X
}

module R = F({
  module N = N
  module M = N
})

let y = R.M.x

// The parameter's module is not an alias: the result already agreed.
module G = (
  X: {
    module N: {
      let x: int
    }
    module M: {
      let x: int
    }
  },
) => {
  module Z = X.M
}

module S = G({
  module N = N
  module M = N
})

let z = S.Z.x
