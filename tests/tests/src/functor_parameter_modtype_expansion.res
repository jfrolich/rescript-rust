// Applying a functor to an anonymous argument removes the dependency on the
// parameter from module types of the result by expanding a module type path
// of the parameter, as OCaml's `Mtype.nondep_supertype` does
// (compiler/ml/mtype.ml:110-113).

module type S = {
  let x: int
}

// The result declares `module type T = X.T` next to a package value.
module F = (
  X: {
    module type T = S
    let p: module(T)
  },
) => {
  module type T = X.T
  let p = X.p
}

module R = F({
  module type T = S
  module M = {
    let x = 1
  }
  let p = module(M: T)
})

let fromR = {
  module Y = unpack(R.p: R.T)
  Y.x
}

// The same with an explicit result signature.
module FSig = (
  X: {
    module type T = S
    let p: module(T)
  },
): {
  module type T = X.T
  let p: module(T)
} => {
  module type T = X.T
  let p = X.p
}

module RSig = FSig({
  module type T = S
  module M = {
    let x = 2
  }
  let p = module(M: T)
})

let fromRSig = {
  module Y = unpack(RSig.p: RSig.T)
  Y.x
}

// In a nested module of the result.
module Nested = (X: {module type T = S}) => {
  module N = {
    module type T = X.T
  }
}

module RNested = Nested({
  module type T = S
})

module MNested: RNested.N.T = {
  let x = 3
}

// As the parameter type of a functor the result returns.
module Curried = (X: {module type T = S}) => (Y: X.T) => {
  let z = Y.x + 1
}

module G = Curried({
  module type T = S
})

module RCurried = G({
  let x = 4
})

// A module type of the parameter that mentions a type of the parameter.
module WithType = (
  X: {
    type t
    module type T = {
      let x: t
    }
  },
) => {
  module type T = X.T
}

module RWithType = WithType({
  type t = int
  module type T = {
    let x: t
  }
})

module MWithType: RWithType.T = {
  let x = 5
}

// A functor in the result whose body declares the module type too.
module Inner = (X: {module type T = S}) => {
  module G = (Y: X.T) => {
    module type U = X.T
    let w = Y.x
  }
}

module RInner = Inner({
  module type T = S
})

module QInner = RInner.G({
  let x = 6
})

// Agreed before: the result names the module type only in a type.
module TypeOnly = (X: {module type T = S}) => {
  type t = module(X.T)
  module type U = S
}

module RTypeOnly = TypeOnly({
  module type T = S
})

let typeOnly: RTypeOnly.t = module(MNested)

let total = fromR + fromRSig + MNested.x + RCurried.z + MWithType.x + QInner.w
