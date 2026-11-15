// Applying a functor to an anonymous argument removes the dependency on the
// parameter from first-class module types of the result by normalizing their
// module type path first, as OCaml's `nondep_type_rec` does
// (compiler/ml/ctype.ml:4443-4446).

module type S = {
  let x: int
}

module F = (
  X: {
    module type T = S
    let p: module(T)
  },
) => {
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
  module Y = unpack(R.p: S)
  Y.x
}

// An abstract module type in the parameter: the argument defines it.
module Abstract = (
  X: {
    module type T
    let p: module(T)
  },
) => {
  let p = X.p
}

module RA = Abstract({
  module type T = S
  module M = {
    let x = 2
  }
  let p = module(M: T)
})

// A module type in a nested module.
module Nested = (
  X: {
    module N: {
      module type T = S
    }
    let p: module(N.T)
  },
) => {
  let p = X.p
}

module RN = Nested({
  module N = {
    module type T = S
  }
  module M = {
    let x = 3
  }
  let p = module(M: N.T)
})

// Through two functors.
module type P = {
  module type T = S
  let p: module(T)
}

module F1 = (X: P) => {
  let p = X.p
}
module F2 = (Y: P) => F1(Y)

module R2 = F2({
  module type T = S
  module M = {
    let x = 4
  }
  let p = module(M: T)
})

// A constrained package.
module type St = {
  type t
  let x: t
}

module Constrained = (
  X: {
    module type T = St
    let p: module(T with type t = int)
  },
) => {
  let p = X.p
}

module RC = Constrained({
  module type T = St
  module M = {
    type t = int
    let x = 5
  }
  let p = module(M: T with type t = int)
})

// A chain of module type abbreviations.
module Chain = (
  X: {
    module type U = S
    module type T = U
    let p: module(T)
  },
) => {
  let p = X.p
}

module RCh = Chain({
  module type U = S
  module type T = U
  module M = {
    let x = 6
  }
  let p = module(M: T)
})

let q: module(S) = RCh.p

// A package type in a type declaration (agreed before).
module G = (
  X: {
    module type T = S
  },
) => {
  type t = module(X.T)
}

module RG = G({
  module type T = S
})
