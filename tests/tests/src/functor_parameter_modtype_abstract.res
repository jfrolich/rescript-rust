// When a module type declaration of a functor's result cannot be made
// independent of the parameter, it becomes abstract in a covariant position
// (compiler/ml/mtype.ml:147-158) and the application is accepted.

module type S = {
  let x: int
}

module A = {
  module type T = S
}

module type P = {
  module type T
}

let m = module(A: P)

// The argument's module type is abstract.
module F = (X: {module type T}) => {
  module type U = X.T
}

module R = F(unpack(m))

// Nested in a module type declaration: the inner one is strict, so the
// outer one becomes abstract.
module Nested = (X: {module type T}) => {
  module type U = {
    module type V = X.T
  }
}

module RNested = Nested(unpack(m))

// The abstract module type is still usable in the result's values.
module WithValue = (X: {module type T}) => {
  module type U = X.T
  let f = (m: module(U)) => m
}

module RWithValue = WithValue(unpack(m))

// The expansion mentions an abstract type of the argument.
module WithType = (
  X: {
    type t
    module type T = {
      let x: t
    }
  },
) => {
  module type T = X.T
  let v = 1
}

module RWithType = WithType({
  type t
  module type T = {
    let x: t
  }
})

let v = RWithType.v
