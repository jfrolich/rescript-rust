// Applying a functor to an anonymous argument makes the extension
// constructors of the result independent of the parameter: their arguments
// and the extended type (compiler/ml/ctype.ml:4521-4552).

module F = (X: {type t}) => {
  exception E(X.t)
}

module R = F({
  type t = int
})

let e = R.E(1)

type base = ..

module Extend = (X: {type t = ..}) => {
  type X.t += A
}

module RExtend = Extend({
  type t = base = ..
})

let a: base = RExtend.A

// Agreed before: the constructor does not mention the parameter.
module Plain = (X: {type t}) => {
  exception P(int)
}

module RPlain = Plain({
  type t
})

let p = RPlain.P(2)
