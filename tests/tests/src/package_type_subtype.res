// A coercion between first-class module types follows OCaml's package arm of
// `subtype_rec` (compiler/ml/ctype.ml:4077-4104).

module type S = {type t}

// A constraint the target does not have is dropped.
let dropConstraint = (x: module(S with type t = int)) => (x :> module(S))

// The same constraints on both sides.
let sameConstraints = (x: module(S with type t = int)) => (x :> module(S with type t = int))

module type S2 = {
  type t
  type u
}

let dropOneOfTwo = (x: module(S2 with type t = int and type u = string)) =>
  (x :> module(S2 with type t = int))

let dropTheFirst = (x: module(S2 with type u = string and type t = int)) =>
  (x :> module(S2 with type u = string))

module type Nested = {
  module M: {
    type t
  }
}

let dropNested = (x: module(Nested with type M.t = int)) => (x :> module(Nested))

// Different module type paths: the module types are included in each other.
module type V = {
  let x: int
}
module type W = {
  let x: int
}

let otherPath = (x: module(V)) => (x :> module(W))

module type T = S

let abbreviation = (x: module(S with type t = int)) => (x :> module(T))

module type X = {
  type t
  let x: t
}
module type Y = {
  type t
  let x: t
}

let otherPathConstrained = (x: module(X with type t = int)) => (x :> module(Y))

module A = {
  module type S = {
    type t
  }
}
module B = A

let moduleAlias = (x: module(A.S with type t = int)) => (x :> module(B.S))

module N = {
  module type T = S
}

let nestedAbbreviation = (x: module(S with type t = int)) => (x :> module(N.T))

module F = (_: {}) => {
  module type T = S
}
module N1 = F({})
module N2 = F({})

let functorResult = (x: module(S with type t = int)) => (x :> module(N1.T))

let twoApplications = (x: module(N1.T with type t = int)) => (x :> module(N2.T))
