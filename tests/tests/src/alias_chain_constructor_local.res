// Constructors, exception and extension constructors and record labels
// read through an alias (`O`) of a module that holds an alias (`A = R`).

module Outer = {
  module R = {
    type t = A | B
    type r = {f: int}
    type u = I({w: int})
    type ext = ..
    type ext += C(int)
    exception E(int)
  }
  module A = R
  module B = A
  module S = {
    module T = {
      type t = X | Y
    }
  }
  module Z = S.T
}
module O = Outer
module P = O

let v = O.A.A
let e = O.A.E(1)
let c = O.A.C(1)
let i = O.A.I({w: 1})
let r = {O.A.f: 1}
let f = r.O.A.f
let b = O.B.B
let p = P.A.B
let z = O.Z.X

let byConstructor = (x: Outer.R.t) =>
  switch x {
  | O.A.A => 1
  | O.B.B => 2
  }

let byLabel = (x: Outer.R.r) =>
  switch x {
  | {O.A.f: n} => n
  }

let byInlineRecord = x =>
  switch x {
  | O.A.I({w}) => w
  }

let byExtension = (x: Outer.R.ext) =>
  switch x {
  | O.A.C(n) => n
  | _ => 0
  }

let byException = g =>
  try g() catch {
  | O.A.E(n) => n
  }

module Inner = {
  module R = {
    type t = Q | W
  }
  module A = R
}
module I = {
  include Inner
}
module J = I
let q = J.A.Q
