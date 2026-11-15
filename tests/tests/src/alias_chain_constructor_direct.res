// Read without the outer alias, and as a value and a type through it: both
// compilers agreed on these before constructors through `O.A` were found.

module Outer = {
  module R = {
    type t = A | B
    type r = {f: int}
    exception E(int)
    let x = 1
  }
  module A = R
}
module O = Outer

let v = Outer.A.A
let e = Outer.A.E(1)
let r = {Outer.A.f: 1}
let x = O.A.x
let t: O.A.t = Outer.R.B

module Q = O.A
let w = Q.A

open O
let u = A.B
