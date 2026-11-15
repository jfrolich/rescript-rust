module Outer = {
  module R = {
    type t = A | B
  }
  module A = R
}
module O = Outer
let v: Outer.R.t = O.A.Bb
