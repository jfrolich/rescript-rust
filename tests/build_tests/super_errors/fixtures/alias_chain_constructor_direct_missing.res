module Outer = {
  module R = {
    type t = A | B
  }
  module A = R
}
let v = Outer.A.C
