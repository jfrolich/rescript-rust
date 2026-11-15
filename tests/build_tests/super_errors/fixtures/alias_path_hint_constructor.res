module Outer = {
  module R = {
    type t = Apple | Banana
  }
  module A = R
}
let v = Outer.A.Aple
