module Outer = {
  module R = {
    type r = {f: int}
  }
  module A = R
}
module O = Outer
let r = {O.A.ff: 1}
