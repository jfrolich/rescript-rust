module Outer = {
  module R = {
    type ext = ..
    type ext += C(int)
  }
}
module G = (X: {}) => {
  let x = 1
}
module M = G({})
let c = Outer.R.C(M.x)
