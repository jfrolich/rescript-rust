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
