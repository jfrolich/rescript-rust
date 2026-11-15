module R = {
  type ext = ..
  type ext += C(int)
}
module G = (X: {}) => {
  module S = {}
}
module M = G({})
let c = R.C(1)
