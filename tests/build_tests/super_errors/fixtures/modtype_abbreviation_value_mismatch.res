module type S = {let x: int}
module R = {
  module Y = {
    module type T = S
  }
  module type T = Y.T
}
module M: R.T = {
  let x = "a"
}
