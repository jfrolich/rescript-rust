module type S = {let x: int}
module R = {
  module Y = {
    module type T = S
  }
  module type T = Y.T
}
module M: R.T = {
  let x = 2
}
module N: {
  let x: int
  let y: int
} = M
