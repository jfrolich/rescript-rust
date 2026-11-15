module type A = {module type T}
module B: A = {
  module type T = {let x: int}
}
module R = {
  module Y = B
  module type T = Y.T
}
module M: R.T = {
  let x = 1
}
