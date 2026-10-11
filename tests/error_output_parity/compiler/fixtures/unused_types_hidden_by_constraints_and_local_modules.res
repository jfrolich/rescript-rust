module type S = {
  type t
  type u = A | B
}
module M: {
  type v
} = {
  type v
  type w = C
}
let f = () => {
  module L = {
    type z = D
  }
  1
}
