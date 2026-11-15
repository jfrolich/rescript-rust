module Outer: {
  module R: {
    type ext = ..
    type ext += C(int)
  }
}
module M: {
  let x: int
}
