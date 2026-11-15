module R = {
  type t = A | B
  type r = {f: int}
  type ext = ..
  type ext += C(int)
  exception E(int)
}
module A = R
module Outer = {
  module R = R
  module A = R
}
