@deprecated("line one
line two")
module M = {
  type r = {a: int, b: int}
  let x = 1
  module type S = {
    let v: int
  }
}
@deprecated({reason: "record payload", migrate: M.x})
module R = {
  let y = 2
}
module Alias = M
module Err = Stdlib_Error
let r1 = {M.a: 1, b: 2}
let r2 = r1.M.a
let r3 = switch r1 {
| {M.a: 1, b} => b
| _ => 0
}
let x2 = Alias.x
let y2 = R.y
let m = Err.message
@warning("-3") let quiet = M.x
module type T = M.S
module F = (X: M.S) => {
  let w = X.v
}
module rec Rec1: {
  let f: int => int
} = {
  let f = n => M.x + n
}
