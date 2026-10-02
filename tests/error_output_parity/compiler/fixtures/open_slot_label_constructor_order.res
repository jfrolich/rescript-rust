// Shadow warnings are reported in lookup order; unused opens at the end.
type t = A | B
type r = {f: int}
let v = 1

module M = {
  type t = A | C
  type r = {f: string}
  let v = "s"
}

module N = {
  let unused = 1
}

open M
open N

let a = (x: r) => x.f
let b = A
let c = v
let d = {
  open M
  C
}
