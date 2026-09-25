// A signature spread expands to the same constructors as the implementation.
module type S = {
  type a = A | B
  type b =
    | ...a
    | C
}
module M: S = {
  type a = A | B
  type b = | ...a | C
}
let x: M.b = M.C
let y: M.b = M.B
let z: int = x
