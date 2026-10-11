// The ambiguity warning is printed before the type error; later messages are
// printed without color tags.
module type S = {
  type a = A | B
  type b = | ...a | C
}
module M: S = {
  type a = A | B
  type b = | ...a | C
}
let y: int = M.A
