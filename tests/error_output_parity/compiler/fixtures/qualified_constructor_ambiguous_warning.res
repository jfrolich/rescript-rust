// A qualified constructor without an expected variant type warns when the
// module defines it in several types (NameChoice.disambiguate).
module M = {
  type a = A | B
  type b = A | C
}
let g = M.A
let f = x =>
  switch x {
  | M.A => 1
  | _ => 2
  }
