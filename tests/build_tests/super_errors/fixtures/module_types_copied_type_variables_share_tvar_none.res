// The copies of x, y and z in g0 and g1 share OCaml's static `Tvar None`: 399 words, printed.
module M: {
  let v: string
} = {
  let id = (x, y, z) => x
  let g0 = id
  let g1 = id
  let h0 = 1
  let v = 1
}
