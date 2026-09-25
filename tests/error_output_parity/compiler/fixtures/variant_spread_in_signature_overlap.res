// Variant spreads in signatures are expanded like in structures.
module type S = {
  type a = A | B
  type b =
    | ...a
    | A
}
