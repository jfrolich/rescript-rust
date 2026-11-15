// Constructors and labels through an alias of another unit that holds an
// alias: their result type is `O.A.t`, so the match's exhaustiveness check
// finds the variant.

module O = Alias_chain_constructor_unit_lib
let v = O.A.A
let e = O.A.E(1)
let c = O.A.C(1)
let r = {O.A.f: 1}
let g = x =>
  switch x {
  | O.A.B => r.O.A.f
  | _ => 0
  }
let h = (x: Alias_chain_constructor_unit_lib.R.t) =>
  switch x {
  | O.A.A => 1
  | O.A.B => 2
  }

module P = O
let w = P.Outer.A.B
let k = x =>
  switch x {
  | P.Outer.A.A => 1
  | _ => 0
  }
