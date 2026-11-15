// The other unit's constructors read without the outer alias: both
// compilers agreed on these before.

let v = Alias_chain_constructor_unit_lib.A.A
let g = x =>
  switch x {
  | Alias_chain_constructor_unit_lib.A.B => 1
  | _ => 0
  }
