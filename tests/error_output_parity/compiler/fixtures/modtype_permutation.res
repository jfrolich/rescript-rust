// error-output-parity: Includemod.Modtype_permutation for equivalent module
// type declarations that require a structure-field permutation.
module type S1 = {
  let x: int
  let y: int
}

module type S2 = {
  let y: int
  let x: int
}

module M: {
  module type T = S1
} = {
  module type T = S2
}
