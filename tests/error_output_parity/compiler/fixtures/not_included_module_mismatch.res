// error-output-parity: Includemod.Module_types via Typemod.Not_included
module M: {
  module N: {
    let x: int
  }
} = {
  module N = {
    let x = "x"
  }
}
