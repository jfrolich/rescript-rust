// error-output-parity: Includemod.Modtype_infos via Typemod.Not_included
module M: {
  module type S = {
    let x: int
  }
} = {
  module type S = {
    let x: string
  }
}
