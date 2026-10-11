// error-output-parity: Typemod.Signature_expected
module M: {
  module type S
} = {
  module type S = {}
}

type p = module(M.S with type t = int)
