// error-output-parity: Typemod.Cannot_apply
module type S = {}

module Arg = {}

module M = {
  let value = 1
}

let value = module(M(Arg): S)
