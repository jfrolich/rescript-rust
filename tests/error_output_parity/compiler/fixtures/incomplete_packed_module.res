// error-output-parity: Typemod.Incomplete_packed_module
module type S = {type t}

let f = (m: module(S with type t = 'a)) => {
  module M = unpack(m)
  ()
}
