// error-output-parity: module rec in a signature runs check_recmod_typedecls.
module type S = {
  module rec A: {
    type t = A.u
    type u = t
  }
}
