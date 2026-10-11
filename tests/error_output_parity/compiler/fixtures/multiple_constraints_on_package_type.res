// error-output-parity: Typetexp.Multiple_constraints_on_type
module type S = {
  type t
}

type p = module(S with type t = int and type t = string)
