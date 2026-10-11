// error-output-parity: Typemod.With_mismatch
module type S = {
  type t = int
}

module type T = S with type t = string
