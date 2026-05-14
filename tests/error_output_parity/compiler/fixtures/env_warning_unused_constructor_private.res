// error-output-parity: Env warning 37 notes constructors exported through private signatures.
module type S = {
  type t = private A | B
}

module M: S = {
  type t = A | B
}
