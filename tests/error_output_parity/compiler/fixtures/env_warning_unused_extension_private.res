// error-output-parity: Env warning 38 notes extensions exported through private signatures.
module type S = {
  type t = ..
  type t += private Hidden
}

module M: S = {
  type t = ..
  type t += Hidden
}
