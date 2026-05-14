// error-output-parity: Env warning 37 notes constructors that are only used in patterns.
module type S = {}

module M: S = {
  type t = A | B

  let check = value =>
    switch value {
    | A => true
    | B => false
    }
}
