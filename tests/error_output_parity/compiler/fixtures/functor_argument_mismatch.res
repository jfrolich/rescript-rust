// error-output-parity: Typemod.Not_included through functor argument checking.
module type S = {
  let x: int
}

module F = (X: S) => {}

module M = {
  let x = "x"
}

module N = F(M)
