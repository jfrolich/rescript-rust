// error-output-parity: Typemod.Signature_expected for including a functor in a signature.
module type S = {}

module type T = {
  include (X: S) => {}
}
