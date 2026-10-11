// error-output-parity: Typemod.Structure_expected for including a functor as a structure.
module type S = {}

module F = (_X: S) => {}

module M = {
  include F
}
