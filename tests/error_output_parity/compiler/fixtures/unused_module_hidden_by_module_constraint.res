// error-output-parity: Warning 60 for an implementation module hidden by an
// explicit module constraint.
module type S = {}

module M: S = {
  module N = {}
}
