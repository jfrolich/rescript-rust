// error-output-parity: Warning 34 for an implementation type hidden by an
// explicit module constraint.
module type S = {}

module M: S = {
  type t = int
}
