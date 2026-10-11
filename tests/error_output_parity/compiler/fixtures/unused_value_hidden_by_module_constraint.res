// error-output-parity: Warning 32 for an implementation value hidden by an
// explicit module constraint.
module type S = {}

module M: S = {
  let value = 1
}
