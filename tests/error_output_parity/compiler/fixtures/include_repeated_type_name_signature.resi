// Signature includes are checked for repeated names.
module type S = {
  type t
}
type t
include S
