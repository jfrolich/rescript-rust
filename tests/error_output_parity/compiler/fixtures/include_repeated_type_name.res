// Included signatures are checked for repeated names.
module A = {
  type t = int
}
include A
include A
