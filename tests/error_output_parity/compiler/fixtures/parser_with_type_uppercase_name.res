// error-output-parity: with-type constraints require lowercase type names.
module type S = {type t}
module type T = S with type T = int
