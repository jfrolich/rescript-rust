// error-output-parity: parser suppresses a cascading dot error after an uppercase type argument.
module M = {
  type t
}

module A = {}

type u = M(A).t
