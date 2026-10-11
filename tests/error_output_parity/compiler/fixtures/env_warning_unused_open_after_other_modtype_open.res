// error-output-parity: Env warning 33 when a later open does not provide the unqualified module type that is used.
@@warning("+33-34-37")

module A = {
  module type Item = {}
}

module B = {
  let value = 1
}

open A
open B

module Result: Item = {}
