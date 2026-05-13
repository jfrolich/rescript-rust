// error-output-parity: Env warning 44 for reopening the same module and using the shadowing module type.
@@warning("+44-34-37")

module M = {
  module type Item = {}
}

open M

module Before: Item = {}

open M

module Result: Item = {}
