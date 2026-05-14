// error-output-parity: Env warning 44 for a signature open shadowing a later-used module type.
@@warning("+44-34-37")

module type Item = {}

module M: {
  module type Item = {}
}

open M

module Result: Item
