// error-output-parity: Env warning 44 for a signature open shadowing a later-used module.
@@warning("+44-34-37")

module Item: {
  type t
}

module M: {
  module Item: {
    type t
  }
}

open M

type result = Item.t
