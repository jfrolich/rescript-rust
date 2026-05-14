// error-output-parity: Env warning 44 for an open shadowing a later-used module.
@@warning("+44-34-37")

module Item = {
  let value = 1
}

module M = {
  module Item = {
    let value = 2
  }
}

open M

let result = Item.value
