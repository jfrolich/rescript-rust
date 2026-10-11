// error-output-parity: Env warning 44 for reopening the same module and using the shadowing module.
@@warning("+44-34-37")

module M = {
  module Item = {
    let value = 1
  }
}

open M

let _before = Item.value

open M

let result = Item.value
