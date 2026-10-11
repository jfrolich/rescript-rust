// error-output-parity: Env warning 44 for an open shadowing a later-used value.
@@warning("+44-32")

let value = 1

module M = {
  let value = 2
}

open M

let result = value
