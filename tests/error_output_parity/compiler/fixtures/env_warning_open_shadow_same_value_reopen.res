// error-output-parity: Env warning 44 for reopening the same module and using the shadowing value.
@@warning("+44-34-37")

module M = {
  let value = 1
}

open M

let _before = value

open M

let result = value
