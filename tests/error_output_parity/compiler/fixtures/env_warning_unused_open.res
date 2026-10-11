// error-output-parity: Env warning 33 for an unused structure open.
@@warning("+33-32-34-37")

module M = {
  let value = 1
}

open M

let result = 2
