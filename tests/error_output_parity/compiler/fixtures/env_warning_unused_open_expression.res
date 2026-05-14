// error-output-parity: Env warning 33 for an unused local open expression.
@@warning("+33-32-34-37")

module M = {
  let value = 1
}

let result = {
  open M
  2
}
