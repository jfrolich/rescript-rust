// error-output-parity: qualified M.value does not mark open M used or trigger warning 44.
@@warning("+33+44-32-34-37")

let value = 1

module M = {
  let value = 2
}

open M

let result = M.value
