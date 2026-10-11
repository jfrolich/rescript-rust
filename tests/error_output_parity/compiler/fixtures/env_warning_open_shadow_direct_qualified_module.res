// error-output-parity: qualified M.Item does not mark open M used or trigger warning 44.
@@warning("+33+44-32-34-37")

module Item = {
  let value = 1
}

module M = {
  module Item = {
    let value = 2
  }
}

open M

let result = M.Item.value
