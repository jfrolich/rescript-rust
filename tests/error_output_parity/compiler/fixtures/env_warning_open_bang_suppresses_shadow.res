// error-output-parity: open! suppresses Env unused-open and open-shadow warnings.
@@warning("+33+44-32-34-37")

let value = 1

module M = {
  let value = 2
}

open! M

let result = value
