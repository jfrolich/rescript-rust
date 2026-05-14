// error-output-parity: Env warning 45 for an open shadowing a later-used label.
@@warning("+45-34-37-41")

type first = {field: int}

module M = {
  type second = {field: int}
}

open M

let result = (value: second) => value.field
