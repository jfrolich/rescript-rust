// error-output-parity: Open-shadow constructor warning precedes the ambiguous constructor warning.
@@warning("+41+45-34-37")

type first = Shared

module M = {
  type second = Shared
}

open M

let result = Shared
