// error-output-parity: Warning 41 for an unqualified constructor shared by multiple visible variant types.
@@warning("+41-34-37-45")

type first = Shared

module M = {
  type second = Shared
}

open M

let result = Shared
