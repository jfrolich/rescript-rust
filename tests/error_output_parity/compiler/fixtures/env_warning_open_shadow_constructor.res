// error-output-parity: Env warning 45 for an open shadowing a later-used constructor.
@@warning("+45-34-37-41")

type first = Shared

module M = {
  type second = Shared
}

open M

let result = Shared
