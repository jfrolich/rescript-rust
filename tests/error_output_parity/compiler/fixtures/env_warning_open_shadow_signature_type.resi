// error-output-parity: Env warning 44 for a signature open shadowing a later-used type.
@@warning("+44-34-37")

type item

module M: {
  type item
}

open M

type result = item
