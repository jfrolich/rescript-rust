// error-output-parity: Env warning 44 for reopening the same module and using the shadowing type.
@@warning("+44-34-37")

module M = {
  type item = int
}

open M

type before = item

open M

type result = item
