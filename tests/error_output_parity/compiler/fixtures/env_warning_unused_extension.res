// error-output-parity: Env emits warning 38 for an unused extension constructor.
module type S = {}

module M: S = {
  exception Unused
}
