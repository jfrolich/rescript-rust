// error-output-parity: Translattribute warns when binding @inline cannot apply to a module body.
@inline
module M = {
  let x = 1
}
