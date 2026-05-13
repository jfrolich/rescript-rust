// error-output-parity: Translattribute warns when module @inlined is not on an apply target.
module M = @inlined {
  let x = 1
}
