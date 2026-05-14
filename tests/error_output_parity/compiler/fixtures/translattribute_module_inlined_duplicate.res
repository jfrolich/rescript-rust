// error-output-parity: Translattribute warns when module @inlined is duplicated on an apply target.
module F = () => {}
module M = (@inlined @inlined F)()
