// error-output-parity: Translattribute warns when @inlined is duplicated on a call target.
let f = x => x
let x = (@inlined @inlined f)(1)
