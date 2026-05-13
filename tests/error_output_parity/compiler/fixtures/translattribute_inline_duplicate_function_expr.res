// error-output-parity: Translattribute warns when binding and function @inline both apply.
@inline
let f = @inline (x => x)
