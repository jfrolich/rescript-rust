// error-output-parity: Translattribute warns when module @inline is duplicated.
module F = @inline @inline () => {}
