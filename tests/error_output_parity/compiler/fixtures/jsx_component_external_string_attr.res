// error-output-parity: JSX v4 rejects @string attributes in component externals.
@react.component
external make: (~kind: @string [#a]) => int = "make"
