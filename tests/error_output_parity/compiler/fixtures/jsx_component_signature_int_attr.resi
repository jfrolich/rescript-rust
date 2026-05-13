// error-output-parity: JSX v4 rejects @int attributes in component signatures.
@react.component
let make: (~kind: @int [#a]) => int
