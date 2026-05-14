// error-output-parity: JSX v4 only allows plain ref args in forwardRef components.
@react.component
let make = React.forwardRef((~value, (left, right)) => value)
