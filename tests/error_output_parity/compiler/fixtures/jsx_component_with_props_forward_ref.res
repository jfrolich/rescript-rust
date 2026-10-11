// error-output-parity: JSX v4 rejects componentWithProps with React.forwardRef.
@react.componentWithProps
let make = React.forwardRef((~value, _ref) => value)
