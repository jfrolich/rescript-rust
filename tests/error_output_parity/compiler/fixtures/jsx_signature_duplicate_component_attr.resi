// error-output-parity: JSX v4 rejects duplicate @react.component attributes in signatures.
@react.component
@react.component
let make: unit => React.element
