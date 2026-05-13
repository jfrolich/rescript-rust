// error-output-parity: JSX v4 rejects duplicate @react.component prop names.
@react.component
let make = (~x, ~x) => React.null
