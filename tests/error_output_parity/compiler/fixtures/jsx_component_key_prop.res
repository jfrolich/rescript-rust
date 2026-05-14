// error-output-parity: JSX v4 rejects key props inside @react.component definitions.
@react.component
let make = (~key) => React.null
