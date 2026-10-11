// error-output-parity: JSX component duplicate props are rejected inside included structures.
include {
  @react.component
  let make = (~x, ~y, ~x, ~y) => React.null
}
