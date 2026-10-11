// error-output-parity: JSX component key props are rejected inside included structures.
include {
  @react.component
  let make = (~key) => React.null
}
