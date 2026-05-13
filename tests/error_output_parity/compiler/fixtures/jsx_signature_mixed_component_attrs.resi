// error-output-parity: JSX signatures reject mixing component and componentWithProps.
@react.component
@react.componentWithProps
let make: unit => React.element
