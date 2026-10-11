// error-output-parity: componentWithProps reports a destructured binding at the pattern.
@react.componentWithProps
let (a, b) = (_: props) => React.null
