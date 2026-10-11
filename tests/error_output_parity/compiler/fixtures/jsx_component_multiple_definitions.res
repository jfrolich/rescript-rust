// error-output-parity: JSX v4 rejects multiple @react.component definitions in one module.
@react.component
let make = () => React.null

@react.component
let make2 = () => React.null
